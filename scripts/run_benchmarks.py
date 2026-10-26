#!/usr/bin/env python3
"""Replay recorded round counts, with explicit parallelism and retained failures."""
import argparse
from concurrent.futures import ProcessPoolExecutor
import gzip
import json
from pathlib import Path
import resource
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def read_records(path):
    if path.suffix == '.gz':
        with gzip.open(path, 'rt') as stream:
            return [json.loads(line) for line in stream]
    return json.loads(path.read_text())


def plan(panel, method, replicates, limit):
    index = {c['case_id']: c for c in json.loads((ROOT / 'data/manifest.json').read_text())['cases']}
    if panel == 'real':
        jobs, accepted_cases = [], set()
        for protocol in json.loads((ROOT / 'results/real/protocols.json').read_text()):
            if protocol['method'] != method:
                continue
            cid = protocol['case_id']
            if limit and cid not in accepted_cases and len(accepted_cases) >= limit:
                continue
            accepted_cases.add(cid)
            for chain in protocol['chains']:
                if chain['replicate'] > replicates:
                    continue
                case = dict(index[cid], input=chain['initial_input'])
                jobs.append(dict(case=case, method=method, N=chain['N'], burn_in=chain['N'] // 5,
                                 seed_hex=chain['seed_hex'], replicate=chain['replicate'],
                                 ablation='none', trace_interval=max(1, chain['N'] // 640),
                                 check_interval=100000, target_CPU_seconds=480))
        return jobs
    if panel in ('ablation', 'selector'):
        source = ROOT / 'results' / panel / 'chains.json'
    else:
        source = ROOT / 'results' / ('decision' if panel == 'decision' else 'finite') / 'chains.jsonl.gz'
    jobs = []
    accepted_cases = set()
    for row in read_records(source):
        if panel not in ('ablation', 'selector', 'decision') and panel not in row['panels']:
            continue
        actual_method = row.get('method', 'BiWeave')
        if actual_method == 'Without guidance':
            actual_method = 'BiWeave'
        if actual_method != method or row['replicate'] > replicates:
            continue
        cid = row['case_id']
        if limit and cid not in accepted_cases and len(accepted_cases) >= limit:
            continue
        accepted_cases.add(cid)
        deletion = row.get('ablation', 'selector' if row.get('method') == 'Without guidance' else 'none')
        jobs.append(dict(case=index[cid], method=method, N=row['N'],
                         burn_in=row.get('burn_rounds', row.get('burn', row['N'] // 5)),
                         seed_hex=row['seed_hex'], replicate=row['replicate'], ablation=deletion,
                         histogram=panel == 'ablation',
                         trace_interval=row.get('trace_interval_rounds', max(1, row['N'] // 640)),
                         check_interval=row.get('constraint_check_interval_rounds') or 100000,
                         target_CPU_seconds=row.get('target_CPU_seconds', 2)))
    return jobs


def run(job):
    folder = Path(job.pop('output'))
    folder.mkdir(parents=True, exist_ok=False)
    prefix = folder / 'sample'
    case = job['case']
    if job['method'] == 'BiWeave':
        command = [sys.executable, '-B', '-m', 'biweave', 'sample', '--ablation', job['ablation']]
    else:
        command = [sys.executable, '-B', '-m', 'biweave.baselines', '--method', job['method']]
    command += ['--input', str(ROOT / case['input']), '--queries', str(ROOT / case['queries']),
                '--output', str(prefix), '--seed', job['seed_hex'], '--steps', str(job['N']),
                '--burn-in', str(job['burn_in']), '--trace-every', str(job['trace_interval']),
                '--check-every', str(job['check_interval'])]
    if job.get('histogram') and job['method'] == 'BiWeave':
        command.append('--histogram')
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    with (folder / 'stdout.txt').open('w') as out, (folder / 'stderr.txt').open('w') as err:
        process = subprocess.run(command, cwd=ROOT, stdout=out, stderr=err, check=False)
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    result = {k: v for k, v in job.items() if k != 'case'}
    result.update(case_id=case['case_id'], returncode=process.returncode,
                  cpu_seconds=(after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime),
                  status='complete' if process.returncode == 0 else 'failed')
    timing_path = Path(str(prefix) + '.cpu.json')
    if timing_path.exists():
        timing = json.loads(timing_path.read_text())
        if 'sampling_cpu_seconds' in timing:
            result['complete_process_cpu_seconds'] = result['cpu_seconds']
            result['cpu_seconds'] = timing['sampling_cpu_seconds']
            result['shared_warmup_cpu_seconds'] = timing.get('shared_warmup_cpu_seconds')
    (folder / 'execution.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--panel', choices=('synthetic', 'web', 'analytic', 'budget', 'decision', 'ablation', 'selector', 'real'), required=True)
    parser.add_argument('--method', default='BiWeave', choices=('BiWeave', 'BiWES', 'Sirius', 'VaLUH-d', 'WGS', 'DG', 'EXACT'))
    parser.add_argument('--replicates', type=int, default=5)
    parser.add_argument('--limit', type=int, default=0, help='maximum distinct inputs; zero selects the full panel')
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--output', type=Path, default=ROOT / 'output/benchmark')
    parser.add_argument('--execute', action='store_true', help='run the plan; otherwise report its size only')
    args = parser.parse_args()
    if args.jobs < 1 or args.replicates < 1 or args.limit < 0:
        parser.error('jobs and replicates must be positive; limit must be nonnegative')
    jobs = plan(args.panel, args.method, args.replicates, args.limit)
    for i, job in enumerate(jobs):
        job['output'] = str(args.output / ('task_' + str(i + 1).zfill(6)))
    print(json.dumps({'panel': args.panel, 'method': args.method, 'tasks': len(jobs),
                      'inputs': len({j['case']['case_id'] for j in jobs}), 'jobs': args.jobs,
                      'execute': args.execute}), flush=True)
    if not args.execute:
        return
    args.output.mkdir(parents=True, exist_ok=True)
    with ProcessPoolExecutor(max_workers=args.jobs) as pool, (args.output / 'results.jsonl').open('x') as stream:
        for result in pool.map(run, jobs, chunksize=1):
            stream.write(json.dumps(result, separators=(',', ':')) + '\n')
            stream.flush()


if __name__ == '__main__':
    main()
