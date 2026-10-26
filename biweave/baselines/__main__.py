"""Run an external method under common degree and strength constraints."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
from ..cli import unsigned
from ..routing import read_graph

ROOT = Path(__file__).resolve().parents[2]


def arguments():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument('--method', required=True, choices=('BiWES', 'Sirius', 'VaLUH-d', 'WGS', 'DG', 'EXACT'))
    for option in ('input', 'queries', 'output'):
        parser.add_argument('--' + option, type=Path, required=True)
    parser.add_argument('--seed', type=unsigned, required=True)
    parser.add_argument('--steps', type=unsigned, required=True)
    parser.add_argument('--burn-in', type=unsigned, required=True)
    parser.add_argument('--trace-every', type=unsigned, required=True)
    parser.add_argument('--check-every', type=unsigned, default=100000)
    args = parser.parse_args()
    if args.steps < 640 or args.steps % 640 or args.burn_in != args.steps // 5 or args.trace_every != args.steps // 640:
        parser.error('baseline observation requires steps divisible by 640, burn-in=steps/5, trace-every=steps/640')
    if args.method in ('WGS', 'DG') and args.seed > 2**53 - 1:
        parser.error('R adapters require an exactly representable integer seed below 2**53')
    if args.seed >= 2**32 and args.method == 'BiWES':
        parser.error('BiWES requires a uint32 seed')
    if not args.queries.is_file():
        parser.error('query file missing')
    if Path(str(args.output) + '.run.json').exists() or Path(str(args.output) + '.json').exists():
        parser.error('output prefix already exists')
    read_graph(args.input)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    return args


def biwes(args):
    from . import biwes_observer
    start = time.process_time()
    context, warmup = biwes_observer.warmup(str(args.input), str(args.queries), True)
    warmup_cpu = time.process_time() - start
    job = dict(input_path=str(args.input), queries_path=str(args.queries),
               outprefix=str(args.output), seed=args.seed, outer_budget=args.steps,
               burn_outer=args.burn_in, probe_trace_every=args.trace_every,
               check_every=args.check_every, batch_width=0,
               allpostburn_sigma_histogram=True)
    pid = os.fork()
    if pid == 0:
        try:
            result = biwes_observer.run_job(job, context)
            Path(str(args.output) + '.sampling_child.json').write_text(
                json.dumps({'status': result['status']}, indent=2) + '\n')
            os._exit(0 if result['status'] == 'completed' else 1)
        except BaseException:
            os._exit(1)
    _, status, usage = os.wait4(pid, 0)
    sampling_cpu = usage.ru_utime + usage.ru_stime
    Path(str(args.output) + '.cpu.json').write_text(json.dumps({
        'sampling_cpu_seconds': sampling_cpu, 'shared_warmup_cpu_seconds': warmup_cpu,
        'scope': 'complete sampling child includes graph setup, all attempts, observations, validation, and export; shared compilation is separate'
    }, indent=2) + '\n')
    if os.waitstatus_to_exitcode(status) != 0:
        raise ValueError('BiWES sampling child failed; inspect its result record')



def main():
    args = arguments()
    for variable in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
                     'NUMEXPR_NUM_THREADS', 'NUMBA_NUM_THREADS'):
        os.environ[variable] = '1'
    if args.method == 'BiWES':
        biwes(args)
        return
    common = ['--input', str(args.input), '--queries', str(args.queries),
              '--out', str(args.output), '--seed', str(args.seed),
              '--outer', str(args.steps), '--burn', str(args.burn_in),
              '--trace-every', str(args.trace_every), '--check-every', str(args.check_every)]
    if args.method in ('Sirius', 'VaLUH-d'):
        binary = ROOT / 'build' / ('sirius' if args.method == 'Sirius' else 'valuh')
        extra = ['--method', 'sirius_default_trace' if args.method == 'Sirius' else 'vaLUH_d_trace',
                 '--kill-denominator', '4', '--fixed-checkpoints', '0',
                 '--allpostburn-sigma-histogram', '1']
        command = [str(binary), *common, *extra]
    elif args.method == 'EXACT':
        command = [str(ROOT / 'build' / 'exact'), *common, '--matrix-type', '1',
                   '--orientation-rule', 'auto', '--memory-guard-bytes', '17179869184']
    else:
        rscript = shutil.which('Rscript')
        if not rscript:
            raise ValueError('Rscript is missing; install R and Rcpp')
        method = args.method.lower()
        if not (ROOT / 'build' / (method + '_loader.txt')).is_file():
            raise ValueError('adapter missing; follow the ' + method.upper() + ' build commands in README.md')
        command = [rscript, str(ROOT / 'biweave' / 'baselines' / 'run.R'), str(ROOT), method,
                   str(args.input.resolve()), str(args.queries.resolve()), str(args.output.resolve()),
                   str(args.seed), str(args.steps), str(args.burn_in), str(args.trace_every),
                   str(args.check_every)]
    if args.method in ('Sirius', 'VaLUH-d', 'EXACT') and not Path(command[0]).is_file():
        raise ValueError('baseline binary missing; build the selected adapter first')
    os.execv(command[0], command)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, UnicodeError) as error:
        raise SystemExit('Baseline: ' + str(error))
