#!/usr/bin/env python3
"""Recompute equal-graph summaries from the distributed chain records."""
import argparse
from collections import defaultdict
import csv
import gzip
import json
import math
from pathlib import Path
import statistics

ROOT = Path(__file__).resolve().parents[1]
METHODS = ['BiWES', 'Sirius', 'VaLUH-d', 'WGS', 'DG', 'EXACT', 'BiWeave']
COMMON = ['Sigma_PMF_TV_allouter', 'cell_presence_RMSE_all', 'pair_tail_RMSE_informative']
RELATIVE = ['Sigma_PMF_TV_allouter', 'cell_presence_relative_RMSE_informative',
            'pair_tail_relative_RMSE_informative']


def records(path):
    with gzip.open(path, 'rt', encoding='ascii') as stream:
        for line in stream:
            yield json.loads(line)


def finite_number(value):
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(value)


def write_csv(path, rows):
    if not rows:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def summarize_main(root):
    groups = defaultdict(list)
    counts = defaultdict(int)
    complete = defaultdict(set)
    for row in records(root / 'results/finite/chains.jsonl.gz'):
        for panel in row['panels']:
            if panel in ('synthetic', 'web', 'analytic'):
                groups[(panel, row['method'], row['case_id'])].append(row)
    graph_means = defaultdict(list)
    for (panel, method, case), rows in groups.items():
        accepted = [r for r in rows if r['analysis_status'] == 'PASS']
        counts[(panel, method)] += len(accepted)
        if len(accepted) == 5:
            complete[(panel, method)].add(case)
        for metric in RELATIVE if panel == 'analytic' else COMMON:
            values = [r[metric] for r in accepted if finite_number(r.get(metric))]
            if values:
                graph_means[(panel, method, metric)].append(statistics.mean(values))
    rows = []
    expected = {'synthetic': 1000, 'web': 180, 'analytic': 90}
    for panel in expected:
        metrics = RELATIVE if panel == 'analytic' else COMMON
        for method in METHODS:
            for metric in metrics:
                values = graph_means[(panel, method, metric)]
                rows.append(dict(panel=panel, method=method, metric=metric,
                                 mean=statistics.mean(values) if values else None,
                                 graph_sd=statistics.stdev(values) if len(values) > 1 else None,
                                 applicable_graphs=len(values), registered_graphs=expected[panel],
                                 completed_chains=counts[(panel, method)],
                                 complete_graphs=len(complete[(panel, method)]),
                                 complete_panel=counts[(panel, method)] == 5 * expected[panel]))
    return rows


def summarize_decisions(root):
    groups = defaultdict(list)
    for row in records(root / 'results/decision/chains.jsonl.gz'):
        if row['analysis_status'] != 'PASS':
            continue
        for metric in ('false_rare_rate_alpha05', 'missed_rare_rate_alpha05'):
            if finite_number(row.get(metric)):
                groups[(row['method'], row['target_CPU_seconds'], metric, row['case_id'])].append(row[metric])
    method_groups = defaultdict(list)
    for (method, budget, metric, case), values in groups.items():
        method_groups[(method, budget, metric)].append(statistics.mean(values))
    return [dict(method=method, target_CPU_seconds=budget, metric=metric,
                 mean=statistics.mean(values), applicable_graphs=len(values))
            for (method, budget, metric), values in sorted(method_groups.items())]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'output/tables')
    args = parser.parse_args()
    rows = summarize_main(ROOT)
    write_csv(args.output / 'main.csv', rows)
    write_csv(args.output / 'decisions.csv', summarize_decisions(ROOT))
    print('Main summaries: ' + str(len(rows)))
    print('Tables written to ' + str(args.output))


if __name__ == '__main__':
    main()
