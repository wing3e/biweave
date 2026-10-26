#!/usr/bin/env python3
"""Regenerate compact figures from the distributed numerical results."""
import argparse
from collections import defaultdict
import csv
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
METHODS = ['BiWES', 'Sirius', 'VaLUH-d', 'WGS', 'DG', 'EXACT', 'BiWeave']
COLORS = dict(zip(METHODS, ['#BC7453', '#B394C5', '#999999', '#E6AF45',
                          '#90AD7B', '#B79B81', '#2584A3']))
PDF_METADATA = {'Author': None, 'Creator': None, 'Producer': None,
                'CreationDate': None, 'ModDate': None}


def rows(path):
    with path.open(newline='') as stream:
        return list(csv.DictReader(stream))


def lines(ax, points, xkey, multiplier=1):
    groups = defaultdict(list)
    for row in points:
        if row.get('error') and row.get('complete', 'True') == 'True':
            groups[row['method']].append(row)
    for method in METHODS:
        points = sorted(groups[method], key=lambda p: float(p[xkey]))
        if not points:
            continue
        ax.plot([float(p[xkey]) for p in points],
                [multiplier * float(p['error']) for p in points],
                label=method, color=COLORS[method], marker='o',
                markersize=4 if method == 'BiWeave' else 2.6,
                linewidth=2.2 if method == 'BiWeave' else 1.1,
                zorder=10 if method == 'BiWeave' else 3)
    ax.grid(alpha=.15, linewidth=.6)
    ax.spines[['top', 'right']].set_visible(False)


def save(fig, path):
    fig.savefig(path, bbox_inches='tight', metadata=PDF_METADATA)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'output/figures')
    args = parser.parse_args()
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9,
                         'pdf.fonttype': 42, 'axes.labelsize': 9})
    args.output.mkdir(parents=True, exist_ok=True)
    budget = rows(ROOT / 'results/finite/budget_points.csv')
    fig, axes = plt.subplots(1, 3, figsize=(10.2, 2.8), constrained_layout=True)
    metrics = ['Sigma_PMF_TV_allouter', 'cell_presence_RMSE_all', 'pair_tail_RMSE_informative']
    labels = ['Null-distribution TV', 'Connection RMSE', 'Overlap-tail RMSE']
    for ax, metric, label in zip(axes, metrics, labels):
        selected = [p for p in budget if p['domain'].lower().startswith('web') and p['metric'] == metric]
        lines(ax, selected, 'CPU')
        ax.set(xscale='log', yscale='log', xlabel='Measured sampling CPU (s)', ylabel=label)
    axes[-1].legend(fontsize=7, frameon=False)
    save(fig, args.output / 'budget_accuracy.pdf')
    plt.close(fig)
    decision = rows(ROOT / 'results/decision/decision_points.csv')
    fig, axes = plt.subplots(1, 2, figsize=(7.2, 2.8), constrained_layout=True)
    for ax, metric, label in zip(axes, ['false_rare_rate_alpha05', 'missed_rare_rate_alpha05'],
                                 ['False flags (%)', 'Missed flags (%)']):
        selected = [p for p in decision if p['metric'] == metric and p.get('displayed') == 'True']
        lines(ax, selected, 'target_CPU_seconds', 100)
        ax.set(xlabel='Target CPU budget (s)', ylabel=label)
    axes[-1].legend(fontsize=7, frameon=False)
    save(fig, args.output / 'decision_accuracy.pdf')
    plt.close(fig)
    coordinates = rows(ROOT / 'results/real/finite_210_coordinates.csv')
    fig = plt.figure(figsize=(6.0, 4.5))
    ax = fig.add_subplot(projection='3d')
    for method in METHODS:
        selected = [p for p in coordinates if p['method'] == method]
        if not selected:
            continue
        ax.scatter([math.asinh((float(p['Rmax']) - 1) / .01) for p in selected],
                   [math.log10(float(p['Bulk_min'])) for p in selected],
                   [math.log10(float(p['Tail_min'])) for p in selected],
                   label=method, c=COLORS[method], alpha=.85,
                   s=27 if method == 'BiWeave' else 14, linewidth=.3, edgecolors='#555555')
    ax.set(xlabel='asinh((Rmax - 1) / 0.01)', ylabel='log10(Bulk ESS)', zlabel='log10(Tail ESS)')
    ax.invert_xaxis()
    ax.legend(fontsize=7, loc='upper left', frameon=False)
    save(fig, args.output / 'diagnostic_space.pdf')
    plt.close(fig)
    print('Three figures written to ' + str(args.output))


if __name__ == '__main__':
    main()
