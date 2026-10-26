#!/usr/bin/env python3
"""Recompute terminal R-hat and ESS from the released five-chain traces.

Requires numpy and arviz. Uses the registered terminal round in each chain,
discards observations at or before one fifth of that round, and retains the
remaining saved observations without interpolation or truncation.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import gzip
import json
import math
from pathlib import Path
import warnings


ROOT = Path(__file__).resolve().parents[1]
FEATURES = ('weight_square_sum', 'overlap_sum', 'signed_cell_projection')


def load_observations(path, wanted):
    observations = {}
    with gzip.open(path, 'rt', encoding='ascii') as stream:
        for line in stream:
            row = json.loads(line)
            key = row['case_id'], row['method']
            if key in wanted:
                observations[key + (int(row['replicate']),)] = row['draws']
    return observations


def statistic(series, criteria, az, np):
    lengths = [len(chain) for chain in series]
    result = {'draws_per_chain': lengths}
    if len(set(lengths)) != 1:
        return dict(result, status='unequal_draw_counts')
    if not lengths or lengths[0] < criteria['minimum_draws_per_chain']:
        return dict(result, status='insufficient_draws')
    if any(len(set(chain)) < 2 for chain in series):
        return dict(result, status='constant_or_stuck_chain')
    offset = min(value for chain in series for value in chain)
    centered = [[value - offset for value in chain] for chain in series]
    if any(int(float(value)) != value for chain in centered for value in chain):
        return dict(result, status='integer_range_exceeds_lossless_float')
    posterior = az.from_dict(posterior={'value': np.asarray(centered, dtype=float)})
    with warnings.catch_warnings():
        warnings.simplefilter('ignore', RuntimeWarning)
        values = {
            'Rhat': float(az.rhat(posterior, method='rank')['value'].item()),
            'ESS_bulk': float(az.ess(posterior, method='bulk')['value'].item()),
            'ESS_tail': float(az.ess(posterior, method='tail')['value'].item()),
            'MCSE_mean': float(az.mcse(posterior, method='mean')['value'].item()),
        }
    if not all(math.isfinite(value) for value in values.values()):
        return dict(result, status='nonfinite_diagnostics')
    return dict(result, status='finite', integer_offset=str(offset), **values)


def recompute(protocol, observations, az, np):
    key = protocol['case_id'], protocol['method']
    result = {'case_id': key[0], 'method': key[1]}
    if sorted(chain['replicate'] for chain in protocol['chains']) != [1, 2, 3, 4, 5]:
        return dict(result, status='invalid_five_chain_registration', statistics={})
    selected = []
    burn = Fraction(protocol['prefix_burn_fraction'])
    for chain in sorted(protocol['chains'], key=lambda item: item['replicate']):
        draws = observations.get(key + (int(chain['replicate']),))
        stop = int(chain['N'])
        if not draws or not any(draw['iteration'] == stop for draw in draws):
            return dict(result, status='missing_terminal_observation', statistics={})
        selected.append([draw for draw in draws if burn * stop < draw['iteration'] <= stop])
    features = {}
    for feature in FEATURES:
        series = [[int(draw[feature]) for draw in chain] for chain in selected]
        features[feature] = statistic(series, protocol['criteria'], az, np)
    result['statistics'] = features
    if not all(row['status'] == 'finite' for row in features.values()):
        return dict(result, status='undefined_coordinate')
    result.update(status='finite', Rmax=max(row['Rhat'] for row in features.values()),
                  Bulk_min=min(row['ESS_bulk'] for row in features.values()),
                  Tail_min=min(row['ESS_tail'] for row in features.values()))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--case', action='append', help='Restrict to a released case ID; repeatable.')
    parser.add_argument('--method', action='append', help='Restrict to a method name; repeatable.')
    parser.add_argument('--limit', type=int, help='Process only the first matching groups.')
    parser.add_argument('--output', type=Path, default=Path('diagnostic_verification.json'))
    parser.add_argument('--check', action='store_true', help='Fail if recomputed finite coordinates disagree with released values.')
    args = parser.parse_args()
    try:
        import arviz as az
        import numpy as np
    except ImportError as exc:
        parser.exit(2, 'Install diagnostic dependencies with: python -m pip install numpy arviz\n')
    directory = args.root / 'results' / 'real'
    protocols = json.loads((directory / 'protocols.json').read_text())
    protocols = [row for row in protocols if (not args.case or row['case_id'] in args.case)
                 and (not args.method or row['method'] in args.method)]
    if args.limit is not None:
        if args.limit < 1:
            parser.error('--limit must be positive')
        protocols = protocols[:args.limit]
    if not protocols:
        parser.error('No diagnostic groups match the selected filters')
    wanted = {(row['case_id'], row['method']) for row in protocols}
    observations = load_observations(directory / 'observations.jsonl.gz', wanted)
    with (directory / 'finite_210_coordinates.csv').open(newline='') as stream:
        expected = {(row['case_id'], row['method']): row for row in csv.DictReader(stream)}
    results, mismatches = [], []
    for protocol in protocols:
        row = recompute(protocol, observations, az, np)
        saved = expected.get((row['case_id'], row['method']))
        row['saved_coordinate_available'] = saved is not None
        agrees = (row['status'] == 'finite') == (saved is not None)
        if agrees and saved:
            errors = {key: abs(row[key] - float(saved[key])) for key in ('Rmax', 'Bulk_min', 'Tail_min')}
            row['absolute_coordinate_differences'] = errors
            agrees = all(math.isclose(row[key], float(saved[key]), rel_tol=1e-10, abs_tol=1e-10)
                         for key in errors)
        row['matches_saved_coordinates'] = agrees
        if not agrees:
            mismatches.append({'case_id': row['case_id'], 'method': row['method'], 'status': row['status']})
        results.append(row)
    output = {'groups': len(results), 'finite_coordinates': sum(row['status'] == 'finite' for row in results),
              'mismatches': mismatches, 'all_match': not mismatches,
              'arviz_version': az.__version__, 'numpy_version': np.__version__, 'results': results}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, allow_nan=False) + '\n')
    print(json.dumps({key: output[key] for key in ('groups', 'finite_coordinates', 'all_match', 'mismatches')}, indent=2))
    if args.check and mismatches:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
