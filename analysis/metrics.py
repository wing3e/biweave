"""Exact-reference metrics from post-burn-in observation counts."""
from fractions import Fraction
import json
import math
from pathlib import Path
import statistics


def read_queries(path):
    lines = Path(path).read_text().splitlines()
    tag, nr, nc, npairs, ncells = lines[0].split()
    if tag != 'fixed_probe_queries_v1':
        raise ValueError('unrecognized query format')
    nr, nc, npairs, ncells = map(int, (nr, nc, npairs, ncells))
    rows = [tuple(map(int, line.split())) for line in lines[1:] if line.strip()]
    if len(rows) != npairs + ncells or any(len(row) != 3 for row in rows):
        raise ValueError('query count or width mismatch')
    return nr, nc, rows[:npairs], rows[npairs:]


def load_truth(case, root):
    root = Path(root)
    oracle = json.loads((root / case['oracle']).read_text())
    nr, nc, pairs, cells = read_queries(root / case['queries'])
    if [nr, nc] != oracle['shape']:
        raise ValueError('oracle dimensions do not match queries')
    if oracle['row_pairs'] != [list(q[:2]) for q in pairs]:
        raise ValueError('oracle pair order mismatch')
    if oracle['observed_common_preference_thresholds'] != [q[2] for q in pairs]:
        raise ValueError('oracle pair thresholds mismatch')
    if 'Sigma_counts' in oracle and 'cell_presence_counts' in oracle:
        count = int(oracle['F_count'])
        sigma = {str(k): Fraction(v, count) for k, v in oracle['Sigma_counts'].items()}
        matrix = oracle['cell_presence_counts']
        if len(matrix) == nr and all(isinstance(r, list) for r in matrix):
            matrix = [x for row in matrix for x in row]
        if len(matrix) != nr * nc:
            raise ValueError('oracle cell count mismatch')
        cell_probabilities = [Fraction(matrix[i * nc + j], count) for i, j, _ in cells]
        tails = [Fraction(v, count) for v in oracle.get('pair_tail_counts', [])]
    else:
        sigma = {str(k): Fraction(v) for k, v in oracle['Sigma_probabilities'].items()}
        cell_probabilities = list(map(Fraction, oracle['cell_presence_probabilities']))
        tails = list(map(Fraction, oracle['pair_tail_probabilities']))
        if oracle['cell_coordinates'] != [list(q[:2]) for q in cells]:
            raise ValueError('oracle cell order mismatch')
    if sum(sigma.values()) != 1 or len(tails) != len(pairs):
        raise ValueError('invalid exact probability distribution')
    if len(cell_probabilities) != len(cells):
        raise ValueError('cell probability count mismatch')
    if any(not 0 <= p <= 1 for p in cell_probabilities + tails):
        raise ValueError('oracle probability outside [0, 1]')
    return dict(sigma=sigma, cells=cell_probabilities, tails=tails,
                pairs=pairs, cell_queries=cells)


def rmse(values):
    values = list(values)
    return math.sqrt(statistics.mean(x * x for x in values)) if values else None


def evaluate(truth, probe, histogram):
    denominator = int(probe['postburn_count'])
    if denominator <= 0 or histogram['postburn_count'] != denominator:
        raise ValueError('observation denominators differ or are empty')
    if sum(histogram['counts'].values()) != denominator:
        raise ValueError('histogram does not count every retained attempt')
    if len(probe['cells']) != len(truth['cells']) or len(probe['pairs']) != len(truth['tails']):
        raise ValueError('observation query count mismatch')
    if not set(histogram['counts']).issubset(truth['sigma']):
        raise ValueError('observed statistic lies outside exact support')
    errors, relative, tails, tail_relative = [], [], [], []
    for query, exact, coordinate in zip(probe['cells'], truth['cells'], truth['cell_queries']):
        if query['cell'] != list(coordinate[:2]) or query['observed_threshold'] != coordinate[2]:
            raise ValueError('observed cell query mismatch')
        count = query['presence_count']
        if not 0 <= count <= denominator:
            raise ValueError('invalid cell count')
        estimate = Fraction(count, denominator)
        errors.append(float(estimate - exact))
        if 0 < exact < 1:
            relative.append(float(estimate / exact - 1))
    false_flags, missed_flags = [], []
    for query, exact, coordinate in zip(probe['pairs'], truth['tails'], truth['pairs']):
        if query['rows'] != list(coordinate[:2]) or query['observed_threshold'] != coordinate[2]:
            raise ValueError('observed pair query mismatch')
        count = query['tail_count']
        if not 0 <= count <= denominator:
            raise ValueError('invalid pair-tail count')
        estimate = Fraction(count, denominator)
        if 0 < exact < 1:
            tails.append(float(estimate - exact))
            tail_relative.append(float(estimate / exact - 1))
            if exact > Fraction(1, 20):
                false_flags.append(estimate <= Fraction(1, 20))
            else:
                missed_flags.append(estimate > Fraction(1, 20))
    tv = sum(abs(Fraction(histogram['counts'].get(s, 0), denominator) - p)
             for s, p in truth['sigma'].items()) / 2
    informative_cells = [e for e, p in zip(errors, truth['cells']) if 0 < p < 1]
    return {
        'Sigma_PMF_TV_allouter': float(tv) if len(truth['sigma']) > 1 else None,
        'cell_presence_RMSE_all': rmse(errors),
        'cell_presence_RMSE_informative': rmse(informative_cells),
        'cell_presence_relative_RMSE_informative': rmse(relative),
        'pair_tail_RMSE_informative': rmse(tails),
        'pair_tail_relative_RMSE_informative': rmse(tail_relative),
        'false_rare_rate_alpha05': statistics.mean(false_flags) if false_flags else None,
        'missed_rare_rate_alpha05': statistics.mean(missed_flags) if missed_flags else None,
    }
