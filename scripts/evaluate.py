#!/usr/bin/env python3
"""Evaluate one sampler output prefix against an exact reference."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from analysis.metrics import evaluate, load_truth


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', required=True, help='case_id in data/manifest.json')
    parser.add_argument('--prefix', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    cases = json.loads((ROOT / 'data/manifest.json').read_text())['cases']
    case = next((c for c in cases if c['case_id'] == args.case), None)
    if case is None or 'oracle' not in case:
        parser.error('case has no exact reference')
    probe = json.loads(Path(str(args.prefix) + '.probe.json').read_text())
    histogram = json.loads(Path(str(args.prefix) + '.structure.hist.json').read_text())
    result = evaluate(load_truth(case, ROOT), probe, histogram)
    text = json.dumps(result, indent=2, allow_nan=False) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
