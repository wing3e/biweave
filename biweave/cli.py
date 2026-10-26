"""Single-process sampling with immutable-margin routing and functional ablations."""
import argparse
import json
import os
from pathlib import Path
import sys
from . import routing

ROOT = Path(__file__).resolve().parent


def unsigned(value):
    try:
        number = int(value, 16 if value.lower().startswith('0x') else 10)
    except ValueError as error:
        raise argparse.ArgumentTypeError('expected a decimal or hexadecimal integer') from error
    if not 0 <= number <= routing.U_MAX:
        raise argparse.ArgumentTypeError('integer must fit uint64')
    return number


def set_flag(flags, key, value):
    if key not in flags:
        raise ValueError('missing native option: ' + key)
    flags[key] = str(value)


def make_command(args):
    graph = routing.read_graph(args.input)
    classifier = routing.classify(graph)
    mode = classifier['auto_mode']
    joint = routing.effective_joint('AUTO', classifier)
    name = 'joint_' + joint if mode == 'joint' else mode
    presets = json.loads((ROOT / 'presets.json').read_text())
    preset = presets[name]
    flags = dict(preset['flags'])
    # The joint acyclic route uses one switching attempt. Other routes use
    # the degree-derived batch. These choices are fixed before sampling.
    flags['--global-equal-weight-switch'] = '1'
    flags['--global-degree-work-batch'] = '0' if mode == 'joint' else '1'
    flags['--global-representation-work-batch'] = '0'
    if args.ablation == 'local':
        set_flag(flags, '--ablation-module', 'local')
        set_flag(flags, '--cycle-compose', 0)
        set_flag(flags, '--capacity-cycle', 0)
        if mode == 'wt':
            set_flag(flags, '--local-surplus-selector', 0)
    elif args.ablation == 'exchange':
        set_flag(flags, '--global-equal-weight-switch', 0)
        set_flag(flags, '--global-degree-work-batch', 0)
        set_flag(flags, '--global-representation-work-batch', 0)
    elif args.ablation == 'coverage':
        set_flag(flags, '--coverage-compose', 0)
        set_flag(flags, '--coverage-bp', 0)
        if mode == 'forest':
            set_flag(flags, '--forest-update', 0)
    elif args.ablation == 'selector' and mode == 'wt':
        set_flag(flags, '--local-surplus-selector', 0)
    run = {
        '--input': str(args.input), '--queries': str(args.queries),
        '--out': str(args.output), '--seed': str(args.seed),
        '--outer': str(args.steps), '--burn': str(args.burn_in),
        '--trace-every': str(args.trace_every),
        '--check-every': str(args.check_every),
        '--histogram': str(int(args.histogram)),
        '--analysis-cpu-millis': '0', '--analysis-cpu-check': '256',
    }
    flags.update(run)
    binary = ROOT.parent / 'build' / preset['binary']
    if not binary.is_file():
        raise ValueError('native sampler missing; follow the build commands in README.md')
    if routing.file_identity(args.input) != graph['input_identity']:
        raise ValueError('input changed while preparing the sampler')
    argv = [str(binary), *[item for pair in flags.items() for item in pair]]
    return argv, graph, classifier, preset['binary']


def sample(args):
    if not 0 <= args.burn_in < args.steps:
        raise ValueError('steps must exceed a nonnegative burn-in')
    if args.trace_every <= 0 or args.check_every <= 0:
        raise ValueError('trace and validation intervals must be positive')
    if not args.queries.is_file():
        raise ValueError('query file missing')
    if Path(str(args.output) + '.run.json').exists():
        raise ValueError('output prefix already exists')
    argv, graph, classifier, branch = make_command(args)
    if args.prepare_only:
        print(json.dumps({'branch': branch, 'ablation': args.ablation,
                          'native_arguments': argv[1:]}, indent=2))
        return
    args.output.parent.mkdir(parents=True, exist_ok=True)
    receipt = {
        'method': 'BiWeave', 'branch': branch, 'ablation': args.ablation,
        'input_sha256': graph['input_SHA256'],
        'native_sha256': routing.digest(argv[0]),
        'shape': [graph['nr'], graph['nc']], 'seed_hex': hex(args.seed),
        'steps': args.steps, 'burn_in': args.burn_in,
        'target_degrees': graph['degree'], 'target_strengths': graph['strength'],
        'nonleaf_count': classifier['nonleaf_count'],
    }
    with Path(str(args.output) + '.dispatch.json').open('x') as stream:
        json.dump(receipt, stream, indent=2)
        stream.write('\n')
    for variable in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
                     'NUMEXPR_NUM_THREADS', 'NUMBA_NUM_THREADS'):
        os.environ[variable] = '1'
    os.execv(argv[0], argv)


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    subparsers = parser.add_subparsers(dest='command', required=True)
    command = subparsers.add_parser('sample', help='sample with fixed degrees and strengths')
    for option in ('input', 'queries', 'output'):
        command.add_argument('--' + option, type=Path, required=True)
    command.add_argument('--seed', type=unsigned, default=0)
    command.add_argument('--steps', type=unsigned, default=6400)
    command.add_argument('--burn-in', type=unsigned, default=1280)
    command.add_argument('--trace-every', type=unsigned, default=10)
    command.add_argument('--check-every', type=unsigned, default=256)
    command.add_argument('--histogram', action='store_true', help='also count full matrix states')
    command.add_argument('--ablation', choices=('none', 'local', 'exchange', 'coverage', 'selector'), default='none')
    command.add_argument('--prepare-only', action='store_true')
    try:
        args = parser.parse_args()
        sample(args)
    except (ValueError, OSError, UnicodeError) as error:
        parser.exit(2, 'BiWeave: ' + str(error) + '\n')
