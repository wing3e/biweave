"""Load and verify an externally installed BiWES source tree."""
import hashlib
import importlib
from pathlib import Path
import sys
import types

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / 'external' / 'biwes'
SOURCE_COMMIT = '3a22fe9fc348935bdb2fa225f993cf7c48035211'
EXPECTED_SOURCE_SHA256 = {'scr/biwes/__init__.py': 'c597703a2c0e80992a6e7dce1882ced293ddec0fa5658feaa7ececc1729035fe', 'scr/biwes/config.py': 'a3cbca9c2ca34cc6a981b18a4f2c05704c179ccfb6473327849f1fc0f6cc1539', 'scr/biwes/core.py': '928b1f49e0db88b3ed4d6d75bb81953027838ac302ddb361e96b83a4f234fe33', 'scr/biwes/data_structures.py': '04097b50b9e43e4b40ef66bad62a0ce53be267053e4a0361cddcb18e74252526', 'scr/biwes/find_configurations.py': '36ee770d146297b555c56775673b5a660a8fa06bbff37f5d3e6c88fb7948b342', 'scr/biwes/moves.py': '39e6417bc16c703d9323ca402972095e4f3fd30745adbe200cdb11dc019449bd'}


def verify_source():
    expected = EXPECTED_SOURCE_SHA256
    for name, digest in expected.items():
        path = SOURCE / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError('BiWES source missing or changed; run scripts/fetch_baselines.py biwes')
    return expected


def load_author():
    verify_source()
    package = types.ModuleType('biwes')
    package.__path__ = [str(SOURCE / 'scr' / 'biwes')]
    sys.modules['biwes'] = package
    import numpy as np
    import numba
    core = importlib.import_module('biwes.core')

    @numba.njit
    def seed_rng(seed):
        np.random.seed(seed)

    return np, core, seed_rng


def load_graph(path, np):
    from ..routing import read_graph
    g = read_graph(path)
    matrix = np.zeros((g['nr'], g['nc']), dtype=np.int64)
    for line in Path(path).read_text().splitlines()[1:]:
        if line.strip():
            row, column, weight = map(int, line.split())
            matrix[row, column] = weight
    return matrix


def signature(matrix):
    return tuple(map(tuple, (matrix.sum(axis=1), matrix.sum(axis=0),
                            (matrix > 0).sum(axis=1), (matrix > 0).sum(axis=0))))
