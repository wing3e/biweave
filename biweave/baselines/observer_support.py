"""Deterministic invariant checks for the BiWES observer."""
from . import biwes_source

def _load_reference_wrapper():
    return biwes_source

HELPER_SOURCE = "@njit(cache=False)\ndef _check(A, row_strength, col_strength, row_degree, col_degree):\n    nr, nc = A.shape\n    for r in range(nr):\n        strength, degree = (np.int64(0), np.int64(0))\n        for c in range(nc):\n            w = A[r, c]\n            if w < 0:\n                raise ValueError('negative author weight')\n            strength += w\n            degree += w > 0\n        if strength != row_strength[r] or degree != row_degree[r]:\n            raise ValueError('author row margins changed')\n    for c in range(nc):\n        strength, degree = (np.int64(0), np.int64(0))\n        for r in range(nr):\n            strength += A[r, c]\n            degree += A[r, c] > 0\n        if strength != col_strength[c] or degree != col_degree[c]:\n            raise ValueError('author column margins changed')"
