from collections import defaultdict
from operator import index

def _integer(value):

    try:
        return index(value)
    except TypeError as exc:
        raise AssertionError("Noninteger matrix weight or sparse index") from exc

def index_check(a, wd, wd2, al, al2, uw, uw2):
    if getattr(a, "ndim", None) != 2 or min(a.shape) < 1:
        raise AssertionError("Expected positive two-dimensional matrix")
    nr, nc = a.shape
    nodes = set(range(nr + nc))
    if set(map(_integer, al.keys())) != nodes or set(map(_integer, al2.keys())) != nodes or len(al) != len(nodes) or len(al2) != len(nodes):
        raise AssertionError("Adjacency map node coverage")

    rows, cols = a.nonzero()
    actual_neighbors = [set() for _ in range(nr + nc)]
    actual_weight_edges = defaultdict(set)
    for r0, c0 in zip(rows, cols):
        r, c = _integer(r0), _integer(c0)
        w = _integer(a[r, c])
        if w <= 0 or a[r, c] != w:
            raise AssertionError("Nonpositive or noninteger indexed weight")
        neighbor = nr + c
        actual_neighbors[r].add(neighbor)
        actual_neighbors[neighbor].add(r)
        actual_weight_edges[w].add((r, neighbor))

    adjacency_entries = 0
    for node in range(nr + nc):
        neighbors = [_integer(x) for x in al2[node]]
        if len(neighbors) != len(set(neighbors)) or set(neighbors) != actual_neighbors[node]:
            raise AssertionError("Adjacency list duplicate, omission or mismatch")
        positions = al[node]
        if len(positions) != len(neighbors) or set(map(_integer, positions.keys())) != set(neighbors):
            raise AssertionError("Complement adjacency coverage")
        for pos, neighbor in enumerate(neighbors):
            if _integer(positions[neighbor]) != pos:
                raise AssertionError("Complement adjacency position")
        adjacency_entries += len(neighbors)
    if adjacency_entries != 2 * len(rows):
        raise AssertionError("Adjacency edge count")

    weights = [_integer(x) for x in uw2]
    actual_weights = set(actual_weight_edges)
    if len(weights) != len(set(weights)) or set(weights) != actual_weights:
        raise AssertionError("Unique weight list duplicate, omission or mismatch")
    for mapping in (uw, wd, wd2):
        if len(mapping) != len(actual_weights) or set(map(_integer, mapping.keys())) != actual_weights:
            raise AssertionError("Weight dictionary coverage")
    grouped_edges = 0
    for pos, w in enumerate(weights):
        if _integer(uw[w]) != pos:
            raise AssertionError("Unique weight position")
        edges = [(_integer(r), _integer(c)) for r, c in wd2[w]]
        expected = actual_weight_edges[w]
        if len(edges) != len(set(edges)) or set(edges) != expected:
            raise AssertionError("Weight edge list duplicate, omission or mismatch")
        positions = wd[w]
        if len(positions) != len(edges) or set((_integer(r), _integer(c)) for r, c in positions.keys()) != expected:
            raise AssertionError("Complement weight edge coverage")
        for k, edge in enumerate(edges):
            if _integer(positions[edge]) != k:
                raise AssertionError("Complement weight edge position")
        grouped_edges += len(edges)
    if grouped_edges != len(rows):
        raise AssertionError("Weight groups omit positive edges")
