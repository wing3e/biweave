from pathlib import Path

INT64_MAX = (1 << 63) - 1

def read_sparse(path):
    tokens = Path(path).read_text().split()
    if len(tokens) < 2 or (len(tokens)-2) % 3:
        raise ValueError("Malformed graph")
    nr, nc = map(int, tokens[:2])
    if min(nr, nc) < 1:
        raise ValueError("Positive graph dimensions required")
    edges = {}
    for i in range(2, len(tokens), 3):
        r, c, w = map(int, tokens[i:i+3])
        if not 0 <= r < nr or not 0 <= c < nc or not 0 < w <= INT64_MAX or (r, c) in edges:
            raise ValueError("Invalid graph edge")
        edges[r, c] = w
    if sum(edges.values()) > INT64_MAX:
        raise ValueError("Graph total exceeds int64")
    return nr, nc, edges

def load_queries(path, nr, nc, value):
    """value(r,c) reads ORIGINAL input; thresholds must match exactly."""
    tokens = Path(path).read_text().split()
    if len(tokens) < 5 or tokens[0] != "fixed_probe_queries_v1":
        raise ValueError("Invalid fixed query header")
    qr, qc, npair, ncell = map(int, tokens[1:5])
    if (qr, qc) != (nr, nc) or not 0 <= npair <= 64 or not 0 <= ncell <= 64 or npair+ncell == 0:
        raise ValueError("Invalid query shape/count")
    if len(tokens) != 5+3*(npair+ncell):
        raise ValueError("Truncated/extra query records")
    pairs, cells, seen = [], [], set()
    offset = 5
    for i in range(npair):
        r, s, threshold = map(int, tokens[offset:offset+3]); offset += 3
        if not 0 <= r < s < nr or (r, s) in seen or not 0 <= threshold <= INT64_MAX:
            raise ValueError("Invalid or duplicate pair")
        seen.add((r, s))
        if threshold != sum(min(int(value(r,c)), int(value(s,c))) for c in range(nc)):
            raise ValueError("Pair threshold differs from original input")
        pairs.append((r, s, threshold))
    seen = set()
    for i in range(ncell):
        r, c, threshold = map(int, tokens[offset:offset+3]); offset += 3
        if not 0 <= r < nr or not 0 <= c < nc or (r, c) in seen or not 0 <= threshold <= INT64_MAX:
            raise ValueError("Invalid or duplicate cell")
        seen.add((r, c))
        if threshold != int(value(r,c)):
            raise ValueError("Cell threshold differs from original input")
        cells.append((r, c, threshold))
    return pairs, cells

def write_queries(path, nr, nc, pair_labels, cell_labels, value):
    pairs = [(r,s,sum(min(int(value(r,c)),int(value(s,c))) for c in range(nc))) for r,s in pair_labels]
    cells = [(r,c,int(value(r,c))) for r,c in cell_labels]
    text = "\n".join(["fixed_probe_queries_v1", f"{nr} {nc}", f"{len(pairs)} {len(cells)}"] +
                     [f"{r} {s} {t}" for r,s,t in pairs] + [f"{r} {c} {t}" for r,c,t in cells])+"\n"
    target = Path(path)
    if target.exists():
        raise RuntimeError("Refusing to overwrite frozen queries")
    target.write_text(text)
    load_queries(target, nr, nc, value)
    return pairs, cells
