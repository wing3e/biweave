"""Graph validation and routing from immutable degree and strength margins."""
from pathlib import Path
from collections import Counter
import hashlib
import re

I_MAX, INT_MAX, U_MAX = (1 << 63)-1, (1 << 31)-1, (1 << 64)-1
CERTIFICATE_PAIR_LOOKUP_LIMIT = 1000000
SIGNED_TOKEN = re.compile(rb"[+-]?[0-9]+\Z")
WHITESPACE = b" \t\n\r\v\f"
SPLIT_WHITESPACE = re.compile(rb"[ \t\n\r\v\f]+")

def require(value, message):
    if not value:
        raise ValueError(message)

def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()

def file_identity(path):
    s = Path(path).stat()
    return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns)

def read_graph(path):
    """Mirror positive nr/nc, edge, duplicate, int64 ledger and 2E+2 limits."""
    p = Path(path)
    require(p.is_file(), "input must be a regular graph file")
    before = file_identity(p)
    h = hashlib.sha256()
    def integers(stream):
        carry = b""
        for block in iter(lambda:stream.read(1 << 16), b""):
            h.update(block); joined = carry+block
            parts = SPLIT_WHITESPACE.split(joined)
            carry = parts.pop() if joined[-1] not in WHITESPACE else b""
            require(len(carry) <= 20, "graph integer token exceeds native range")
            for token in parts:
                if token:
                    require(len(token) <= 20 and SIGNED_TOKEN.fullmatch(token), "nondecimal/native-range graph token")
                    yield int(token)
        if carry:
            require(SIGNED_TOKEN.fullmatch(carry), "nondecimal graph token")
            yield int(carry)
    with p.open("rb") as stream:
        it = integers(stream)
        try:
            nr, nc = next(it), next(it)
        except StopIteration:
            raise ValueError("input needs positive nr nc header") from None
        require(1 <= nr <= INT_MAX and 1 <= nc <= INT_MAX and nr+nc <= INT_MAX-1,
                "native support-cap dimensions require positive int32 nr/nc and nr+nc<=INT_MAX-1")
        degree, strength = [0]*(nr+nc), [0]*(nr+nc)
        cells, total, edges = set(), 0, 0
        for r in it:
            try:
                c,w = next(it),next(it)
            except StopIteration:
                raise ValueError("malformed graph edge record") from None
            require(0 <= r < nr and 0 <= c < nc and 1 <= w <= I_MAX,
                    "invalid native edge coordinate or positive int64 weight")
            require((r,c) not in cells, "duplicate input edge")
            cells.add((r,c)); edges += 1; total += w
            require(total <= I_MAX, "native total input diagnostic mass exceeds int64")
            require(edges <= (INT_MAX-2)//2, "native support cap 2E+2 exceeds int index")
            degree[r] += 1; degree[nr+c] += 1
            strength[r] += w; strength[nr+c] += w
            require(strength[r] <= I_MAX and strength[nr+c] <= I_MAX,
                    "native node strength exceeds int64")
    require(file_identity(p) == before, "input changed while reading")
    return {"nr":nr, "nc":nc, "degree":degree, "strength":strength,
            "edge_count":edges, "total_input_weight":total,
            "input_SHA256":h.hexdigest(), "input_identity":before}

def forest_certificate(g):
    """Evaluate the sufficient margin certificate, including duplicate strengths.

    Python uses deterministic insertion order for leaf strengths. Native hash
    iteration can change lookup counts before refusal, but cannot change the
    boolean certificate: success examines the same finite complement tests;
    either a prohibited pair or exhausting the cap rejects matching-core.
    A refused certificate retains the ordinary exact branch.
    """
    nr, nc, degree, strength = g["nr"], g["nc"], g["degree"], g["strength"]
    sides = (degree[:nr], degree[nr:])
    weights = (strength[:nr], strength[nr:])
    lookups, limited, matching = 0, False, False
    if all(0 <= d <= 2 for d in degree):
        centers = [s.count(2) for s in sides]
        leaves = [s.count(1) for s in sides]
        leaf_weights = [Counter(w for d,w in zip(ds,ws) if d==1)
                        for ds,ws in zip(sides,weights)]
        candidate = (leaves[0] == centers[1] and leaves[1] == centers[0]
                     and not (leaf_weights[0].keys() & leaf_weights[1].keys()))
        matching = candidate
        if candidate:
            for axis in (0,1):
                opposite = leaf_weights[1-axis]
                for d,total in zip(sides[axis], weights[axis]):
                    if d != 2:
                        continue
                    for w,multiplicity in opposite.items():
                        if lookups >= CERTIFICATE_PAIR_LOOKUP_LIMIT:
                            limited, matching = True, False
                            break
                        lookups += 1
                        complement = total-w
                        if 0 < complement <= I_MAX and complement in opposite:
                            if w != complement or multiplicity >= 2:
                                matching = False
                                break
                    if not matching:
                        break
                if not matching:
                    break
    whole_leaf = [all(d <= 1 for d in sides[1-axis]) for axis in (0,1)]
    certified = [whole_leaf[axis] or matching for axis in (0,1)]
    counts = [sides[axis].count(2) if certified[axis] else 0 for axis in (0,1)]
    sizes = [min(4,n) for n in counts]
    axis_active = [certified[axis] and sizes[axis] >= 2 for axis in (0,1)]
    return {"matching_core_certificate":matching, "whole_leaf_axis_certificate":whole_leaf,
            "axis_certificate":certified, "eligible_object_count":counts, "k":sizes,
            "axis_active":axis_active, "FC_active":any(axis_active),
            "certificate_pair_lookups":lookups, "certificate_scan_limited":limited,
            "lookup_limit":CERTIFICATE_PAIR_LOOKUP_LIMIT,
            "lookup_order_scope":"The certificate depends only on preserved margins."}

def classify(g):
    cert = forest_certificate(g)
    nr = g["nr"]
    counts = [sum(d >= 2 for d in g["degree"][:nr]),
              sum(d >= 2 for d in g["degree"][nr:])]
    mode = "forest" if cert["FC_active"] else "joint" if min(counts) < 2 else "wt"
    return {"auto_mode":mode, "nonleaf_count":counts, "certificate":cert,
            "rule":"Certified record reassignment first; then acyclic joint updates; otherwise ordinary updates."}

def effective_joint(mode, classifier):
    if mode != "AUTO":
        return mode
    rows, columns = classifier["nonleaf_count"]
                                                                                            
                                                                             
    return "B" if columns == 1 and rows >= 3 else "L"
