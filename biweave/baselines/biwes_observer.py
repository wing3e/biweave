from __future__ import annotations
import ast
import copy
import csv
import hashlib
import json
from pathlib import Path
import resource
import time
import traceback
from . import observer_support as original_observer
from .query_io import INT64_MAX, load_queries
from .index_validation import index_check as linear_index_check

HERE = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

HELPER_SOURCE = '''
@njit(cache=False)
def _probe_values(A, al2, pairs, cell_labels, minimum, weights):
    nr = A.shape[0]
    for i in range(len(pairs)):
        r, s = pairs[i,0], pairs[i,1]
        small, other = r, s
        if len(al2[r]) > len(al2[s]):
            small, other = s, r
        total = np.int64(0)
        for neighbor in al2[small]:
            c = neighbor - nr
            total += min(A[small,c], A[other,c])
        minimum[i] = total
    for i in range(len(cell_labels)):
        weights[i] = A[cell_labels[i,0],cell_labels[i,1]]

@njit(cache=False)
def _probe_flush(stats, cached_min, cached_weights, thresholds, cell_thresholds,
                 tails, min_sums, presence, cell_tails, weight_sums,
                 batch_index, batch_counts, batch_tails, batch_sums,
                 batch_presence, batch_cell_tails, batch_weight_sums):
    pending = stats[1]
    if pending == 0:
        return
    for i in range(len(cached_min)):
        tail = pending if cached_min[i] >= thresholds[i] else 0
        value_sum = cached_min[i] * pending
        tails[i] += tail
        min_sums[i] += value_sum
        if batch_index >= 0:
            batch_tails[batch_index,i] += tail
            batch_sums[batch_index,i] += value_sum
    for i in range(len(cached_weights)):
        positive = pending if cached_weights[i] > 0 else 0
        tail = pending if cached_weights[i] >= cell_thresholds[i] else 0
        value_sum = cached_weights[i] * pending
        presence[i] += positive
        cell_tails[i] += tail
        weight_sums[i] += value_sum
        if batch_index >= 0:
            batch_presence[batch_index,i] += positive
            batch_cell_tails[batch_index,i] += tail
            batch_weight_sums[batch_index,i] += value_sum
    if batch_index >= 0:
        batch_counts[batch_index] += pending
    stats[1] = 0
    stats[3] += 1

@njit(cache=False)
def _probe_observe(A, al2, t, burn, batch_width, pairs, cell_labels,
                   thresholds, cell_thresholds, current_min, current_weights,
                   cached_min, cached_weights, tails, min_sums, presence,
                   cell_tails, weight_sums, stats, batch_counts, batch_tails,
                   batch_sums, batch_presence, batch_cell_tails, batch_weight_sums):
    _probe_values(A, al2, pairs, cell_labels, current_min, current_weights)
    same = stats[0] != 0
    for i in range(len(current_min)):
        if current_min[i] != cached_min[i]:
            same = False
    for i in range(len(current_weights)):
        if current_weights[i] != cached_weights[i]:
            same = False
    batch_index = (t-burn-1)//batch_width if batch_width else -1
    if not same:
        _probe_flush(stats, cached_min, cached_weights, thresholds, cell_thresholds,
                     tails, min_sums, presence, cell_tails, weight_sums,
                     batch_index, batch_counts, batch_tails, batch_sums,
                     batch_presence, batch_cell_tails, batch_weight_sums)
        for i in range(len(current_min)):
            cached_min[i] = current_min[i]
        for i in range(len(current_weights)):
            cached_weights[i] = current_weights[i]
        stats[0] = 1
        stats[2] += 1
    else:
        stats[4] += 1
    stats[1] += 1
    stats[5] += 1
    if batch_width and (t-burn)%batch_width == 0:
        _probe_flush(stats, cached_min, cached_weights, thresholds, cell_thresholds,
                     tails, min_sums, presence, cell_tails, weight_sums,
                     batch_index, batch_counts, batch_tails, batch_sums,
                     batch_presence, batch_cell_tails, batch_weight_sums)

@njit(cache=False)
def _probe_trace(A, al2, t, index, pairs, cell_labels, trace_iterations,
                 trace_min, trace_weights, debug_flat):
    _probe_values(A, al2, pairs, cell_labels, trace_min[index], trace_weights[index])
    trace_iterations[index] = t
    if debug_flat.shape[0]:
        nr, nc = A.shape
        for r in range(nr):
            for c in range(nc):
                debug_flat[index,r*nc+c] = A[r,c]
'''

HELPER_SOURCE += '\n@njit(cache=False)\ndef _star_sigma_record(A, al2, hub, fixed_leaf, row_strength, col_strength, row_degree, col_degree,\n                       scratch_strength, scratch_degree, trace_sigma, index):\n    nr,nc=A.shape\n    for c in range(nc):\n        scratch_strength[c]=0\n        scratch_degree[c]=0\n    sigma=np.int64(0)\n    for r in range(nr):\n        if len(al2[r])!=row_degree[r]:\n            raise ValueError("generic Sigma observer row degree changed")\n        strength=np.int64(0)\n        for label in al2[r]:\n            c=label-nr\n            if c<0 or c>=nc or A[r,c]<=0:\n                raise ValueError("generic Sigma observer invalid adjacency")\n            w=A[r,c]\n            sigma+=w*w\n            strength+=w\n            scratch_strength[c]+=w\n            scratch_degree[c]+=1\n        if strength!=row_strength[r]:\n            raise ValueError("generic Sigma observer row strength changed")\n    for c in range(nc):\n        if scratch_strength[c]!=col_strength[c] or scratch_degree[c]!=col_degree[c]:\n            raise ValueError("generic Sigma observer column margins changed")\n    trace_sigma[index]=sigma\n'

ALLPOSTBURN_SIGMA_HELPER_SOURCE = """
@njit(cache=False)
def _sigma_update_modified_weights(sigma_cache, old_weights, new_weights):
    sigma = sigma_cache[0]
    # Subtract all old distinct positive edges before adding new edges.
    for weight in old_weights:
        sigma -= weight * weight
    for weight in new_weights:
        sigma += weight * weight
    sigma_cache[0] = sigma

@njit(cache=False)
def _sigma_from_weight_groups(weight_dict2):
    sigma = np.int64(0)
    for weight in weight_dict2:
        if weight <= 0:
            raise ValueError("Positive author weight group required")
        sigma += weight * weight * np.int64(len(weight_dict2[weight]))
    return sigma

@njit(cache=False)
def _sigma_histogram_record(sigma_cache, sigma_histogram):
    sigma = sigma_cache[0]
    sigma_histogram[sigma] = sigma_histogram.get(sigma, np.int64(0)) + np.int64(1)
"""

def _generate_source(allpostburn_sigma_histogram=False):
    if type(allpostburn_sigma_histogram) is not bool:
        raise ValueError("allpostburn_sigma_histogram must be bool")
    helper = original_observer._load_reference_wrapper()
    source = (helper.SOURCE/"scr/biwes/core.py").read_text()
    tree = ast.parse(source)
    original = next(x for x in tree.body if isinstance(x, ast.FunctionDef) and x.name=="BiWES2")
    loops = [x for x in original.body if isinstance(x, ast.For)]
    if len(loops)!=1 or ast.unparse(loops[0].iter)!="range(n_iterations)":
        raise RuntimeError("Unknown original loop")
    loop = loops[0]
    if any(isinstance(x,(ast.Break,ast.Continue,ast.Return)) for x in ast.walk(loop)):
        raise RuntimeError("Original loop control flow unsupported")
    instrumented = copy.deepcopy(original)
    instrumented.name = "instrumented_probe_BiWES2"
    instrumented.decorator_list = ast.parse("@njit(cache=False)\ndef x(): pass").body[0].decorator_list
    extra = ("burn_outer trace_every check_every batch_width pair_rows cell_labels thresholds cell_thresholds "
             "current_min current_weights cached_min cached_weights tails min_sums presence cell_tails weight_sums "
             "stats batch_counts batch_tails batch_sums batch_presence batch_cell_tails batch_weight_sums "
             "trace_iterations trace_min trace_weights debug_flat row_strength col_strength row_degree col_degree star_hub star_fixed_leaf star_scratch_strength star_scratch_degree star_trace_sigma").split()
    if allpostburn_sigma_histogram:
        extra.extend(["sigma_histogram", "sigma_cache"])
    instrumented.args.args.extend(ast.arg(arg=name) for name in extra)
    new_loop = next(x for x in instrumented.body if isinstance(x,ast.For))
    original_dump = ast.dump(loop,include_attributes=False)
    prefix_length = len(new_loop.body)
    new_loop.body.extend(ast.parse('''
t = it + 1
if t > burn_outer:
    _probe_observe(A2, adj_list2, t, burn_outer, batch_width, pair_rows, cell_labels,
                   thresholds, cell_thresholds, current_min, current_weights,
                   cached_min, cached_weights, tails, min_sums, presence,
                   cell_tails, weight_sums, stats, batch_counts, batch_tails,
                   batch_sums, batch_presence, batch_cell_tails, batch_weight_sums)
if check_every > 0 and t % check_every == 0:
    _check(A2, row_strength, col_strength, row_degree, col_degree)
if trace_every > 0 and (t % trace_every == 0 or t == n_iterations):
    _probe_trace(A2, adj_list2, t, trace_count, pair_rows, cell_labels,
                 trace_iterations, trace_min, trace_weights, debug_flat)
    _star_sigma_record(A2, adj_list2, star_hub, star_fixed_leaf, row_strength, col_strength, row_degree, col_degree, star_scratch_strength, star_scratch_degree, star_trace_sigma, trace_count)
    trace_count += 1
''').body)
    if allpostburn_sigma_histogram:
        new_loop.body.extend(ast.parse("if t > burn_outer:\n    _sigma_histogram_record(sigma_cache, sigma_histogram)\n").body)
    prefix = copy.deepcopy(new_loop); prefix.body = prefix.body[:prefix_length]
    if ast.dump(prefix,include_attributes=False)!=original_dump:
        raise AssertionError("Original author loop prefix changed")
    observed_move_source = ""
    if allpostburn_sigma_histogram:
        move_names = {"weight_shuffling", "simple_edge_swap", "bridge_edge_swap"}
        move_tree = ast.parse((helper.SOURCE/"scr/biwes/moves.py").read_text())
        class AddSigmaHook(ast.NodeTransformer):
            def visit_Assign(self, node):
                node = self.generic_visit(node)
                if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == "update_weight_dict":
                    args = node.value.args
                    if len(args) != 8:
                        raise RuntimeError("Unknown author update_weight_dict arity")
                    hook = ast.Expr(value=ast.Call(func=ast.Name(id="_sigma_update_modified_weights",ctx=ast.Load()),args=[ast.Name(id="sigma_cache",ctx=ast.Load()),copy.deepcopy(args[4]),copy.deepcopy(args[5])],keywords=[]))
                    return [hook,node]
                return node
        observed_moves=[]
        for node in move_tree.body:
            if isinstance(node,ast.FunctionDef) and node.name in move_names:
                func=copy.deepcopy(node);func.name="_sigma_"+func.name
                func.decorator_list=ast.parse("@njit(cache=False)\ndef f(): pass").body[0].decorator_list
                func.args.args.append(ast.arg(arg="sigma_cache"))
                func=AddSigmaHook().visit(func);ast.fix_missing_locations(func);observed_moves.append(func)
        if len(observed_moves)!=3:
            raise RuntimeError("Expected three author moves")
        for node in ast.walk(new_loop):
            if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id in move_names:
                node.func.id="_sigma_"+node.func.id;node.args.append(ast.Name(id="sigma_cache",ctx=ast.Load()))
        observed_move_source="\n".join(ast.unparse(f)for f in observed_moves)+"\n"
        instrumented.body.insert(instrumented.body.index(new_loop),ast.parse("sigma_cache[0] = _sigma_from_weight_groups(weight_dict2)").body[0])
    index = instrumented.body.index(new_loop)
    instrumented.body[index:index] = ast.parse('''
trace_count = 0
if trace_every > 0:
    _probe_trace(A2, adj_list2, 0, 0, pair_rows, cell_labels,
                 trace_iterations, trace_min, trace_weights, debug_flat)
    _star_sigma_record(A2, adj_list2, star_hub, star_fixed_leaf, row_strength, col_strength, row_degree, col_degree, star_scratch_strength, star_scratch_degree, star_trace_sigma, 0)
    trace_count = 1
''').body
    if not isinstance(instrumented.body[-1],ast.Return) or ast.unparse(instrumented.body[-1].value)!="A2":
        raise RuntimeError("Unknown author return")
    instrumented.body[-1:] = ast.parse('''
batch_index = (n_iterations-burn_outer-1)//batch_width if batch_width else -1
_probe_flush(stats, cached_min, cached_weights, thresholds, cell_thresholds,
             tails, min_sums, presence, cell_tails, weight_sums,
             batch_index, batch_counts, batch_tails, batch_sums,
             batch_presence, batch_cell_tails, batch_weight_sums)
_check(A2, row_strength, col_strength, row_degree, col_degree)
return A2, weight_dict, weight_dict2, adj_list, adj_list2, unique_weights, unique_weights2, trace_count
''').body
    ast.fix_missing_locations(instrumented)
    check = next(x for x in ast.parse(original_observer.HELPER_SOURCE).body if isinstance(x,ast.FunctionDef) and x.name=="_check")
    observer_helpers = HELPER_SOURCE + (ALLPOSTBURN_SIGMA_HELPER_SOURCE if allpostburn_sigma_histogram else "")
    generated = observer_helpers+"\n"+(observed_move_source+"\n" if allpostburn_sigma_histogram else "")+ast.unparse(check)+"\n"+ast.unparse(instrumented)+"\n"
    provenance = dict(source_commit=helper.SOURCE_COMMIT,source_sha256=helper.verify_source(),
        original_loop_ast_sha256=hashlib.sha256(original_dump.encode()).hexdigest(),
        generated_source_sha256=hashlib.sha256(generated.encode()).hexdigest(),wrapper_sha256=sha(__file__),
        original_observer_dependency_sha256=sha(original_observer.__file__),
        query_parser_sha256=sha(HERE/"query_io.py"),loop_prefix_identical=True,
        sampler_modifications="none; fixed read-only probe/periodic check statements appended after complete original loop body",
        idle_policy="Original author has no update version; evaluate sparse query features each postburn step and exactly compress equal feature vectors; all holds counted")
    provenance.update(final_index_validator_sha256=sha(HERE/"index_validation.py"),
        final_index_validator_policy="One dense ndarray.nonzero call, then exact O(m+nr+nc+K) positive-edge/adjacency/weight/position checks; read-only/no RNG; previous wrapper cost O(K*nr*nc) removed, not sampler acceleration",
        base_wrapper_sha256=sha(__file__))
    if allpostburn_sigma_histogram:
        provenance.update(loop_prefix_identical_after_stripping_sigma_hooks=True,loop_prefix_identical=False,
            sampler_modifications="deterministic Sigma observer hooks in AST-cloned three author moves; strip hook/extra cache args restores author AST; no RNG or probability changes",
            observer_policy="One exact weight-group initialization; subtract old modified-edge squares then add new; all postburn macro histogram from cache; no sum of Sigma over time in int64")
    dest = HERE/("generated_sigma" if allpostburn_sigma_histogram else "generated_generic");dest.mkdir(exist_ok=True)
    path = dest/"observed_biwes.py"
    if path.exists() and path.read_text()!=generated:
        raise RuntimeError("Refusing to change generated author probe source")
    path.write_text(generated)
    return helper,generated,path,provenance

def _buffers(context, a0, n, burn, queries_path, batch_width, trace_every, debug_matrix_trace=False, allpostburn_sigma_histogram=False):
    if type(allpostburn_sigma_histogram) is not bool:
        raise ValueError("allpostburn_sigma_histogram must be bool")
    np = context["np"]
    if isinstance(n,bool) or not isinstance(n,int) or not 0<n<=INT64_MAX or isinstance(burn,bool) or not isinstance(burn,int) or not 0<=burn<n:
        raise ValueError("Fixed N/B integers required")
    if any(isinstance(x,bool) or not isinstance(x,int) or x<0 for x in [batch_width,trace_every]):
        raise ValueError("Invalid fixed batch/trace width")

    if np.issubdtype(a0.dtype, np.integer):
        max_weight = int(a0.max()) if a0.size else 0
        nonnegative = not a0.size or int(a0.min()) >= 0
        if nonnegative and int(a0.size) * max_weight <= INT64_MAX:
            total = int(np.sum(a0, dtype=np.int64))
        else:
            total = sum(int(w) for w in a0.flat)
    else:
        total = sum(int(w) for w in a0.flat)
    if n*max(1,total)>INT64_MAX:
        raise ValueError("N*total exceeds int64 exact observation bound")
    nr,nc = a0.shape
    pairs,cells = load_queries(queries_path,nr,nc,lambda r,c:int(a0[r,c]))
    nb = (n-burn-1)//batch_width+1 if batch_width else 0
    nt = n//trace_every+2 if trace_every else 0
    if max(nb,nt)>100000:
        raise ValueError("Too many fixed batch/trace records")
    if debug_matrix_trace and (not trace_every or nr*nc>4096):
        raise ValueError("Debug matrix trace requires schedule and <=4096cells")
    b = dict(pair_rows=np.asarray([(r,s) for r,s,t in pairs],dtype=np.int64).reshape((-1,2)),
        thresholds=np.asarray([t for r,s,t in pairs],dtype=np.int64),
        cell_labels=np.asarray([(r,c) for r,c,t in cells],dtype=np.int64).reshape((-1,2)),
        cell_thresholds=np.asarray([t for r,c,t in cells],dtype=np.int64),
        stats=np.zeros(6,dtype=np.int64),burn_outer=burn,trace_every=trace_every,batch_width=batch_width,total_weight=total,
        trace_iterations=np.zeros(nt,dtype=np.int64),
        trace_min=np.zeros((nt,len(pairs)),dtype=np.int64),trace_weights=np.zeros((nt,len(cells)),dtype=np.int64),
        debug_flat=np.zeros((nt,nr*nc) if debug_matrix_trace else (0,0),dtype=np.int64),
        row_strength=a0.sum(axis=1),col_strength=a0.sum(axis=0),
        row_degree=(a0>0).sum(axis=1),col_degree=(a0>0).sum(axis=0))
    for key,length in [("current_min",len(pairs)),("cached_min",len(pairs)),("tails",len(pairs)),("min_sums",len(pairs)),
                       ("current_weights",len(cells)),("cached_weights",len(cells)),("presence",len(cells)),
                       ("cell_tails",len(cells)),("weight_sums",len(cells))]:
        b[key]=np.zeros(length,dtype=np.int64)
    b["batch_counts"]=np.zeros(nb,dtype=np.int64)
    for key,length in [("batch_tails",len(pairs)),("batch_sums",len(pairs)),("batch_presence",len(cells)),
                       ("batch_cell_tails",len(cells)),("batch_weight_sums",len(cells))]:
        b[key]=np.zeros((nb,length),dtype=np.int64)
    if n % 640 or burn != n//5 or trace_every != n//640:
        raise ValueError("Generic Sigma requires multiple640N,20pctburn,641checkpoints")

    edge_upper=min(max(map(int,b["row_strength"]),default=0),max(map(int,b["col_strength"]),default=0))
    if total*edge_upper>INT64_MAX:
        raise ValueError("Generic exact int64 Sigma bound exceeded")
    hub=0
    fixed=0
    b.update(star_hub=hub,star_fixed_leaf=np.int64(fixed),star_scratch_strength=np.zeros(nc,dtype=np.int64),star_scratch_degree=np.zeros(nc,dtype=np.int64),star_trace_sigma=np.zeros(nt,dtype=np.int64))
    if allpostburn_sigma_histogram:
        if total*total > INT64_MAX:
            raise ValueError("Allpostburn group Sigma requires total squared <= INT64_MAX")
        from numba.typed import Dict
        from numba import types
        b["sigma_histogram"] = Dict.empty(key_type=types.int64, value_type=types.int64)
        b["sigma_cache"] = np.zeros(1,dtype=np.int64)
        b["allpostburn_sigma_histogram"] = True
    return b

def execute(context,prepared,b,n,check_every):
    a,wd,wd2,al,al2,uw,uw2=prepared
    keys=("burn_outer trace_every batch_width pair_rows cell_labels thresholds cell_thresholds current_min current_weights "
          "cached_min cached_weights tails min_sums presence cell_tails weight_sums stats batch_counts batch_tails batch_sums "
          "batch_presence batch_cell_tails batch_weight_sums trace_iterations trace_min trace_weights debug_flat "
          "row_strength col_strength row_degree col_degree star_hub star_fixed_leaf star_scratch_strength star_scratch_degree star_trace_sigma").split()
    args=[b[k] for k in keys]
    args.insert(2,check_every)
    if b.get("allpostburn_sigma_histogram", False):
        if not context.get("histogram_ready"):
            raise RuntimeError("Explicit allpostburn histogram warmup required")
        return context["loop_histogram"](a,wd,wd2,uw,uw2,al,al2,n,*args,b["sigma_histogram"],b["sigma_cache"])
    return context["loop"](a,wd,wd2,uw,uw2,al,al2,n,*args)

def warmup(input_path,queries_path,allpostburn_sigma_histogram=False):
    if type(allpostburn_sigma_histogram) is not bool:
        raise ValueError("allpostburn_sigma_histogram must be bool")
    start=time.perf_counter();helper,generated,path,provenance=_generate_source()
    np,core,seed_rng=helper.load_author()
    import numba
    namespace=dict(np=np,njit=numba.njit,weight_shuffling=core.weight_shuffling,
                   simple_edge_swap=core.simple_edge_swap,bridge_edge_swap=core.bridge_edge_swap)
    exec(compile(generated,str(path),"exec"),namespace)
    context=dict(helper=helper,np=np,core=core,seed_rng=seed_rng,loop=namespace["instrumented_probe_BiWES2"],
                 provenance=provenance,generated_path=str(path))
    imported=time.perf_counter();a0=helper.load_graph(input_path,np)
    b=_buffers(context,a0,640,128,queries_path,0,1,False);prepared=core.pre_compute(a0);seed_rng(0)
    out=execute(context,prepared,b,640,100000);linear_index_check(*out[:7])
    if helper.signature(a0)!=helper.signature(out[0]):
        raise AssertionError("Warmup four margins changed")
    if allpostburn_sigma_histogram:
        _,hist_source,hist_path,hist_provenance=_generate_source(True)
        hist_namespace=dict(np=np,njit=numba.njit,weight_shuffling=core.weight_shuffling,
                            simple_edge_swap=core.simple_edge_swap,bridge_edge_swap=core.bridge_edge_swap)
        move_globals=getattr(core.weight_shuffling,"py_func",core.weight_shuffling).__globals__
        for name,value in move_globals.items():
            if name not in hist_namespace:
                hist_namespace[name]=value
        exec(compile(hist_source,str(hist_path),"exec"),hist_namespace)
        context.update(loop_histogram=hist_namespace["instrumented_probe_BiWES2"],histogram_ready=True,
                       histogram_provenance=hist_provenance,histogram_generated_path=str(hist_path))
        hist_b=_buffers(context,a0,640,128,queries_path,0,1,False,True)
        hist_prepared=core.pre_compute(a0);seed_rng(0)
        hist_out=execute(context,hist_prepared,hist_b,640,100000);linear_index_check(*hist_out[:7])
        if helper.signature(a0)!=helper.signature(hist_out[0]):
            raise AssertionError("Histogram warmup four margins changed")
        if sum(map(int,hist_b["sigma_histogram"].values()))!=512:
            raise AssertionError("Histogram warmup allouter accounting")
    context["ready"]=True
    return context,dict(startup_and_import_seconds=imported-start,global_warmup_and_jit_seconds=time.perf_counter()-imported,
                        global_warmup_status="passed",provenance=provenance)

def export_probe(a0,b,n,burn,trace_count):
    if int(b["stats"][5])!=n-burn or int(b["stats"][2]+b["stats"][4])!=n-burn or int(b["stats"][1])!=0:
        raise AssertionError("Probe all-step accounting mismatch")
    if b["batch_width"] and sum(map(int,b["batch_counts"]))!=n-burn:
        raise AssertionError("Probe batch accounting mismatch")
    batches=[]
    for i,count in enumerate(b["batch_counts"]):
        first=burn+1+i*b["batch_width"];last=min(n,first+b["batch_width"]-1)
        if int(count)!=last-first+1:
            raise AssertionError("Noncontiguous query batches")
        batches.append(dict(first_outer=first,last_outer=last,count=int(count),
            pair_tail_counts=list(map(int,b["batch_tails"][i])),pair_min_sums=[str(int(v)) for v in b["batch_sums"][i]],
            cell_presence_counts=list(map(int,b["batch_presence"][i])),cell_tail_counts=list(map(int,b["batch_cell_tails"][i])),
            cell_weight_sums=[str(int(v)) for v in b["batch_weight_sums"][i]]))
    return dict(format="fixed_probe_statistics_v1",nr=int(a0.shape[0]),nc=int(a0.shape[1]),outer_budget=n,
        burn_outer=burn,observed_outer=n,postburn_count=n-burn,
        pairs=[dict(rows=list(map(int,p)),observed_threshold=int(b["thresholds"][i]),
                    tail_count=int(b["tails"][i]),pair_min_sum=str(int(b["min_sums"][i]))) for i,p in enumerate(b["pair_rows"])],
        cells=[dict(cell=list(map(int,p)),observed_threshold=int(b["cell_thresholds"][i]),presence_count=int(b["presence"][i]),
                    tail_count=int(b["cell_tails"][i]),weight_sum=str(int(b["weight_sums"][i]))) for i,p in enumerate(b["cell_labels"])],
        batch_width=b["batch_width"],batches=batches,probe_trace_every=b["trace_every"],
        feature_recomputations=int(b["stats"][2]),feature_flushes=int(b["stats"][3]),run_length_extensions=int(b["stats"][4]),
        integer_precision="int64 exact sums guarded by N*max(1,total)<=INT64_MAX",
        sample_policy="Each complete outer burn<t<=N, all holds/rejects; original author loop; fixed batches; no RNG/no support TV",
        missing_truth="Real large graph exact target not supplied; query estimates are not accuracy metrics")

def run_job(job,context):
    if not context.get("ready"):
        raise RuntimeError("Global warmup context required")
    start=time.perf_counter();prefix=Path(job["outprefix"]);prefix.parent.mkdir(parents=True,exist_ok=True)
    n,burn=job["outer_budget"],job["burn_outer"]
    observe_histogram=job.get("allpostburn_sigma_histogram",False)
    if type(observe_histogram) is not bool:
        raise ValueError("allpostburn_sigma_histogram must be bool")
    result=dict(status="running",method="official_biwes",format="official_probe",seed=job["seed"],
                requested_outer_budget=n,counters={"outer":0},provenance=context["provenance"])
    try:
        if not isinstance(job["seed"],int) or not 0<=job["seed"]<2**32:
            raise ValueError("Unsigned32 seed required")
        check=job.get("check_every",10000)
        if not isinstance(check,int) or isinstance(check,bool) or check<0:
            raise ValueError("Nonnegative check interval required")
        for key in ("input","queries"):
            if job.get(key+"_sha256") and sha(job[key+"_path"])!=job[key+"_sha256"]:
                raise RuntimeError("Frozen "+key+" changed")
        t=time.perf_counter();a0=context["helper"].load_graph(job["input_path"],context["np"])
        b=_buffers(context,a0,n,burn,job["queries_path"],job.get("batch_width",1000),job.get("probe_trace_every",0),job.get("debug_matrix_trace",False),observe_histogram)
        result["input_and_target_setup_seconds"]=time.perf_counter()-t
        t=time.perf_counter();prepared=context["core"].pre_compute(a0);context["seed_rng"](job["seed"])
        result["setup_seconds"]=time.perf_counter()-t
        t=time.perf_counter();out=execute(context,prepared,b,n,check);result["run_seconds_including_checks_and_trace"]=time.perf_counter()-t
        a,wd,wd2,al,al2,uw,uw2,trace_count=out
        t=time.perf_counter()
        if context["helper"].signature(a)!=context["helper"].signature(a0):
            raise AssertionError("Final author margins changed")
        linear_index_check(a,wd,wd2,al,al2,uw,uw2)
        result["final_index_check_seconds"]=time.perf_counter()-t
        t=time.perf_counter();probe=export_probe(a0,b,n,burn,trace_count)
        Path(str(prefix)+".probe.json").write_text(json.dumps(probe,indent=2)+"\n")
        if b["trace_every"]:
            with Path(str(prefix)+".probe.trace.jsonl").open("w") as f:
                for i in range(trace_count):
                    f.write(json.dumps(dict(iteration=int(b["trace_iterations"][i]),
                        pair_minimum=list(map(int,b["trace_min"][i])),cell_weights=list(map(int,b["trace_weights"][i]))))+"\n")
        if b["debug_flat"].shape[0]:
            with Path(str(prefix)+".debug.trace.jsonl").open("w") as f:
                for i in range(trace_count):
                    f.write(json.dumps(dict(iteration=int(b["trace_iterations"][i]),flat=list(map(int,b["debug_flat"][i]))))+"\n")
        if observe_histogram:
            hist={str(int(k)):int(b["sigma_histogram"][k]) for k in sorted(b["sigma_histogram"])}
            if any(int(k)<0 or int(k)>b["total_weight"]**2 or v<=0 for k,v in hist.items()) or sum(hist.values())!=n-burn:
                raise AssertionError("Allpostburn Sigma histogram exact count/qualification")
            artifact=dict(format="allpostburn_sigma_histogram_v1",outer_budget=n,burn_outer=burn,postburn_count=n-burn,
                          counts=hist,initial_sigma=str(int(b["star_trace_sigma"][0])),final_sigma=str(int(b["star_trace_sigma"][trace_count-1])))
            Path(str(prefix)+".structure.hist.json").write_text(json.dumps(artifact,indent=2)+"\n")
            result.update(allpostburn_sigma_histogram_requested=True,allpostburn_sigma_histogram_records=n-burn,
                          allpostburn_sigma_histogram_distinct_values=len(hist),allpostburn_sigma_histogram_integer_bound=str(b["total_weight"]**2),
                          histogram_provenance=context["histogram_provenance"],histogram_observation_policy="After each complete postburn author outer including holds/rejections; O(number of modified edges) exact Sigma cache; one O(K_t) initialization; original sparse641 checks retained; all observation/export CPU charged")
        if trace_count!=641 or sum(int(t)>burn for t in b["trace_iterations"][:trace_count])!=512:
            raise AssertionError("Generic Sigma structure641/512 count mismatch")
        with Path(str(prefix)+".structure.trace.jsonl").open("w") as f:
            for i in range(trace_count):
                f.write(json.dumps(dict(iteration=int(b["trace_iterations"][i]),weight_square_sum=str(int(b["star_trace_sigma"][i]))))+"\n")
        fullsigma=sum(int(a[r,int(label)-a.shape[0]])**2 for r in range(a.shape[0]) for label in al2[r])
        if fullsigma!=int(b["star_trace_sigma"][trace_count-1]):
            raise AssertionError("Generic Sigma final independent adjacency scan")
        with Path(str(prefix)+".final.graph").open("w") as f:
            f.write(str(a.shape[0])+" "+str(a.shape[1])+"\n")
            for r in range(a.shape[0]):
                for label in al2[r]:
                    c=int(label)-a.shape[0]
                    f.write(str(r)+" "+str(c)+" "+str(int(a[r,c]))+"\n")
        result.update(status="completed",structure_trace_records=641,postburn_structure_records=512,structure_certificate="generic sparse adjacency integer square sum; four margins verified at all641 checkpoints",counters={"outer":n},postburn_count=n-burn,all_checkpoints_passed=True,
                      serialization_seconds=time.perf_counter()-t,final_matrix=[[int(v) for v in row] for row in a] if a.size<=4096 else None,
                      integer_safety_bound=n*max(1,b["total_weight"]))
    except Exception as exc:
        result.update(status="failed",error=repr(exc),traceback=traceback.format_exc(),all_checkpoints_passed=False)
    result.update(total_seconds_including_build=time.perf_counter()-start,proc_vm_hwm_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        memory_policy="Author persistent process cumulative peak includes imports/JIT; query buffers bounded by fixed record schedule",
        timing_policy="Global JIT separately reported; perrun input/precompute/sample/observer/check/output charged; first summary write included; timing field rewrite excluded",
        sample_policy="FixedN all original author outer attempts; no RNG in queries, no full support TV")
    target=Path(str(prefix)+".json");target.write_text(json.dumps(result,indent=2)+"\n")
    result["total_seconds_including_build"]=time.perf_counter()-start;target.write_text(json.dumps(result,indent=2)+"\n")
    return result
