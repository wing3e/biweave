# BiWeave

BiWeave samples vertex-labeled, integer-weighted bipartite graphs with every node's degree and strength fixed, combining local reconfiguration, equal-weight switching, and coverage exploration.

## Contents

- `biweave/`: sampling kernels, routing, and external-method adapters.
- `analysis/` and `scripts/`: experiment execution, evaluation, summaries, plotting, and diagnostics.
- `data/`: 1,414 graph inputs, fixed queries, exact references, and real-graph initial states.
- `results/`: chain results, sufficient statistics, and final experimental summaries.

## Build

Native sampling requires a C++17 compiler and GMP. Core sampling and evaluation use the Python standard library. Additional packages support BiWES, plotting, and diagnostics; the dependency configuration is tested with Python 3.13.

```bash
sudo apt-get install g++ libgmp-dev
python -m pip install -r requirements.txt
mkdir -p build
for method in forest ordinary pair triple sirius valuh; do
  g++ -O3 -std=c++17 -DNDEBUG "-ffile-prefix-map=$PWD=." \
    -I "biweave/native/$method" "biweave/native/$method/sampler.cpp" \
    -o "build/$method" -lgmpxx -lgmp
done
```

The first four branches implement BiWeave's routing. Sirius and VaLUH-d provide comparison kernels.

## Run

Execute commands from the repository root:

```bash
python -m biweave sample \
  --input data/synthetic/syn_0001/input.graph \
  --queries data/synthetic/syn_0001/queries.txt \
  --output output/example/sample \
  --seed 0x1020304 --steps 6400 --burn-in 1280
python scripts/evaluate.py --case syn_0001 --prefix output/example/sample
```

All attempted updates count toward `--steps`, including holds and rejections. Each update starts from the preceding state. Estimates include every post-burn-in attempt. `--ablation local`, `exchange`, `coverage`, or `selector` removes the corresponding operation or selection mechanism; `none` runs the complete algorithm.

Replay recorded experiments or regenerate result summaries:

```bash
python scripts/run_benchmarks.py --panel web --method BiWeave \
  --limit 3 --replicates 5 --jobs 2 --execute
python scripts/run_benchmarks.py --panel ablation --replicates 8 --execute
python scripts/summarize.py
python scripts/plot.py
python scripts/diagnostics.py --case real_retail_0001 --check
```

Panels are `synthetic`, `web`, `analytic`, `budget`, `decision`, `real`, `ablation`, and `selector`. Omit `--execute` to inspect a plan. Recorded rounds and seeds are retained. Each sampling process uses one CPU thread; `--jobs` controls concurrency. CPU targets are calibration targets, and measured costs vary with hardware. Use a fresh `--output` directory for each replay.

## External methods

BiWES preserves all four margins directly. Sirius, VaLUH-d, WGS, and DG use reversible first-return adapters to additionally enforce degrees on strength-preserving trials. EXACT rejects degree-incompatible independent proposals. Only feasible outer states enter estimates, including held states; rejected and aborted work contributes to cost.

Fetch fixed upstream dependencies:

```bash
python scripts/fetch_baselines.py all
```

WGS and DG require R and Rcpp. Build their bindings before sampling:

```bash
sudo apt-get install r-base r-cran-rcpp
Rscript biweave/baselines/build.R "$PWD" wgs
Rscript biweave/baselines/build.R "$PWD" dg
```

Build EXACT after fetching its source:

```bash
gcc -O3 -std=c99 -fPIC -c \
  biweave/baselines/exact/bridge.c -o build/exact_bridge.o
g++ -O3 -std=c++17 biweave/baselines/exact/driver.cpp \
  build/exact_bridge.o -lgmp -lm -o build/exact
```

`python -m biweave.baselines --help` lists the shared arguments. Upstream sources retain their own license notices.

## Data and results

The inputs comprise 1,000 synthetic graphs, 180 Web-derived graphs, 90 analytic constructions, 100 decision controls, 40 real graphs, three operation-deletion inputs, and one selection-mechanism input. The budget study reuses twenty inputs per main family. `data/manifest.json` records relative paths and graph families.

Graph files begin with row and column counts, followed by zero-based `row column positive_integer_weight` records. Missing entries are zero. Degree counts nonzero entries; strength sums weights. Real graphs include five feasible initial states.

Query files begin with `fixed_probe_queries_v1 nr nc number_of_pairs number_of_cells`. Pair rows contain `row_a row_b threshold`; cell rows contain `row column threshold`. Weighted overlap is `sum_j min(x[row_a,j], x[row_b,j])`. Query thresholds remain fixed during sampling. Oracles store exact counts or rational probabilities in query order.

Compressed observations link to chain results through `observation_id`. They retain concentration histograms for `sum_ij x[i,j]^2`, cell-presence counts, and overlap-tail counts. Operation deletions also retain full-state histograms. Real-graph traces support R-hat and effective sample size calculations. Failed runs remain represented; missing measurements are not zero errors.

Main comparisons use five seeds, averaging completed seeds within graphs and then graphs equally. Budget curves use seventeen targets; decisions use seven targets and a threshold of `1/20`. Operation deletions use eight seeds; the selector study uses four. Seed values use hexadecimal notation. Main metrics are total variation distance and query-probability RMSE; analytic query errors are relative. Final summaries retain completeness information.

## Sources

- Lastfm listening records: [GroupLens](https://grouplens.org/datasets/hetrec-2011/).
- Online Retail, contributed by Daqing Chen: [UCI](https://doi.org/10.24432/C5BW33), under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
- MOOC actions: [SNAP](https://snap.stanford.edu/data/act-mooc.html).
- Implementations: [BiWES](https://github.com/Glaviano/biwes), [cgsampr](https://github.com/jscott6/cgsampr), [EXACT](https://jwmi.github.io/software/).

Web-derived graphs retain interaction weights and use local indices instead of original platform identifiers. Source dataset terms remain applicable.
