args <- commandArgs(trailingOnly=TRUE)
project <- normalizePath(args[1])
method <- args[2]
base <- file.path(project, "biweave", "baselines", method)
cache <- file.path(project, "build", paste0(method, "_cache"))
dir.create(cache, recursive=TRUE, showWarnings=FALSE)
Sys.setenv(R_MAKEVARS_USER=file.path(project, "biweave", "baselines", "Makevars"),
           PKG_CPPFLAGS=paste0("-I", shQuote(base)), MAKEFLAGS="-j1",
           OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1", MKL_NUM_THREADS="1")
Rcpp::sourceCpp(file.path(base, "bridge.cpp"), cacheDir=cache,
                rebuild=TRUE, showOutput=TRUE)
loaders <- list.files(cache, pattern="bridge[.]cpp[.]R$", recursive=TRUE,
                      full.names=TRUE)
stopifnot(length(loaders)==1L)
relative <- substring(normalizePath(loaders[1]), nchar(project)+2L)
writeLines(relative, file.path(project, "build", paste0(method, "_loader.txt")))
