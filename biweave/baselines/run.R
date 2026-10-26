args <- commandArgs(trailingOnly=TRUE)
project <- normalizePath(args[1])
method <- args[2]
loader <- readLines(file.path(project, "build", paste0(method, "_loader.txt")))
invisible(loadNamespace("Rcpp"))
source(file.path(project, loader), local=globalenv())
fn <- if (method=="wgs") wgs_job else ds1998_job
stopifnot(length(args)==10L)
fn(args[3], args[4], args[5], as.numeric(args[6]), as.numeric(args[7]),
   as.numeric(args[8]), as.numeric(args[9]), "trace", 0.05, as.numeric(args[10]))
