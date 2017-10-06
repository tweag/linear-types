
# Build the two main plots as PDFs:
default: sumtree_all_plot.pdf maptree_plot.pdf
all: default sumtree_other_plot.pdf sumtree_packed_plot.pdf 

.PHONY: all default clean publish

# This will start off pointing to preloaded data, but be overwritten
# once you run the benchmarks yourself.
DATA=default_dataset.csv
# DATA=swarm_benchmark03.csv

# By default we normalize to the status-quo way of doing things:
# Unpack serialized data, operate on it, and repack it.
BASELINE=unpack-repack

HSBG=../bin/hsbencher-graph

# This uses hsbencher-graph-0.13
sumtree_all_plot.pdf:
	${HSBG} ${DATA} \
          --title="Summing binary tree leaves" \
          --xlabel="Depth of complete binary tree" \
          --ylabel="Speedup over unpack-repack version" \
	  --renames=renames.txt \
          --ylog -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,sumtree \
          --lines --GPL -o sumtree_all_plot.csv --template template_keyhigh.gpl \
          --factor=${BASELINE} --inverse

maptree_plot.pdf:
	${HSBG} ${DATA} \
          --title="Mapping (+1) over binary tree leaves" \
          --xlabel="Depth of complete binary tree" \
          --ylabel="Speedup over unpack-repack version" \
	  --renames=renames.txt \
          --ylog -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,maptree \
          --lines --GPL -o maptree_plot.csv --template template_keyhigh.gpl \
          --factor=${BASELINE} --inverse

# =============================================================

TMPD=/tmp/output_$(shell date +%s)
TAG=parfunc/linear-haskell-popl18-artifact-plots

# Run and plot the benchmarks under docker, cache the results as a
# Docker image.  Extract the results to the host as well.
docker-bench:
	docker build --no-cache=true -t $(TAG) .
	mkdir -p $(TMPD)/
	echo "cp -av /examples/plots /host/ && chown -R "$(shell id -u):$(shell id -g)" /host" | \
          docker run --rm -iv$(TMPD):/host $(TAG) bash
	cp -f $(TMPD)/*.csv ./
	cp -f $(TMPD)/*.pdf ./

clean:
	rm -f *_plot.csv *_plot.gpl *_plot.pdf

publish: default
	cp -f sumtree_all_plot.pdf ../../POPL2018/figures/sumtree_all_plot_baseline_unpack-repack.pdf
	cp -f maptree_plot.pdf ../../POPL2018/figures/maptree_plot_baseline_unpack-repack.pdf

# Alternate version:
# Broken out to see the packed/boxed speed with non-log Y axis:
# =============================================================

sumtree_packed_plot.pdf:
	${HSBG} ${DATA} \
          --title="Summing binary tree leaves" \
          --xlabel="Depth of complete binary tree" \
          --ylabel="Speedup over regular/boxed version" \
          -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,sumtree \
          --filtEq=VARIANT,packed,boxed \
          --lines --GPL -o sumtree_packed_plot.csv --template template_keyhigh.gpl \
          --factor=boxed --inverse

sumtree_other_plot.pdf:
	${HSBG} ${DATA} \
          --title="Summing binary tree leaves" \
          --xlabel="Depth of complete binary tree" \
          --ylabel="Speedup over regular/boxed version" \
          --ylog -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,sumtree \
          --filtEq=VARIANT,boxed,ST-packed,unpack-repack \
          --lines --GPL -o sumtree_other_plot.csv --template template_keylow.gpl \
          --factor=boxed --inverse

