

default: sumtree_all_plot.pdf maptree_plot.pdf
all: default sumtree_other_plot.pdf sumtree_packed_plot.pdf 

.PHONY: all default clean publish

DATA=swarm_benchmark03.csv
# BASELINE=boxed
BASELINE=unpack-repack

sumtree_all_plot.pdf:
	hsbencher-graph ${DATA} \
          --title="Summing binary tree leaves" \
          --xlabel="Depth of complete binary tree" \
          --ylabel="Speedup over regular/boxed version" \
          --ylog -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,sumtree \
          --lines --GPL -o sumtree_all_plot.csv --template template_keyhigh.gpl \
          --factor=${BASELINE} --inverse --renames=renames.txt

maptree_plot.pdf:
	hsbencher-graph ${DATA} \
          --title="Mapping (+1) over binary tree leaves" \
          --xlabel="Depth of complete binary tree" \
          --ylabel="Speedup over regular/boxed version" \
          --ylog -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,maptree \
          --lines --GPL -o maptree_plot.csv --template template_keyhigh.gpl \
          --factor=${BASELINE} --inverse --renames=renames.txt

clean:
	rm -f *_plot.csv *_plot.gpl *_plot.pdf

publish: default
	cp -f sumtree_all_plot.pdf ../../POPL2018/figures/sumtree_all_plot_baseline_unpack-repack.pdf
	cp -f maptree_plot.pdf ../../POPL2018/figures/maptree_plot_baseline_unpack-repack.pdf

# Broken out to see the packed/boxed speed with non-log Y axis:
# =============================================================

sumtree_packed_plot.pdf:
	hsbencher-graph ${DATA} \
          --title="Summing binary tree leaves" \
          --xlabel="Depth of complete binary tree" \
          --ylabel="Speedup over regular/boxed version" \
          -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,sumtree \
          --filtEq=VARIANT,packed,boxed \
          --lines --GPL -o sumtree_packed_plot.csv --template template_keyhigh.gpl \
          --factor=boxed --inverse

sumtree_other_plot.pdf:
	hsbencher-graph ${DATA} \
          --title="Summing binary tree leaves" \
          --xlabel="Depth of complete binary tree" \
          --ylabel="Speedup over regular/boxed version" \
          --ylog -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,sumtree \
          --filtEq=VARIANT,boxed,ST-packed,unpack-repack \
          --lines --GPL -o sumtree_other_plot.csv --template template_keylow.gpl \
          --factor=boxed --inverse


