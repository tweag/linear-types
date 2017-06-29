

plots: sumtree_plot.pdf maptree_plot.pdf

sumtree_plot.pdf:
	hsbencher-graph swarm_benchmark01.csv \
          --title="Summing binary tree leaves" \
          --xlabel="Depth of complete binary tree" \
          --ylabel="Speedup over regular/boxed version" \
          --ylog -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,sumtree \
          --lines --GPL -o sumtree_plot.csv --template template.gpl \
          --factor=boxed
#          --filtRange=ARGS,8,21 \

maptree_plot.pdf:
	hsbencher-graph swarm_benchmark01.csv \
          --title="Mapping over binary tree leaves" \
          --xlabel="Depth of complete binary tree" \
          --ylabel="Speedup over regular/boxed version" \
          --ylog -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,maptree \
          --lines --GPL -o maptree_plot.csv --template template.gpl \
          --factor=boxed

#          --filtRange=ARGS,8,21 \

clean:
	rm -f *_plot.csv *_plot.gpl *_plot.pdf
