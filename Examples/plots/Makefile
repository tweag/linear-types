

plots: sumtree_plot.pdf maptree_plot.pdf

sumtree_plot.pdf:
	hsbencher-graph swarm_benchmark01.csv \
          --filtRange=ARGS,8,21 \
          -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,sumtree \
          --lines --GPL -o sumtree_plot.csv --template template.gpl \
          --factor=boxed

# --ylog
maptree_plot.pdf:
	hsbencher-graph swarm_benchmark01.csv \
          --filtRange=ARGS,8,21 \
          -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,maptree \
          --lines --GPL -o maptree_plot.csv --template template.gpl \
          --factor=boxed

clean:
	rm -f *_plot.csv *_plot.gpl *_plot.pdf
