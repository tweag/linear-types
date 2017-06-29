

plots: sumtree_all_plot.pdf sumtree_packed_plot.pdf sumtree_other_plot.pdf maptree_plot.pdf

DATA=swarm_benchmark03.csv

sumtree_all_plot.pdf:
	hsbencher-graph ${DATA} \
          --title="Summing binary tree leaves" \
          --xlabel="Depth of complete binary tree" \
          --ylabel="Speedup over regular/boxed version" \
          --ylog -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,sumtree \
          --lines --GPL -o sumtree_all_plot.csv --template template_keyhigh.gpl \
          --factor=boxed --inverse

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


#          --filtRange=ARGS,8,21 \

maptree_plot.pdf:
	hsbencher-graph ${DATA} \
          --title="Mapping over binary tree leaves" \
          --xlabel="Depth of complete binary tree" \
          --ylabel="Speedup over regular/boxed version" \
          --ylog -x ARGS -y MEDIANTIME --key VARIANT --filtEq=PROGNAME,maptree \
          --lines --GPL -o maptree_plot.csv --template template_keyhigh.gpl \
          --factor=boxed --inverse

#          --filtRange=ARGS,8,21 \
 
clean:
	rm -f *_plot.csv *_plot.gpl *_plot.pdf
