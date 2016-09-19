all: FormalSystem.pdf

%.pdf: %.tex
	xelatex $<

%.tex: %.org
	bin/org-to-tex.sh $*.org
