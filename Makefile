all: FormalSystem.pdf

%.pdf: %.tex
	xelatex $<

