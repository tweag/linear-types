all: hlt.pdf

%.pdf: %.tex acmart.cls
	pdflatex $<

%.cls: %.ins
	latex $<
