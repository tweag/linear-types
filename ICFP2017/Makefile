all: hlt.pdf

%.pdf: acmart.cls %.tex
	pdflatex $<

%.cls: %.ins
	latex $<
