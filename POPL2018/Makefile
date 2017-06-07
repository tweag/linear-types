all: hlt.pdf

PaperTools/bibtex/jp.bib:
	echo "Get the submodules:"
	echo "Try 'git submodule update --init'"
	false

clean:
	rm -f *.tex *.aux *.bbl *.ptb *.pdf *.toc *.out *.run.xml

%.tex: %.lhs
	lhs2TeX -o $@ $<

%.pdf: %.tex  ../PaperTools/bibtex/jp.bib ../local.bib acmart.cls
	latexmk -pdf $*

%.cls: %.ins
	latex $<
