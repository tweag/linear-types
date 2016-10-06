all: FormalSystem.pdf

PaperTools/bibtex/jp.bib:
	echo "Get the submodules:"
	echo "Try 'git submodule update --init'"
	false

clean:
	rm -f *.aux *.bbl *.ptb FormalSystem.tex *.pdf

%.tex: %.lhs
	lhs2TeX -o $@ $<

%.pdf: %.tex PaperTools/bibtex/jp.bib
	xelatex $*
	biber $*
	xelatex $*

%.tex: %.org
	bin/org-to-tex.sh $*.org
