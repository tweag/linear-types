all: HaskeLL.pdf intro.pdf why.pdf

PaperTools/bibtex/jp.bib:
	echo "Get the submodules:"
	echo "Try 'git submodule update --init'"
	false

clean:
	rm -f *.tex *.aux *.bbl *.ptb *.pdf *.toc *.out *.run.xml

%.tex: %.lhs
	lhs2TeX -o $@ $<

%.pdf: %.tex PaperTools/bibtex/jp.bib local.bib
	xelatex $*
	biber $*
	xelatex $*

%.tex: %.org
	bin/org-to-tex.sh $*.org
