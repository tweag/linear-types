all: FormalSystem.pdf

PaperTools/bibtex/jp.bib:
	echo "Get the submodules"
	false

%.pdf: %.tex PaperTools/bibtex/jp.bib
	xelatex $*
	biber $*
	xelatex $*

%.tex: %.org
	bin/org-to-tex.sh $*.org
