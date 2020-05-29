all: HaskeLL.pdf intro.pdf why.pdf lionear.pdf applications.pdf Slides/2017-01-10-IRIF/spiwack.pdf Slides/2017-03-10-LIPN/spiwack.pdf

PaperTools/bibtex/jp.bib:
	echo "Get the submodules:"
	echo "Try 'git submodule update --init'"
	false

clean:
	rm -f *.tex *.aux *.bbl *.ptb *.pdf *.toc *.out *.run.xml

%.tex: %.lhs
	lhs2TeX -o $@ $<

%.pdf: %.tex PaperTools/bibtex/jp.bib local.bib
	cd $(dir $<) && xelatex -halt-on-error $(notdir $*)
	cd $(dir $<) && biber $(notdir $*)
	cd $(dir $<) && xelatex -halt-on-error  $(notdir $*)

%.tex: %.org
	bin/org-to-tex.sh $*.org
