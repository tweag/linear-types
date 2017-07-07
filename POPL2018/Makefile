all: hlt.pdf

submission: rlt.pdf appendix.pdf

PaperTools/bibtex/jp.bib:
	echo "Get the submodules:"
	echo "Try 'git submodule update --init'"
	false

plain:
	touch no-editing-marks
	$(MAKE) clean
	$(MAKE) 

ed:
	rm -f no-editing-marks
	$(MAKE) clean
	$(MAKE)

clean:
	rm -f *.tex *.aux *.bbl *.ptb hlt*.pdf *.toc *.out *.run.xml

%.tex: %.lhs
	lhs2TeX -o $@ $<

%.pdf: %.tex  ../PaperTools/bibtex/jp.bib ../local.bib acmart.cls
	latexmk -pdf $*

rlt.pdf: hlt.pdf
	pdftk $< cat 1-28 output temp.pdf
	pdftk $< dump_data_utf8 | pdftk temp.pdf update_info_utf8 - output $@
appendix.pdf: hlt.pdf
	pdftk hlt.pdf cat 29-end output $@

%.cls: %.ins
	latex $<

.PHONY: all submission plain ed clean
