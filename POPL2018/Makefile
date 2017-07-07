all: hlt.pdf

submission: rlt.pdf supplementary.zip
	@echo %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	@echo
	@echo Submission instructions:
	@echo
	@echo Submit rlt.pdf as the main document
	@echo and supplementary.zip as the archive
	@echo of supplementary material
	@echo
	@echo %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

rlt-full.pdf: hlt.pdf
	cp $< $@

appendix.pdf: hlt.pdf
	pdftk hlt.pdf cat 29-end output $@

README.md: supplementary-readme.md
	cp $< $@

supplementary.zip: rlt-full.pdf appendix.pdf README.md
	zip $@ $^

%.cls: %.ins
	latex $<

.PHONY: all submission plain ed clean
