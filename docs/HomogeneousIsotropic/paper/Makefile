# Build the manuscript.
#
#   make          build main.pdf (pdflatex, bibtex, pdflatex twice)
#   make check    list undefined references, overfull boxes and LaTeX errors in main.log
#   make clean    remove the build products, except main.pdf

MAIN := main
SRC  := $(MAIN).tex macros.tex refs.bib $(wildcard sections/*.tex)

.PHONY: pdf check clean
pdf: $(MAIN).pdf

$(MAIN).pdf: $(SRC)
	pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex
	bibtex $(MAIN)
	pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex
	pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex

check: $(MAIN).pdf
	! grep -n -i -E 'undefined|multiply defined|Overfull|LaTeX Error' $(MAIN).log

clean:
	rm -f $(MAIN).aux $(MAIN).bbl $(MAIN).blg $(MAIN).log $(MAIN).out $(MAIN).toc
