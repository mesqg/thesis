
export SHELL := /bin/bash

all:
	pdflatex formulas.tex
	pdflatex formulas.tex
	pdflatex formulas.tex

clean:
	$(RM) *.dvi *.aux *.log *.bbl *.blg *.toc *.out *.fls *.haux *.fdb_latexmk formulas.lof formulas.lot *~

distclean: clean
	$(RM) formulas.pdf
	$(RM) *-eps-converted-to.pdf

