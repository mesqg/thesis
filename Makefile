
export SHELL := /bin/bash

all:
	pdflatex formulas.tex
	pdflatex formulas.tex
	pdflatex formulas.tex
	pdflatex formulas_improved.tex
	pdflatex formulas_improved.tex
	pdflatex formulas_improved.tex

clean:
	$(RM) *.dvi *.aux *.log *.bbl *.blg *.toc *.out *.fls *.haux *.fdb_latexmk formulas.lof formulas.lot formulas_improved.lof formulas_improved.lot *~

distclean: clean
	$(RM) formulas.pdf
	$(RM) formulas_improved.pdf
	$(RM) *-eps-converted-to.pdf

