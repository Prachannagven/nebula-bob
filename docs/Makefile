# Makefile for building and cleaning LaTeX Beamer presentations

PDF= presentation.pdf
TEX= presentation.tex
AUXFILES= *.aux *.log *.nav *.out *.snm *.toc *.vrb *.fdb_latexmk *.fls

all: $(PDF)

$(PDF): $(TEX)
	pdflatex $(TEX)
	pdflatex $(TEX)

clean:
	rm -f $(AUXFILES) $(PDF)

cleanaux:
	rm -f $(AUXFILES)
