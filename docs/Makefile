# Makefile for building and cleaning LaTeX Beamer presentations

# Use FILE variable; default to 'presentation' if not provided
FILE ?= presentation
PDF = $(FILE).pdf
TEX = $(FILE).tex
AUXFILES = *.aux *.log *.nav *.out *.snm *.toc *.vrb *.fdb_latexmk *.fls

all: $(PDF)

$(PDF): $(TEX)
	pdflatex $(TEX)
	pdflatex $(TEX)

clean:
	rm -f $(AUXFILES) $(PDF)

cleanaux:
	rm -f $(AUXFILES)
