all: tale.pdf

tale.pdf: slides.tex
	pdflatex slides.tex
