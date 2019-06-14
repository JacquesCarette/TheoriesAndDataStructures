all: TandDS.pdf

TandDS.pdf: TandDS.tex
	pdflatex TandDS.tex

slides: slides.tex
	pdflatex slides.tex
