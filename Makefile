TEXINPUTS=.:ltx:

all: tale.pdf

tale.pdf: ltx/slides.tex slides.lagda
	pdflatex ltx/slides.tex

ltx/slides.tex: slides.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=ltx slides.lagda > ltx/slides.tex
