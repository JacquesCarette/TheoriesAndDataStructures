TEXINPUTS=.:ltx:

all: tale.pdf

tale.pdf: ltx/slides.tex slides.ltx
	pdflatex ltx/slides.tex

ltx/slides.tex: slides.ltx
	ln -s slides.ltx slides.lagda
	agda --latex -i . --latex-dir=ltx slides.lagda > ltx/slides.tex
