TEXOPTIONS = -file-line-error -halt-on-error

default: gc-pacing.pdf

gc-pacing.pdf: gc-pacing.tex
	pdflatex ${TEXOPTIONS} gc-pacing.tex <&-

full:
	pdflatex ${TEXOPTIONS} gc-pacing.tex <&-
	pdflatex ${TEXOPTIONS} gc-pacing.tex <&-

