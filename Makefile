TEXOPTIONS = -file-line-error -halt-on-error

default: gc-pacing.pdf

.PHONY: gc-pacing.pdf
gc-pacing.pdf:
	pdflatex ${TEXOPTIONS} gc-pacing.tex <&-
	pdflatex ${TEXOPTIONS} gc-pacing.tex <&-
