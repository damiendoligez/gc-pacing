TEXOPTIONS = -file-line-error -halt-on-error

default: gc-pacing.pdf equations.vo \
  existence_sl.vo existence_cl.vo existence_el.vo

clean:
	rm -f *.glob *.vo* *.aux *.log *.out gc-pacing.pdf

gc-pacing.pdf: gc-pacing.tex
	pdflatex ${TEXOPTIONS} gc-pacing.tex <&-
	pdflatex ${TEXOPTIONS} gc-pacing.tex <&-

%.vo: %.v
	rocq c $^
