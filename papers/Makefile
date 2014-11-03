all: $(patsubst %.tex,%.pdf,$(wildcard *.tex)) $(patsubst %.lhs,%.pdf,$(wildcard *.lhs))

talk.tex: talk.lhs
	lhs2TeX $< -o $@

talk.pdf: talk.tex
	pdflatex -halt-on-error $< -o $@

clean:
	rm -f *.dvi
	rm -f *.pdf
	rm -f *.aux
	rm -f *.ptb
	rm -f *.log
