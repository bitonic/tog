all: $(patsubst %.tex,%.pdf,$(wildcard *.tex)) $(patsubst %.lhs,%.pdf,$(wildcard *.lhs))

unifications-constraints.pdf: unifications-constraints.tex unifications-constraints.bib
	pdflatex -halt-on-error $< -o $@
	bibtex $(patsubst %.tex,%,$<)
	pdflatex -halt-on-error $< -o $@
	pdflatex -halt-on-error $< -o $@

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
