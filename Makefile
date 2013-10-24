proposal.pdf: proposal.tex proposal.bib plan.tex background.tex
	pdflatex proposal
	bibtex proposal
	pdflatex proposal
	pdflatex proposal

clean:
	rm -f *.aux *.log *.bbl *.blg proposal.pdf
