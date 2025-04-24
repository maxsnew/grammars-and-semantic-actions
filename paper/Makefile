paper.pdf:	paper.tex refs.bib
	latexmk -pdf -bibtex paper --synctex=1
clean:
	latexmk -C
diff:
	latexdiff --math-markup=fine --graphics-markup=both --allow-spaces submission.tex paper.tex > diff.tex
	latexmk -pdf diff
