paper.pdf:	paper.tex refs.bib
	latexmk -pdf paper --synctex=1
clean:
	latexmk -C
# diff:
# 	latexdiff-vc --git --force --math-markup=fine --graphics-markup=both -r origin/main paper.tex
# 	mv paper-difforigin/main.tex paper-difforigin/diff.tex
# 	# the following will almost surely fail, but gives a good estimate of the diff
# 	latexmk -pdf -interaction=nonstopmode paper-difforigin/diff.tex
