.PHONY: pdf haddock FORCE_MAKE

pdf: haddock doc
	rm -rf haddock/main.tex
	rm -rf haddock/haddock.sty

doc:
	 latexmk -pdf -shell-escape -synctex=1 doc.tex

clean:
	latexmk -c
	rm -rf _minted-*
	rm -rf *.aux *.fdb_latexmk *.fls *.log *.synctex.gz *.idx *.ilg *.ind *.toc \
		*.bbl *.dvi *.xml haddock.sty
	rm -rf *.pdf
	rm -rf haddock

.ONESHELL:
haddock:
	mkdir -p haddock
	cd ..
	haddock --latex --latex-style=mystyle --title="Sofia/Haskell documentation" -o doc/haddock sofia.hs
