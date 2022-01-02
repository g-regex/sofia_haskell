.PHONY: pdf haddock fixtex doc FORCE_MAKE

pdf: fixtex doc.pdf
	rm -rf haddock/main.tex
	rm -rf haddock/haddock.sty

doc.pdf: haddock/*.tex
	 latexmk -pdf -shell-escape -synctex=1 doc.tex

clean:
	rm -rf _minted-*
	rm -rf *.aux *.fdb_latexmk *.fls *.log *.synctex.gz *.idx *.ilg *.ind \
		*.toc *.bbl *.dvi *.xml haddock.sty
	rm -rf *.pdf
	rm -rf haddock

.ONESHELL:
haddock:
	mkdir -p haddock
	cd ..
	haddock --latex --latex-style=mystyle \
		--title="Sofia/Haskell documentation" -o doc/haddock Sofia.hs

fixtex: haddock
	cd haddock
	for f in *.tex
	do
		awk '{a=gensub(/^\\item\[\\begin\{tabular\}\{@\{\}l\}/,
			 "\\\\item[\\\\mintinline{haskell}{", "g", $$0);
			 b=gensub(/^\\end\{tabular\}\]/, "}]", "g", a);
			 c=gensub(/\{\\char 91\}/, "[", "g", b);
			 d=gensub(/\{\\char 93\}/, "]", "g", c);
			 e=gensub(/\\vbox/, "", "g", d);
			 print e}' $$f > $$(basename $$f .tex)_fixed.tex
		rm $$f
		mv $$(basename $$f .tex)_fixed.tex $$f
	done
