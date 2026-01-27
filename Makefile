test: test.tin card.tin prelude.dl
	cabal run && souffle out.dl -F. -D-
comp: test.tin card.tin prelude.dl
	cabal run && souffle -F. -D- -c out.dl
