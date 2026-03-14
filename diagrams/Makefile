all: over.pdf seq.pdf comma.pdf attr.pdf abc.pdf

abc.svg: Comma2.hs
	runghc Comma2.hs abc.svg

%.pdf: %.svg
	./svg-to-pdf.sh $*

