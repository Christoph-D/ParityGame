isabelle=~/local/Isabelle2016-1/bin/isabelle

all:
	$(isabelle) build -o browser_info -o document=pdf -j 4 -v -d ../Coinductive/ -D .

jedit:
	$(isabelle) jedit -d ../Coinductive/ -l Coinductive *.thy
