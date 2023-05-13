isabelle=~/local/Isabelle2022/bin/isabelle

all:
	$(isabelle) build -o browser_info -o document=pdf -j 4 -v -d ../Coinductive/ -d ../Graph_Theory -D .

jedit:
	$(isabelle) jedit -d ../Coinductive/ -l Coinductive *.thy
