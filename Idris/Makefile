
RLWRAP=$(shell which rlwrap)
IDRIS=$(shell which idris2)

all: gen

gen: AST.idr
	$(RLWRAP) $(IDRIS) -p idris2 -p elab-util AST.idr

repl:
	$(RLWRAP) $(IDRIS)

erl: example.erl
	erlc example.erl
	erl example.beam -noshell -eval 'example:mainPar()' -eval 'init:stop()' 

clean:
	rm -rf build

init:
	git clone git@github.com:stefan-hoeck/idris2-elab-util.git
	cd idris2-elab-util
	$(IDRIS) --install elab-util.ipkg
