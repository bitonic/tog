bnfc_output = $(patsubst %,bnfc/Syntax/Raw/%,Abs.hs ErrM.hs Layout.hs Print.hs Lex.x Par.y)
hs_sources = $(shell find src/ -name '*.hs')
alex_file = bnfc/Syntax/Raw/Lex
happy_file = bnfc/Syntax/Raw/Par

.PHONY: build
build: dist/build/tog/tog

$(bnfc_output): src/Syntax/Raw.cf
	-@mkdir -p bnfc
	-@rm $(bnfc_output)
	@(cd bnfc && bnfc -p Syntax -d ../$<)

$(alex_file).hs: $(alex_file).x
	alex $<

$(happy_file).hs: $(happy_file).y
	happy $<

dist/build/tog/tog: $(bnfc_output) $(hs_sources)
	cabal build

.PHONY: clean
clean:
	rm -rf bnfc
	cabal clean

.PHONY: test
test: dist/build/tog/tog
	time ./test.sh

modules.pdf: $(bnfc_output) $(hs_sources)
	graphmod -i src -i bnfc -i dist/build/tog/tog-tmp src/Main.hs | dot -T pdf -o modules.pdf

.PHONY: install-prof
install-prof: $(bnfc_output) $(hs_sources)
	cabal install --enable-executable-profiling --disable-documentation

.PHONY: install
install: $(bnfc_output) $(hs_source)
	cabal install --disable-documentation

.PHONY: ghci
ghci:
	cabal repl

