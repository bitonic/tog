
bnfc_output = $(patsubst %,bnfc/Syntax/Raw/%,Abs.hs ErrM.hs Layout.hs Print.hs Lex.x Par.y)
hs_sources = $(shell find src/ -name '*.hs')
alex_file = bnfc/Syntax/Raw/Lex
happy_file = bnfc/Syntax/Raw/Par

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

all: dist/build/tog/tog

# The sed is to work around a GHC bug that makes the tag generating
# thing crash when it gets a LINE pragma whose file it can't find.
TAGS: $(bnfc_output) $(hs_sources) $(alex_file).hs $(happy_file).hs
	hasktags -e src bnfc

.PHONY: clean
clean:
	rm -rf bnfc
	cabal clean

modules.pdf: $(bnfc_output) $(hs_sources)
	graphmod -i src -i bnfc src/Main.hs | dot -T pdf -o modules.pdf
