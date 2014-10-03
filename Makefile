
bnfc_output = $(patsubst %,bnfc/Syntax/Raw/%,Abs.hs ErrM.hs Layout.hs Print.hs Lex.x Par.y)
hs_sources = $(shell find src/ -name '*.hs')

$(bnfc_output): src/Syntax/Raw.cf
	-@mkdir -p bnfc
	-@rm $(bnfc_output)
	@(cd bnfc && bnfc -p Syntax -d ../$<)

dist/build/tog/tog: $(bnfc_output) $(hs_sources)
	cabal build

all: dist/build/tog/tog

.PHONY: clean
clean:
	rm -rf bnfc
	cabal clean

modules.pdf: $(bnfc_output) $(hs_sources)
	graphmod -i src -i bnfc src/Main.hs | dot -T pdf -o modules.pdf
