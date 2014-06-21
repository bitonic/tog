
bnfc_output = $(patsubst %,bnfc/Syntax/%,Abs.hs ErrM.hs Layout.hs Print.hs Lex.x Par.y)

$(bnfc_output): src/Syntax.cf
	-@mkdir -p bnfc
	-@rm $(bnfc_output)
	@(cd bnfc && bnfc -d ../$<)

all: $(bnfc_output)
	cabal build

clean:
	rm -rf bnfc
	cabal clean

