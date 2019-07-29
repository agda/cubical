AGDA_EXEC=agda
RTS_OPTIONS=+RTS -H3G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)

test: check-whitespace check

fix-whitespace: 
	cabal exec -- fix-agda-whitespace

check-whitespace:
	cabal exec -- fix-agda-whitespace --check

check: $(wildcard **/*.agda)
	$(AGDA) Cubical/Core/Everything.agda
	$(AGDA) Cubical/Foundations/Everything.agda
	$(AGDA) Cubical/Codata/Everything.agda
	$(AGDA) Cubical/Data/Everything.agda
	$(AGDA) Cubical/HITs/Everything.agda
	$(AGDA) Cubical/Relation/Everything.agda
	$(AGDA) Cubical/Experiments/Everything.agda

clean :
	find . -type f -name '*.agdai' -delete
