AGDA_EXEC=agda
RTS_OPTIONS=+RTS -H3G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)

.PHONY : all
all : check

.PHONY : test
test: check-whitespace check-everythings check

.PHONY : fix-whitespace
fix-whitespace:
	cabal exec -- fix-agda-whitespace

.PHONY : check-whitespace
check-whitespace:
	cabal exec -- fix-agda-whitespace --check

.PHONY : check-everythings
check-everythings:
	runhaskell ./GenEverythings.hs check Experiments

.PHONY : gen-everythings
gen-everythings:
	runhaskell ./GenEverythings.hs gen Core Foundations Codata Experiments

.PHONY : check
check:
	$(AGDA) Cubical/Core/Everything.agda
	$(AGDA) Cubical/Foundations/Everything.agda
	$(AGDA) Cubical/Codata/Everything.agda
	$(AGDA) Cubical/Data/Everything.agda
	$(AGDA) Cubical/HITs/Everything.agda
	$(AGDA) Cubical/Relation/Everything.agda
	$(AGDA) Cubical/Induction/Everything.agda
	$(AGDA) Cubical/Modalities/Everything.agda
	$(AGDA) Cubical/Structures/Everything.agda
	$(AGDA) Cubical/WithK.agda
	$(AGDA) Cubical/Experiments/Everything.agda
	$(AGDA) Cubical/ZCohomology/Everything.agda
	$(AGDA) Cubical/Categories/Everything.agda

.PHONY: listings
listings:
	$(AGDA) -i. -isrc --html Cubical/README.agda -v0

.PHONY : clean
clean :
	find . -type f -name '*.agdai' -delete
