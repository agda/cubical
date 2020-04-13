AGDA_EXEC=agda
RTS_OPTIONS=+RTS -H3G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)
EVERYTHINGS=runhaskell ./Everythings.hs

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
	$(EVERYTHINGS) check-except Experiments

.PHONY : gen-everythings
gen-everythings:
	$(EVERYTHINGS) gen-except Core Foundations Codata Experiments

.PHONY : check-README
check-README:
	$(EVERYTHINGS) checkREADME

.PHONY : check
check: $(wildcard Cubical/**/*.agda)
	$(AGDA) Cubical/Core/Everything.agda
	$(AGDA) Cubical/Foundations/Everything.agda
	$(AGDA) Cubical/Codata/Everything.agda
	$(AGDA) Cubical/Data/Everything.agda
	$(AGDA) Cubical/HITs/Everything.agda
	$(AGDA) Cubical/Homotopy/Everything.agda
	$(AGDA) Cubical/Relation/Everything.agda
	$(AGDA) Cubical/Induction/Everything.agda
	$(AGDA) Cubical/Modalities/Everything.agda
	$(AGDA) Cubical/Structures/Everything.agda
	$(AGDA) Cubical/WithK.agda
	$(AGDA) Cubical/Experiments/Everything.agda
	$(AGDA) Cubical/ZCohomology/Everything.agda
	$(AGDA) Cubical/Categories/Everything.agda

.PHONY: listings
listings: $(wildcard Cubical/**/*.agda)
	$(AGDA) -i. -isrc --html Cubical/README.agda -v0

.PHONY : clean
clean :
	find . -type f -name '*.agdai' -delete
