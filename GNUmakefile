AGDA_EXEC=agda
RTS_OPTIONS=+RTS -H3G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)
EVERYTHINGS=runhaskell ./Everythings.hs

.PHONY : all
all : gen-everythings check

.PHONY : test
test: check-whitespace gen-and-check-everythings check-README check

# checking and fixing whitespace

.PHONY : fix-whitespace
fix-whitespace:
	cabal exec -- fix-whitespace

.PHONY : check-whitespace
check-whitespace:
	cabal exec -- fix-whitespace --check

# checking and generating Everything files

.PHONY : check-everythings
check-everythings:
	$(EVERYTHINGS) check-except Experiments

.PHONY : gen-everythings
gen-everythings:
	$(EVERYTHINGS) gen-except Core Foundations Codata Experiments

.PHONY : gen-and-check-everythings
gen-and-check-everythings:
	$(EVERYTHINGS) gen-except Core Foundations Codata Experiments
	$(EVERYTHINGS) check Core Foundations Codata

.PHONY : check-README
check-README:
	$(EVERYTHINGS) check-README

# typechecking and generating listings for all files imported in in README

.PHONY : check
check: $(wildcard Cubical/**/*.agda)
	$(foreach f, $(shell $(EVERYTHINGS) get-imports-README), $(AGDA) "$(f)" && ) true
	$(AGDA) Cubical/WithK.agda

.PHONY: listings
listings: $(wildcard Cubical/**/*.agda)
	$(AGDA) -i. -isrc --html Cubical/README.agda -v0

.PHONY : clean
clean :
	find . -type f -name '*.agdai' -delete
