AGDA_EXEC=agda
RTS_OPTIONS=+RTS -H3G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)

.PHONY : all
all : check

.PHONY : test
test: check-whitespace check

.PHONY : fix-whitespace
fix-whitespace:
	cabal exec -- fix-agda-whitespace

.PHONY : check-whitespace
check-whitespace:
	cabal exec -- fix-agda-whitespace --check

.PHONY : check
check: $(wildcard **/*.agda)
	$(AGDA) Cubical/Core/Everything.agda
	$(AGDA) Cubical/Foundations/Everything.agda
	$(AGDA) Cubical/Codata/Everything.agda
	$(AGDA) Cubical/Data/Everything.agda
	$(AGDA) Cubical/HITs/Everything.agda
	$(AGDA) Cubical/Relation/Everything.agda
	$(AGDA) Cubical/Experiments/Everything.agda

.PHONY : clean
clean :
	find . -type f -name '*.agdai' -delete
