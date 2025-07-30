AGDA_BIN?=agda
AGDA_FLAGS?=-W error
AGDA_EXEC?=$(AGDA_BIN) $(AGDA_FLAGS)
FIX_WHITESPACE?=fix-whitespace
RTS_OPTIONS=+RTS -M32G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)

.PHONY : all
all : build

.PHONY : build
build :
	$(MAKE) AGDA_EXEC=$(AGDA_BIN) check

.PHONY : test
test : check-whitespace check

# checking and fixing whitespace

.PHONY : fix-whitespace
fix-whitespace:
	$(FIX_WHITESPACE)

.PHONY : check-whitespace
check-whitespace:
	$(FIX_WHITESPACE) --check

# typechecking and generating listings for all files

.PHONY : check
check:
	$(AGDA) --build-library

.PHONY : timings
timings: clean
	$(AGDA) --build-library -v profile.modules:10

.PHONY : listings
listings: $(wildcard Cubical/**/*.agda)
	./generate-everything.sh > Cubical/Everything.agda
	$(AGDA) Cubical/Everything.agda -i. -isrc --html -vhtml:0

.PHONY : clean
clean:
	find . -type f -name '*.agdai' -delete

.PHONY: debug
debug : ## Print debug information.
	@echo "AGDA_BIN              = $(AGDA_BIN)"
	@echo "AGDA_FLAGS            = $(AGDA_FLAGS)"
	@echo "AGDA_EXEC             = $(AGDA_EXEC)"
	@echo "AGDA                  = $(AGDA)"
