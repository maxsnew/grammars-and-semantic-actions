AGDA_BIN?=agda
AGDA_FLAGS?=-W error
AGDA_EXEC?=$(AGDA_BIN) $(AGDA_FLAGS)
FIX_WHITESPACE?=fix-whitespace
RTS_OPTIONS=+RTS -M8G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)
RUNHASKELL?=runhaskell
EVERYTHINGS=$(RUNHASKELL) ./Everythings.hs

# Finds all .agda files in the current directory and subdirectories
FIND_AGDA_FILES = find . -name "*.agda"
AGDA_FILES = $(shell $(FIND_AGDA_FILES))

# The targets are the .agdai files corresponding to the .agda files
AGDAI_FILES = $(AGDA_FILES:.agda=.agdai)
.PHONY : all
all : build

.PHONY : build
build :
	$(MAKE) AGDA_EXEC=$(AGDA_BIN) gen-everythings check

.PHONY : test
test : check-whitespace gen-and-check-everythings check-README check

# checking and fixing whitespace

.PHONY : fix-whitespace
fix-whitespace:
	$(FIX_WHITESPACE)

.PHONY : check-whitespace
check-whitespace:
	$(FIX_WHITESPACE) --check

.PHONY : litmus
litmus :
	$(AGDA) Grammar.agda

# checking and generating Everything files

.PHONY : check-everythings
check-everythings:
	$(EVERYTHINGS) check-except

.PHONY : gen-everythings
gen-everythings:
	$(EVERYTHINGS) gen-except Grammar/Coinductive

.PHONY : gen-and-check-everythings
gen-and-check-everythings:
	$(EVERYTHINGS) gen-except Grammar/Coinductive
	$(EVERYTHINGS) check-except Grammar/Coinductive

.PHONY : check-README
check-README:
	$(EVERYTHINGS) check-README

# typechecking and generating listings for all files imported in README

.PHONY : check
check: gen-everythings
	$(AGDA) README.agda

.PHONY : timings
timings: clean gen-everythings
	$(AGDA) -v profile.modules:10 README.agda

.PHONY : listings
listings: $(wildcard Cubical/**/*.agda)
	$(AGDA) -i. -isrc --html README.agda -v0

.PHONY : clean
clean:
	find . -type f -name '*.agdai' -delete
	find . -type f -name "Everything.agda" -delete

.PHONY: debug
debug : ## Print debug information.
	@echo "AGDA_BIN              = $(AGDA_BIN)"
	@echo "AGDA_FLAGS            = $(AGDA_FLAGS)"
	@echo "AGDA_EXEC             = $(AGDA_EXEC)"
	@echo "AGDA                  = $(AGDA)"

.PHONY: check-line-lengths
check-line-lengths:
	bash check-line-lengths.sh
