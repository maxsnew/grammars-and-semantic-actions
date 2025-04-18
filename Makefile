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
all : test

.PHONY : litmus
litmus :
	$(AGDA) Grammar.agda

.PHONY : test
test :
	$(AGDA) Evaluate.agda

.PHONY : gen-and-check-everythings
gen-and-check-everythings:
	$(EVERYTHINGS) gen-except
	$(EVERYTHINGS) check-except

.PHONY : clean
clean:
	find . -type f -name '*.agdai' -delete
