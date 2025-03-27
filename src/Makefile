AGDA_BIN?=agda
AGDA_FLAGS?=-W error
SRC_DIR=.
README_AGDA=./README.agda
AGDA_EXEC?=$(AGDA_BIN) $(AGDA_FLAGS)
RTS_OPTIONS=+RTS -M8G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)
RUNHASKELL?=runhaskell
EVERYTHINGS=$(RUNHASKELL) ./Everythings.hs

# Finds all .agda files in the current directory and subdirectories
FIND_AGDA_FILES = find $(SRC_DIR) -name "*.agda"
AGDA_FILES = $(shell $(FIND_AGDA_FILES))

# The targets are the .agdai files corresponding to the .agda files
AGDAI_FILES = $(AGDA_FILES:.agda=.agdai)
.PHONY : all
all : test

.PHONY : README_only
README-only :
	$(AGDA) $(README_AGDA)

.PHONY : litmus
litmus :
	$(AGDA) $(SRC_DIR)/Grammar.agda

.PHONY : test
test :
	$(MAKE) AGDA_EXEC=$(AGDA_BIN) gen-everythings check

.PHONY : checks
checks : gen-and-check-everythings check-README check

# checking and generating Everything files

.PHONY : check-everythings
check-everythings:
	$(EVERYTHINGS) check-except

.PHONY : gen-everythings
gen-everythings:
	$(EVERYTHINGS) gen-except

.PHONY : gen-and-check-everythings
gen-and-check-everythings:
	$(EVERYTHINGS) gen-except
	$(EVERYTHINGS) check-except

.PHONY : check-README
check-README:
	$(EVERYTHINGS) check-README

.PHONY : check
check: gen-everythings
	$(AGDA) $(README_AGDA)

.PHONY : clean
clean:
	find $(SRC_DIR) -type f -name '*.agdai' -delete
	find $(SRC_DIR) -type f -name "Everything.agda" -delete
	rm -rf ./_build

.PHONY: debug
debug : ## Print debug information.
	@echo "AGDA_BIN              = $(AGDA_BIN)"
	@echo "AGDA_FLAGS            = $(AGDA_FLAGS)"
	@echo "AGDA_EXEC             = $(AGDA_EXEC)"
	@echo "AGDA                  = $(AGDA)"
	@echo "SRC_DIR               = $(SRC_DIR)"
	@echo "README_AGDA           = $(README_AGDA)"

