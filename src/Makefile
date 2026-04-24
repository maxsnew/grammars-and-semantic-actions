AGDA_BIN?=agda
AGDA_FLAGS?= -j10
SRC_DIR=.
AGDA_EXEC?=$(AGDA_BIN) $(AGDA_FLAGS)
RTS_OPTIONS=+RTS -M16G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)

.PHONY : all
all : test

.PHONY : test
test : check

.PHONY : check
check:
	$(AGDA) --build-library

.PHONY : clean
clean:
	find $(SRC_DIR) -type f -name '*.agdai' -delete

.PHONY: debug
debug : ## Print debug information.
	@echo "AGDA_BIN              = $(AGDA_BIN)"
	@echo "AGDA_FLAGS            = $(AGDA_FLAGS)"
	@echo "AGDA_EXEC             = $(AGDA_EXEC)"
	@echo "AGDA                  = $(AGDA)"
	@echo "SRC_DIR               = $(SRC_DIR)"
