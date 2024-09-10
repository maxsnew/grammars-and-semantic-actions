AGDA = agda +RTS -M6G -RTS
FIX_WHITESPACE = fix-whitespace

# Finds all .agda files in the current directory and subdirectories
FIND_AGDA_FILES = find . -name "*.agda"
AGDA_FILES = $(shell $(FIND_AGDA_FILES))

# The targets are the .agdai files corresponding to the .agda files
AGDAI_FILES = $(AGDA_FILES:.agda=.agdai)

.PHONY: all
all: test check-whitespace check-line-lengths

.PHONY: quicktest
quicktest : clean
	@for file in $(AGDA_FILES); do \
		$(AGDA) $$file || exit 1; \
	done; \
    echo "All files compiled successfully."

.PHONY: test
test :
	@failed=""; \
	for file in $(AGDA_FILES); do \
		$(AGDA) $$file || failed="$$failed $$file"; \
	done; \
	[ -z "$$failed" ] || (echo "Failed to compile:$$failed" && false)

.PHONY: check-whitespace
check-whitespace:
	cd ../.. && $(FIX_WHITESPACE) --check

.PHONY: check-line-lengths
check-line-lengths:
	bash check-line-lengths.sh

.PHONY: clean
clean:
	find . -name "*.agdai" -type f -delete
