KNOWNTARGETS 			:= CoqMakefile
KNOWNFILES   			:= Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
				$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
				$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

create-doc-folder:
				@echo "Creating documentation directory."

				@mkdir -p documentation

				@mkdir -p documentation/Definitions
				@mkdir -p documentation/Theorems

build-doc: | create-doc-folder
				@echo "Building documentation."
				@for f in theories/Definitions/*.v; do \
						echo "Building documentation for file $${f}."; \
						coqdoc -d documentation/Definitions $${f}; \
				done
				@for f in theories/Theorems/*.v; do \
						echo "Building documentation for file $${f}."; \
						coqdoc -d documentation/Theorems $${f}; \
				done	

clean:
				@echo "Deleting build files."
				@rm -rf .CoqMakefile.d CoqMakefile CoqMakefile.conf .lia.cache
				@rm -rf theories/Definitions/*.vo theories/Definitions/*.vok theories/Definitions/*.vos theories/Definitions/*.glob theories/Definitions/.*.aux theories/Theorems/*.vo theories/Theorems/*.vok theories/Theorems/*.vos theories/Theorems/*.glob theories/Theorems/.*.aux
				@echo "Deleting documentation."
				@rm -rf documentation

all: invoke-coq_makefile build-doc

.PHONY: invoke-coqmakefile $(KNOWNFILES)

%: invoke-coqmakefile
				@true