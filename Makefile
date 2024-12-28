KNOWNTARGETS 			:= CoqMakefile
KNOWNFILES   			:= Makefile _CoqProject
DEFINITIONS_FILES := definitions/*.v

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
				$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
				$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

create-doc-folder:
				@echo "Creating documentation directory."

				@mkdir -p documentation

build-doc: | create-doc-folder
				@echo "Building documentation."
				@for f in definitions/*.v; do \
						echo "Building documentation for file $${f}."; \
						coqdoc -d documentation $${f}; \
				done
				

clean:
				@echo "Deleting build files."
				@rm -rf definitions/*.vo definitions/*.vok definitions/*.vos definitions/*.glob definitions/.*.aux
				@echo "Deleting documentation."
				@rm -rf documentation

all: invoke-coq_makefile build-doc

.PHONY: invoke-coqmakefile $(KNOWNFILES)

%: invoke-coqmakefile
				@true