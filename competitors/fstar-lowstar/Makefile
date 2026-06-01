# Low* in-place quicksort: verify -> extract C (KaRaMeL) -> compile (gcc).
#
# Run inside the per-folder devShell (which puts fstar.exe, krml, gcc on PATH
# and sets KRML_HOME):
#
#     nix develop          # or: direnv allow
#     make                 # verify + extract + compile + run
#
# KRML_HOME is exported by the flake's devShell shellHook.

FSTAR    ?= fstar.exe
KRML     ?= krml
CC       ?= gcc

# KaRaMeL ships its ulib overlay (e.g. C, WasmSupport) under $(KRML_HOME)/krmllib;
# F* needs it on the include path to typecheck Low* that mentions those modules.
FSTAR_INCLUDES = --include $(KRML_HOME)/krmllib
FSTAR_FLAGS    = $(FSTAR_INCLUDES) --z3rlimit 400

OUT = out

.PHONY: all verify extract compile run clean

all: run

# 1. Verify: sorted /\ permutation /\ memory-safety /\ disjoint-range modifies.
verify:
	$(FSTAR) $(FSTAR_FLAGS) Quicksort.fst

# 2. Extract to C. Proofs/specs are erased; only the in-place algorithm remains.
extract: verify
	rm -rf $(OUT) && mkdir -p $(OUT)
	$(KRML) -skip-linking -skip-compilation -tmpdir $(OUT) \
	        -no-prefix Quicksort Quicksort.fst

# 3. Compile the extracted C together with the hand-written driver.
compile: extract
	$(CC) -O2 -Wall \
	      -I $(OUT) -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	      $(OUT)/Quicksort.c driver.c -o $(OUT)/quicksort_test

run: compile
	./$(OUT)/quicksort_test

clean:
	rm -rf $(OUT)
