DUNE?=dune
DUNEARGS?=--display=short

BUILDCMD?=$(DUNE) build $(DUNEARGS)
CLEANCMD?=$(DUNE) clean $(DUNEARGS)

all:
	@$(BUILDCMD) -- @all

doc:
	@$(BUILDCMD) -- @doc

%.vo:FORCE
	@$(BUILDCMD) -- "$@"

%.required_vo:FORCE
# A trick from https://github.com/ocaml/dune/issues/7972#issue-1757514337
# to build the .vo files needed to check interactively $*.v
	@$(DUNE) rocq top $(DUNEARGS) --toplevel=true -- $*.v

clean:
	@$(CLEANCMD)
#	@rm -f -- .lia.cache

.PHONY:all clean FORCE
FORCE:
