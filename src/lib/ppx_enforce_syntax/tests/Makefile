# Makefile for ppx_enforce_syntax tests

# useful for negative tests, so we know the failure is the failure
# we expect

ifdef VERBOSE
REDIRECT=
else
REDIRECT= > /dev/null 2>&1
endif

.PHONY: positive-tests negative-tests

all : positive-tests negative-tests

positive-tests :
	@ echo -n "Good syntax, should succeed..."
	@ dune build good_syntax.cma ${REDIRECT}
	@ echo "OK"

negative-tests :
	@ echo -n "Missing deriving version, should fail..."
	@ ! dune build bad_syntax_missing_version.cma ${REDIRECT}
	@ echo "OK"
