#!/bin/sh

./rebar3 clean

if [ ! -f ./_build/default/bin/cauder ]; then
   ./rebar3 escriptize
fi

./_build/default/bin/cauder