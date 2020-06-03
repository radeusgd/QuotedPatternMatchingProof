#!/bin/bash
set -xe
rm *.vo || echo "Nothing to clean"
coqc syntax.v
coqc types.v
coqc semantics.v
coqc properties.v

echo "Success!"
