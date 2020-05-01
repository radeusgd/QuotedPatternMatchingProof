#!/bin/bash
set -xe
rm *.vo
coqc syntax.v
coqc types.v
coqc semantics.v
coqc properties.v
