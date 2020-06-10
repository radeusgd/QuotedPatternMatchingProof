# A Mechanized Theory of Quoted Patterns

This is a semester project done in the Spring semester of 2020/2021 in the LAMP laboratory at the EPFL under supervision of Fengyun Liu and Nicolas Stucki.

Its goal was to create a mechanized proof of soundness of calculus defined in *A Theory of Quoted Code Patterns* which is a formalization of pattern matching on code available in Scala 3 as part of its new macro system.

## Artifacts

The mechanization in the Coq proof assistant can be found in the [`calculus/`](calculus/) directory.

It uses Coq version 8.9.1 and [DbLib](https://github.com/coq-community/dblib/) library.

The report of the semester project is available at [`report.pdf`](report.pdf).
The [`examples/`](examples/) directory contains some examples from the report.
