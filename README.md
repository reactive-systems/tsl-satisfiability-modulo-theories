# TSL Satisfiability modulo Theories – Proof of Concept


This project implements a proof of concept of a partial algorithm solving the satisfiability problem of Temporal Stream Logic in the theory of uninterpreted functions (and possibly also the theory of equality).
This implementation contains the implementation of the algorithm (``tslsat``) as a small fuzzer for TSL specification (``tslfuzz``) and a pretty printer for BSAs (``tsl2bsa``). 

## Overview

The source code can be found in the ``src/`` folder.
The ``benchmarks`` folder contains the following subfolders:

- benchmarks/test: Different special benchmarks made to test this algorithm
- benchmarks/fuzzed: Benchmarks created by ``tslfuzz``. The "depth" is included in the benchmarks name "randD<DEPTH>..."
- benchmarks/syntroids: The specifications of the [syntroids](https://www.react.uni-saarland.de/casestudies/syntroids/) project
- benchmarks/scalability: Benchmarks to test the scalability of this approach
- benchmarks/story: Benchmarks tied to a small story.

Our results of the benchmarking can be found in the ``results/`` folder in the form of SCV files.

## Building and Usage

Perquisites:
- [stack](https://docs.haskellstack.org/en/stable/README/)
- [spot (2.9.4)](https://spot.lrde.epita.fr/)

To build the project, simply call ``make`` in the top-level folder.
If you want to install the tools locally (no root required!), call ``make install``.
Note that for ``tsl2bsa`` and ``tsltusat`` to qork properly, spots ``ltl2tgba`` and ``randltl`` have to be in your ``$PATH``.

To see how exactly each tools is called, call it without any arguments.

## Benchmarking

Benchmarking can be done by calling ``./benchmark.sh``. 
The benchmarks in ``benchmarks/story/`` have a timeout of 2 minutes, all other have a timeout of 30 seconds.
In each case spot has a 20 second timeout for doing optimizations.
The result for each benchmarks is a CSV entry (in a separate file for each subfolder) with
- the benchmarks name
- the result of spot (``ltl2tgba``), which can be:
    - "OPT": ``ltl2tgba`` was able to optimize the Buechi automaton (within 20 seconds).
    - "-": an unoptimized Buechi automaton was used.
    - "TO": ``ltl2tgba`` did not terminate at all, hence it is responsible for the general timeout
- the algorithms result: "SAT", "UNSAT" or "TO" if the program timed out
- the execution time in milliseconds

