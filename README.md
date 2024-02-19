# SESAME

An implementation of the Strong Exponential Substitution Abstract Machine without
Erasure (SESAME) described in the paper.

"IMELL Cut Elimination with Linear Overhead" by
B. Accattoli and C. Sacerdoti Coen, submitted at FSCD 2024.


## Description

The sesame executable implements a REPL (Read Eval Print Loop) to evaluate
Intuitionistic Multiplicative Exponential Linear Logic (IMELL) terms. The loop
asks the user to enter a term, checks the term for properness and then evaluates
it, showing all reduction steps.

The terms are encoded in the Exponential Substitution Calculus (ESC) syntax.
The implementation is based on term graphs. Reduction takes time which is
bi-linear in the size of the initial term and the number of
exponential/multiplicative steps of IMELL.

Before starting the REPL loop, some example terms are evaluated. Among them
there are examples from a family of terms that perform a number of exponential
steps without even a single multiplicative steps. They show that, contrarily to
what happens for lambda-calculi, the number of beta-steps alone is not a cost
model.

## Library API

Searchable documentation for every datatype and function can be found at
<https://sacerdot.github.io/sesame>.


## Compiling and running sesame

To compile sesame, one needs a working installation of OCaml and Dune.
The simplest way is to use the OPAM package manager for OCaml:

- Install OPAM <https://opam.ocaml.org/doc/Install.html>
- Install dune, odoc and sherlodoc via opam:
  `opam update && opam install dune odoc sherlodoc`
- [optional] Compile sesame's documentation via dune and open it in a browser:
  `opam build @doc && open _build/default/_doc/_html/sesame/index.html`
  The same documentation can be found at <https://sacerdot.github.io/sesame>
- Run sesame's REPL: `opam exec sesame`
  The input grammar is printed by the REPL itself.
