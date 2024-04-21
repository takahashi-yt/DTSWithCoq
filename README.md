# DTS With Coq Library

# Outline

This library provides Coq tactics to Dependent Type Semantics (\[1, 2\], which is a framework for natural language semantics.

\[1\] Daisuke Bekki. Representing Anaphora with Dependent Types. Nicholas Asher and Sergei Soloviev (eds.), *Logical Aspects of Computational Linguistics - 8th International Conference, LACL 2014, Toulouse, France, June 18-20, 2014. Proceedings*, vol. 8535 of Lecture Notes in Computer Science, 14--29. Springer. (2014)

\[2\] Daisuke Bekki and Koji Mineshima. Context-Passing and Underspecification in Dependent Type Semantics. Stergios Chatzikyriakidis and Zhaohui Luo (eds.), *Modern Perspectives in Type-Theoretical Semantics*, vol. 98 of Studies in Linguistics and Philosophy, 11--41. Springer, Cham. (2017)

## To Use the Library

Download the library to your working directory, then run the following on the directory including the library's _CoqProject

`coq_makefile -f _CoqProject -o CoqMakefile`

and compile the library with

`make -f CoqMakefile`

To use the semantic templates and tactics in the library, it suffices to load DTSTactics.v by writing, e.g.,

`Require Import DTSTactics.`

## To Customize the Library

You can add a new tactic (resp. a new semantic template) to DTSTactics.v (resp. SemanticTemplates.v).

Don't forget to recompile the library when you revised DTSTactics.v and/or SemanticTemplates.v!
