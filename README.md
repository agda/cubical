An experimental library for Cubical Agda
========================================

This library compiles with the master branch of the development
version of [Agda](https://github.com/agda/agda/). For detailed install
instructions see the
[INSTALL](https://github.com/agda/cubical/blob/master/INSTALL.md)
file.


The type theory that Cubical Agda implements is a variation of the
cubical type theory of:

[Cubical Type Theory: a constructive interpretation of the univalence
axiom](https://arxiv.org/abs/1611.02108) - Cyril Cohen, Thierry
Coquand, Simon Huber, Anders Mörtberg.


The key difference is that the Kan composition operations are
decomposed into homogeneous composition and generalized transport as
in:

[On Higher Inductive Types in Cubical Type
Theory](https://arxiv.org/abs/1802.01170) - Thierry Coquand, Simon
Huber, Anders Mörtberg.

This makes it possible to directly represent higher inductive types.

For an introduction to Cubical Agda and this library see this
[blog post](https://homotopytypetheory.org/2018/12/06/cubical-agda/). Note
that many files and results have moved compared to state of the
library described in the blog post.


Maintainers
-----------

* [Anders Mörtberg](http://www.cs.cmu.edu/~amoertbe/)

* [Andrea Vezzosi](http://www.cse.chalmers.se/~vezzosi/)

[![Build Status](https://travis-ci.org/agda/cubical.svg?branch=master)](https://travis-ci.org/agda/cubical)
