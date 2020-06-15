An experimental library for Cubical Agda
========================================

[![Gitter](https://badges.gitter.im/agda/cubical.svg)](https://gitter.im/agda/cubical?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge)

This library compiles with the master branch of the development
version of [Agda](https://github.com/agda/agda/). For detailed install
instructions see the
[INSTALL](https://github.com/agda/cubical/blob/master/INSTALL.md)
file.

If you want to use Agda 2.6.0.1 instead of the latest development version, you
can check out the tag `v0.1` of this library.

If you want to use Agda 2.6.1 instead of the latest development version, you
can check out the tag `v0.2` of this library.

For an introduction to Cubical Agda, see [Cubical Agda: a dependently typed
programming language with univalence and higher inductive
types](https://dl.acm.org/doi/10.1145/3341691) by Andrea Vezzosi, Anders
Mörtberg, and Andreas Abel.

For an introduction to this library, see this [blog
post](https://homotopytypetheory.org/2018/12/06/cubical-agda/). Note that many
files and results have moved since this blog post was written.

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

Maintainers
-----------

* [Anders Mörtberg](http://www.cs.cmu.edu/~amoertbe/)

* [Andrea Vezzosi](http://saizan.github.io/)

[![Build Status](https://travis-ci.org/agda/cubical.svg?branch=master)](https://travis-ci.org/agda/cubical)
