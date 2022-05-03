A standard library for Cubical Agda
===================================

This library compiles with the latest official release of
[Agda](https://github.com/agda/agda/). For detailed install
instructions see the
[INSTALL](https://github.com/agda/cubical/blob/master/INSTALL.md)
file.

The source code has a glorious clickable [rendered version](https://agda.github.io/cubical/Cubical.README.html).

If you want to use Agda 2.6.2 instead of the latest release version, you
can check out the tag `v0.3` of this library.

If you want to use Agda 2.6.1.3 instead of the latest release version, you
can check out the tag `v0.2` of this library.

If you want to use Agda 2.6.0.1 instead of the latest release version, you
can check out the tag `v0.1` of this library.

For some introductory lecture notes see the material for the Cubical Agda course
of the [EPIT 2021 spring school](https://github.com/HoTT/EPIT-2020/blob/main/04-cubical-type-theory/).

For a paper on with details about Cubical Agda, see [Cubical Agda: a dependently typed
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

* [Anders Mörtberg](https://staff.math.su.se/anders.mortberg/)

* [Andrea Vezzosi](http://saizan.github.io/)

* [Evan Cavallo](https://staff.math.su.se/evan.cavallo/)

[![Build Status](https://travis-ci.org/agda/cubical.svg?branch=master)](https://travis-ci.org/agda/cubical)

[![Gitter](https://badges.gitter.im/agda/cubical.svg)](https://gitter.im/agda/cubical?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge)
