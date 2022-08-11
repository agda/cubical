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


Reviewing of pull requests
--------------------------
If you switch your draft pull request (PR) to 'ready to merge',
or directly create an open PR,
we should request a review, by one of the reviewers below.
If that doesn't happen, you can also request a reviewer yourself (for reviewer expertise see below),
to make us aware of the open PR.

| Reviewer                                                                | github handle | Area of expertise                           |
|-------------------------------------------------------------------------|---------------|---------------------------------------------|
| [Anders Mörtberg](https://staff.math.su.se/anders.mortberg/)            | [mortberg](https://github.com/mortberg) | *Most topics*  |
| [Evan Cavallo](https://staff.math.su.se/evan.cavallo/)                  | [ecavallo](https://github.com/ecavallo) |                |
| [Felix Cherubini](https://felix-cherubini.de)                           | [felixwellen](https://github.com/felixwellen) | *Mainly algebra related topics* |
| [Max Zeuner](https://www.su.se/english/profiles/maze1512-1.450461)      | [mzeuner](https://github.com/mzeuner) | *Algebra related topics*                   |
| [Axel Ljungström](https://www.su.se/english/profiles/axlj4439-1.450268) | [aljungstrom](https://github.com/aljungstrom) | *Synthetic homotopy theory and cohomology* |
| [Andrea Vezzosi](http://saizan.github.io/)                              | [Saizan](https://github.com/Saizan)   | *Inactive*                                 |

[Overview of the current open PRs, descending time since last action](https://github.com/agda/cubical/pulls?q=is%3Apr+is%3Aopen+sort%3Aupdated-asc+draft%3Afalse)

[![Build Status](https://travis-ci.org/agda/cubical.svg?branch=master)](https://travis-ci.org/agda/cubical)
