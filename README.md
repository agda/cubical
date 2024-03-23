A standard library for Cubical Agda
===================================

The source code has a glorious clickable [rendered version](https://agda.github.io/cubical/Cubical.README.html).

There is also a [discord server](https://discord.gg/yjTKHzepMx), shared with [agda-unimath](https://unimath.github.io/agda-unimath/) and the [1lab](https://1lab.dev/).

Compiling, using and installing
-------------------------------
This library checks with [Agda](https://github.com/agda/agda/) version indicated in the table below.
For detailed install instructions see the
[INSTALL](https://github.com/agda/cubical/blob/master/INSTALL.md)
file.
If you want to use some specific release of Agda,
the following table lists which releases of Agda you can use with which release of this library.
Agda versions as written below, correspond to tags.

| cubical library version | Agda versions       |
|-------------------------|---------------------|
| current master          | `v2.6.4` `v2.6.4.1` |
| `v0.7`                  | `v2.6.4` `v2.6.4.1` |
| `v0.6`                  | `v2.6.4`            |
| `v0.5`                  | `v2.6.3` `v2.6.4`   |
| `v0.4`                  | `v2.6.2.2`          |
| `v0.3`                  | `v2.6.2`            |
| `v0.2`                  | `v2.6.1.3`          |
| `v0.1`                  | `v2.6.0.1`          |

For example, if you have Agda 2.6.2.2, you can switch to version 0.4 of the cubical library with
```
git checkout v0.4
```

Learning materials
------------------
* Introductory material from the HoTTest summer school:
  [literate agda files](https://github.com/martinescardo/HoTTEST-Summer-School/tree/main/Agda/Cubical)
  [recordings on youtube](https://www.youtube.com/channel/UC-9jDbJ-HegCFuWuam1SfvQ)

* For an introduction to this library, see this [blog
  post](https://homotopytypetheory.org/2018/12/06/cubical-agda/). Note that many
  files and results have moved since this blog post was written.

* For some introductory lecture notes see the material for the Cubical Agda course
  of the [EPIT 2021 spring school](https://github.com/HoTT/EPIT-2020/blob/main/04-cubical-type-theory/).


Theoretical background
----------------------
For a paper with details about Cubical Agda, see [Cubical Agda: a dependently typed
programming language with univalence and higher inductive
types](https://dl.acm.org/doi/10.1145/3341691) by Andrea Vezzosi, Anders
Mörtberg, and Andreas Abel.

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
to make us aware of the open PR. Feel free to use Discord to get in touch with a reviewer in case reviewing is taking a very long time.

| Reviewer                                                                | github handle | Area of expertise                           | Queue |
|-------------------------------------------------------------------------|---------------|---------------------------------------------|------|
| [Anders Mörtberg](https://staff.math.su.se/anders.mortberg/)            | [mortberg](https://github.com/mortberg) | *Most topics*  | [link](https://github.com/agda/cubical/pulls?q=is%3Apr+review-requested%3Amortberg+) |
| [Evan Cavallo](https://staff.math.su.se/evan.cavallo/)                  | [ecavallo](https://github.com/ecavallo) | *Most topics*  | [link](https://github.com/agda/cubical/pulls?q=is%3Apr+review-requested%3Aecavallo+) |
| [Felix Cherubini](https://felix-cherubini.de)                           | [felixwellen](https://github.com/felixwellen) | *Mainly algebra related topics* | [link](https://github.com/agda/cubical/pulls?q=is%3Apr+review-requested%3Afelixwellen+) |
| [Max Zeuner](https://www.su.se/english/profiles/maze1512-1.450461)      | [mzeuner](https://github.com/mzeuner) | *Algebra related topics*                   | [link](https://github.com/agda/cubical/pulls?q=is%3Apr+review-requested%3Amzeuner+) |
| [Axel Ljungström](https://www.su.se/english/profiles/axlj4439-1.450268) | [aljungstrom](https://github.com/aljungstrom) | *Synthetic homotopy theory and cohomology* | [link](https://github.com/agda/cubical/pulls?q=is%3Apr+review-requested%3Aaljungstrom+) |
| [Andrea Vezzosi](http://saizan.github.io/)                              | [Saizan](https://github.com/Saizan)   | *Inactive*                                 | [link](https://github.com/agda/cubical/pulls?q=is%3Apr+review-requested%3ASaizan+) |

[Overview](https://github.com/agda/cubical/pulls?q=is%3Apr+is%3Aopen+sort%3Aupdated-asc+draft%3Afalse) of the current open PRs, descending time since last action.

[![Build Status](https://travis-ci.org/agda/cubical.svg?branch=master)](https://travis-ci.org/agda/cubical)
