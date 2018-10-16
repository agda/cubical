A basic experimental library for Cubical Agda
=============================================

At the moment (2018-10-16) this requires the hits-transp branch of
Agda:


```
git clone https://github.com/agda/agda
cd agda
git checkout hits-transp
cabal install
```

The type theory is a variation of the "CCHM" cubical type theory of:

[Cubical Type Theory: a constructive interpretation of the univalence
axiom](https://arxiv.org/abs/1611.02108) - Cyril Cohen, Thierry
Coquand, Simon Huber, Anders Mörtberg.


The key difference is that the Kan composition operations are
decomposed into homogeneous composition and generalized transport as
in:

[On Higher Inductive Types in Cubical Type
Theory](https://arxiv.org/abs/1802.01170) - Thierry Coquand, Simon
Huber, Anders Mörtberg



Maintainers
-----------

* [Anders Mörtberg](http://www.cs.cmu.edu/~amoertbe/)

* [Andrea Vezzosi](http://www.cse.chalmers.se/~vezzosi/)
