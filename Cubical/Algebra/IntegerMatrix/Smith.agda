{-

Smith Normal Form

Referrences:
  Guillaume Cano, Cyril Cohen, Maxime Dénès, Anders Mörtberg, Vincent Siles,
  "Formalized linear algebra over Elementary Divisor Rings in Coq"
  (https://arxiv.org/abs/1601.07472)

-}
module Cubical.Algebra.IntegerMatrix.Smith where

open import Cubical.Algebra.IntegerMatrix.Smith.NormalForm public
open import Cubical.Algebra.IntegerMatrix.Smith.Normalization public using (smith)
