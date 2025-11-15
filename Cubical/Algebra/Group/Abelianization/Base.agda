{-

This file contains:
    - the abelianization of groups as a HIT as proposed in https://arxiv.org/abs/2007.05833

The definition of the abelianization is not as a set-quotient, since the relation of abelianization is cumbersome to work with.

-}
module Cubical.Algebra.Group.Abelianization.Base where

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties

private
  variable
    ℓ : Level

module _ (G : Group ℓ) where
  open GroupStr {{...}}
  open GroupTheory G
  private
    instance
      _ = snd G

  {-
    The definition of the abelianization of a group as a higher inductive type.
    The generality of the comm relation will be needed to define the group structure on the abelianization.
  -}
  data Abelianization : Type ℓ where
    η : (g : fst G) → Abelianization
    comm : (a b c : fst G) → η (a · (b · c)) ≡ η (a · (c · b))
    isset : (x y : Abelianization) → (p q : x ≡ y) → p ≡ q
