{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.NatAsAlmostRing where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Algebra.RingSolver.AlmostRing
open import Cubical.Algebra.Semigroup    hiding (⟨_⟩)
open import Cubical.Algebra.Monoid       hiding (⟨_⟩)
open import Cubical.Algebra.AbGroup   hiding (⟨_⟩)


ℕAsAlmostRing : AlmostRing {ℓ-zero}
ℕAsAlmostRing = almostring ℕ 0 1  _+_ _*_ (λ n → n)
                (isalmostring
                  (ismonoid (issemigroup isSetℕ +-assoc) (λ n → (+-zero n) , refl))
                  (ismonoid (issemigroup isSetℕ *-assoc) λ n → (*-identityʳ n) , (*-identityˡ n))
                  +-comm
                  *-comm
                  (λ k l n → sym (*-distribˡ k l n) )
                  (λ k l n → sym (*-distribʳ k l n))
                  (λ _ _ → refl) λ _ _ → refl)
