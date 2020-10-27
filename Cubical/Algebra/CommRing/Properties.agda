{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.CommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.CommRing.Base

private
  variable
    ℓ : Level

module Exponentiation (R' : CommRing {ℓ}) where
 open CommRingStr (snd R')
 private R = R' .fst

 -- introduce exponentiation
 _^_ : R → ℕ → R
 f ^ zero = 1r
 f ^ suc n = f · (f ^ n)

 infix 9 _^_

 -- and prove some laws
 ·-of-^-is-^-of-+ : (f : R) (m n : ℕ) → (f ^ m) · (f ^ n) ≡ f ^ (m +ℕ n)
 ·-of-^-is-^-of-+ f zero n = ·-lid _
 ·-of-^-is-^-of-+ f (suc m) n = sym (·-assoc _ _ _) ∙ cong (f ·_) (·-of-^-is-^-of-+ f m n)

 ^-ldist-· : (f g : R) (n : ℕ) → (f · g) ^ n ≡ (f ^ n) · (g ^ n)
 ^-ldist-· f g zero = sym (·-lid 1r)
 ^-ldist-· f g (suc n) = path
  where
  path : f · g · ((f · g) ^ n) ≡ f · (f ^ n) · (g · (g ^ n))
  path = f · g · ((f · g) ^ n)       ≡⟨ cong (f · g ·_) (^-ldist-· f g n) ⟩
         f · g · ((f ^ n) · (g ^ n)) ≡⟨ ·-assoc _ _ _ ⟩
         f · g · (f ^ n) · (g ^ n)   ≡⟨ cong (_· (g ^ n)) (sym (·-assoc _ _ _)) ⟩
         f · (g · (f ^ n)) · (g ^ n) ≡⟨ cong (λ r → (f · r) · (g ^ n)) (·-comm _ _) ⟩
         f · ((f ^ n) · g) · (g ^ n) ≡⟨ cong (_· (g ^ n)) (·-assoc _ _ _) ⟩
         f · (f ^ n) · g · (g ^ n)   ≡⟨ sym (·-assoc _ _ _) ⟩
         f · (f ^ n) · (g · (g ^ n)) ∎
