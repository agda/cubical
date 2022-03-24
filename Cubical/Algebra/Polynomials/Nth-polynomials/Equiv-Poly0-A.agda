{-# OPTIONS --safe #-}
module Cubical.Algebra.Polynomials.Nth-polynomials.Equiv-Poly0-A where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec 

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Polynomials.Polynomials

open import Cubical.Algebra.Polynomials.Nth-polynomials.Base
open import Cubical.Algebra.Polynomials.Nth-polynomials.CommRing-Structure

private variable
  l l' : Level

module Equiv-Poly0-A (A' : CommRing l) where
  A = fst A'
  cra = snd A'

  open CommRingStr cra renaming (is-set to isSetA)
  open PolyHIT A'
  open Nth-Pol-CommRing A' 0


-----------------------------------------------------------------------------
-- Equivalence

  Poly0→A : Poly 0 → A
  Poly0→A = Poly-Rec-Set.f 0 A isSetA 
             0r
             (λ v a → a)
             _+_
             +Assoc
             +Rid
             +Comm
             (λ _ → refl)
             λ _ a b → refl

  A→Poly0 : A → Poly 0
  A→Poly0 a = base [] a

  e_sect : (a : A) → Poly0→A (A→Poly0 a) ≡ a
  e_sect a = refl

  e_retr : (P : Poly 0) → A→Poly0 (Poly0→A P) ≡ P
  e_retr = Poly-Ind-Prop.f 0
           (λ P → A→Poly0 (Poly0→A P) ≡ P)
           (λ _ → trunc _ _)
           (base-0P [])
           (λ { [] a → refl })
           λ {U V} ind-U ind-V → (sym (base-Poly+ [] (Poly0→A U) (Poly0→A V))) ∙ (cong₂ _Poly+_ ind-U ind-V)


-----------------------------------------------------------------------------
-- Ring homomorphism

  map-0P : Poly0→A 0P ≡ 0r
  map-0P = refl

  Poly0→A-gmorph : (P Q : Poly 0) → Poly0→A ( P Poly+ Q) ≡ Poly0→A P + Poly0→A Q
  Poly0→A-gmorph P Q = refl

  map-1P : Poly0→A 1P ≡ 1r
  map-1P = refl
  
  Poly0→A-rmorph : (P Q : Poly 0) → Poly0→A ( P Poly* Q) ≡ Poly0→A P · Poly0→A Q
  Poly0→A-rmorph = Poly-Ind-Prop.f 0
                    (λ P → (Q : Poly 0) → Poly0→A (P Poly* Q) ≡ Poly0→A P · Poly0→A Q)
                    (λ P p q i Q j → isSetA (Poly0→A (P Poly* Q)) (Poly0→A P · Poly0→A Q) (p Q) (q Q) i j)
                    (λ Q → sym (RingTheory.0LeftAnnihilates (CommRing→Ring A') (Poly0→A Q)))
                    (λ v a → Poly-Ind-Prop.f 0
                              (λ P → Poly0→A (base v a Poly* P) ≡ Poly0→A (base v a) · Poly0→A P)
                              (λ _ → isSetA _ _)
                              (sym (RingTheory.0RightAnnihilates (CommRing→Ring A') (Poly0→A (base v a))))
                              (λ v' a' → refl)
                              λ {U V} ind-U ind-V → (cong₂ _+_ ind-U ind-V) ∙ (sym (·Rdist+ _ _ _)))
                    λ {U V} ind-U ind-V Q → (cong₂ _+_ (ind-U Q) (ind-V Q)) ∙ (sym (·Ldist+ _ _ _))
