{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.Equiv.Poly0-A where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.Polynomials.Univariate.Base

open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.Polynomials.Multivariate.Properties
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly

private variable
  ℓ : Level

module Equiv-Poly0-A (A' : CommRing ℓ) where
  A = fst A'
  cra = snd A'

  open CommRingStr cra renaming (is-set to isSetA)
  open Nth-Poly-structure A' 0


-----------------------------------------------------------------------------
-- Equivalence

  Poly0→A : Poly A' 0 → A
  Poly0→A = Poly-Rec-Set.f A' 0 A isSetA
             0r
             (λ v a → a)
             _+_
             +Assoc
             +Rid
             +Comm
             (λ _ → refl)
             λ _ a b → refl

  A→Poly0 : A → Poly A' 0
  A→Poly0 a = base [] a

  e-sect : (a : A) → Poly0→A (A→Poly0 a) ≡ a
  e-sect a = refl

  e-retr : (P : Poly A' 0) → A→Poly0 (Poly0→A P) ≡ P
  e-retr = Poly-Ind-Prop.f A' 0
           (λ P → A→Poly0 (Poly0→A P) ≡ P)
           (λ _ → trunc _ _)
           (base-0P [])
           (λ { [] a → refl })
           λ {U V} ind-U ind-V → (sym (base-Poly+ [] (Poly0→A U) (Poly0→A V))) ∙ (cong₂ _Poly+_ ind-U ind-V)


-----------------------------------------------------------------------------
-- Ring homomorphism

  map-0P : Poly0→A 0P ≡ 0r
  map-0P = refl

  Poly0→A-gmorph : (P Q : Poly A' 0) → Poly0→A ( P Poly+ Q) ≡ Poly0→A P + Poly0→A Q
  Poly0→A-gmorph P Q = refl

  map-1P : Poly0→A 1P ≡ 1r
  map-1P = refl

  Poly0→A-rmorph : (P Q : Poly A' 0) → Poly0→A ( P Poly* Q) ≡ Poly0→A P · Poly0→A Q
  Poly0→A-rmorph = Poly-Ind-Prop.f A' 0
                    (λ P → (Q : Poly A' 0) → Poly0→A (P Poly* Q) ≡ Poly0→A P · Poly0→A Q)
                    (λ P p q i Q j → isSetA (Poly0→A (P Poly* Q)) (Poly0→A P · Poly0→A Q) (p Q) (q Q) i j)
                    (λ Q → sym (RingTheory.0LeftAnnihilates (CommRing→Ring A') (Poly0→A Q)))
                    (λ v a → Poly-Ind-Prop.f A' 0
                              (λ P → Poly0→A (base v a Poly* P) ≡ Poly0→A (base v a) · Poly0→A P)
                              (λ _ → isSetA _ _)
                              (sym (RingTheory.0RightAnnihilates (CommRing→Ring A') (Poly0→A (base v a))))
                              (λ v' a' → refl)
                              λ {U V} ind-U ind-V → (cong₂ _+_ ind-U ind-V) ∙ (sym (·Rdist+ _ _ _)))
                    λ {U V} ind-U ind-V Q → (cong₂ _+_ (ind-U Q) (ind-V Q)) ∙ (sym (·Ldist+ _ _ _))


-----------------------------------------------------------------------------
-- Ring Equivalence

module _ (A' : CommRing ℓ) where

  open Equiv-Poly0-A A'

  CRE-Poly0-A : CommRingEquiv (PolyCommRing A' 0) A'
  fst CRE-Poly0-A = isoToEquiv is
    where
    is : Iso (Poly A' 0) (A' .fst)
    Iso.fun is = Poly0→A
    Iso.inv is = A→Poly0
    Iso.rightInv is = e-sect
    Iso.leftInv is = e-retr
  snd CRE-Poly0-A = makeIsRingHom map-1P Poly0→A-gmorph Poly0→A-rmorph
