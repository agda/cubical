{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.EquivCarac.Poly0-A where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly

private variable
  ℓ : Level

module Equiv-Poly0-A
  (Acr@(A , Astr) : CommRing ℓ) where

  private
    PA = PolyCommRing Acr 0

  open CommRingStr



-----------------------------------------------------------------------------
-- Equivalence

  Poly0→A : Poly Acr 0 → A
  Poly0→A = DS-Rec-Set.f _ _ _ _ (is-set Astr)
             (0r Astr)
             (λ v a → a)
             (_+_ Astr)
             (+Assoc Astr)
             (+IdR Astr)
             (+Comm Astr)
             (λ _ → refl)
             λ _ a b → refl

  A→Poly0 : A → Poly Acr 0
  A→Poly0 a = base [] a

  e-sect : (a : A) → Poly0→A (A→Poly0 a) ≡ a
  e-sect a = refl

  e-retr : (P : Poly Acr 0) → A→Poly0 (Poly0→A P) ≡ P
  e-retr = DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
           (base-neutral [])
           (λ { [] a → refl })
           λ {U V} ind-U ind-V → (sym (base-add _ _ _)) ∙ (cong₂ (snd PA ._+_ ) ind-U ind-V)


-----------------------------------------------------------------------------
-- Ring homomorphism

  Poly0→A-pres1 : Poly0→A (snd PA .1r) ≡ 1r Astr
  Poly0→A-pres1 = refl

  Poly0→A-pres+ : (P Q : Poly Acr 0) → Poly0→A (snd PA ._+_ P Q) ≡ Astr ._+_ (Poly0→A P) (Poly0→A Q)
  Poly0→A-pres+ P Q = refl

  Poly0→A-pres· : (P Q : Poly Acr 0) → Poly0→A ( snd PA ._·_ P Q) ≡ Astr ._·_ (Poly0→A P) (Poly0→A Q)
  Poly0→A-pres· = DS-Ind-Prop.f _ _ _ _ (λ _ → isPropΠ λ _ → is-set Astr _ _)
                    (λ Q → sym (RingTheory.0LeftAnnihilates (CommRing→Ring Acr) (Poly0→A Q)))
                    (λ v a → DS-Ind-Prop.f _ _ _ _ (λ _ → is-set Astr _ _)
                              (sym (RingTheory.0RightAnnihilates (CommRing→Ring Acr) (Poly0→A (base v a))))
                              (λ v' a' → refl)
                              λ {U V} ind-U ind-V → (cong₂ (Astr ._+_) ind-U ind-V) ∙ sym (·DistR+ Astr _ _ _))
                    λ {U V} ind-U ind-V Q → (cong₂ (Astr ._+_) (ind-U Q) (ind-V Q)) ∙ sym (·DistL+ Astr _ _ _)


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
  snd CRE-Poly0-A = makeIsCommRingHom Poly0→A-pres1 Poly0→A-pres+ Poly0→A-pres·
