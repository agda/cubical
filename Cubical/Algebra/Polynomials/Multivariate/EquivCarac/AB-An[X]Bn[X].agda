{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.EquivCarac.AB-An[X]Bn[X] where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Vec
open import Cubical.Data.Vec.OperationsNat
open import Cubical.Data.Sigma

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly

private variable
  ℓ : Level


-----------------------------------------------------------------------------
-- Lift

open IsRingHom
open CommRingStr

module _
  (A'@(A , Astr) : CommRing ℓ)
  (B'@(B , Bstr) : CommRing ℓ)
  (n : ℕ)
  where

  private
    PA = PolyCommRing A' n
    PB = PolyCommRing B' n

  makeCommRingHomPoly : (f : CommRingHom A' B') → CommRingHom (PolyCommRing A' n) (PolyCommRing B' n)
  fst (makeCommRingHomPoly (f , fstr)) = DS-Rec-Set.f _ _ _ _ trunc
                                         (0r (snd PB))
                                         (λ v a → base v (f a))
                                         (_+_ (snd PB))
                                         (+Assoc (snd PB))
                                         (+IdR (snd PB))
                                         (+Comm (snd PB))
                                         (λ v → (cong (base v) (pres0 fstr)) ∙ (base-neutral v))
                                         (λ v a b → (base-add v (f a) (f b)) ∙ (cong (base v) (sym (pres+ fstr a b))))
  snd (makeCommRingHomPoly (f , fstr)) = makeIsRingHom
                                         (cong (base (replicate zero)) (pres1 fstr))
                                         (λ _ _ → refl)
                                         (DS-Ind-Prop.f _ _ _ _ (λ _ → isPropΠ λ _ → trunc _ _)
                                             (λ _ → refl)
                                             (λ v a → DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
                                                                    refl
                                                                    (λ v' b → cong (base (v +n-vec v')) (pres· fstr a b))
                                                                    (λ {U V} ind-U ind-V → cong₂ (_+_ (snd PB)) ind-U  ind-V))
                                             λ {U V} ind-U ind-V Q → cong₂ (_+_ (snd PB)) (ind-U Q) (ind-V Q))


-----------------------------------------------------------------------------
-- Lift preserve equivalence

module _
  (A'@(A , Astr) : CommRing ℓ)
  (B'@(B , Bstr) : CommRing ℓ)
  (n : ℕ)
  where

  private
    PA = PolyCommRing A' n
    PB = PolyCommRing B' n

  open Iso
  open RingEquivs

  lift-equiv-poly : (e : CommRingEquiv A' B') → CommRingEquiv (PolyCommRing A' n) (PolyCommRing B' n)
  fst (lift-equiv-poly (e , fstr)) = isoToEquiv is
    where
    f = fst e
    g = invEq e
    gstr : IsRingHom (snd (CommRing→Ring B')) g (snd (CommRing→Ring A'))
    gstr = isRingHomInv (e , fstr)

    is : Iso (fst PA) (fst PB)
    fun is = fst (makeCommRingHomPoly A' B' n (f , fstr))
    inv is = fst (makeCommRingHomPoly B' A' n (g , gstr))
    rightInv is = DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
                  refl
                  (λ v a → cong (base v) (secEq e a))
                  λ {U V} ind-U ind-V → cong₂ (_+_ (snd PB)) ind-U ind-V
    leftInv is = DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
                 refl
                 (λ v a → cong (base v) (retEq e a))
                 λ {U V} ind-U ind-V → cong₂ (_+_ (snd PA)) ind-U ind-V
  snd (lift-equiv-poly (e , fstr)) = snd (makeCommRingHomPoly A' B' n ((fst e) , fstr))
