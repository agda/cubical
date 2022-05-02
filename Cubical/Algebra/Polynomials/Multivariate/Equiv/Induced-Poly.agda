{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.Equiv.Induced-Poly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.Polynomials.Univariate.Base

open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.Polynomials.Multivariate.Properties
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly
open Nth-Poly-structure

private variable
  ℓ : Level


-----------------------------------------------------------------------------
-- Lift

open IsRingHom

makeCommRingHomPoly : (A' B' : CommRing ℓ) → (f : CommRingHom A' B') → (n : ℕ) → CommRingHom (PolyCommRing A' n) (PolyCommRing B' n)
fst (makeCommRingHomPoly A' B' (f , fcrhom) n) = Poly-Rec-Set.f A' n (Poly B' n) trunc
                                     0P
                                     (λ v a → base v (f a))
                                     _Poly+_
                                     Poly+-assoc
                                     Poly+-Rid
                                     Poly+-comm
                                     (λ v → (cong (base v) (pres0 fcrhom)) ∙ (base-0P v))
                                     λ v a b → (base-Poly+ v (f a) (f b)) ∙ (cong (base v) (sym (pres+ fcrhom a b)))
snd (makeCommRingHomPoly A' B' (f , fcrhom) n) = makeIsRingHom
                          (cong (base (replicate zero)) (pres1 fcrhom))
                          (λ P Q → refl)
                          (Poly-Ind-Prop.f A' n _ (λ P p q i Q j → trunc _ _ (p Q) (q Q) i j)
                          (λ Q → refl)
                          (λ v a → Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
                                    refl
                                    (λ v' a' → cong (base (v +n-vec v')) (pres· fcrhom a a'))
                                    λ {U V} ind-U ind-V → cong₂ _Poly+_ ind-U  ind-V)
                           λ {U V} ind-U ind-V Q → cong₂ _Poly+_ (ind-U Q) (ind-V Q))



-----------------------------------------------------------------------------
-- Lift preserve equivalence

open RingEquivs

lift-equiv-poly : (A' B' : CommRing ℓ) → (e : CommRingEquiv A' B') → (n : ℕ) → CommRingEquiv (PolyCommRing A' n) (PolyCommRing B' n)
fst (lift-equiv-poly A' B' e n) = isoToEquiv is
  where
    et = fst e
    fcrh = snd e
    f = fst et
    g = invEq et
    gcrh : IsRingHom (snd (CommRing→Ring B')) g (snd (CommRing→Ring A'))
    gcrh = isRingHomInv (et , fcrh)

    is : Iso _ _
    Iso.fun is = fst (makeCommRingHomPoly A' B' (f , fcrh) n)
    Iso.inv is = fst (makeCommRingHomPoly B' A' (g , gcrh) n)
    Iso.rightInv is = (Poly-Ind-Prop.f B' n _ (λ _ → trunc _ _)
                      refl
                      (λ v a → cong (base v) (secEq et a))
                      λ {U V} ind-U ind-V → cong₂ _Poly+_ ind-U ind-V)
    Iso.leftInv is = (Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
                     refl
                     (λ v a → cong (base v) (retEq et a))
                     λ {U V} ind-U ind-V → cong₂ _Poly+_ ind-U ind-V)
snd (lift-equiv-poly A' B' e n) = snd (makeCommRingHomPoly A' B' (fst (fst e) , snd e) n)
