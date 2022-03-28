{-# OPTIONS --safe #-}
module Cubical.Algebra.Polynomials.Nth-polynomials.Polyn-Equiv where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Polynomials.Polynomials

open import Cubical.Algebra.Polynomials.Nth-polynomials.Base
open import Cubical.Algebra.Polynomials.Nth-polynomials.CommRing-Structure
open Nth-Poly-structure

private variable
  l l' : Level


-----------------------------------------------------------------------------
-- Lift

open IsRingHom

lift-poly : (A' B' : CommRing l) → (f : CommRingHom A' B') → (n : ℕ) → CommRingHom (PolyCommRing A' n) (PolyCommRing B' n)
fst (lift-poly A' B' (f , fcrhom) n) = Poly-Rec-Set.f A' n (Poly B' n) trunc
                                     0P
                                     (λ v a → base v (f a))
                                     _Poly+_
                                     Poly+-assoc
                                     Poly+-Rid
                                     Poly+-comm
                                     (λ v → (cong (base v) (pres0 fcrhom)) ∙ (base-0P v))
                                     λ v a b → (base-Poly+ v (f a) (f b)) ∙ (cong (base v) (sym (pres+ fcrhom a b)))
snd (lift-poly A' B' (f , fcrhom) n) = makeIsRingHom
                          (cong (base (replicate zero)) (pres1 fcrhom))
                          (λ P Q → refl)
                          (Poly-Ind-Prop.f A' n _ (λ P p q i Q j → trunc _ _ (p Q) (q Q) i j)
                          (λ Q → refl)
                          (λ v a → Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
                                    refl
                                    (λ v' a' → cong (base ((B' Nth-Poly-structure.+n-vec n) v v')) (pres· fcrhom a a'))
                                    λ {U V} ind-U ind-V → cong₂ _Poly+_ ind-U  ind-V)
                           λ {U V} ind-U ind-V Q → cong₂ _Poly+_ (ind-U Q) (ind-V Q))



-----------------------------------------------------------------------------
-- Lift preserve equivalence

open RingEquivs

lift-equiv-poly : (A' B' : CommRing l) → (e : CommRingEquiv A' B') → (n : ℕ) → CommRingEquiv (PolyCommRing A' n) (PolyCommRing B' n)
lift-equiv-poly A' B' e n = isoToEquiv (iso
                                        (fst (lift-poly A' B' (f , fcrh) n))
                                        (fst (lift-poly B' A' (g , gcrh) n))
                                        (Poly-Ind-Prop.f B' n _ (λ _ → trunc _ _)
                                          refl
                                          (λ v a → cong (base v) (secEq et a))
                                          λ {U V} ind-U ind-V → cong₂ _Poly+_ ind-U ind-V)
                                        (Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
                                          refl
                                          (λ v a → cong (base v) (retEq et a))
                                          λ {U V} ind-U ind-V → cong₂ _Poly+_ ind-U ind-V))
                            , snd (lift-poly A' B' (f , fcrh) n)
  where
  et = fst e
  fcrh = snd e
  f = fst et
  g = invEq et
  gcrh : IsRingHom (snd (CommRing→Ring B')) g (snd (CommRing→Ring A')) 
  gcrh = isRingHomInv (CommRing→Ring A') (CommRing→Ring B') (et , fcrh)
