-- In this file we consider the special of localising at a single
-- element f : R (or rather the set of powers of f). This is also
-- known as inverting f.

{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommRing.Localisation.InvertingElements where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

module _(R' : CommRing {ℓ}) where
 open isMultClosedSubset
 private R = R' .fst
 -- open CommRingStr ⦃...⦄
 open CommRingStr (R' .snd)
 open Exponentiation R'


 [_ⁿ|n≥0] : R → ℙ R
 [ f ⁿ|n≥0] g = (∃[ n ∈ ℕ ] g ≡ f ^ n) , propTruncIsProp
 -- Σ[ n ∈ ℕ ] (s ≡ f ^ n) × (∀ m → s ≡ f ^ m → n ≤ m) maybe better, this isProp:
 -- (n,s≡fⁿ,p) (m,s≡fᵐ,q) then n≤m by p and  m≤n by q => n≡m

 powersFormMultClosedSubset : (f : R) → isMultClosedSubset R' [ f ⁿ|n≥0]
 powersFormMultClosedSubset f .containsOne = ∣ zero , refl ∣
 powersFormMultClosedSubset f .multClosed =
             PT.map2 λ (m , p) (n , q) → (m +ℕ n) , (λ i → (p i) · (q i)) ∙ ·-of-^-is-^-of-+ f m n


 R[1/_] : R → Type ℓ
 R[1/ f ] = Loc.S⁻¹R R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f)


 R[1/_]AsCommRing : R → CommRing {ℓ}
 R[1/ f ]AsCommRing = Loc.S⁻¹RAsCommRing R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f)

 -- A useful lemma: (gⁿ/1)≡(g/1)ⁿ in R[1/f]
 ^-respects-/1 : {f g : R} (n : ℕ) → [ (g ^ n) , 1r , ∣ 0 , (λ _ → 1r) ∣ ] ≡
     Exponentiation._^_ R[1/ f ]AsCommRing [ g , 1r , powersFormMultClosedSubset _ .containsOne ] n
 ^-respects-/1 zero = refl
 ^-respects-/1 {f} {g} (suc n) = eq/ _ _ ( (1r , powersFormMultClosedSubset f .containsOne)
                                         , cong (1r · (g · (g ^ n)) ·_) (·-lid 1r))
                           ∙ cong (CommRingStr._·_ (R[1/ f ]AsCommRing .snd)
                           [ g , 1r , powersFormMultClosedSubset f .containsOne ]) (^-respects-/1 n)

 -- A slight improvement for eliminating into propositions
 InvElPropElim : {f : R} {P : R[1/ f ] → Type ℓ'}
               → (∀ x →  isProp (P x))
               → (∀ (r : R) (n : ℕ) → P [ r , (f ^ n) , ∣ n , refl ∣ ])
              ----------------------------------------------------------
               → (∀ x → P x)
 InvElPropElim {f = f} {P = P} PisProp base = elimProp (λ _ → PisProp _) []-case
  where
  S[f] = Loc.S R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f)
  []-case : (a : R × S[f]) → P [ a ]
  []-case (r , s , s∈S[f]) = PT.rec (PisProp _) Σhelper s∈S[f]
   where
   Σhelper : Σ[ n ∈ ℕ ] s ≡ f ^ n → P [ r , s , s∈S[f] ]
   Σhelper (n , p) = subst P (cong [_] (≡-× refl (Σ≡Prop (λ _ → propTruncIsProp) (sym p)))) (base r n)

