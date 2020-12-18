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
open import Cubical.Data.Nat.Order
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
 private R = fst R'
 -- open CommRingStr ⦃...⦄
 open CommRingStr (snd R')
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
                                         , cong (1r · (g · (g ^ n)) ·_) (·Lid 1r))
                           ∙ cong (CommRingStr._·_ (R[1/ f ]AsCommRing .snd)
                           [ g , 1r , powersFormMultClosedSubset f .containsOne ]) (^-respects-/1 n)

 -- A slight improvement for eliminating into propositions
 InvElPropElim : {f : R} {P : R[1/ f ] → Type ℓ'}
               → (∀ x →  isProp (P x))
               → (∀ (r : R) (n : ℕ) → P [ r , (f ^ n) , ∣ n , refl ∣ ])    -- ∀ r n → P (r/fⁿ)
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

 -- For predicates over the set of powers
 powersPropElim : {f : R} {P : R → Type ℓ'}
                → (∀ x →  isProp (P x))
                → (∀ n → P (f ^ n))
               ------------------------------
                → ∀ s → s ∈ [ f ⁿ|n≥0] → P s
 powersPropElim {f = f} {P = P} PisProp base s =
                PT.rec (PisProp s) λ (n , p) → subst P (sym p) (base n)

-- Check: (R[1/f])[1/g] ≡ R[1/fg]
-- still TODO:
-- ψ : R[1/f][1/g] → R[1/fg]
-- η : section φ ψ
-- ε : retract φ ψ
-- prove that φ is ring hom
module check (R' : CommRing {ℓ}) (f g : (fst R')) where
 open isMultClosedSubset
 open CommRingStr (snd R')
 open CommTheory R'
 open Exponentiation R'
 open Theory (CommRing→Ring R')
 open CommRingStr (snd (R[1/_]AsCommRing R' f)) renaming ( _·_ to _·ᶠ_ ; 1r to 1ᶠ
                                                         ; _+_ to _+ᶠ_ ; 0r to 0ᶠ
                                                         ; ·Lid to ·ᶠ-lid ; ·Rid to ·ᶠ-rid
                                                         ; ·Assoc to ·ᶠ-assoc ; ·-comm to ·ᶠ-comm)

 private
  R = fst R'
  R[1/f] = R[1/_] R' f
  R[1/f]AsCommRing = R[1/_]AsCommRing R' f
  R[1/fg] = R[1/_] R' (f · g)
  R[1/fg]AsCommRing = R[1/_]AsCommRing R' (f · g)
  R[1/f][1/g] = R[1/_] (R[1/_]AsCommRing R' f)
                                [ g , 1r , powersFormMultClosedSubset R' f .containsOne ]
  R[1/f][1/g]AsCommRing = R[1/_]AsCommRing (R[1/_]AsCommRing R' f)
                                [ g , 1r , powersFormMultClosedSubset R' f .containsOne ]
  R[1/f][1/g]ˣ = R[1/f][1/g]AsCommRing ˣ

 φ : R[1/fg] → R[1/f][1/g]
 φ = SQ.rec squash/ ϕ ϕcoh
   where
   S[fg] = Loc.S R' ([_ⁿ|n≥0] R' (f · g)) (powersFormMultClosedSubset R' (f · g))

   curriedϕΣ : (r s : R) → Σ[ n ∈ ℕ ] s ≡ (f · g) ^ n → R[1/f][1/g]
   curriedϕΣ r s (n , s≡fg^n) =
    [ [ r , (f ^ n) , ∣ n , refl ∣ ] , [ (g ^ n) , 1r , ∣ 0 , refl ∣ ] , ∣ n , ^-respects-/1 R' n ∣ ]

   curriedϕ : (r s : R) → ∃[ n ∈ ℕ ] s ≡ (f · g) ^ n → R[1/f][1/g]
   curriedϕ r s = elim→Set (λ _ → squash/) (curriedϕΣ r s) coh
    where
    coh : (x y : Σ[ n ∈ ℕ ] s ≡ (f · g) ^ n) → curriedϕΣ r s x ≡ curriedϕΣ r s y
    coh (n , s≡fg^n) (m , s≡fg^m) = eq/ _ _ ((1ᶠ , ∣ 0 , refl ∣) ,
                                    eq/ _ _ ( (1r , powersFormMultClosedSubset R' f .containsOne)
                                            , path))
     where
     path : 1r · (1r · r · (g ^ m)) · (1r · (f ^ m) · 1r)
          ≡ 1r · (1r · r · (g ^ n)) · (1r · (f ^ n) · 1r)
     path = 1r · (1r · r · (g ^ m)) · (1r · (f ^ m) · 1r)
          ≡⟨ (λ i → ·Lid ((·Lid r i) · (g ^ m)) i · (·Rid (·Lid (f ^ m) i) i)) ⟩
            r · g ^ m · f ^ m
          ≡⟨ sym (·Assoc _ _ _) ⟩
            r · (g ^ m · f ^ m)
          ≡⟨ cong (r ·_) (sym (^-ldist-· g f m)) ⟩
            r · ((g · f) ^ m)
          ≡⟨ cong (λ x → r · (x ^ m)) (·-comm _ _) ⟩
            r · ((f · g) ^ m)
          ≡⟨ cong (r ·_) ((sym s≡fg^m) ∙ s≡fg^n) ⟩
            r · ((f · g) ^ n)
          ≡⟨ cong (λ x → r · (x ^ n)) (·-comm _ _) ⟩
            r · ((g · f) ^ n)
          ≡⟨ cong (r ·_) (^-ldist-· g f n) ⟩
            r · (g ^ n · f ^ n)
          ≡⟨ ·Assoc _ _ _ ⟩
            r · g ^ n · f ^ n
          ≡⟨ (λ i → ·Lid ((·Lid r (~ i)) · (g ^ n)) (~ i) · (·Rid (·Lid (f ^ n) (~ i)) (~ i))) ⟩
            1r · (1r · r · (g ^ n)) · (1r · (f ^ n) · 1r) ∎

   ϕ : R × S[fg] → R[1/f][1/g]
   ϕ (r , s , |n,s≡fg^n|) = curriedϕ r s |n,s≡fg^n|
   -- λ (r / (fg)ⁿ) → ((r / fⁿ) / gⁿ)

   curriedϕcohΣ : (r s r' s' u : R) → (p : u · r · s' ≡ u · r' · s)
                                    → (α : Σ[ n ∈ ℕ ] s ≡ (f · g) ^ n)
                                    → (β : Σ[ m ∈ ℕ ] s' ≡ (f · g) ^ m)
                                    → (γ : Σ[ l ∈ ℕ ] u ≡ (f · g) ^ l)
                                    → ϕ (r , s , ∣ α ∣) ≡ ϕ (r' , s' , ∣ β ∣)
   curriedϕcohΣ r s r' s' u p (n , s≡fgⁿ) (m , s'≡fgᵐ) (l , u≡fgˡ) =
    eq/ _ _ ( ( [ (g ^ l) , 1r , powersFormMultClosedSubset R' f .containsOne ]
              , ∣ l , ^-respects-/1 R' l ∣)
            , eq/ _ _ ((f ^ l , ∣ l , refl ∣) , path))
    where
    path : f ^ l · (g ^ l · transp (λ i → R) i0 r · transp (λ i → R) i0 (g ^ m))
                 · (1r · transp (λ i → R) i0 (f ^ m) · transp (λ i → R) i0 1r)
         ≡ f ^ l · (g ^ l · transp (λ i → R) i0 r' · transp (λ i → R) i0 (g ^ n))
                 · (1r · transp (λ i → R) i0 (f ^ n) · transp (λ i → R) i0 1r)
    path = f ^ l · (g ^ l · transp (λ i → R) i0 r · transp (λ i → R) i0 (g ^ m))
                 · (1r · transp (λ i → R) i0 (f ^ m) · transp (λ i → R) i0 1r)
         ≡⟨ (λ i → f ^ l · (g ^ l · transportRefl r i · transportRefl (g ^ m) i)
                         · (1r · transportRefl (f ^ m) i · transportRefl 1r i)) ⟩
           f ^ l · (g ^ l · r · g ^ m) · (1r · f ^ m · 1r)
         ≡⟨ (λ i → ·Assoc (f ^ l) ((g ^ l) · r) (g ^ m) i · ·Rid (1r · (f ^ m)) i) ⟩
           f ^ l · (g ^ l · r) · g ^ m · (1r · f ^ m)
         ≡⟨ (λ i → ·Assoc (f ^ l) (g ^ l) r i · g ^ m ·  ·Lid (f ^ m) i) ⟩
           f ^ l · g ^ l · r · g ^ m · f ^ m
         ≡⟨ sym (·Assoc _ _ _) ⟩
           f ^ l · g ^ l · r · (g ^ m · f ^ m)
         ≡⟨ (λ i → ^-ldist-· f g l (~ i) · r · ^-ldist-· g f m (~ i)) ⟩
           (f · g) ^ l · r · (g · f) ^ m
         ≡⟨ cong (λ x → (f · g) ^ l · r · x ^ m) (·-comm _ _) ⟩
           (f · g) ^ l · r · (f · g) ^ m
         ≡⟨ (λ i → u≡fgˡ (~ i) · r · s'≡fgᵐ (~ i)) ⟩
           u · r · s'
         ≡⟨ p ⟩
           u · r' · s
         ≡⟨ (λ i → u≡fgˡ i · r' · s≡fgⁿ i) ⟩
           (f · g) ^ l · r' · (f · g) ^ n
         ≡⟨ cong (λ x → (f · g) ^ l · r' · x ^ n) (·-comm _ _) ⟩
           (f · g) ^ l · r' · (g · f) ^ n
         ≡⟨ (λ i → ^-ldist-· f g l i · r' · ^-ldist-· g f n i) ⟩
           f ^ l · g ^ l · r' · (g ^ n · f ^ n)
         ≡⟨ ·Assoc _ _ _ ⟩
           f ^ l · g ^ l · r' · g ^ n · f ^ n
         ≡⟨ (λ i → ·Assoc (f ^ l) (g ^ l) r' (~ i) · g ^ n ·  ·Lid (f ^ n) (~ i)) ⟩
           f ^ l · (g ^ l · r') · g ^ n · (1r · f ^ n)
         ≡⟨ (λ i → ·Assoc (f ^ l) ((g ^ l) · r') (g ^ n) (~ i) · ·Rid (1r · (f ^ n)) (~ i)) ⟩
           f ^ l · (g ^ l · r' · g ^ n) · (1r · f ^ n · 1r)
         ≡⟨ (λ i → f ^ l · (g ^ l · transportRefl r' (~ i) · transportRefl (g ^ n) (~ i))
                         · (1r · transportRefl (f ^ n) (~ i) · transportRefl 1r (~ i))) ⟩
           f ^ l · (g ^ l · transp (λ i → R) i0 r' · transp (λ i → R) i0 (g ^ n))
                 · (1r · transp (λ i → R) i0 (f ^ n) · transp (λ i → R) i0 1r) ∎

   curriedϕcoh : (r s r' s' u : R) → (p : u · r · s' ≡ u · r' · s)
                                   → (α : ∃[ n ∈ ℕ ] s ≡ (f · g) ^ n)
                                   → (β : ∃[ m ∈ ℕ ] s' ≡ (f · g) ^ m)
                                   → (γ : ∃[ l ∈ ℕ ] u ≡ (f · g) ^ l)
                                   → ϕ (r , s , α) ≡ ϕ (r' , s' , β)
   curriedϕcoh r s r' s' u p = PT.elim (λ _ → isPropΠ2 (λ _ _ → squash/ _ _))
                         λ α → PT.elim (λ _ → isPropΠ (λ _ → squash/ _ _))
                         λ β → PT.rec (squash/ _ _)
                         λ γ →  curriedϕcohΣ r s r' s' u p α β γ

   ϕcoh : (a b : R × S[fg])
        → Loc._≈_ R' ([_ⁿ|n≥0] R' (f · g)) (powersFormMultClosedSubset R' (f · g)) a b
        → ϕ a ≡ ϕ b
   ϕcoh (r , s , α) (r' , s' , β) ((u , γ) , p) =  curriedϕcoh r s r' s' u p α β γ


 _/1/1 : R → R[1/f][1/g]
 r /1/1 = [ [ r , 1r , ∣ 0 , refl ∣ ] , 1ᶠ , ∣ 0 , refl ∣ ]

 /1/1AsCommRingHom : CommRingHom R' R[1/f][1/g]AsCommRing
 RingHom.f /1/1AsCommRingHom = _/1/1
 RingHom.pres1 /1/1AsCommRingHom = refl
 RingHom.isHom+ /1/1AsCommRingHom r r' = cong [_] (≡-× (cong [_]
                                                  (≡-×
                         (cong₂ _+_ (sym (·Rid _) ∙ (λ i → (·Rid r (~ i)) · (·Rid 1r (~ i))))
                         (sym (·Rid _) ∙ (λ i → (·Rid r' (~ i)) · (·Rid 1r (~ i)))))
                                                  (Σ≡Prop (λ _ → propTruncIsProp)
                         (sym (·Lid _) ∙ (λ i → (·Lid 1r (~ i)) · (·Lid 1r (~ i)))))))
                                                  (Σ≡Prop (λ _ → propTruncIsProp) (sym (·ᶠ-lid 1ᶠ))))
 RingHom.isHom· /1/1AsCommRingHom r r' = cong [_] (≡-× (cong [_]
                                                  (≡-× refl (Σ≡Prop (λ _ → propTruncIsProp)
                                                  (sym (·Lid _)))))
                                                  (Σ≡Prop (λ _ → propTruncIsProp) (sym (·ᶠ-lid 1ᶠ))))
 -- takes forever to compute...
 R[1/fg]≡R[1/f][1/g] : R[1/fg]AsCommRing ≡ R[1/f][1/g]AsCommRing
 R[1/fg]≡R[1/f][1/g] = S⁻¹RChar R' ([_ⁿ|n≥0] R' (f · g))
                         (powersFormMultClosedSubset R' (f · g)) _ /1/1AsCommRingHom pathtoR[1/fg]
  where
  open PathToS⁻¹R
  pathtoR[1/fg] : PathToS⁻¹R R' ([_ⁿ|n≥0] R' (f · g)) (powersFormMultClosedSubset R' (f · g))
                             R[1/f][1/g]AsCommRing /1/1AsCommRingHom
  φS⊆Aˣ pathtoR[1/fg] s = PT.elim (λ _ → R[1/f][1/g]ˣ (s /1/1) .snd) Σhelper
   where
   Σhelper : Σ[ n ∈ ℕ ] s ≡ (f · g) ^ n → (s /1/1) ∈ R[1/f][1/g]ˣ
   Σhelper (n , p) =
    [ [ 1r , (f ^ n) , ∣ n , refl ∣ ] , [ (g ^ n) , 1r , ∣ 0 , refl ∣ ] , ∣ n , ^-respects-/1 _ n ∣ ]
                   , eq/ _ _ ((1ᶠ , powersFormMultClosedSubset _ _ .containsOne)
                   , eq/ _ _ ((1r , powersFormMultClosedSubset _ _ .containsOne)
                   , path))
    where
    path : 1r · (1r · (s · 1r) · 1r) · (1r · 1r · (1r · 1r))
         ≡ 1r · (1r · 1r · (1r · g ^ n)) · (1r · (1r · f ^ n) · 1r)
    path = 1r · (1r · (s · 1r) · 1r) · (1r · 1r · (1r · 1r))
         ≡⟨ (λ i → ·Lid (·Rid (·Lid (·Rid s i) i) i) i · (·Lid 1r i · ·Lid 1r i) ) ⟩
           s · (1r · 1r)
         ≡⟨ cong (s ·_) (·Rid _) ⟩
           s · 1r
         ≡⟨ ·Rid _ ⟩
           s
         ≡⟨ p ⟩
           (f · g) ^ n
         ≡⟨ ^-ldist-· _ _ _ ⟩
           f ^ n · g ^ n
         ≡⟨ (λ i → ·-comm (f ^ n) (·Lid (g ^ n) (~ i)) i) ⟩
           1r · g ^ n · f ^ n
         ≡⟨ (λ i → ·Lid (·Lid 1r (~ i) · ·Lid (g ^ n) (~ i)) (~ i)
                   · ·Rid (·Lid (·Lid (f ^ n) (~ i)) (~ i)) (~ i)) ⟩
           1r · (1r · 1r · (1r · g ^ n)) · (1r · (1r · f ^ n) · 1r) ∎

  kerφ⊆annS pathtoR[1/fg] r p = toGoal helperR[1/f]
   where
   open Theory (CommRing→Ring R[1/f]AsCommRing) renaming ( 0RightAnnihilates to 0ᶠRightAnnihilates
                                                         ; 0LeftAnnihilates to 0ᶠ-leftNullifies)
   open Exponentiation R[1/f]AsCommRing renaming (_^_ to _^ᶠ_)
                                        hiding (·-of-^-is-^-of-+ ; ^-ldist-·)

   S[f] = Loc.S R' ([_ⁿ|n≥0] R' f) (powersFormMultClosedSubset R' f)
   S[fg] = Loc.S R' ([_ⁿ|n≥0] R' (f · g)) (powersFormMultClosedSubset R' (f · g))
   g/1 : R[1/_] R' f
   g/1 = [ g , 1r , powersFormMultClosedSubset R' f .containsOne ]
   S[g/1] = Loc.S R[1/f]AsCommRing
                  ([_ⁿ|n≥0] R[1/f]AsCommRing g/1)
                  (powersFormMultClosedSubset R[1/f]AsCommRing g/1)
   r/1 : R[1/_] R' f
   r/1 = [ r , 1r , powersFormMultClosedSubset R' f .containsOne ]

   -- this is the crucial step, modulo truncation we can take p to be generated
   -- by the quotienting relation of localisation. Note that we wouldn't be able
   -- to prove our goal if kerφ⊆annS was formulated with a Σ instead of a ∃
   ∥r/1,1/1≈0/1,1/1∥ : ∃[ u ∈ S[g/1] ] fst u ·ᶠ r/1 ·ᶠ 1ᶠ ≡ fst u ·ᶠ 0ᶠ ·ᶠ 1ᶠ
   ∥r/1,1/1≈0/1,1/1∥ = Iso.fun (SQ.isEquivRel→TruncIso (Loc.locIsEquivRel _ _ _) _ _) p

   helperR[1/f] : ∃[ n ∈ ℕ ] [ g ^ n · r , 1r , ∣ 0 , refl ∣ ] ≡ 0ᶠ
   helperR[1/f] = PT.rec propTruncIsProp
                  (uncurry (uncurry (powersPropElim R[1/f]AsCommRing
                                    (λ _ → isPropΠ (λ _ → propTruncIsProp)) baseCase)))
                  ∥r/1,1/1≈0/1,1/1∥
    where
    baseCase : ∀ n → g/1 ^ᶠ n ·ᶠ r/1 ·ᶠ 1ᶠ ≡ g/1 ^ᶠ n ·ᶠ 0ᶠ ·ᶠ 1ᶠ
                   → ∃[ n ∈ ℕ ] [ g ^ n · r , 1r , ∣ 0 , refl ∣ ] ≡ 0ᶠ
    baseCase n q = ∣ n , path ∣
     where
     path : [ g ^ n · r , 1r , ∣ 0 , refl ∣ ] ≡ 0ᶠ
     path = [ g ^ n · r , 1r , ∣ 0 , refl ∣ ]
          ≡⟨ cong [_] (≡-× refl (Σ≡Prop (λ _ → propTruncIsProp) (sym (·Rid _)))) ⟩
            [ g ^ n , 1r , ∣ 0 , refl ∣ ] ·ᶠ r/1
          ≡⟨ cong (_·ᶠ r/1) (^-respects-/1 _ n) ⟩
            g/1 ^ᶠ n ·ᶠ r/1
          ≡⟨ sym (·ᶠ-rid _) ⟩
            g/1 ^ᶠ n ·ᶠ r/1 ·ᶠ 1ᶠ
          ≡⟨ q ⟩
            g/1 ^ᶠ n ·ᶠ 0ᶠ ·ᶠ 1ᶠ
          ≡⟨ cong (_·ᶠ 1ᶠ) (0ᶠRightAnnihilates _) ∙ 0ᶠ-leftNullifies 1ᶠ ⟩
            0ᶠ ∎

   toGoal : ∃[ n ∈ ℕ ] [ g ^ n · r , 1r , ∣ 0 , refl ∣ ] ≡ 0ᶠ
          → ∃[ u ∈ S[fg] ] fst u · r ≡ 0r
   toGoal = PT.rec propTruncIsProp Σhelper
    where
    Σhelper : Σ[ n ∈ ℕ ] [ g ^ n · r , 1r , ∣ 0 , refl ∣ ] ≡ 0ᶠ
            → ∃[ u ∈ S[fg] ] fst u · r ≡ 0r
    Σhelper (n , q) = PT.map Σhelper2 helperR
     where
     -- now, repeat the above strategy with q
     ∥gⁿr≈0∥ : ∃[ u ∈ S[f] ] fst u · (g ^ n · r) · 1r ≡ fst u · 0r · 1r
     ∥gⁿr≈0∥ = Iso.fun (SQ.isEquivRel→TruncIso (Loc.locIsEquivRel _ _ _) _ _) q

     helperR : ∃[ m ∈ ℕ ] f ^ m · g ^ n · r ≡ 0r
     helperR = PT.rec propTruncIsProp
               (uncurry (uncurry (powersPropElim R'
                                 (λ _ → isPropΠ (λ _ → propTruncIsProp)) baseCase)))
               ∥gⁿr≈0∥
      where
      baseCase : (m : ℕ) → f ^ m · (g ^ n · r) · 1r ≡ f ^ m · 0r · 1r
               → ∃[ m ∈ ℕ ] f ^ m · g ^ n · r ≡ 0r
      baseCase m q' = ∣ m , path ∣
       where
       path : f ^ m · g ^ n · r ≡ 0r
       path = (λ i → ·Rid (·Assoc (f ^ m) (g ^ n) r (~ i)) (~ i))
            ∙∙ q' ∙∙ (λ i → ·Rid (0RightAnnihilates (f ^ m) i) i)

     Σhelper2 : Σ[ m ∈ ℕ ] f ^ m · g ^ n · r ≡ 0r
              → Σ[ u ∈ S[fg] ] fst u · r ≡ 0r
     Σhelper2 (m , q') = (((f · g) ^ l) , ∣ l , refl ∣) , path
      where
      l = max m n

      path : (f · g) ^ l · r ≡ 0r
      path = (f · g) ^ l · r
           ≡⟨ cong (_· r) (^-ldist-· _ _ _) ⟩
             f ^ l · g ^ l · r
           ≡⟨ cong₂ (λ x y → f ^ x · g ^ y · r) (sym (≤-∸-+-cancel {m = m} left-≤-max))
                                                (sym (≤-∸-+-cancel {m = n} right-≤-max)) ⟩
             f ^ (l ∸ m +ℕ m) · g ^ (l ∸ n +ℕ n) · r
           ≡⟨ cong₂ (λ x y → x · y · r) (sym (·-of-^-is-^-of-+ _ _ _))
                                        (sym (·-of-^-is-^-of-+ _ _ _)) ⟩
             f ^ (l ∸ m) · f ^ m · (g ^ (l ∸ n) · g ^ n) · r
           ≡⟨ cong (_· r) (·-commAssocSwap _ _ _ _) ⟩
             f ^ (l ∸ m) · g ^ (l ∸ n) · (f ^ m · g ^ n) · r
           ≡⟨ sym (·Assoc _ _ _) ⟩
             f ^ (l ∸ m) · g ^ (l ∸ n) · (f ^ m · g ^ n · r)
           ≡⟨ cong (f ^ (l ∸ m) · g ^ (l ∸ n) ·_) q' ⟩
             f ^ (l ∸ m) · g ^ (l ∸ n) · 0r
           ≡⟨ 0RightAnnihilates _ ⟩
             0r ∎

  surχ pathtoR[1/fg] = InvElPropElim _ (λ _ → propTruncIsProp) foo2
   where
   open Exponentiation R[1/f]AsCommRing renaming (_^_ to _^ᶠ_)
                                               hiding (·-of-^-is-^-of-+ ; ^-ldist-·)
   open CommRingStr (snd R[1/f][1/g]AsCommRing) renaming (_·_ to _·R[1/f][1/g]_)
                    hiding (1r ; ·Lid ; ·Rid ; ·Assoc)
   open Units R[1/f][1/g]AsCommRing
   g/1 : R[1/_] R' f
   g/1 = [ g , 1r , powersFormMultClosedSubset R' f .containsOne ]
   S[fg] = Loc.S R' ([_ⁿ|n≥0] R' (f · g)) (powersFormMultClosedSubset R' (f · g))

   bar : (r : R) (m n : ℕ) → ∃[ x ∈ R × S[fg] ] (x .fst /1/1)
       ≡ [ [ r , f ^ m , ∣ m , refl ∣ ] , [ g ^ n , 1r , ∣ 0 , refl ∣ ] , ∣ n , ^-respects-/1 _ n ∣ ]
       ·R[1/f][1/g] (x .snd .fst /1/1)
   bar r m n = ∣ ((r · f ^ (l ∸ m) · g ^ (l ∸ n)) -- x .fst
               , (f · g) ^ l , ∣ l , refl ∣)      -- x .snd
               , eq/ _ _ ((1ᶠ , ∣ 0 , refl ∣) , eq/ _ _ ((1r , ∣ 0 , refl ∣) , path)) ∣
               -- reduce equality of double fractions into equality in R
    where
    l = max m n
    path : 1r · (1r · (r · f ^ (l ∸ m) · g ^ (l ∸ n)) · (g ^ n · 1r)) · (1r · (f ^ m · 1r) · 1r)
         ≡ 1r · (1r · (r · (f · g) ^ l) · 1r) · (1r · 1r · (1r · 1r))
    path = 1r · (1r · (r · f ^ (l ∸ m) · g ^ (l ∸ n)) · (g ^ n · 1r)) · (1r · (f ^ m · 1r) · 1r)
         ≡⟨ (λ i → ·Lid (·Lid (r · f ^ (l ∸ m) · g ^ (l ∸ n)) i · ·Rid (g ^ n) i) i
                 · ·Rid (·Lid (·Rid (f ^ m) i) i) i) ⟩
           r · f ^ (l ∸ m) · g ^ (l ∸ n) · g ^ n · f ^ m
         ≡⟨ cong (_· f ^ m) (sym (·Assoc _ _ _)) ⟩
           r · f ^ (l ∸ m) · (g ^ (l ∸ n) · g ^ n) · f ^ m
         ≡⟨ cong (λ x → r · f ^ (l ∸ m) · x · f ^ m) (·-of-^-is-^-of-+ _ _ _) ⟩
           r · f ^ (l ∸ m) · g ^ (l ∸ n +ℕ n) · f ^ m
         ≡⟨ cong (λ x → r · f ^ (l ∸ m) · g ^ x · f ^ m) (≤-∸-+-cancel right-≤-max) ⟩
           r · f ^ (l ∸ m) · g ^ l · f ^ m
         ≡⟨ ·-commAssocr _ _ _ ⟩
           r · f ^ (l ∸ m) · f ^ m · g ^ l
         ≡⟨ cong (_· g ^ l) (sym (·Assoc _ _ _)) ⟩
           r · (f ^ (l ∸ m) · f ^ m) · g ^ l
         ≡⟨ cong (λ x → r · x · g ^ l) (·-of-^-is-^-of-+ _ _ _) ⟩
           r · f ^ (l ∸ m +ℕ m) · g ^ l
         ≡⟨ cong (λ x → r · f ^ x · g ^ l) (≤-∸-+-cancel left-≤-max) ⟩
           r · f ^ l · g ^ l
         ≡⟨ sym (·Assoc _ _ _) ⟩
           r · (f ^ l · g ^ l)
         ≡⟨ cong (r ·_) (sym (^-ldist-· _ _ _)) ⟩
           r · (f · g) ^ l
         ≡⟨ sym (·Rid _) ∙ cong (r · (f · g) ^ l ·_) (sym (·Rid _))⟩
           r · (f · g) ^ l · (1r · 1r)
         ≡⟨ (λ i → ·Lid (·Rid (·Lid (r · (f · g) ^ l) (~ i)) (~ i)) (~ i)
                 · (·Rid 1r (~ i) · ·Rid 1r (~ i))) ⟩
           1r · (1r · (r · (f · g) ^ l) · 1r) · (1r · 1r · (1r · 1r)) ∎

   baz : (r : R) (m n : ℕ) → ∃[ x ∈ R × S[fg] ] (x .fst /1/1)
       ≡ [ [ r , f ^ m , ∣ m , refl ∣ ] , g/1 ^ᶠ n , ∣ n , refl ∣ ] ·R[1/f][1/g] (x .snd .fst /1/1)
   baz r m n = subst (λ y →  ∃[ x ∈ R × S[fg] ] (x .fst /1/1)
                          ≡ [ [ r , f ^ m , ∣ m , refl ∣ ] , y ] ·R[1/f][1/g] (x .snd .fst /1/1))
                     (Σ≡Prop (λ _ → propTruncIsProp) (^-respects-/1 _ n)) (bar r m n)

   foo : (r : R[1/_] R' f) (n : ℕ) → ∃[ x ∈ R × S[fg] ]
         (x .fst /1/1) ≡ [ r , g/1 ^ᶠ n , ∣ n , refl ∣ ] ·R[1/f][1/g] (x .snd .fst /1/1)
   foo = InvElPropElim _ (λ _ → isPropΠ λ _ → propTruncIsProp) baz

   foo2 : (r : R[1/_] R' f) (n : ℕ) → ∃[ x ∈ R × S[fg] ]
          (x .fst /1/1) ·R[1/f][1/g]
          ((x .snd .fst /1/1) ⁻¹) ⦃ φS⊆Aˣ pathtoR[1/fg] (x .snd .fst) (x .snd .snd) ⦄
        ≡ [ r , g/1 ^ᶠ n , ∣ n , refl ∣ ]
   foo2 r n = PT.map Σhelper (foo r n)
    where
    Σhelper : Σ[ x ∈ R × S[fg] ]
               (x .fst /1/1) ≡ [ r , g/1 ^ᶠ n , ∣ n , refl ∣ ] ·R[1/f][1/g] (x .snd .fst /1/1)
            → Σ[ x ∈ R × S[fg] ]
               (x .fst /1/1) ·R[1/f][1/g] ((x .snd .fst /1/1) ⁻¹)
               ⦃ φS⊆Aˣ pathtoR[1/fg] (x .snd .fst) (x .snd .snd) ⦄
               ≡ [ r , g/1 ^ᶠ n , ∣ n , refl ∣ ]
    Σhelper ((r' , s , s∈S[fg]) , p) = (r' , s , s∈S[fg])
                                     , ⁻¹-eq-elim ⦃ φS⊆Aˣ pathtoR[1/fg] s s∈S[fg] ⦄ p

