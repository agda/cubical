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


-- Check: (R[1/f])[1/g] ≡ R[1/fg]
-- still TODO:
-- ψ : R[1/f][1/g] → R[1/fg]
-- η : section φ ψ
-- ε : retract φ ψ
-- prove that φ is ring hom
module check (R' : CommRing {ℓ}) (f g : (R' .fst)) where
 open isMultClosedSubset
 open CommRingStr (R' .snd)
 open Exponentiation R'
 open Theory (CommRing→Ring R')
 open CommRingStr (R[1/_]AsCommRing R' f .snd) renaming ( _·_ to _·ᶠ_ ; 1r to 1ᶠ ; _+_ to _+ᶠ_
                                                        ; ·-lid to ·ᶠ-lid ; ·-rid to ·ᶠ-rid
                                                        ; ·-assoc to ·ᶠ-assoc ; ·-comm to ·ᶠ-comm)


 private
  R = R' .fst
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
          ≡⟨ (λ i → ·-lid ((·-lid r i) · (g ^ m)) i · (·-rid (·-lid (f ^ m) i) i)) ⟩
            r · g ^ m · f ^ m
          ≡⟨ sym (·-assoc _ _ _) ⟩
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
          ≡⟨ ·-assoc _ _ _ ⟩
            r · g ^ n · f ^ n
          ≡⟨ (λ i → ·-lid ((·-lid r (~ i)) · (g ^ n)) (~ i) · (·-rid (·-lid (f ^ n) (~ i)) (~ i))) ⟩
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
         ≡⟨ (λ i → ·-assoc (f ^ l) ((g ^ l) · r) (g ^ m) i · ·-rid (1r · (f ^ m)) i) ⟩
           f ^ l · (g ^ l · r) · g ^ m · (1r · f ^ m)
         ≡⟨ (λ i → ·-assoc (f ^ l) (g ^ l) r i · g ^ m ·  ·-lid (f ^ m) i) ⟩
           f ^ l · g ^ l · r · g ^ m · f ^ m
         ≡⟨ sym (·-assoc _ _ _) ⟩
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
         ≡⟨ ·-assoc _ _ _ ⟩
           f ^ l · g ^ l · r' · g ^ n · f ^ n
         ≡⟨ (λ i → ·-assoc (f ^ l) (g ^ l) r' (~ i) · g ^ n ·  ·-lid (f ^ n) (~ i)) ⟩
           f ^ l · (g ^ l · r') · g ^ n · (1r · f ^ n)
         ≡⟨ (λ i → ·-assoc (f ^ l) ((g ^ l) · r') (g ^ n) (~ i) · ·-rid (1r · (f ^ n)) (~ i)) ⟩
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
                         (cong₂ _+_ (sym (·-rid _) ∙ (λ i → (·-rid r (~ i)) · (·-rid 1r (~ i))))
                         (sym (·-rid _) ∙ (λ i → (·-rid r' (~ i)) · (·-rid 1r (~ i)))))
                                                  (Σ≡Prop (λ _ → propTruncIsProp)
                         (sym (·-lid _) ∙ (λ i → (·-lid 1r (~ i)) · (·-lid 1r (~ i)))))))
                                                  (Σ≡Prop (λ _ → propTruncIsProp) (sym (·ᶠ-lid 1ᶠ))))
 RingHom.isHom· /1/1AsCommRingHom r r' = cong [_] (≡-× (cong [_]
                                                  (≡-× refl (Σ≡Prop (λ _ → propTruncIsProp)
                                                  (sym (·-lid _)))))
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
         ≡⟨ (λ i → ·-lid (·-rid (·-lid (·-rid s i) i) i) i · (·-lid 1r i · ·-lid 1r i) ) ⟩
           s · (1r · 1r)
         ≡⟨ cong (s ·_) (·-rid _) ⟩
           s · 1r
         ≡⟨ ·-rid _ ⟩
           s
         ≡⟨ p ⟩
           (f · g) ^ n
         ≡⟨ ^-ldist-· _ _ _ ⟩
           f ^ n · g ^ n
         ≡⟨ (λ i → ·-comm (f ^ n) (·-lid (g ^ n) (~ i)) i) ⟩
           1r · g ^ n · f ^ n
         ≡⟨ (λ i → ·-lid (·-lid 1r (~ i) · ·-lid (g ^ n) (~ i)) (~ i)
                   · ·-rid (·-lid (·-lid (f ^ n) (~ i)) (~ i)) (~ i)) ⟩
           1r · (1r · 1r · (1r · g ^ n)) · (1r · (1r · f ^ n) · 1r) ∎

  kerφ⊆annS pathtoR[1/fg] r p = {!!}
   where
   ∥r/1,1/1≈0/1,1/1∥ = Iso.fun (SQ.isEquivRel→TruncIso (Loc.locIsEquivRel _ _ _) _ _) p

  surχ pathtoR[1/fg] = InvElPropElim _ (λ _ → propTruncIsProp) {!!}
