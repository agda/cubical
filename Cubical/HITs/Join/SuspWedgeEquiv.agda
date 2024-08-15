{-

For pointed types, join X Y is equivalent to the suspension of their wedge.

This file is split off to prevent cyclic imports.

-}


{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.Join.SuspWedgeEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.HITs.Pushout
open import Cubical.HITs.Join
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SmashProduct

module _ {ℓ ℓ'} (X∙ @ (X , x₀) : Pointed ℓ) (Y∙ @ (Y , y₀) : Pointed ℓ') where

  {-
    We consider the 3×3 lemma applied to
      1 <--- 1 ---> 1
      ↑      ↑      ↑
      X <- X ⋁ Y -> Y
      ↓      ↓      ↓
      X <- X × Y -> Y
    This admittedly makes it annoying to accomodate for higher universes.
  -}

  open 3x3-span
  smash-span : 3x3-span
  smash-span .A00 = Unit* {ℓ}
  smash-span .A02 = Unit* {ℓ-max ℓ ℓ'}
  smash-span .A04 = Unit* {ℓ'}
  smash-span .A20 = X
  smash-span .A22 = X∙ ⋁ Y∙
  smash-span .A24 = Y
  smash-span .A40 = X
  smash-span .A42 = X × Y
  smash-span .A44 = Y
  smash-span .f10 = _ -- Unique map
  smash-span .f12 = _
  smash-span .f14 = _
  smash-span .f30 = idfun X
  smash-span .f32 = ⋁↪
  smash-span .f34 = idfun Y
  smash-span .f01 = _
  smash-span .f21 = ⋁proj₁ X∙ Y∙
  smash-span .f41 = fst
  smash-span .f03 = _
  smash-span .f23 = ⋁proj₂ X∙ Y∙
  smash-span .f43 = snd
  smash-span .H11 _ = refl
  smash-span .H13 _ = refl
  smash-span .H31 (inl x) = refl
  smash-span .H31 (inr y) = refl
  smash-span .H31 (push _ i) j = doubleCompPath-filler (refl {x = x₀}) refl refl j i
  smash-span .H33 (inl x) = refl
  smash-span .H33 (inr x) = refl
  smash-span .H33 (push _ i) j = doubleCompPath-filler (refl {x = y₀}) refl refl j i

  -- Perhaps some clever leveling will avoid these two trivial proofs
  A□2≃Unit* : A0□ smash-span ≃ Unit* {ℓ-max ℓ ℓ'}
  A□2≃Unit* = _ , record { equiv-proof =
    λ _ → (inl tt* , refl) ,
    λ { (inl _ , q) → refl
      ; (inr _ , q) → ΣPathP (push _ , refl)
      ; (push _ i , q) j → push _ (i ∧ j) , refl } }

  open Iso  -- This simply switches the Unit to Unit*
  Iso-A□2-⋀ : Iso (A□2 smash-span) (X∙ ⋀ Y∙)
  Iso-A□2-⋀ .fun (inl _) = inl _
  Iso-A□2-⋀ .fun (inr x) = inr x
  Iso-A□2-⋀ .fun (push a i) = push a i
  Iso-A□2-⋀ .inv (inl _) = inl _
  Iso-A□2-⋀ .inv (inr x) = inr x
  Iso-A□2-⋀ .inv (push a i) = push a i
  Iso-A□2-⋀ .rightInv (inl _) = refl
  Iso-A□2-⋀ .rightInv (inr x) = refl
  Iso-A□2-⋀ .rightInv (push a i) = refl
  Iso-A□2-⋀ .leftInv (inl _) = refl
  Iso-A□2-⋀ .leftInv (inr x) = refl
  Iso-A□2-⋀ .leftInv (push a i) = refl

  A4□≃join : A4□ smash-span ≃ join X Y
  A4□≃join = joinPushout≃join X Y

  A2□≃Unit* : A2□ smash-span ≃ Unit* {ℓ-max ℓ ℓ'}
  A2□≃Unit* = compEquiv (Pushout⋁≃Unit _ _) Unit≃Unit*

  A○□≡join : A○□ smash-span ≡ join X Y
  A○□≡join = spanEquivToPushoutPath record
    { e0 = A□2≃Unit*
    ; e2 = A2□≃Unit*
    ; e4 = A4□≃join
    ; H1 = λ _ → refl
    ; H3 = λ x → subst (λ x → inl x₀ ≡ A4□≃join .fst (f3□ smash-span x))
      (cong fst (A2□≃Unit* .snd .equiv-proof _ .snd (x , refl)))
      (sym (join-inr-null _))
    } ∙ sym (ua (pushoutIdfunEquiv' _))

  A□○≡Σ : A□○ smash-span ≡ Susp (X∙ ⋀ Y∙)
  A□○≡Σ = spanEquivToPushoutPath record {
      e0 = invEquiv (pushoutIdfunEquiv _) ;
      e2 = isoToEquiv Iso-A□2-⋀ ;
      e4 = invEquiv (pushoutIdfunEquiv _) ;
      H1 = λ _ → refl ;
      H3 = λ _ → refl
    } ∙ sym (Susp≡PushoutSusp* {ℓ-max ℓ ℓ'})

  join≡Susp : Susp (X∙ ⋀ Y∙) ≡ join X Y
  join≡Susp = sym A□○≡Σ ∙ 3x3-lemma smash-span ∙ A○□≡join

