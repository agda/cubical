{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Group.Properties where

open import Cubical.Foundations.Prelude

{- Proof that inv (g h) ≡ (inv h) (inv g) -}
invComp : {ℓ : Level} {(group type _ (group-struct _ inv _∘_ _ _ _ _ _)) : Group ℓ} (g g' : type) → inv (g ∘ g') ≡ inv g' ∘ inv g
invComp {_} {group type _ (group-struct _ inv _∘_ lUnit rUnit assoc lCancel rCancel)} g g' =
  sym (rUnit (inv (g ∘ g'))) ∙∙
  cong (inv (g ∘ g') ∘_) ((sym (rCancel g)) ∙∙
      cong (_∘ (inv g)) (sym (rUnit g)) ∙∙
      cong (λ z → (g ∘ z) ∘ (inv g)) (sym (rCancel g')) ∙∙
      cong (_∘ (inv g)) (sym (assoc g g' (inv g'))) ∙∙
      assoc (g ∘ g') (inv g') (inv g)) ∙∙
  sym (assoc (inv (g ∘ g')) (g ∘ g') ((inv g') ∘ (inv g))) ∙∙
  cong (_∘ ((inv g') ∘ (inv g))) (lCancel (g ∘ g')) ∙∙
  lUnit ((inv g') ∘ (inv g))

{- Proof that inv id ≡ id -}
invId : {ℓ : Level} ((group type _ (group-struct id inv _ _ _ _ _  _)) : Group ℓ) → inv id ≡ id
invId {_} (group _ _ (group-struct id inv _ _ rUnit _ lCancel _)) = sym (rUnit (inv id)) ∙ (lCancel id)
