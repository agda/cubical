{-# OPTIONS --safe #-}
module Cubical.Categories.Multicategory.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.FinData as Fin
open import Cubical.Data.List as List
open import Cubical.Data.List.FinData as List

private variable
  ℓ ℓ' : Level

record Multicategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality

  field
    ob : Type ℓ
    Hom : List ob → ob → Type ℓ'
    id : {x : ob} → Hom [ x ] x
    _⋆_ : {ys : List ob} {z : ob} {xss : FinVec (List ob) (length ys)}
        → (fs : ∀ k → Hom (xss k) (lookup ys k)) → (g : Hom ys z) → Hom (foldrFinVec _++_ [] xss) z

    ⋆IdR : {xs : List ob} {y : ob} → (f : Hom xs y)
         → PathP (λ i → Hom (++-unit-r xs i) y) (_⋆_ {xss = λ _ → xs} (λ where zero → f) id) f

    ⋆IdL : {xs : List ob} {y : ob} → (f : Hom xs y)
         → PathP (λ i → Hom (tabulate'-lookup xs i) y) ((λ _ → id) ⋆ f) f

    ⋆Assoc : {zs : List ob} {w : ob} {yss : FinVec (List ob) (length zs)} {xsss : ∀ k → FinVec (List ob) (length (yss k))}
           → (h : Hom zs w) (gs : ∀ k → Hom (yss k) (lookup zs k)) (fss : ∀ k l → Hom (xsss k l) (lookup (yss k) l))
           → PathP (λ i → Hom {!   !} w)
             ((λ kl → {!   !}) ⋆ (gs ⋆ h))
             ((λ k → fss k ⋆ gs k) ⋆ h)