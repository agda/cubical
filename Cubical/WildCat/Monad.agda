module Cubical.WildCat.Monad where

open import Cubical.Foundations.Prelude
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private variable
  ℓ ℓ' : Level

module _ {C : WildCat ℓ ℓ'} (M : WildFunctor C C) where
  open WildCat C
  open WildFunctor
  open WildNatTrans

  IsPointed : Type (ℓ-max ℓ ℓ')
  IsPointed = WildNatTrans C C (idWildFunctor C) M

  record IsMonad : Type (ℓ-max ℓ ℓ') where
    field
      η : IsPointed
      μ : WildNatTrans _ _ (comp-WildFunctor M M) M
      idl-μ : {X : ob} → μ .N-ob X ∘ η .N-ob (M .F-ob X) ≡ id
      idr-μ : {X : ob} → μ .N-ob X ∘ M .F-hom (η .N-ob X) ≡ id
      assoc-μ : {X : ob} → μ .N-ob X ∘ M .F-hom (μ .N-ob X) ≡ μ .N-ob X ∘ μ .N-ob (M .F-ob X)

    bind : {X Y : ob} → Hom[ X , M .F-ob Y ] → Hom[ M .F-ob X , M .F-ob Y ]
    bind f = μ .N-ob _ ∘ M .F-hom f

WildMonad : WildCat ℓ ℓ' → Type (ℓ-max ℓ ℓ')
WildMonad C = Σ[ M ∈ WildFunctor C C ] IsMonad M
