{-# OPTIONS --cubical --safe #-}

module Cubical.Categories.NaturalTransformation where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓ𝒞 ℓ𝒞' ℓ𝒟 ℓ𝒟' : Level

module _ {𝒞 : Precategory ℓ𝒞 ℓ𝒞'} {𝒟 : Precategory ℓ𝒟 ℓ𝒟'} where
  record NatTrans (F G : Functor 𝒞 𝒟) : Type (ℓ-max (ℓ-max ℓ𝒞 ℓ𝒞') (ℓ-max ℓ𝒟 ℓ𝒟')) where
    open Precategory
    open Functor

    field
      N-ob : (x : 𝒞 .ob) → 𝒟 .hom (F .F-ob x) (G .F-ob x)
      N-hom : {x y : 𝒞 .ob} (f : 𝒞 .hom x y) → 𝒟 .seq (F .F-hom f) (N-ob y) ≡ 𝒟 .seq (N-ob x) (G .F-hom f)


  open Precategory
  open Functor
  open NatTrans

  id-trans : (F : Functor 𝒞 𝒟) → NatTrans F F
  id-trans F .N-ob x = 𝒟 .idn (F .F-ob x)
  id-trans F .N-hom f =
     𝒟 .seq (F .F-hom f) (id-trans F .N-ob _)
       ≡⟨ 𝒟 .seq-ρ _ ⟩
     F .F-hom f
       ≡⟨ sym (𝒟 .seq-λ _) ⟩
     𝒟 .seq (𝒟 .idn (F .F-ob _)) (F .F-hom f)
       ∎


  seq-trans : {F G H : Functor 𝒞 𝒟} (α : NatTrans F G) (β : NatTrans G H) → NatTrans F H
  seq-trans α β .N-ob x = 𝒟 .seq (α .N-ob x) (β .N-ob x)
  seq-trans {F} {G} {H} α β .N-hom f =
    𝒟 .seq (F .F-hom f) (𝒟 .seq (α .N-ob _) (β .N-ob _))
      ≡⟨ sym (𝒟 .seq-α _ _ _) ⟩
    𝒟 .seq (𝒟 .seq (F .F-hom f) (α .N-ob _)) (β .N-ob _)
      ≡[ i ]⟨ 𝒟 .seq (α .N-hom f i) (β .N-ob _) ⟩
    𝒟 .seq (𝒟 .seq (α .N-ob _) (G .F-hom f)) (β .N-ob _)
      ≡⟨ 𝒟 .seq-α _ _ _ ⟩
    𝒟 .seq (α .N-ob _) (𝒟 .seq (G .F-hom f) (β .N-ob _))
      ≡[ i ]⟨ 𝒟 .seq (α .N-ob _) (β .N-hom f i) ⟩
    𝒟 .seq (α .N-ob _) (𝒟 .seq (β .N-ob _) (H .F-hom f))
      ≡⟨ sym (𝒟 .seq-α _ _ _) ⟩
    𝒟 .seq (𝒟 .seq (α .N-ob _) (β .N-ob _)) (H .F-hom f)
      ∎

  module _  ⦃ 𝒟-category : isCategory 𝒟 ⦄ {F G : Functor 𝒞 𝒟} {α β : NatTrans F G} where
    open Precategory
    open Functor
    open NatTrans

    make-nat-trans-path : α .N-ob ≡ β .N-ob → α ≡ β
    make-nat-trans-path p i .N-ob = p i
    make-nat-trans-path p i .N-hom f = rem i
      where
        rem : PathP (λ i → 𝒟 .seq (F .F-hom f) (p i _) ≡ 𝒟 .seq (p i _) (G .F-hom f)) (α .N-hom f) (β .N-hom f)
        rem = toPathP (𝒟-category .homIsSet _ _ _ _)


module _ (𝒞 : Precategory ℓ𝒞 ℓ𝒞') (𝒟 : Precategory ℓ𝒟 ℓ𝒟') ⦃ _ : isCategory 𝒟 ⦄ where
  open Precategory
  open NatTrans
  open Functor

  FUNCTOR : Precategory (ℓ-max (ℓ-max ℓ𝒞 ℓ𝒞') (ℓ-max ℓ𝒟 ℓ𝒟')) (ℓ-max (ℓ-max ℓ𝒞 ℓ𝒞') (ℓ-max ℓ𝒟 ℓ𝒟'))
  FUNCTOR .ob = Functor 𝒞 𝒟
  FUNCTOR .hom = NatTrans
  FUNCTOR .idn = id-trans
  FUNCTOR .seq = seq-trans
  FUNCTOR .seq-λ α = make-nat-trans-path λ i x → 𝒟 .seq-λ (α .N-ob x) i
  FUNCTOR .seq-ρ α = make-nat-trans-path λ i x → 𝒟 .seq-ρ (α .N-ob x) i
  FUNCTOR .seq-α α β γ = make-nat-trans-path λ i x → 𝒟 .seq-α (α .N-ob x) (β .N-ob x) (γ .N-ob x) i
