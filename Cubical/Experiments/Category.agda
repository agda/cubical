{-# OPTIONS --cubical --postfix-projections #-}

module Cubical.Experiments.Category where

open import Cubical.Foundations.Prelude

record Precategory ℓ : Type (ℓ-suc ℓ) where
  field
    ob : Type ℓ
    hom : ob → ob → Type ℓ
    idn : ∀ x → hom x x
    seq : ∀ {x y z} (f : hom x y) (g : hom y z) → hom x z
    seq-λ : ∀ {x y : ob} (f : hom x y) → seq (idn x) f ≡ f
    seq-ρ : ∀ {x y} (f : hom x y) → seq f (idn y) ≡ f
    seq-α : ∀ {u v w x} (f : hom u v) (g : hom v w) (h : hom w x) → seq (seq f g) h ≡ seq f (seq g h)

open Precategory

module _ {ℓ𝒞 ℓ𝒟} where
  record Functor (𝒞 : Precategory ℓ𝒞) (𝒟 : Precategory ℓ𝒟) : Type (ℓ-max ℓ𝒞 ℓ𝒟) where
    open Precategory

    field
      F-ob : 𝒞 .ob → 𝒟 .ob
      F-hom : {x y : 𝒞 .ob} → 𝒞 .hom x y → 𝒟 .hom (F-ob x) (F-ob y)
      F-idn : {x : 𝒞 .ob} → F-hom (𝒞 .idn x) ≡ 𝒟 .idn (F-ob x)
      F-seq : {x y z : 𝒞 .ob} (f : 𝒞 .hom x y) (g : 𝒞 .hom y z) → F-hom (𝒞 .seq f g) ≡ 𝒟 .seq (F-hom f) (F-hom g)


module _ {ℓ𝒞 ℓ𝒟 : Level} {𝒞 : Precategory ℓ𝒞} {𝒟 : Precategory ℓ𝒟} where
  record NatTrans (F G : Functor 𝒞 𝒟) : Type (ℓ-max ℓ𝒞 ℓ𝒟) where
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

  module _ (𝒟/hom/set : ∀ {x y} → isSet (𝒟 .hom x y)) where
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


    FTR : Precategory (ℓ-max ℓ𝒞 ℓ𝒟)
    FTR .ob = Functor 𝒞 𝒟
    FTR .hom = NatTrans
    FTR .idn = id-trans
    FTR .seq = seq-trans
    FTR .seq-λ α i .N-ob x = 𝒟 .seq-λ (α .N-ob x) i
    FTR .seq-λ {F} {G} α i .N-hom f = rem i
      where
        rem : PathP (λ i → 𝒟 .seq (F .F-hom f) (𝒟 .seq-λ (α .N-ob _) i) ≡ 𝒟 .seq (𝒟 .seq-λ (α .N-ob _) i) (G .F-hom f)) (seq-trans (id-trans _) α .N-hom _) (α .N-hom _)
        rem = toPathP (𝒟/hom/set _ _ _ _)
    FTR .seq-ρ α i .N-ob x = 𝒟 .seq-ρ (α .N-ob x) i
    FTR .seq-ρ {F} {G} α i .N-hom f = rem i
      where
        rem : PathP (λ i → 𝒟 .seq (F .F-hom f) (𝒟 .seq-ρ (α .N-ob _) i) ≡ 𝒟 .seq (𝒟 .seq-ρ (α .N-ob _) i) (G .F-hom f)) (seq-trans α (id-trans _) .N-hom _) (α .N-hom _)
        rem = toPathP (𝒟/hom/set _ _ _ _)
    FTR .seq-α α β γ i .N-ob x = 𝒟 .seq-α (α .N-ob x) (β .N-ob x) (γ .N-ob x) i
    FTR .seq-α {F} {G} {H} {I} α β γ i .N-hom f = rem i
      where
        rem : PathP (λ i → 𝒟 .seq (F .F-hom f) (𝒟 .seq-α (α .N-ob _) (β .N-ob _) (γ .N-ob _) i) ≡ 𝒟 .seq (𝒟 .seq-α (α .N-ob _) (β .N-ob _) (γ .N-ob _) i) (F-hom I f)) (seq-trans (seq-trans α β) γ .N-hom _) (seq-trans α (seq-trans β γ) .N-hom _)
        rem = toPathP (𝒟/hom/set _ _ _ _)

module _ (ℓ : Level) where
  open Precategory

  TYPE : Precategory (ℓ-suc ℓ)
  TYPE .ob = Type ℓ
  TYPE .hom A B = Lift (A → B)
  TYPE .idn A .lower x = x
  TYPE .seq (lift f) (lift g) .lower x = g (f x)
  TYPE .seq-λ f = refl
  TYPE .seq-ρ f = refl
  TYPE .seq-α f g h = refl
