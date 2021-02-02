{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.NaturalTransformation where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} where
  -- syntax for sequencing in category D
  _⋆ᴰ_ : ∀ {x y z} (f : D [ x , y ]) (g : D [ y , z ]) → D [ x , z ]
  f ⋆ᴰ g = f ⋆⟨ D ⟩ g


  record NatTrans (F G : Functor C D) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    open Precategory
    open Functor

    field
      -- components of the natural transformation
      N-ob : (x : C .ob) → D [(F .F-ob x) , (G .F-ob x)]
      -- naturality condition
      N-hom : {x y : C .ob} (f : C [ x , y ]) → (F .F-hom f) ⋆ᴰ (N-ob y) ≡ (N-ob x) ⋆ᴰ (G .F-hom f)


  open Precategory
  open Functor
  open NatTrans

  idTrans : (F : Functor C D) → NatTrans F F
  idTrans F .N-ob x = D .id (F .F-ob x)
  idTrans F .N-hom f =
     (F .F-hom f) ⋆ᴰ (idTrans F .N-ob _)
       ≡⟨ D .⋆IdR _ ⟩
     F .F-hom f
       ≡⟨ sym (D .⋆IdL _) ⟩
     (D .id (F .F-ob _)) ⋆ᴰ (F .F-hom f)
       ∎


  seqTrans : {F G H : Functor C D} (α : NatTrans F G) (β : NatTrans G H) → NatTrans F H
  seqTrans α β .N-ob x = (α .N-ob x) ⋆ᴰ (β .N-ob x)
  seqTrans {F} {G} {H} α β .N-hom f =
    (F .F-hom f) ⋆ᴰ ((α .N-ob _) ⋆ᴰ (β .N-ob _))
      ≡⟨ sym (D .⋆Assoc _ _ _) ⟩
    ((F .F-hom f) ⋆ᴰ (α .N-ob _)) ⋆ᴰ (β .N-ob _)
      ≡[ i ]⟨ (α .N-hom f i) ⋆ᴰ (β .N-ob _) ⟩
    ((α .N-ob _) ⋆ᴰ (G .F-hom f)) ⋆ᴰ (β .N-ob _)
      ≡⟨ D .⋆Assoc _ _ _ ⟩
    (α .N-ob _) ⋆ᴰ ((G .F-hom f) ⋆ᴰ (β .N-ob _))
      ≡[ i ]⟨ (α .N-ob _) ⋆ᴰ (β .N-hom f i) ⟩
    (α .N-ob _) ⋆ᴰ ((β .N-ob _) ⋆ᴰ (H .F-hom f))
      ≡⟨ sym (D .⋆Assoc _ _ _) ⟩
    ((α .N-ob _) ⋆ᴰ (β .N-ob _)) ⋆ᴰ (H .F-hom f)
      ∎

  module _  ⦃ D-category : isCategory D ⦄ {F G : Functor C D} {α β : NatTrans F G} where
    open Precategory
    open Functor
    open NatTrans

    makeNatTransPath : α .N-ob ≡ β .N-ob → α ≡ β
    makeNatTransPath p i .N-ob = p i
    makeNatTransPath p i .N-hom f = rem i
      where
        rem : PathP (λ i → (F .F-hom f) ⋆ᴰ (p i _) ≡ (p i _) ⋆ᴰ (G .F-hom f)) (α .N-hom f) (β .N-hom f)
        rem = toPathP (D-category .isSetHom _ _ _ _)


module _ (C : Precategory ℓC ℓC') (D : Precategory ℓD ℓD') ⦃ _ : isCategory D ⦄ where
  open Precategory
  open NatTrans
  open Functor

  FUNCTOR : Precategory (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
  FUNCTOR .ob = Functor C D
  FUNCTOR .Hom[_,_] = NatTrans
  FUNCTOR .id = idTrans
  FUNCTOR ._⋆_ = seqTrans
  FUNCTOR .⋆IdL α = makeNatTransPath λ i x → D .⋆IdL (α .N-ob x) i
  FUNCTOR .⋆IdR α = makeNatTransPath λ i x → D .⋆IdR (α .N-ob x) i
  FUNCTOR .⋆Assoc α β γ = makeNatTransPath λ i x → D .⋆Assoc (α .N-ob x) (β .N-ob x) (γ .N-ob x) i
