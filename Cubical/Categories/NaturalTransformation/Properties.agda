
{-# OPTIONS --safe #-}

module Cubical.Categories.NaturalTransformation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (iso to iIso)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism renaming (isIso to isIsoC)
open import Cubical.Categories.NaturalTransformation.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open isIsoC
open NatIso
open NatTrans
open Category
open Functor

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  private
    _⋆ᴰ_ : ∀ {x y z} (f : D [ x , y ]) (g : D [ y , z ]) → D [ x , z ]
    f ⋆ᴰ g = f ⋆⟨ D ⟩ g

  -- natural isomorphism is symmetric
  symNatIso : ∀ {F G : Functor C D}
            → F ≅ᶜ G
            → G ≅ᶜ F
  symNatIso η .trans .N-ob x = η .nIso x .inv
  symNatIso η .trans .N-hom _ = sqLL η
  symNatIso η .nIso x .inv = η .trans .N-ob x
  symNatIso η .nIso x .sec = η .nIso x .ret
  symNatIso η .nIso x .ret = η .nIso x .sec

  -- Properties

  -- path helpers
  module NatTransP where

    module _ {F G : Functor C D} where
      open Iso

      -- same as Sigma version
      NatTransΣ = Σ[ ob ∈ ((x : C .ob) → D [(F .F-ob x) , (G .F-ob x)]) ]
                     ({x y : _ } (f : C [ x , y ]) → (F .F-hom f) ⋆ᴰ (ob y) ≡ (ob x) ⋆ᴰ (G .F-hom f))

      NatTransIsoΣ : Iso (NatTrans F G) NatTransΣ
      NatTransIsoΣ .fun (natTrans N-ob N-hom) = N-ob , N-hom
      NatTransIsoΣ .inv (N-ob , N-hom) = (natTrans N-ob N-hom)
      NatTransIsoΣ .rightInv _ = refl
      NatTransIsoΣ .leftInv _ = refl

      NatTrans≡Σ = ua (isoToEquiv NatTransIsoΣ)

      -- introducing paths
      NatTrans-≡-intro : ∀ {αo βo : N-ob-Type F G}
                           {αh : N-hom-Type F G αo}
                           {βh : N-hom-Type F G βo}
                       → (p : αo ≡ βo)
                       → PathP (λ i → ({x y : C .ob} (f : C [ x , y ]) → (F .F-hom f) ⋆ᴰ (p i y) ≡ (p i x) ⋆ᴰ (G .F-hom f))) αh βh
                       → natTrans {F = F} {G} αo αh ≡ natTrans βo βh
      NatTrans-≡-intro p q i = natTrans (p i) (q i)
    module _ {F G : Functor C D} {α β : NatTrans F G} where
      open Iso
      private
        αOb = α .N-ob
        βOb = β .N-ob
        αHom = α .N-hom
        βHom = β .N-hom
      -- path between natural transformations is the same as a pair of paths (between ob and hom)
      NTPathIsoPathΣ : Iso (α ≡ β)
                         (Σ[ p ∈ (αOb ≡ βOb) ]
                              (PathP (λ i → ({x y : _} (f : _) → F ⟪ f ⟫ ⋆ᴰ (p i y) ≡ (p i x) ⋆ᴰ G ⟪ f ⟫))
                                  αHom
                                  βHom))
      NTPathIsoPathΣ .fun p = (λ i → p i .N-ob) , (λ i → p i .N-hom)
      NTPathIsoPathΣ .inv (po , ph) i = record { N-ob = po i ; N-hom = ph i }
      NTPathIsoPathΣ .rightInv pσ = refl
      NTPathIsoPathΣ .leftInv p = refl

      NTPath≃PathΣ = isoToEquiv NTPathIsoPathΣ

      NTPath≡PathΣ = ua NTPath≃PathΣ

  module _ where
    open NatTransP

    -- if the target category has hom Sets, then any natural transformation is a set
    isSetNatTrans : ∀ {F G : Functor C D}
                  → isSet (NatTrans F G)
    isSetNatTrans {F} {G} α β p1 p2 i = comp (λ i → NTPath≡PathΣ {F = F} {G} {α} {β} (~ i))
                                             (λ j → λ {(i = i0) → transport-filler NTPath≡PathΣ p1 (~ j) ;
                                                       (i = i1) → transport-filler NTPath≡PathΣ p2 (~ j)})
                                             (p1Σ≡p2Σ i)
      where
        αOb = α .N-ob
        βOb = β .N-ob
        αHom = α .N-hom
        βHom = β .N-hom

        -- convert to sigmas so we can reason about constituent paths separately
        p1Σ : Σ[ p ∈ (αOb ≡ βOb) ]
                (PathP (λ i → ({x y : _} (f : _) → F ⟪ f ⟫ ⋆ᴰ (p i y) ≡ (p i x) ⋆ᴰ G ⟪ f ⟫))
                      αHom
                      βHom)
        p1Σ = transport NTPath≡PathΣ p1

        p2Σ : Σ[ p ∈ (αOb ≡ βOb) ]
                (PathP (λ i → ({x y : _} (f : _) → F ⟪ f ⟫ ⋆ᴰ (p i y) ≡ (p i x) ⋆ᴰ G ⟪ f ⟫))
                       αHom
                       βHom)
        p2Σ = transport NTPath≡PathΣ p2

        -- type aliases
        typeN-ob = (x : C .ob) → D [(F .F-ob x) , (G .F-ob x)]
        typeN-hom : typeN-ob → Type _
        typeN-hom ϕ = {x y : C .ob} (f : C [ x , y ]) → (F .F-hom f) ⋆ᴰ (ϕ y) ≡ (ϕ x) ⋆ᴰ (G .F-hom f)

        -- the Ob function is a set
        isSetN-ob : isSet ((x : C .ob) → D [(F .F-ob x) , (G .F-ob x)])
        isSetN-ob = isOfHLevelΠ 2 λ _ → D .isSetHom

        -- the Hom function is a set
        isSetN-hom : (ϕ : typeN-ob) → isSet (typeN-hom ϕ)
        isSetN-hom γ = isProp→isSet (isPropImplicitΠ2 λ x y → isPropΠ λ f → D .isSetHom _ _)

        -- in fact it's a dependent Set, which we need because N-hom depends on N-ob
        isSetN-homP : isOfHLevelDep 2 (λ γ → {x y : C .ob} (f : C [ x , y ]) → (F .F-hom f) ⋆ᴰ (γ y) ≡ (γ x) ⋆ᴰ (G .F-hom f))
        isSetN-homP = isOfHLevel→isOfHLevelDep 2 isSetN-hom

        -- components of the equality
        p1Ob≡p2Ob : fst p1Σ ≡ fst p2Σ
        p1Ob≡p2Ob = isSetN-ob _ _ (fst p1Σ) (fst p2Σ)

        p1Hom≡p2Hom : PathP (λ i → PathP (λ j → typeN-hom (p1Ob≡p2Ob i j)) αHom βHom)
                            (snd p1Σ) (snd p2Σ)
        p1Hom≡p2Hom = isSetN-homP _ _ (snd p1Σ) (snd p2Σ) p1Ob≡p2Ob

        p1Σ≡p2Σ : p1Σ ≡ p2Σ
        p1Σ≡p2Σ = ΣPathP (p1Ob≡p2Ob , p1Hom≡p2Hom)
