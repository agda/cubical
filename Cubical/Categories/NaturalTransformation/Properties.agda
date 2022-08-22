
{-# OPTIONS --safe #-}

module Cubical.Categories.NaturalTransformation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (iso to iIso)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open isIsoC
open NatIso
open NatTrans
open Category
open Functor
open Iso

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

      -- same as Sigma version
      NatTransΣ : Type (ℓ-max (ℓ-max ℓC ℓC') ℓD')
      NatTransΣ = Σ[ ob ∈ ((x : C .ob) → D [(F .F-ob x) , (G .F-ob x)]) ]
                     ({x y : _ } (f : C [ x , y ]) → (F .F-hom f) ⋆ᴰ (ob y) ≡ (ob x) ⋆ᴰ (G .F-hom f))

      NatTransIsoΣ : Iso (NatTrans F G) NatTransΣ
      NatTransIsoΣ .fun (natTrans N-ob N-hom) = N-ob , N-hom
      NatTransIsoΣ .inv (N-ob , N-hom) = (natTrans N-ob N-hom)
      NatTransIsoΣ .rightInv _ = refl
      NatTransIsoΣ .leftInv _ = refl

      NatTrans≡Σ : NatTrans F G ≡ NatTransΣ
      NatTrans≡Σ = isoToPath NatTransIsoΣ

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

    isSetNatTrans : {F G : Functor C D} → isSet (NatTrans F G)
    isSetNatTrans =
      isSetRetract (fun NatTransIsoΣ) (inv NatTransIsoΣ) (leftInv NatTransIsoΣ)
                   (isSetΣSndProp (isSetΠ (λ _ → isSetHom D))
                                  (λ _ → isPropImplicitΠ2 (λ _ _ → isPropΠ (λ _ → isSetHom D _ _))))


-- Natural isomorphism is path when the target category is univalent.

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}(isUnivD : isUnivalent D)
  {F G : Functor C D} where

  open isUnivalent isUnivD

  NatIsoToPath : NatIso F G → F ≡ G
  NatIsoToPath niso =
    Functor≡ (λ x → CatIsoToPath (_ , niso .nIso x))
      (λ f → isoToPath-Square isUnivD _ _ _ _ (niso .trans .N-hom f))

  NatIso→Path→NatIso : (niso : NatIso F G) → pathToNatIso (NatIsoToPath niso) ≡ niso
  NatIso→Path→NatIso niso = NatIso≡ (λ i x → secEq (univEquiv _ _) (_ , niso .nIso x) i .fst)

  Path→NatIso→Path : (p : F ≡ G) → NatIsoToPath (pathToNatIso p) ≡ p
  Path→NatIso→Path p = FunctorPath≡ (λ i j x → retEq (univEquiv _ _) (λ i → p i .F-ob x) i j)

  Iso-Path-NatIso : Iso (F ≡ G) (NatIso F G)
  Iso-Path-NatIso = iso pathToNatIso NatIsoToPath NatIso→Path→NatIso Path→NatIso→Path

  Path≃NatIso : (F ≡ G) ≃ NatIso F G
  Path≃NatIso = isoToEquiv Iso-Path-NatIso
