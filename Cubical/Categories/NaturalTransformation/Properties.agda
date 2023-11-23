
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
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation.Base

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'
    F F' : Functor C D

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
  (isUnivD : isUnivalent D)
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
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  seqNatIso : {F G H : Functor C D} → NatIso F G → NatIso G H → NatIso F H
  seqNatIso ı ı' .trans = seqTrans (ı .trans) (ı' .trans)
  seqNatIso ı ı' .nIso x .inv = ı' .nIso x .inv ⋆⟨ D ⟩ ı .nIso x .inv
  seqNatIso ı ı' .nIso x .sec =
    D .⋆Assoc _ _ _
    ∙ cong (_⋆_ D (ı' .nIso x .inv))
      (sym (D .⋆Assoc _ _ _)
      ∙ cong (D ∘ ı' .trans .N-ob x) (ı .nIso x .sec)
      ∙ D .⋆IdL (ı' .trans .N-ob x))
    ∙ ı' .nIso x .sec
  seqNatIso ı ı' .nIso x .ret =
    (sym (D .⋆Assoc _ _ _))
    ∙ cong (_∘_ D (ı .nIso x .inv))
      (D .⋆Assoc _ _ _
      ∙ cong (D ⋆ ı .trans .N-ob x) (ı' .nIso x .ret)
      ∙ D .⋆IdR (ı .trans .N-ob x))
    ∙ ı .nIso x .ret

  CAT⋆IdR : {F : Functor C D} → NatIso (Id ∘F F) F
  CAT⋆IdR {F} .trans .N-ob = idTrans F .N-ob
  CAT⋆IdR {F} .trans .N-hom = idTrans F .N-hom
  CAT⋆IdR {F} .nIso = idNatIso F .nIso

module _ {B : Category ℓB ℓB'}{C : Category ℓC ℓC'}{D : Category ℓD ℓD'} where
  _∘ʳi_ : ∀ (K : Functor C D) → {G H : Functor B C} (β : NatIso G H)
       → NatIso (K ∘F G) (K ∘F H)
  _∘ʳi_ K β .trans = K ∘ʳ β .trans
  _∘ʳi_ K β .nIso x = preserveIsosF {F = K} (β .trans .N-ob _ , β .nIso x) .snd

  open Functor
  _∘ˡi_ : ∀ (K : Functor B C) → {G H : Functor C D} (β : NatIso G H)
       → NatIso (G ∘F K) (H ∘F K)
  _∘ˡi_ K β .trans = β .trans ∘ˡ K
  _∘ˡi_ K β .nIso b  = β .nIso (K ⟅ b ⟆)

  CAT⋆Assoc : {E : Category ℓE ℓE'}
            (F : Functor B C)(G : Functor C D)(H : Functor D E)
            → NatIso (H ∘F (G ∘F F)) ((H ∘F G) ∘F F)
  CAT⋆Assoc F G H .trans .N-ob = idTrans ((H ∘F G) ∘F F) .N-ob
  CAT⋆Assoc F G H .trans .N-hom = idTrans ((H ∘F G) ∘F F) .N-hom
  CAT⋆Assoc F G H .nIso = idNatIso ((H ∘F G) ∘F F) .nIso



⇒^opFiso : Iso (F ⇒ F') (_^opF {C = C} {D = D} F' ⇒ F ^opF )
N-ob (fun ⇒^opFiso x) = N-ob x
N-hom (fun ⇒^opFiso x) f = sym (N-hom x f)
inv ⇒^opFiso = _
rightInv ⇒^opFiso _ = refl
leftInv ⇒^opFiso _ = refl

congNatIso^opFiso : Iso (F ≅ᶜ F') (_^opF  {C = C} {D = D} F'  ≅ᶜ F ^opF )
trans (fun congNatIso^opFiso x) = Iso.fun ⇒^opFiso (trans x)
inv (nIso (fun congNatIso^opFiso x) x₁) = _
sec (nIso (fun congNatIso^opFiso x) x₁) = ret (nIso x x₁)
ret (nIso (fun congNatIso^opFiso x) x₁) = sec (nIso x x₁)
inv congNatIso^opFiso = _
rightInv congNatIso^opFiso _ = refl
leftInv congNatIso^opFiso _ = refl

