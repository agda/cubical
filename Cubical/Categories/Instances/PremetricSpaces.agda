{- Categories of premetric spaces with different kinds of mappings -}

module Cubical.Categories.Instances.PremetricSpaces where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP

open import Cubical.Categories.Category.Base as Cat

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

module _ (ℓ ℓ' : Level) where
  open Category
  open PremetricStr

  PrSpacesᶜ : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  ob       PrSpacesᶜ = PremetricSpace ℓ ℓ'
  Hom[_,_] PrSpacesᶜ = C[_,_]
  id       PrSpacesᶜ = idᶜ
  _⋆_      PrSpacesᶜ = flip _∘C_
  ⋆IdL     PrSpacesᶜ = λ _ → C≡ refl
  ⋆IdR     PrSpacesᶜ = λ _ → C≡ refl
  ⋆Assoc   PrSpacesᶜ = λ _ _ _ → C≡ refl
  isSetHom PrSpacesᶜ {y = N} =
    isSetΣSndProp (isSet→ (N .snd .isSetM)) (flip (isPropIsContinuous _) _)

  PrSpacesᵘᶜ : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  ob       PrSpacesᵘᶜ = PremetricSpace ℓ ℓ'
  Hom[_,_] PrSpacesᵘᶜ = UC[_,_]
  id       PrSpacesᵘᶜ = idᵘᶜ
  _⋆_      PrSpacesᵘᶜ = flip _∘UC_
  ⋆IdL     PrSpacesᵘᶜ = λ _ → UC≡ refl
  ⋆IdR     PrSpacesᵘᶜ = λ _ → UC≡ refl
  ⋆Assoc   PrSpacesᵘᶜ = λ _ _ _ → UC≡ refl
  isSetHom PrSpacesᵘᶜ {y = N} =
    isSetΣSndProp (isSet→ (N .snd .isSetM)) (flip (isPropIsUContinuous _) _)

  PrSpacesᴸ : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  ob       PrSpacesᴸ = PremetricSpace ℓ ℓ'
  Hom[_,_] PrSpacesᴸ = L[_,_]
  id       PrSpacesᴸ = idᴸ
  _⋆_      PrSpacesᴸ = flip _∘L_
  ⋆IdL     PrSpacesᴸ = λ _ → L≡ refl
  ⋆IdR     PrSpacesᴸ = λ _ → L≡ refl
  ⋆Assoc   PrSpacesᴸ = λ _ _ _ → L≡ refl
  isSetHom PrSpacesᴸ {y = N} =
    isSetΣSndProp (isSet→ (N .snd .isSetM)) (flip (isPropIsLipschitz _) _)

  PrSpacesⁿ : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  ob       PrSpacesⁿ = PremetricSpace ℓ ℓ'
  Hom[_,_] PrSpacesⁿ = NE[_,_]
  id       PrSpacesⁿ = idⁿ
  _⋆_      PrSpacesⁿ = flip _∘NE_
  ⋆IdL     PrSpacesⁿ = λ _ → NE≡ refl
  ⋆IdR     PrSpacesⁿ = λ _ → NE≡ refl
  ⋆Assoc   PrSpacesⁿ = λ _ _ _ → NE≡ refl
  isSetHom PrSpacesⁿ {y = N} =
    isSetΣSndProp (isSet→ (N .snd .isSetM)) (flip (isPropIsNonExpansive _) _)

  PrSpacesᴵ : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  ob       PrSpacesᴵ = PremetricSpace ℓ ℓ'
  Hom[_,_] PrSpacesᴵ = Isometry[_,_]
  id       PrSpacesᴵ = idᴵ
  _⋆_      PrSpacesᴵ = flip _∘Isometry_
  ⋆IdL     PrSpacesᴵ = λ _ → Isometry≡ refl
  ⋆IdR     PrSpacesᴵ = λ _ → Isometry≡ refl
  ⋆Assoc   PrSpacesᴵ = λ _ _ _ → Isometry≡ refl
  isSetHom PrSpacesᴵ {y = N} =
    isSetΣSndProp (isSet→ (N .snd .isSetM)) (flip (isPropIsIsometry _) _)

module _ {ℓ ℓ'} {M N : PremetricSpace ℓ ℓ'} where
  open Cat.isIso
  open Iso

  private
    module M = PremetricStr (M .snd)
    module N = PremetricStr (N .snd)

  CatIsoᴵ→CatIsoⁿ : CatIso (PrSpacesᴵ ℓ ℓ') M N → CatIso (PrSpacesⁿ ℓ ℓ') M N
  fst (CatIsoᴵ→CatIsoⁿ f)       = Isometry→NE (fst f)
  inv (snd (CatIsoᴵ→CatIsoⁿ f)) = Isometry→NE (inv (snd f))
  sec (snd (CatIsoᴵ→CatIsoⁿ f)) = NE≡ $ cong fst $ sec (snd f)
  ret (snd (CatIsoᴵ→CatIsoⁿ f)) = NE≡ $ cong fst $ ret (snd f)

  CatIsoⁿ→CatIsoᴸ : CatIso (PrSpacesⁿ ℓ ℓ') M N → CatIso (PrSpacesᴸ ℓ ℓ') M N
  fst (CatIsoⁿ→CatIsoᴸ f)       = NE→L (fst f)
  inv (snd (CatIsoⁿ→CatIsoᴸ f)) = NE→L (inv (snd f))
  sec (snd (CatIsoⁿ→CatIsoᴸ f)) = L≡ $ cong fst $ sec (snd f)
  ret (snd (CatIsoⁿ→CatIsoᴸ f)) = L≡ $ cong fst $ ret (snd f)

  CatIsoⁿ→CatIsoᵘᶜ : CatIso (PrSpacesⁿ ℓ ℓ') M N → CatIso (PrSpacesᵘᶜ ℓ ℓ') M N
  fst (CatIsoⁿ→CatIsoᵘᶜ f)       = NE→UC (fst f)
  inv (snd (CatIsoⁿ→CatIsoᵘᶜ f)) = NE→UC (inv (snd f))
  sec (snd (CatIsoⁿ→CatIsoᵘᶜ f)) = UC≡ $ cong fst $ sec (snd f)
  ret (snd (CatIsoⁿ→CatIsoᵘᶜ f)) = UC≡ $ cong fst $ ret (snd f)

  CatIsoᴸ→CatIsoᵘᶜ : CatIso (PrSpacesᴸ ℓ ℓ') M N → CatIso (PrSpacesᵘᶜ ℓ ℓ') M N
  fst (CatIsoᴸ→CatIsoᵘᶜ f)       = L→UC (fst f)
  inv (snd (CatIsoᴸ→CatIsoᵘᶜ f)) = L→UC (inv (snd f))
  sec (snd (CatIsoᴸ→CatIsoᵘᶜ f)) = UC≡ $ cong fst $ sec (snd f)
  ret (snd (CatIsoᴸ→CatIsoᵘᶜ f)) = UC≡ $ cong fst $ ret (snd f)

  CatIsoᵘᶜ→CatIsoᶜ : CatIso (PrSpacesᵘᶜ ℓ ℓ') M N → CatIso (PrSpacesᶜ ℓ ℓ') M N
  fst (CatIsoᵘᶜ→CatIsoᶜ f)       = UC→C (fst f)
  inv (snd (CatIsoᵘᶜ→CatIsoᶜ f)) = UC→C (inv (snd f))
  sec (snd (CatIsoᵘᶜ→CatIsoᶜ f)) = C≡ $ cong fst $ sec (snd f)
  ret (snd (CatIsoᵘᶜ→CatIsoᶜ f)) = C≡ $ cong fst $ ret (snd f)

  CatIsoᴸ→CatIsoᶜ : CatIso (PrSpacesᴸ ℓ ℓ') M N → CatIso (PrSpacesᶜ ℓ ℓ') M N
  CatIsoᴸ→CatIsoᶜ = CatIsoᵘᶜ→CatIsoᶜ ∘ CatIsoᴸ→CatIsoᵘᶜ

  CatIsoⁿ→CatIsoᶜ : CatIso (PrSpacesⁿ ℓ ℓ') M N → CatIso (PrSpacesᶜ ℓ ℓ') M N
  CatIsoⁿ→CatIsoᶜ = CatIsoᵘᶜ→CatIsoᶜ ∘ CatIsoⁿ→CatIsoᵘᶜ

  CatIsoᴵ→CatIsoᴸ : CatIso (PrSpacesᴵ ℓ ℓ') M N → CatIso (PrSpacesᴸ ℓ ℓ') M N
  CatIsoᴵ→CatIsoᴸ = CatIsoⁿ→CatIsoᴸ ∘ CatIsoᴵ→CatIsoⁿ

  CatIsoᴵ→CatIsoᵘᶜ : CatIso (PrSpacesᴵ ℓ ℓ') M N → CatIso (PrSpacesᵘᶜ ℓ ℓ') M N
  CatIsoᴵ→CatIsoᵘᶜ = CatIsoⁿ→CatIsoᵘᶜ ∘ CatIsoᴵ→CatIsoⁿ

  CatIsoᴵ→CatIsoᶜ : CatIso (PrSpacesᴵ ℓ ℓ') M N → CatIso (PrSpacesᶜ ℓ ℓ') M N
  CatIsoᴵ→CatIsoᶜ = CatIsoⁿ→CatIsoᶜ ∘ CatIsoᴵ→CatIsoⁿ

  -- Isomorphisms in PrSpacesⁿ are equivalent to Isometric equivalences

  CatIsoⁿ→Iso : CatIso (PrSpacesⁿ ℓ ℓ') M N → Iso ⟨ M ⟩ ⟨ N ⟩
  fun (CatIsoⁿ→Iso f) = fst (fst f)
  inv (CatIsoⁿ→Iso f) = fst (inv (snd f))
  sec (CatIsoⁿ→Iso f) = funExt⁻ $ cong fst $ sec (snd f)
  ret (CatIsoⁿ→Iso f) = funExt⁻ $ cong fst $ ret (snd f)

  CatIsoⁿ→Isometric≃ : CatIso (PrSpacesⁿ ℓ ℓ') M N → Isometric≃[ M , N ]
  fst (CatIsoⁿ→Isometric≃ f) = isoToEquiv (CatIsoⁿ→Iso f)
  snd (CatIsoⁿ→Isometric≃ (f , f-iso)) .IsIsometric≃.pres≈ x ε y = propBiimpl→Equiv
    (M.isProp≈ x y ε)
    (N.isProp≈ (fst f x) (fst f y) ε)
    (IsNonExpansive.pres≈ (snd f) x y ε)
    (subst2 M._≈[ ε ]_ (funExt⁻ (cong fst f.ret) x) (funExt⁻ (cong fst f.ret) y)
      ∘ IsNonExpansive.pres≈ (snd f.inv) (fst f x) (fst f y) ε)
    where module f = Cat.isIso f-iso

  Isometric≃→CatIsoⁿ : Isometric≃[ M , N ] → CatIso (PrSpacesⁿ ℓ ℓ') M N
  fst (Isometric≃→CatIsoⁿ e)       = Isometric≃→NE e
  inv (snd (Isometric≃→CatIsoⁿ e)) = Isometric≃→NE (invIsometric≃ e)
  sec (snd (Isometric≃→CatIsoⁿ e)) = NE≡ $ funExt $ secEq (fst e)
  ret (snd (Isometric≃→CatIsoⁿ e)) = NE≡ $ funExt $ retEq (fst e)

  CatIsoⁿ≅Isometric≃ : Iso (CatIso (PrSpacesⁿ ℓ ℓ') M N) Isometric≃[ M , N ]
  fun CatIsoⁿ≅Isometric≃ = CatIsoⁿ→Isometric≃
  inv CatIsoⁿ≅Isometric≃ = Isometric≃→CatIsoⁿ
  sec CatIsoⁿ≅Isometric≃ = λ _ → Isometric≃≡ (equivEq refl)
  ret CatIsoⁿ≅Isometric≃ = λ _ → CatIso≡ _ _ (NE≡ refl)

  CatIsoⁿ≃Isometric≃ : (CatIso (PrSpacesⁿ ℓ ℓ') M N) ≃ Isometric≃[ M , N ]
  CatIsoⁿ≃Isometric≃ = isoToEquiv CatIsoⁿ≅Isometric≃

  -- Isomorphisms in PrSpacesᴵ are equivalent to Isometric equivalences

  CatIsoᴵ→Iso : CatIso (PrSpacesᴵ ℓ ℓ') M N → Iso ⟨ M ⟩ ⟨ N ⟩
  CatIsoᴵ→Iso = CatIsoⁿ→Iso ∘ CatIsoᴵ→CatIsoⁿ

  CatIsoᴵ→Isometric≃ : CatIso (PrSpacesᴵ ℓ ℓ') M N → Isometric≃[ M , N ]
  CatIsoᴵ→Isometric≃ = CatIsoⁿ→Isometric≃ ∘ CatIsoᴵ→CatIsoⁿ

  Isometric≃→CatIsoᴵ : Isometric≃[ M , N ] → CatIso (PrSpacesᴵ ℓ ℓ') M N
  fst (Isometric≃→CatIsoᴵ e)       = Isometric≃→Isometry e
  inv (snd (Isometric≃→CatIsoᴵ e)) = Isometric≃→Isometry (invIsometric≃ e)
  sec (snd (Isometric≃→CatIsoᴵ e)) = Isometry≡ $ funExt $ secEq (fst e)
  ret (snd (Isometric≃→CatIsoᴵ e)) = Isometry≡ $ funExt $ retEq (fst e)

  CatIsoᴵ≅Isometric≃ : Iso (CatIso (PrSpacesᴵ ℓ ℓ') M N) Isometric≃[ M , N ]
  fun CatIsoᴵ≅Isometric≃ = CatIsoᴵ→Isometric≃
  inv CatIsoᴵ≅Isometric≃ = Isometric≃→CatIsoᴵ
  sec CatIsoᴵ≅Isometric≃ = λ _ → Isometric≃≡ (equivEq refl)
  ret CatIsoᴵ≅Isometric≃ = λ _ → CatIso≡ _ _ (Isometry≡ refl)

  CatIsoᴵ≃Isometric≃ : (CatIso (PrSpacesᴵ ℓ ℓ') M N) ≃ Isometric≃[ M , N ]
  CatIsoᴵ≃Isometric≃ = isoToEquiv CatIsoᴵ≅Isometric≃

isUnivalentPrSpacesⁿ : ∀ {ℓ ℓ'} → isUnivalent (PrSpacesⁿ ℓ ℓ')
isUnivalent.univ isUnivalentPrSpacesⁿ M N =
  precomposesToId→Equiv pathToIso _
    (funExt (CatIso≡ _ _ ∘ NE≡ ∘ λ _ → transportRefl _))
    (snd (CatIsoⁿ≃Isometric≃ ∙ₑ PremetricSIP M N))

isUnivalentPrSpacesᴵ : ∀ {ℓ ℓ'} → isUnivalent (PrSpacesᴵ ℓ ℓ')
isUnivalent.univ isUnivalentPrSpacesᴵ M N =
  precomposesToId→Equiv pathToIso _
    (funExt (CatIso≡ _ _ ∘ Isometry≡ ∘ λ _ → transportRefl _))
    (snd (CatIsoᴵ≃Isometric≃ ∙ₑ PremetricSIP M N))
