
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Equivalences.PeifferGraphS2G where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function

open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.Structures.Subtype
open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction
open import Cubical.Structures.Group.Semidirect

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Meta.Isomorphism
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group
open import Cubical.DStructures.Structures.Action
open import Cubical.DStructures.Structures.XModule
open import Cubical.DStructures.Structures.PeifferGraph
open import Cubical.DStructures.Structures.Strict2Group
open import Cubical.DStructures.Equivalences.GroupSplitEpiAction
open import Cubical.DStructures.Equivalences.PreXModReflGraph


private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' ℓ≅B' : Level

open Kernel
open GroupHom -- such .fun!
open GroupLemmas
open MorphismLemmas
open ActionLemmas

module _ (ℓ ℓ' : Level) where
  ℓℓ' = ℓ-max ℓ ℓ'

  𝒮-Iso-PG-S2G : 𝒮ᴰ-♭iso (idfun (ReflGraph ℓ ℓℓ')) (𝒮ᴰ-ReflGraph\Peiffer ℓ ℓℓ') (𝒮ᴰ-Strict2Group ℓ ℓℓ')

  RelIso.fun (𝒮-Iso-PG-S2G 𝒢) isPeifferGraph = q
    where
      open ReflGraphNotation ℓ ℓℓ' 𝒢
      open VertComp
      _⊙_ = λ (g f : ⟨ G₁ ⟩) → (g -₁ (𝒾s g)) +₁ f

      q : VertComp ℓ ℓℓ' 𝒢
      vcomp q g f _ = g ⊙ f
      σ-∘ q g f c = r
        where
          isg = 𝒾s g
          abstract
            r = s ((g -₁ isg) +₁ f)
                  ≡⟨ (σ .isHom (g -₁ isg) f) ⟩
                s (g -₁ isg) +₀ s f
                  ≡⟨ cong (_+₀ s f) (σ-g--isg g) ⟩
                0₀ +₀ s f
                  ≡⟨ lId₀ (s f) ⟩
                s f ∎
      τ-∘ q g f c = r
        where
          isg = 𝒾s g
          -isg = -₁ (𝒾s g)
          abstract
            r = t ((g -₁ isg) +₁ f)
                  ≡⟨ τ .isHom (g -₁ isg) f ⟩
                t (g -₁ isg) +₀ t f
                  ≡⟨ cong (_+₀ t f)
                          (τ .isHom g (-₁ isg))  ⟩
                (t g +₀ t -isg) +₀ t f
                  ≡⟨ cong ((t g +₀ t -isg) +₀_)
                          (sym c) ⟩
                (t g +₀ t -isg) +₀ s g
                  ≡⟨ cong (λ z → (t g +₀ z) +₀ s g)
                          (mapInv τ isg) ⟩
                (t g -₀ (t isg)) +₀ s g
                  ≡⟨ cong (λ z → (t g -₀ z) +₀ s g)
                          (τι-≡-fun (s g)) ⟩
                (t g -₀ (s g)) +₀ s g
                  ≡⟨ (sym (assoc₀ (t g) (-₀ s g) (s g))) ∙ (cong (t g +₀_) (lCancel₀ (s g))) ⟩
                t g +₀ 0₀
                  ≡⟨ rId₀ (t g) ⟩
                t g ∎
      isHom-∘ q g f _ g' f' _ _ = r
        where
          isg = 𝒾s g
          isg' = 𝒾s g'
          abstract
            r = (g +₁ g') ⊙ (f +₁ f')
                  ≡⟨ assoc₁ ((g +₁ g') -₁ 𝒾s (g +₁ g')) f f' ⟩
                (((g +₁ g') -₁ 𝒾s (g +₁ g')) +₁ f) +₁ f'
                  ≡⟨ cong (λ z → (z +₁ f) +₁ f')
                          (sym (assoc₁ g g' (-₁ (𝒾s (g +₁ g'))))) ⟩
                ((g +₁ (g' -₁ (𝒾s (g +₁ g')))) +₁ f) +₁ f'
                  ≡⟨ cong (_+₁ f')
                          (sym (assoc₁ g (g' -₁ (𝒾s (g +₁ g'))) f)) ⟩
                (g +₁ ((g' -₁ (𝒾s (g +₁ g'))) +₁ f)) +₁ f'
                  ≡⟨ cong (λ z → (g +₁ z) +₁ f')
                          {!!} ⟩
                (g +₁ {!!}) +₁ f'
                  ≡⟨ {!assoc...!} ⟩
                ((g -₁ isg) +₁ f) +₁ ((g' -₁ isg') +₁ f')
                  ≡⟨ refl ⟩
                (g ⊙ f) +₁ (g' ⊙ f') ∎
      -- behold! use of symmetry is lurking around the corner
      -- (in stark contrast to composability proofs)
      assoc-∘ q h g f _ _ _ _ = sym r
        where
          isg = 𝒾s g
          ish = 𝒾s h
          -ish = -₁ 𝒾s h
          abstract
            r = (h ⊙ g) ⊙ f
                  -- ≡⟨ cong (λ z → (((h -₁ ish) +₁ g) -₁ 𝒾s ((h -₁ ish) +₁ g)) +₁ f) {!!} ⟩
                  ≡⟨ cong (λ z → (((h -₁ ish) +₁ g) -₁ z) +₁ f)
                          (ι∘σ .isHom (h -₁ ish) g) ⟩
                (((h -₁ ish) +₁ g) -₁ (𝒾s (h -₁ ish) +₁ 𝒾s g)) +₁ f
                  ≡⟨ cong (λ z → (((h -₁ ish) +₁ g) -₁ (z +₁ 𝒾s g)) +₁ f)
                          (ι∘σ .isHom h (-₁ ish)) ⟩
                (((h -₁ ish) +₁ g) -₁ ((𝒾s h +₁ (𝒾s -ish)) +₁ 𝒾s g)) +₁ f
                  ≡⟨ cong (λ z → (((h -₁ ish) +₁ g) -₁ ((𝒾s h +₁ z) +₁ 𝒾s g)) +₁ f)
                          (ισ-ι (s h)) ⟩
                (((h -₁ ish) +₁ g) -₁ ((ish -₁ ish) +₁ isg)) +₁ f
                  ≡⟨ cong (λ z → (((h -₁ ish) +₁ g) -₁ z) +₁ f)
                          (rCancel-lId G₁ ish isg) ⟩
                (((h -₁ ish) +₁ g) -₁ isg) +₁ f
                  ≡⟨ (cong (_+₁ f) (sym (assoc₁ (h -₁ ish) g (-₁ isg)))) ∙ (sym (assoc₁ (h -₁ ish) (g -₁ isg) f)) ⟩
                h ⊙ (g ⊙ f) ∎
      lid-∘ q f _ = r
        where
          itf = 𝒾t f
          abstract
            r = itf ⊙ f
                  ≡⟨ cong (λ z → (itf -₁ (𝒾 z)) +₁ f) (σι-≡-fun (t f)) ⟩
                (itf -₁ itf) +₁ f
                  ≡⟨ rCancel-lId G₁ itf f ⟩
                f ∎
      rid-∘ q g _ = r
        where
          isg = 𝒾s g
          -isg = -₁ (𝒾s g)
          abstract
            r = g ⊙ isg
                  ≡⟨ sym (assoc₁ g -isg isg) ⟩
                g +₁ (-isg +₁ isg)
                  ≡⟨ lCancel-rId G₁ g isg ⟩
                g ∎

  RelIso.inv (𝒮-Iso-PG-S2G 𝒢) VComp = q
    where
      open ReflGraphNotation ℓ ℓℓ' 𝒢

      abstract
        q : isPeifferGraph ι σ τ
        q f g = ((isg +₁ (f -₁ itf)) +₁ (-isg +₁ g)) +₁ itf
                  ≡⟨ {!!} ⟩
                g +₁ f ∎
          where
            isg = 𝒾s g
            -isg = -₁ (𝒾s g)
            itf = 𝒾t f



  RelIso.leftInv (𝒮-Iso-PG-S2G _) _ = tt
  RelIso.rightInv (𝒮-Iso-PG-S2G _) _ = tt
