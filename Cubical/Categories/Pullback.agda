{-
  This file contains cospans, cones, pullbacks and maps of cones in precategories.
-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Pullback where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

open Precategory

private
  variable
    ℓ ℓ' : Level


record Cospan (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor cospan
  field
    l r vertex : Precategory.ob C
    s₁ : C [ l , vertex ]
    s₂ : C [ r , vertex ]

record Cone {C : Precategory ℓ ℓ'} (cspn : Cospan C) (c : ob C) : Type (ℓ-max ℓ ℓ') where
  constructor cone
  field
    p₁ : C [ c , (Cospan.l cspn)]
    p₂ : C [ c , (Cospan.r cspn)]
    sq : p₁ ⋆⟨ C ⟩ (Cospan.s₁ cspn) ≡ p₂ ⋆⟨ C ⟩ (Cospan.s₂ cspn)

record Pullback {C : Precategory ℓ ℓ'} (cspn : Cospan C) : Type (ℓ-max ℓ ℓ') where
  constructor pullback
  field
    pbOb : ob C
    pbCn : Cone cspn pbOb
    universal : ∀ {c' : ob C} (cn' : Cone cspn c')
              → ∃![ f ∈ C [ c' , pbOb ] ] Σ[ q ∈ Cone.p₁ cn' ≡ f ⋆⟨ C ⟩ (Cone.p₁ pbCn) ] (Cone.p₂ cn' ≡ f ⋆⟨ C ⟩ (Cone.p₂ pbCn))

-- extend a cone on c by a morphism c'→c using precomposition
coneMap : {C : Precategory ℓ ℓ'} {cspn : Cospan C} {c c' : ob C} (cn : Cone cspn c) (f : C [ c' , c ]) → Cone cspn c'
coneMap {C = C} {cospan _ _ _ s₁ s₂} (cone p₁ p₂ sq) f =
  cone (f ⋆⟨ C ⟩ p₁)  (f ⋆⟨ C ⟩ p₂) ((C .⋆Assoc f p₁ s₁) ∙∙ lPrecatWhisker {C = C} f (p₁ ⋆⟨ C ⟩ s₁) (p₂ ⋆⟨ C ⟩ s₂) sq ∙∙ sym (C .⋆Assoc f p₂ s₂))
