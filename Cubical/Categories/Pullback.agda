{-
  This file contains cospans, cones, pullbacks and maps of cones in precategories.
-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Pullback where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' : Level

record Cospan (𝒞 : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor cospan
  field
    S₁ S₂ vertex : Precategory.ob 𝒞
    s₁ : hom 𝒞 S₁ vertex
    s₂ : hom 𝒞 S₂ vertex

record Cone {𝒞 : Precategory ℓ ℓ'} (cspn : Cospan 𝒞) (c : ob 𝒞) : Type (ℓ-max ℓ ℓ') where
  constructor cone
  field
    p₁ : hom 𝒞 c (Cospan.S₁ cspn)
    p₂ : hom 𝒞 c (Cospan.S₂ cspn)
    sq : seq 𝒞 p₁ (Cospan.s₁ cspn) ≡ seq 𝒞 p₂ (Cospan.s₂ cspn)

record Pullback {𝒞 : Precategory ℓ ℓ'} (cspn : Cospan 𝒞) : Type (ℓ-max ℓ ℓ') where
  constructor pullback
  field
    c : ob 𝒞
    cn : Cone cspn c
    universal : {c' : ob 𝒞} (cn' : Cone cspn c') → ∃![ f ∈ 𝒞 .hom c' c ] Σ[ q ∈ Cone.p₁ cn' ≡ 𝒞 .seq f (Cone.p₁ cn) ] (Cone.p₂ cn' ≡ 𝒞 .seq f (Cone.p₂ cn))

-- whisker the parallel morphisms g and g' with f
lPrecatWhisker : {𝒞 : Precategory ℓ ℓ'} {x y z : 𝒞 .ob} (f : 𝒞 .hom x y) (g g' : 𝒞 .hom y z) (p : g ≡ g') → 𝒞 .seq f g ≡ 𝒞 .seq f g'
lPrecatWhisker {𝒞 = 𝒞} f _ _ p = cong (𝒞 .seq f) p

-- extend a cone on c by a morphism c'→c using precomposition
coneMap : {𝒞 : Precategory ℓ ℓ'} {cspn : Cospan 𝒞} {c c' : ob 𝒞} (cn : Cone cspn c) (f : hom 𝒞 c' c) → Cone cspn c'
coneMap {𝒞 = 𝒞} {cospan _ _ _ s₁ s₂} (cone p₁ p₂ sq) f =
  cone (𝒞 .seq f p₁)  (𝒞 .seq f p₂) ((𝒞 .seq-α f p₁ s₁) ∙∙ lPrecatWhisker {𝒞 = 𝒞} f (𝒞 .seq p₁ s₁) (𝒞 .seq p₂ s₂) sq ∙∙ sym (𝒞 .seq-α f p₂ s₂))
