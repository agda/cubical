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

record Cospan (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor cospan
  field
    S₁ S₂ vertex : Precategory.ob C
    s₁ : C [ S₁ , vertex ]
    s₂ : C [ S₂ , vertex ]

record Cone {C : Precategory ℓ ℓ'} (cspn : Cospan C) (c : ob C) : Type (ℓ-max ℓ ℓ') where
  constructor cone
  field
    p₁ : C [ c , (Cospan.S₁ cspn)]
    p₂ : C [ c , (Cospan.S₂ cspn)]
    sq : seq C p₁ (Cospan.s₁ cspn) ≡ seq C p₂ (Cospan.s₂ cspn)

record Pullback {C : Precategory ℓ ℓ'} (cspn : Cospan C) : Type (ℓ-max ℓ ℓ') where
  constructor pullback
  field
    c : ob C
    cn : Cone cspn c
    universal : {c' : ob C} (cn' : Cone cspn c') → ∃![ f ∈ C [ c' , c ] ] Σ[ q ∈ Cone.p₁ cn' ≡ f ◾⟨ C ⟩ (Cone.p₁ cn) ] (Cone.p₂ cn' ≡ f ◾⟨ C ⟩ (Cone.p₂ cn))

-- whisker the parallel morphisms g and g' with f
lPrecatWhisker : {C : Precategory ℓ ℓ'} {x y z : C .ob} (f : C [ x , y ]) (g g' : C [ y , z ]) (p : g ≡ g') → f ◾⟨ C ⟩ g ≡ f ◾⟨ C ⟩ g'
lPrecatWhisker {C = C} f _ _ p = cong (_◾_ C f) p

-- extend a cone on c by a morphism c'→c using precomposition
coneMap : {C : Precategory ℓ ℓ'} {cspn : Cospan C} {c c' : ob C} (cn : Cone cspn c) (f : C [ c' , c ]) → Cone cspn c'
coneMap {C = C} {cospan _ _ _ s₁ s₂} (cone p₁ p₂ sq) f =
  cone (f ◾⟨ C ⟩ p₁)  (f ◾⟨ C ⟩ p₂) ((C .seq-α f p₁ s₁) ∙∙ lPrecatWhisker {C = C} f (p₁ ◾⟨ C ⟩ s₁) (p₂ ◾⟨ C ⟩ s₂) sq ∙∙ sym (C .seq-α f p₂ s₂))
