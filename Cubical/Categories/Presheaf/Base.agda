module Cubical.Categories.Presheaf.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets

private
  variable
    ℓ ℓ' ℓS : Level

Presheaf : Category ℓ ℓ' → (ℓS : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
Presheaf C ℓS = Functor (C ^op) (SET ℓS)

PresheafCategory : Category ℓ ℓ' → (ℓS : Level)
       → Category (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
                  (ℓ-max (ℓ-max ℓ ℓ') ℓS)
PresheafCategory C ℓS = FUNCTOR (C ^op) (SET ℓS)

isUnivalentPresheafCategory : {C : Category ℓ ℓ'}
                            → isUnivalent (PresheafCategory C ℓS)
isUnivalentPresheafCategory = isUnivalentFUNCTOR _ _ isUnivalentSET

open Category
open Functor

action : {C : Category ℓ ℓ'} → (P : Presheaf C ℓS)
       → {a b : C .ob} → C [ a , b ] → fst (P ⟅ b ⟆) → fst (P ⟅ a ⟆)
action P = P .F-hom

-- Convenient notation for naturality
syntax action P f ϕ = ϕ ∘ᴾ⟨ P ⟩ f

∘ᴾId : ∀ (C : Category ℓ ℓ') → (P : Presheaf C ℓS) → {a : C .ob}
     → (ϕ : fst (P ⟅ a ⟆))
     → ϕ ∘ᴾ⟨ P ⟩ C .id ≡ ϕ
∘ᴾId C P ϕ i = P .F-id i ϕ

∘ᴾAssoc : ∀ (C : Category ℓ ℓ') → (P : Presheaf C ℓS) → {a b c : C .ob}
        → (ϕ : fst (P ⟅ c ⟆))
        → (f : C [ b , c ])
        → (g : C [ a , b ])
        → ϕ ∘ᴾ⟨ P ⟩ (f ∘⟨ C ⟩ g) ≡ (ϕ ∘ᴾ⟨ P ⟩ f) ∘ᴾ⟨ P ⟩ g
∘ᴾAssoc C P ϕ f g i = P .F-seq f g i ϕ
