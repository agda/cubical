-- Monoidal categories

module Cubical.Categories.Monoidal.Base where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Monoid


module _ {ℓ ℓ' : Level} (C : Category ℓ ℓ') where
  open Category C

  record TensorStr : Type (ℓ-max ℓ ℓ') where
    field
      ─⊗─ : Functor (C ×C C) C
      unit : ob

    open Functor

    -- Useful tensor product notation
    _⊗_ : ob → ob → ob
    x ⊗ y = ─⊗─ .F-ob (x , y)

    _⊗ₕ_ : ∀ {x y z w} → Hom[ x , y ] → Hom[ z , w ]
         → Hom[ x ⊗ z , y ⊗ w ]
    f ⊗ₕ g = ─⊗─ .F-hom (f , g)


  record StrictMonStr : Type (ℓ-max ℓ ℓ') where
    field
      tenstr : TensorStr

    open TensorStr tenstr public

    field
      -- Axioms - strict
      is-monoid : IsMonoid unit _⊗_

    open IsMonoid is-monoid renaming (·Assoc to assoc; ·IdL to idl; ·IdR to idr) public

    field
      -- Axioms for the morphisms
      assocₕ : ∀ {x y z x' y' z'}
             → (f : Hom[ x , x' ]) (g : Hom[ y , y' ]) (h : Hom[ z , z' ])
             → (λ i → Hom[ assoc x y z i , assoc x' y' z' i ])
               [ f ⊗ₕ (g ⊗ₕ h) ≡ (f ⊗ₕ g) ⊗ₕ h ]

      idlₕ : ∀ {x x'} (f : Hom[ x , x' ])
           → (λ i → Hom[ idl x i , idl x' i ])
             [ id ⊗ₕ f ≡ f ]

      idrₕ : ∀ {x x'} (f : Hom[ x , x' ])
           → (λ i → Hom[ idr x i , idr x' i ])
             [ f ⊗ₕ id ≡ f ]

  record MonoidalStr : Type (ℓ-max ℓ ℓ') where
    field
      tenstr : TensorStr

    open TensorStr tenstr public

    private
      -- Private names to make the axioms below look nice
      x⊗[y⊗z] : Functor (C ×C C ×C C) C
      x⊗[y⊗z] = ─⊗─ ∘F (𝟙⟨ C ⟩ ×F ─⊗─)

      [x⊗y]⊗z : Functor (C ×C C ×C C) C
      [x⊗y]⊗z = ─⊗─ ∘F (─⊗─ ×F 𝟙⟨ C ⟩) ∘F (×C-assoc C C C)

      x = 𝟙⟨ C ⟩
      1⊗x = ─⊗─ ∘F (rinj C C unit)
      x⊗1 = ─⊗─ ∘F (linj C C unit)

    field
      -- "Axioms" - up to natural isomorphism
      α : x⊗[y⊗z] ≅ᶜ [x⊗y]⊗z
      η : 1⊗x ≅ᶜ x
      ρ : x⊗1 ≅ᶜ x

    open NatIso

    -- More nice notations
    α⟨_,_,_⟩ : (x y z : ob) → Hom[ x ⊗ (y ⊗ z) , (x ⊗ y) ⊗ z ]
    α⟨ x , y , z ⟩ = α .trans ⟦ (x , y , z) ⟧

    η⟨_⟩ : (x : ob) → Hom[ unit ⊗ x , x ]
    η⟨ x ⟩ = η .trans ⟦ x ⟧

    ρ⟨_⟩ : (x : ob) → Hom[ x ⊗ unit , x ]
    ρ⟨ x ⟩ = ρ .trans ⟦ x ⟧

    field
      -- Coherence conditions
      pentagon : ∀ w x y z →
        id ⊗ₕ α⟨ x , y , z ⟩  ⋆  α⟨ w , x ⊗ y , z ⟩  ⋆  α⟨ w , x , y ⟩ ⊗ₕ id
            ≡   α⟨ w , x , y ⊗ z ⟩  ⋆  α⟨ w ⊗ x , y , z ⟩

      triangle : ∀ x y →
        α⟨ x , unit , y ⟩  ⋆  ρ⟨ x ⟩ ⊗ₕ id  ≡  id ⊗ₕ η⟨ y ⟩

    open isIso

    -- Inverses of α, η, ρ for convenience
    α⁻¹⟨_,_,_⟩ : (x y z : ob) → Hom[ (x ⊗ y) ⊗ z , x ⊗ (y ⊗ z) ]
    α⁻¹⟨ x , y , z ⟩ = α .nIso (x , y , z) .inv

    η⁻¹⟨_⟩ : (x : ob) → Hom[ x , unit ⊗ x ]
    η⁻¹⟨ x ⟩ = η .nIso (x) .inv

    ρ⁻¹⟨_⟩ : (x : ob) → Hom[ x , x ⊗ unit ]
    ρ⁻¹⟨ x ⟩ = ρ .nIso (x) .inv


record StrictMonCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    C : Category ℓ ℓ'
    sms : StrictMonStr C

  open Category C public
  open StrictMonStr sms public


record MonoidalCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    C : Category ℓ ℓ'
    monstr : MonoidalStr C

  open Category C public
  open MonoidalStr monstr public
