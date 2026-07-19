{-
  Definition of an adjoint pair displayed over another adjoint pair
-}
module Cubical.Categories.Displayed.Adjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module UnitCounitᴰ where

  -- Adjoint definition 1: unit-counit
  record _⊣[_]_ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    {F : Functor C D} {G : Functor D C}

    {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (A : F UnitCounit.⊣ G) (Gᴰ : Functorᴰ G Dᴰ Cᴰ)
    : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ')) (ℓ-max (ℓ-max ℓD ℓD') (ℓ-max ℓDᴰ ℓDᴰ'))) where

    open Category
    open NatTransᴰ
    private
      module A = UnitCounit._⊣_ A
      module Cᴰ = Categoryᴰ Cᴰ
      module Dᴰ = Categoryᴰ Dᴰ
      module Fᴰ = Functorᴰ Fᴰ
      module Gᴰ = Functorᴰ Gᴰ

    field
      -- unit
      ηᴰ : NatTransᴰ A.η 𝟙ᴰ⟨ Cᴰ ⟩ (funcCompᴰ Gᴰ Fᴰ)
      -- counit
      εᴰ : NatTransᴰ A.ε (funcCompᴰ Fᴰ Gᴰ) 𝟙ᴰ⟨ Dᴰ ⟩
      -- triangle identities
      Δ₁ᴰ : {x : C .ob} (xᴰ : Cᴰ.ob[ x ])
        → Fᴰ.F-homᴰ (ηᴰ .N-obᴰ xᴰ) Dᴰ.⋆ᴰ εᴰ .N-obᴰ (Fᴰ.F-obᴰ xᴰ)
            Dᴰ.≡[ A.Δ₁ x ]
          Dᴰ.idᴰ
      Δ₂ᴰ : {y : D .ob} (yᴰ : Dᴰ.ob[ y ])
        → ηᴰ .N-obᴰ (Gᴰ.F-obᴰ yᴰ) Cᴰ.⋆ᴰ Gᴰ.F-homᴰ (εᴰ .N-obᴰ yᴰ)
            Cᴰ.≡[ A.Δ₂ y ]
          Cᴰ.idᴰ
