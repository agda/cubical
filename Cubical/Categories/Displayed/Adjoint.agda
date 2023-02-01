{-# OPTIONS --safe #-}
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

  -- Adjoint def 1: unit-counit
  record _⊣ᴰ_ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    {F : Functor C D} {G : Functor D C}
    (A : F UnitCounit.⊣ G)
    {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Gᴰ : Functorᴰ G Dᴰ Cᴰ)
    : Type {!!} where

    private
      module A = UnitCounit._⊣_ A

    field
      -- unit
      η : NatTransᴰ A.η 𝟙ᴰ⟨ Cᴰ ⟩ (funcCompᴰ Gᴰ Fᴰ)
      -- counit
      ε : NatTransᴰ A.ε (funcCompᴰ Fᴰ Gᴰ) 𝟙ᴰ⟨ Dᴰ ⟩
      -- triangle identities
      Δ₁ : PathP (λ i → NatTransᴰ (A.Δ₁ i) (F-lUnitᴰ {Fᴰ = Fᴰ} i) (F-rUnitᴰ {Fᴰ = Fᴰ} i))
        {!!} -- (seqTransP F-assoc (F ∘ʳ η) (ε ∘ˡ F))
        {!!} -- (1[ F ])
      Δ₂ : PathP (λ i → NatTransᴰ (A.Δ₂ i) (F-rUnitᴰ {Fᴰ = Gᴰ} i) (F-lUnitᴰ {Fᴰ = Gᴰ} i))
        {!!} -- (seqTransP (sym F-assoc) (η ∘ˡ G) (G ∘ʳ ε))
        {!!} -- (1[ G ])
