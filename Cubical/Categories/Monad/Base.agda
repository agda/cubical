{-# OPTIONS --safe #-}
module Cubical.Categories.Monad.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} (M : Functor C C) where
  open Category C

  IsPointed : Type (ℓ-max ℓ ℓ')
  IsPointed = NatTrans (funcId C) M

  record IsMonad : Type (ℓ-max ℓ ℓ') where
    field
      η : IsPointed
      μ : NatTrans (funcComp M M) M
      idl-μ : PathP (λ i → NatTrans (F-rUnit {F = M} i) M) (compTrans μ (η ∘ˡ M)) (idTrans M)
      idr-μ : PathP (λ i → NatTrans (F-lUnit {F = M} i) M) (compTrans μ (M ∘ʳ η)) (idTrans M)
      assoc-μ : PathP (λ i → NatTrans (F-assoc {F = M} {G = M} {H = M} i) M) (compTrans μ (M ∘ʳ μ)) (compTrans μ (μ ∘ˡ M))
