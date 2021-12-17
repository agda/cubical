{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Instances.Terminal where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.Algebra.Base using (IsAlgebraHom)

private
  variable
    ℓ : Level

module _ (R : CommRing ℓ) where
  terminalCAlg : CommAlgebra R ℓ
  terminalCAlg = Unit* , commAlgStr
    where open CommAlgebraStr

          commAlgStr : CommAlgebraStr R Unit*
          0a commAlgStr = tt*
          1a commAlgStr = tt*
          _+_ commAlgStr = λ _ _ → tt*
          _·_ commAlgStr = λ _ _ → tt*
          - commAlgStr = λ _ → tt*
          _⋆_ commAlgStr = λ _ _ → tt*
          isCommAlgebra commAlgStr = makeIsCommAlgebra isSetUnit*
                                       (λ _ _ _ → refl) (λ _ → refl)
                                       (λ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl)
                                       (λ _ → refl) (λ _ _ _ → refl) (λ _ _ → refl)
                                       (λ _ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl)
                                       (λ _ → refl) λ _ _ _ → refl

  module _ (A : CommAlgebra R ℓ) where
    terminalMap : CommAlgebraHom A terminalCAlg
    terminalMap = (λ _ → tt*) , isHom
      where open IsAlgebraHom
            isHom : IsCommAlgebraHom (snd A) _ (snd terminalCAlg)
            pres0 isHom = isPropUnit* _ _
            pres1 isHom = isPropUnit* _ _
            pres+ isHom = λ _ _ → isPropUnit* _ _
            pres· isHom = λ _ _ → isPropUnit* _ _
            pres- isHom = λ _ → isPropUnit* _ _
            pres⋆ isHom = λ _ _ → isPropUnit* _ _

    terminalityContr : isContr (CommAlgebraHom A terminalCAlg)
    terminalityContr = terminalMap , path
      where path : (ϕ : CommAlgebraHom A terminalCAlg) → terminalMap ≡ ϕ
            path ϕ = Σ≡Prop (isPropIsCommAlgebraHom {M = A} {N = terminalCAlg})
                            λ i _ → isPropUnit* _ _ i
