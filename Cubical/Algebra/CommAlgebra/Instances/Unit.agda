{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Instances.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommRing.Instances.Unit
open import Cubical.Algebra.Algebra.Base using (IsAlgebraHom)
open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' : Level

module _ (R : CommRing ℓ) where
  UnitCommAlgebra : CommAlgebra R ℓ'
  UnitCommAlgebra =
    commAlgebraFromCommRing
      UnitCommRing
      (λ _ _ → tt*) (λ _ _ _ → refl) (λ _ _ _ → refl)
      (λ _ _ _ → refl) (λ _ → refl) (λ _ _ _ → refl)

  module _ (A : CommAlgebra R ℓ) where
    terminalMap : CommAlgebraHom A (UnitCommAlgebra {ℓ' = ℓ})
    terminalMap = (λ _ → tt*) , isHom
      where open IsAlgebraHom
            isHom : IsCommAlgebraHom (snd A) _ (snd UnitCommAlgebra)
            pres0 isHom = isPropUnit* _ _
            pres1 isHom = isPropUnit* _ _
            pres+ isHom = λ _ _ → isPropUnit* _ _
            pres· isHom = λ _ _ → isPropUnit* _ _
            pres- isHom = λ _ → isPropUnit* _ _
            pres⋆ isHom = λ _ _ → isPropUnit* _ _

    terminalityContr : isContr (CommAlgebraHom A UnitCommAlgebra)
    terminalityContr = terminalMap , path
      where path : (ϕ : CommAlgebraHom A UnitCommAlgebra) → terminalMap ≡ ϕ
            path ϕ = Σ≡Prop (isPropIsCommAlgebraHom {M = A} {N = UnitCommAlgebra})
                            λ i _ → isPropUnit* _ _ i

    open CommAlgebraStr (snd A)
    module _ (1≡0 : 1a ≡ 0a) where

      1≡0→isContr : isContr ⟨ A ⟩
      1≡0→isContr = 0a , λ a →
        0a      ≡⟨ solve! S ⟩
        a · 0a  ≡⟨ cong (λ b → a · b) (sym 1≡0) ⟩
        a · 1a  ≡⟨ solve! S ⟩
        a       ∎
          where S = CommAlgebra→CommRing A

      equivFrom1≡0 : CommAlgebraEquiv A UnitCommAlgebra
      equivFrom1≡0 = isContr→Equiv 1≡0→isContr isContrUnit*  ,
                     snd terminalMap
