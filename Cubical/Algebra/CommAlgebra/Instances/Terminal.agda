{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Instances.Terminal where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.Algebra.Base using (IsAlgebraHom)
open import Cubical.Algebra.CommRing.Instances.Unit

private
  variable
    ℓ : Level

module _ (R : CommRing ℓ) where
  terminalCAlg : CommAlgebra R ℓ
  terminalCAlg =
    commAlgebraFromCommRing
      UnitCommRing
      (λ _ _ → tt*) (λ _ _ _ → refl) (λ _ _ _ → refl)
      (λ _ _ _ → refl) (λ _ → refl) (λ _ _ _ → refl)

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

    open CommAlgebraStr (snd A)
    module _ (1≡0 : 1a ≡ 0a) where

      isContrFrom1≡0 : isContr (fst A )
      isContrFrom1≡0 = 0a , λ a →
        0a      ≡⟨ {!!} ⟩
        a · 0a  ≡⟨ cong (λ b → a · b) (sym 1≡0) ⟩
        a · 1a  ≡⟨ {!!} ⟩
        a       ∎
--        where open isCommAlgebra

--      terminalMapIsEquiv : isEquiv (fst terminalMap)
--      terminalMapIsEquiv = {!!}

      equivFrom1≡0 : CommAlgebraEquiv A terminalCAlg
      equivFrom1≡0 = (fst terminalMap , {!terminalMapIsEquiv!}) , snd terminalMap
