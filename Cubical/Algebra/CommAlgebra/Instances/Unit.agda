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
open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' : Level

module _ (R : CommRing ℓ) where
  UnitCommAlgebra : CommAlgebra R ℓ'
  UnitCommAlgebra = UnitCommRing , mapToUnitCommRing R

  module _ (A : CommAlgebra R ℓ') where
    terminalMap : CommAlgebraHom A (UnitCommAlgebra {ℓ' = ℓ})
    terminalMap .fst = mapToUnitCommRing (A .fst)
    terminalMap .snd = isPropMapToUnitCommRing _ _ _

{-
  module _ (A : CommAlgebra R ℓ) where

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
-}
