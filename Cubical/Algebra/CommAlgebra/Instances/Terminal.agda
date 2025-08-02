{-
  Define terminal R-algebra as a commutative algebra and prove the universal property.
  The universe level of the terminal R-algebra is fixed to be the universe level of R.
-}
module Cubical.Algebra.CommAlgebra.Instances.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommRing.Instances.Unit
open import Cubical.Algebra.CommAlgebra.Notation

open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (R : CommRing ℓ) where
  terminalCAlg : CommAlgebra R ℓ
  terminalCAlg = UnitCommRing , mapToUnitCommRing R

  module _ (A : CommAlgebra R ℓ'') where
    terminalMap : CommAlgebraHom A terminalCAlg
    terminalMap = CommRingHom→CommAlgebraHom (mapToUnitCommRing (A .fst)) $ isPropMapToUnitCommRing _ _ _

  module _ (A : CommAlgebra R ℓ'') where
    terminalityContr : isContr (CommAlgebraHom A terminalCAlg)
    terminalityContr = (terminalMap A) , λ f → CommAlgebraHom≡ (funExt (λ _ → refl))

    isContr→EquivTerminal : isContr ⟨ A ⟩ₐ → CommAlgebraEquiv A terminalCAlg
    isContr→EquivTerminal isContrA =
      (isContr→≃Unit* isContrA) ,
      record { isCommRingHom = mapToUnitCommRing (A .fst) .snd ;
               commutes = CommRingHom≡ (funExt (λ _ → refl)) }

    open InstancesForCAlg A
    equivFrom1≡0 : 1r ≡ (0r :> ⟨ A ⟩ₐ)
                   → CommAlgebraEquiv A terminalCAlg
    equivFrom1≡0 1≡0 = isContr→EquivTerminal (0r , λ x →
                                                   0r ≡⟨ solve! A' ⟩
                                                   0r · x ≡⟨ cong (λ u → u · x) (sym 1≡0) ⟩
                                                   1r · x ≡⟨ solve! A' ⟩
                                                   x  ∎)
      where A' = CommAlgebra→CommRing A
