{-# OPTIONS --safe #-}
module Cubical.Algebra.Algebra.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.SIP

open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Algebra.Base
open import Cubical.Algebra.Algebra.Properties

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    R : Ring ℓ
    A B C D : Algebra R ℓ


-- the Algebra version of uaCompEquiv
module AlgebraUAFunctoriality where
 open AlgebraStr
 open AlgebraEquivs

 caracAlgebra≡ : (p q : A ≡ B) → cong ⟨_⟩ p ≡ cong ⟨_⟩ q → p ≡ q
 caracAlgebra≡ _ _ α =
   isEmbedding→Inj (iso→isEmbedding (invIso ΣPathIsoPathΣ)) _ _ $
   Σ≡Prop (λ _ → isOfHLevelPathP' 1 (isSetAlgebraStr _) _ _) α

 uaCompAlgebraEquiv : (f : AlgebraEquiv A B) (g : AlgebraEquiv B C)
                  → uaAlgebra (compAlgebraEquiv f g) ≡ uaAlgebra f ∙ uaAlgebra g
 uaCompAlgebraEquiv f g = caracAlgebra≡ _ _ (
   cong ⟨_⟩ (uaAlgebra (compAlgebraEquiv f g))
     ≡⟨ uaCompEquiv _ _ ⟩
   cong ⟨_⟩ (uaAlgebra f) ∙ cong ⟨_⟩ (uaAlgebra g)
     ≡⟨ sym (cong-∙ ⟨_⟩ (uaAlgebra f) (uaAlgebra g)) ⟩
   cong ⟨_⟩ (uaAlgebra f ∙ uaAlgebra g) ∎)
