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

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Algebra.Base
open import Cubical.Algebra.Algebra.Properties

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    R : Ring ℓ
    A B C D : Algebra R ℓ

open IsAlgebraHom

𝒮ᴰ-Algebra : (R : Ring ℓ) → DUARel (𝒮-Univ ℓ') (AlgebraStr R) (ℓ-max ℓ ℓ')
𝒮ᴰ-Algebra R =
  𝒮ᴰ-Record (𝒮-Univ _) (IsAlgebraEquiv {R = R})
    (fields:
      data[ 0a ∣ nul ∣ pres0 ]
      data[ 1a ∣ nul ∣ pres1 ]
      data[ _+_ ∣ bin ∣ pres+ ]
      data[ _·_ ∣ bin ∣ pres· ]
      data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
      data[ _⋆_ ∣ autoDUARel _ _ ∣ pres⋆ ]
      prop[ isAlgebra ∣ (λ A ΣA →
                          isPropIsAlgebra
                            R
                            (snd (fst (fst (fst (fst (fst ΣA))))))
                            (snd (fst (fst (fst (fst ΣA)))))
                            (snd (fst (fst (fst ΣA))))
                            (snd (fst (fst ΣA)))
                            (snd (fst ΣA))
                            (snd ΣA))  ])
  where
  open AlgebraStr

  -- faster with some sharing
  nul = autoDUARel (𝒮-Univ _) (λ A → A)
  bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)

AlgebraPath : (A B : Algebra R ℓ') → (AlgebraEquiv A B) ≃ (A ≡ B)
AlgebraPath {R = R} = ∫ (𝒮ᴰ-Algebra R) .UARel.ua

uaAlgebra : AlgebraEquiv A B → A ≡ B
uaAlgebra {A = A} {B = B} = equivFun (AlgebraPath A B)

isGroupoidAlgebra : isGroupoid (Algebra R ℓ')
isGroupoidAlgebra _ _ = isOfHLevelRespectEquiv 2 (AlgebraPath _ _) (isSetAlgebraEquiv _ _)

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
