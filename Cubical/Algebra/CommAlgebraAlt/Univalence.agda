module Cubical.Algebra.CommAlgebraAlt.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Univalence
open import Cubical.Algebra.CommAlgebraAlt.Base

private
  variable
    ℓ ℓ' ℓ'' : Level


module _ (R : CommRing ℓ) where
  private
    to : (A B : CommAlgebra R ℓ') → CommAlgebraEquiv A B → A ≡ B
    to A B e = CommAlgebra≡
             r≡
             ((pathToEquiv $ cong fst r≡) .fst ∘ A .snd .fst
                ≡⟨ cong (_∘ A .snd .fst) (cong fst $ pathToEquiv-ua (e .fst .fst) )  ⟩
              CommAlgebraEquiv→CommRingHom e .fst ∘ A .snd .fst
                ≡⟨ cong fst (e .snd) ⟩
              B .snd .fst ∎)
           where r≡ : (A .fst) ≡ (B .fst)
                 r≡ = CommRingPath (A .fst) (B .fst) .fst (e .fst)

    test : (A : CommAlgebra R ℓ') → to A A (idCAlgEquiv A) ≡ refl
    test A = {!to A A (idCAlgEquiv A)!} ≡⟨ {!!} ⟩ ? ≡⟨ {!!} ⟩ refl ∎

    toIsEquiv : (A : CommAlgebra R ℓ') {B' : CommAlgebra R ℓ'} → (p : A ≡ B') → isContr (fiber (to A B') p)
    toIsEquiv A =
      J (λ B' A≡B' → isContr (fiber (to A B') A≡B'))
        ((idCAlgEquiv A , {!test A!}) ,
          λ {(e , toe≡refl) → {!!}})

  CommAlgebraPath : (A B : CommAlgebra R ℓ') → (CommAlgebraEquiv A B) ≃ (A ≡ B)
  CommAlgebraPath {ℓ' = ℓ'} A B = to A B , {!!}

{-
CommAlgebraPath : (R : CommRing ℓ) → (A B : CommAlgebra R ℓ') → (CommAlgebraEquiv A B) ≃ (A ≡ B)
CommAlgebraPath R = ∫ (𝒮ᴰ-CommAlgebra R) .UARel.ua

uaCommAlgebra : {R : CommRing ℓ} {A B : CommAlgebra R ℓ'} → CommAlgebraEquiv A B → A ≡ B
uaCommAlgebra {R = R} {A = A} {B = B} = equivFun (CommAlgebraPath R A B)

isGroupoidCommAlgebra : {R : CommRing ℓ} → isGroupoid (CommAlgebra R ℓ')
isGroupoidCommAlgebra A B = isOfHLevelRespectEquiv 2 (CommAlgebraPath _ _ _) (isSetAlgebraEquiv _ _)
-}
