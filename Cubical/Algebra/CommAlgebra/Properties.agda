{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure using (⟨_⟩; withOpaqueStr)

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module _ {R : CommRing ℓ} where

  opaque
    compIdCommAlgebraHom : {A B : CommAlgebra R ℓ'} (f : CommAlgebraHom A B)
                      →  (f ∘ca idCAlgHom A) ≡ f
    compIdCommAlgebraHom f = CommAlgebraHom≡ refl

    idCompCommAlgebraHom : {A B : CommAlgebra R ℓ'} (f : CommAlgebraHom A B)
                      → (idCommAlgebraHom B) ∘ca f ≡ f
    idCompCommAlgebraHom f = CommAlgebraHom≡ refl

    compAssocCommAlgebraHom : {A B C D : CommAlgebra R ℓ'}
                           (f : CommAlgebraHom A B) (g : CommAlgebraHom B C) (h : CommAlgebraHom C D)
                         →  h ∘ca (g ∘ca f) ≡ (h ∘ca g) ∘ca f
    compAssocCommAlgebraHom f g h = CommAlgebraHom≡ refl

  invCommAlgebraEquiv : {A B : CommAlgebra R ℓ'}
                        → CommAlgebraEquiv A B
                        → CommAlgebraEquiv B A
  invCommAlgebraEquiv {A = A} {B = B} f = f⁻¹ , commutes
    where f⁻¹ = invCommRingEquiv (CommAlgebra→CommRing A) (CommAlgebra→CommRing B) (f .fst)
          f⁻¹∘f≡Id : f⁻¹ .fst .fst ∘ f .fst .fst .fst ≡ idfun _
          f⁻¹∘f≡Id = funExt (secIsEq (equivIsEquiv (f⁻¹ .fst)))
          abstract
            commutes : (CommRingEquiv→CommRingHom f⁻¹) ∘cr B .snd ≡ A .snd
            commutes =
              CommRingHom≡ $
                f⁻¹ .fst .fst ∘ B .snd .fst                     ≡⟨ sym ( cong ((f⁻¹ .fst .fst) ∘_) (cong fst (f .snd))) ⟩
                f⁻¹ .fst .fst ∘  f .fst .fst .fst ∘ A .snd .fst ≡⟨ cong (_∘ A .snd .fst) f⁻¹∘f≡Id  ⟩
                A .snd .fst ∎
