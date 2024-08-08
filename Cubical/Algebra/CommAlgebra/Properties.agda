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
