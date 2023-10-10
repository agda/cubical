{-# OPTIONS --safe #-}
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommRing

module Cubical.Algebra.CommAlgebra.Subalgebra
  {ℓ ℓ' : Level}
  (R : CommRing ℓ) (A : CommAlgebra R ℓ')
  where

open import Cubical.Algebra.Algebra.Subalgebra
  (CommRing→Ring R) (CommAlgebra→Algebra A)
  public

module _ (S : Subalgebra) where
  Subalgebra→CommAlgebra≡ = Subalgebra→Algebra≡ S

  Subalgebra→CommAlgebra : CommAlgebra R ℓ'
  Subalgebra→CommAlgebra =
      Subalgebra→Algebra S .fst
    , record
      { AlgebraStr (Subalgebra→Algebra S .snd)
      ; isCommAlgebra = iscommalgebra
          (Subalgebra→Algebra S .snd .AlgebraStr.isAlgebra)
          (λ x y → Subalgebra→CommAlgebra≡
            (CommAlgebraStr.·Comm (snd A) (fst x) (fst y)))}

  Subalgebra→CommAlgebraHom : CommAlgebraHom Subalgebra→CommAlgebra A
  Subalgebra→CommAlgebraHom = Subalgebra→AlgebraHom S

  SubalgebraHom : (B : CommAlgebra R ℓ') (f : CommAlgebraHom B A)
                → ((b : ⟨ B ⟩) → fst f b ∈ fst S)
                → CommAlgebraHom B Subalgebra→CommAlgebra
  SubalgebraHom _ f fb∈S = let open IsAlgebraHom (f .snd)
          in (λ b → (f .fst b) , fb∈S b)
           , makeIsAlgebraHom (Subalgebra→CommAlgebra≡ pres1)
                              (λ x y → Subalgebra→CommAlgebra≡ (pres+ x y))
                              (λ x y → Subalgebra→CommAlgebra≡ (pres· x y))
                              (λ x y → Subalgebra→CommAlgebra≡ (pres⋆ x y))

