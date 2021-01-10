{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Cubical.Algebra.CommAlgebra.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra using (algebrahom)

private
  variable
    ℓ : Level

CAlgHom : {R : CommRing {ℓ}} → CommAlgebra R → CommAlgebra R → Type ℓ
CAlgHom A B = AlgebraHom (CommAlgebra→Algebra A) (CommAlgebra→Algebra B)

homEq : {(R , str) : CommRing {ℓ}} (A B : CommAlgebra (R , str)) → (f g : CAlgHom A B)
        → ((x : CommAlgebra.Carrier A) → (f $a x) ≡ (g $a x)) → f ≡ g
homEq {ℓ} {(R , str)} A B f g mapEq i =
  let
    open AlgebraHom
    open CommAlgebra ⦃...⦄
    _*_ : R → ⟨ B ⟩a → ⟨ B ⟩a
    r * a = CommAlgebra._⋆_ B r a
    isSetB = isSetAlgebra (CommAlgebra→Algebra B)
    A′ = CommAlgebra.Carrier A
    instance
      _ : CommAlgebra (R , str)
      _ = A
      _ : CommAlgebra (R , str)
      _ = B
  in algebrahom (λ x → mapEq x i)
                (λ x y j → isOfHLevel→isOfHLevelDep 1
                             (λ (f : A′ → _) → isSetB (f (x + y)) (f x + f y))
                             (isHom+ f x y) (isHom+ g x y)
                             (λ i x → mapEq x i) i j)
                (λ x y j → isOfHLevel→isOfHLevelDep 1
                             (λ (f : A′ → _) → isSetB (f (x · y)) (f x · f y))
                             (isHom· f x y) (isHom· g x y)
                             (λ i x → mapEq x i) i j)
                (λ j → isOfHLevel→isOfHLevelDep 1
                             (λ (f : A′ → _) → isSetB (f 1a) 1a)
                             (pres1 f) (pres1 g)
                             (λ i x → mapEq x i) i j)
                (λ r x j →
                      isOfHLevel→isOfHLevelDep 1
                      (λ (f : A′ → _) →
                         isSetB (f ((A CommAlgebra.⋆ r) x)) (r * f x))
                      (comm⋆ f r x) (comm⋆ g r x)
                      ((λ i x → mapEq x i)) i j)
