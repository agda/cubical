{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Cubical.Algebra.CommAlgebra.Examples where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra.Base using (algebrahom)
open import Cubical.Algebra.CommAlgebra.Base

private
  variable
    ℓ : Level

module CommAlgebraExamples ((R , str) : CommRing {ℓ}) where

  initial : CommAlgebra (R , str)
  initial =
    let open CommRingStr str
    in commalgebra R _ _ _ _ _ (λ r x → r · x)
                    (makeIsCommAlgebra (isSetRing (CommRing→Ring (R , str)))
                       +Assoc +Rid +Rinv +Comm
                       ·Assoc ·Lid
                       ·Ldist+ ·-comm
                        (λ x y z → sym (·Assoc x y z)) ·Ldist+ ·Rdist+ ·Lid λ x y z → sym (·Assoc x y z))


  module _ (A : CommAlgebra (R , str)) where
    open CommAlgebra ⦃... ⦄
    instance
      _ : CommAlgebra (R , str)
      _ = A
      _ : CommAlgebra (R , str)
      _ = initial

    _*_ : R → ⟨ A ⟩a → ⟨ A ⟩a
    r * a = CommAlgebra._⋆_ A r a

    initialMap : CAlgHom initial A
    initialMap =
      algebrahom (λ r → r * 1a)
                 (λ x y → ⋆-ldist x y 1a)
                 (λ x y →  (x · y) * 1a ≡⟨ ⋆-assoc _ _ _ ⟩
                           x * (y * 1a)                   ≡[ i ]⟨ x * (·Lid (y * 1a) (~ i)) ⟩
                           x * (1a · (y * 1a))            ≡⟨ sym (⋆-lassoc _ _ _) ⟩
                           (x * 1a) · (y * 1a) ∎)
                 (⋆-lid _)
                 λ r x → (r · x) * 1a   ≡⟨ ⋆-assoc _ _ _ ⟩
                         (r * (x * 1a)) ∎

    homEq : (f g : CAlgHom initial A)
            → ((x : R) → (f $a x) ≡ (g $a x)) → f ≡ g
    homEq f g mapEq i =
      let
        open AlgebraHom
        isSetA = isSetAlgebra (CommAlgebra→Algebra A)
      in algebrahom (λ x → mapEq x i)
                    (λ x y j → isOfHLevel→isOfHLevelDep 1
                                 (λ (f : R → _) → isSetA (f (x + y)) (f x + f y))
                                 (isHom+ f x y) (isHom+ g x y)
                                 (λ i x → mapEq x i) i j)
                    (λ x y j → isOfHLevel→isOfHLevelDep 1
                                 (λ (f : R → _) → isSetA (f (x · y)) (f x · f y))
                                 (isHom· f x y) (isHom· g x y)
                                 (λ i x → mapEq x i) i j)
                    (λ j → isOfHLevel→isOfHLevelDep 1 (λ (f : R → _) → isSetA (f 1a) 1a)
                                 (pres1 f) (pres1 g)
                                 (λ i x → mapEq x i) i j)
                    (λ r x j →
                          isOfHLevel→isOfHLevelDep 1
                          (λ (f : R → _) →
                             isSetA (f ((initial CommAlgebra.⋆ r) x)) (r * f x))
                          (comm⋆ f r x) (comm⋆ g r x)
                          ((λ i x → mapEq x i)) i j)

    initialMapEq : (f : CAlgHom initial A)
                   → f ≡ initialMap
    initialMapEq f = homEq f initialMap
                           (λ r → f $a r         ≡[ i ]⟨ f $a (·Rid r (~ i)) ⟩
                                  f $a (r · 1a)    ≡⟨ AlgebraHom.comm⋆ f r 1a ⟩
                                  r * (f $a 1a)    ≡[ i ]⟨ r * (AlgebraHom.pres1 f i) ⟩
                                  r * 1a ∎)

    isInitial : CAlgHom initial A ≡ Unit*
    isInitial =
      isoToPath (iso (λ _ → tt*)
                     (λ _ → initialMap)
                     (λ {tt*x → refl})
                     λ f → sym (initialMapEq f))
