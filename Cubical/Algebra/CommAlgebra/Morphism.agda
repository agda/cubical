{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Cubical.Algebra.CommAlgebra.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra

private
  variable
    ℓ : Level

CAlgHom : {R : CommRing ℓ} → CommAlgebra R ℓ → CommAlgebra R ℓ → Type ℓ
CAlgHom A B = CommAlgebraHom A B

homEq : {(R , str) : CommRing ℓ} (A B : CommAlgebra (R , str) ℓ) → (f g : CAlgHom A B)
        → ((x : fst A) → (f $a x) ≡ (g $a x)) → f ≡ g
homEq {ℓ} {(R , str)} A B f g mapEq = CommAlgebraHomEq A B f g mapEq

idCAlg : {R : CommRing ℓ} (A : CommAlgebra R ℓ) → CAlgHom A A
idCAlg A = (λ x → x) , (record
                          { pres0 = refl
                          ; pres1 = refl
                          ; pres+ = λ _ _ → refl
                          ; pres· = λ _ _ → refl
                          ; pres- = λ _ → refl
                          ; pres⋆ = λ _ _ → refl
                          }) 

