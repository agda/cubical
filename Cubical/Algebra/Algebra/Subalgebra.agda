open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Algebra.Algebra
open import Cubical.Algebra.Module.Submodule
open import Cubical.Algebra.Monoid.Submonoid
open import Cubical.Algebra.Ring

module Cubical.Algebra.Algebra.Subalgebra
  {ℓ ℓ' : Level}
  (R : Ring ℓ) (A : Algebra R ℓ')
  where

open AlgebraStr (str A)

record isSubalgebra (S : ℙ ⟨ A ⟩) : Type (ℓ-max ℓ ℓ') where
  field
    submodule : isSubmodule R (Algebra→Module A) S
    submonoid : isSubmonoid (Algebra→MultMonoid A) S
  open isSubmodule submodule public
    renaming ( 0r-closed to 0a-closed )
  open isSubmonoid submonoid public
    renaming (ε-closed to 1a-closed)

module _
  (S : ℙ ⟨ A ⟩)
  (+-closed : {x y : ⟨ A ⟩} → x ∈ S → y ∈ S → x + y ∈ S)
  (0a-closed : 0a ∈ S)
  (⋆-closed :  {x : ⟨ A ⟩} (r : ⟨ R ⟩) → x ∈ S → r ⋆ x ∈ S)
  (1a-closed : 1a ∈ S)
  (·-closed : {x y : ⟨ A ⟩} → (x ∈ S) → (y ∈ S) → (x · y) ∈ S)
  where
  private
    module sAlg = isSubalgebra
    module sMod = isSubmodule
    module sMon = isSubmonoid

  makeSubalgebra : isSubalgebra S
  makeSubalgebra .sAlg.submodule .sMod.+-closed = +-closed
  makeSubalgebra .sAlg.submodule .sMod.0r-closed = 0a-closed
  makeSubalgebra .sAlg.submodule .sMod.⋆-closed = ⋆-closed
  makeSubalgebra .sAlg.submonoid .sMon.ε-closed = 1a-closed
  makeSubalgebra .sAlg.submonoid .sMon.·-closed = ·-closed

Subalgebra : Type (ℓ-max ℓ (ℓ-suc ℓ'))
Subalgebra = Σ[ S ∈ ℙ ⟨ A ⟩ ] isSubalgebra S

module _ ((S , isSubalgebra) : Subalgebra) where
  open isSubalgebra isSubalgebra
  private module algStr = AlgebraStr

  Subalgebra→Algebra≡ : {x y : Σ[ a ∈ ⟨ A ⟩ ] a ∈ S} → fst x ≡ fst y → x ≡ y
  Subalgebra→Algebra≡ eq = Σ≡Prop (∈-isProp S) eq

  Subalgebra→Algebra : Algebra R ℓ'
  Subalgebra→Algebra .fst = Σ[ a ∈ ⟨ A ⟩ ] a ∈ S
  Subalgebra→Algebra .snd .algStr.0a = 0a , 0a-closed
  Subalgebra→Algebra .snd .algStr.1a = 1a , 1a-closed
  Subalgebra→Algebra .snd .algStr._+_ (a , a∈) (b , b∈) = a + b , +-closed a∈ b∈
  Subalgebra→Algebra .snd .algStr._·_ (a , a∈) (b , b∈) = a · b , ·-closed a∈ b∈
  Subalgebra→Algebra .snd .algStr.-_ (a , a∈) = - a , -closed a∈
  Subalgebra→Algebra .snd .algStr._⋆_ r (a , a∈) = r ⋆ a , ⋆-closed r a∈
  Subalgebra→Algebra .snd .algStr.isAlgebra =
    let
      isSet-A' = isSetΣSndProp is-set (∈-isProp S)
      +Assoc' = λ x y z → Subalgebra→Algebra≡ (+Assoc (fst x) (fst y) (fst z))
      +IdR' = λ x → Subalgebra→Algebra≡ (+IdR (fst x))
      +InvR' = λ x → Subalgebra→Algebra≡ (+InvR (fst x))
      +Comm' = λ x y → Subalgebra→Algebra≡ (+Comm (fst x) (fst y))
      ·Assoc' = λ x y z → Subalgebra→Algebra≡ (·Assoc (fst x) (fst y) (fst z))
      ·IdR' = λ x → Subalgebra→Algebra≡ (·IdR (fst x))
      ·IdL' = λ x → Subalgebra→Algebra≡ (·IdL (fst x))
      ·DistR+' = λ x y z → Subalgebra→Algebra≡ (·DistR+ (fst x) (fst y) (fst z))
      ·DistL+' = λ x y z → Subalgebra→Algebra≡ (·DistL+ (fst x) (fst y) (fst z))
      ⋆Assoc' = λ r s x → Subalgebra→Algebra≡ (⋆Assoc r s (fst x))
      ⋆DistR+' = λ r x y → Subalgebra→Algebra≡ (⋆DistR+ r (fst x) (fst y))
      ⋆DistL+' = λ r s y → Subalgebra→Algebra≡ (⋆DistL+ r s (fst y))
      ⋆IdL' = λ x → Subalgebra→Algebra≡ (⋆IdL (fst x))
      ⋆AssocR' = λ r x y → Subalgebra→Algebra≡ (⋆AssocR r (fst x) (fst y))
      ⋆AssocL' = λ r x y → Subalgebra→Algebra≡ (⋆AssocL r (fst x) (fst y))
    in makeIsAlgebra isSet-A'
         +Assoc' +IdR' +InvR' +Comm' ·Assoc' ·IdR' ·IdL' ·DistR+' ·DistL+'
         ⋆Assoc' ⋆DistR+' ⋆DistL+' ⋆IdL' ⋆AssocR' ⋆AssocL'

  Subalgebra→AlgebraHom : AlgebraHom Subalgebra→Algebra A
  Subalgebra→AlgebraHom =
    fst , makeIsAlgebraHom refl (λ x y → refl) (λ x y → refl) (λ x y → refl)
