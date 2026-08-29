module Cubical.Foundations.Smallness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Displayed.Base

is[_]Small : (ℓ : Level) {ℓ' : Level} (A : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
is[_]Small ℓ A = Σ (Type ℓ) λ B → B ≃ A

isLocally[_]Small : (ℓ : Level) {ℓ' : Level} (A : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
isLocally[_]Small ℓ A = (x y : A) → is[ ℓ ]Small (x ≡ y)

isSmall-≃-isSmall :  ∀ {ℓ} {ℓ'} {ℓ''} {A : Type ℓ'} {A' : Type ℓ''} → is[ ℓ ]Small A → A ≃ A' → is[ ℓ ]Small A'
isSmall-≃-isSmall small equiv .fst = small .fst
isSmall-≃-isSmall small equiv .snd = compEquiv (small .snd) equiv

isSmall≃ : ∀ {ℓ} {ℓ'} {ℓ''} {A : Type ℓ'} {A' : Type ℓ''}
  → is[ ℓ ]Small A
  → is[ ℓ ]Small A'
  → is[ ℓ ]Small (A ≃ A')
isSmall≃ smallA smallA' .fst = smallA .fst ≃ smallA' .fst
isSmall≃ smallA smallA' .snd = equivComp (smallA .snd) (smallA' .snd)

isSmall≡ : ∀ {ℓ} {ℓ'} {A : Type ℓ'} {A' : Type ℓ'}
  → is[ ℓ ]Small A
  → is[ ℓ ]Small A'
  → is[ ℓ ]Small (A ≡ A')
isSmall≡ smallA smallA' = isSmall-≃-isSmall (isSmall≃ smallA smallA') (invEquiv univalence)

isℓSmallℓ : ∀ {ℓ} (A : Type ℓ) → is[ ℓ ]Small A
isℓSmallℓ A .fst = A
isℓSmallℓ A .snd = idEquiv A

isSmallΣ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ'} {B : A → Type ℓ''}
  → is[ ℓ ]Small A
  → ((a : A) → is[ ℓ ]Small (B a))
  → is[ ℓ ]Small (Σ A B)
isSmallΣ sA sB .fst = Σ[ a' ∈ sA .fst ] sB (sA .snd .fst a') .fst
isSmallΣ sA sB .snd = Σ-cong-equiv (sA .snd) (λ a' → sB (sA .snd .fst a') .snd)

isSmallΠ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ'} {B : A → Type ℓ''}
  → is[ ℓ ]Small A
  → ((a : A) → is[ ℓ ]Small (B a))
  → is[ ℓ ]Small ((a : A) → B a)
isSmallΠ sA sB .fst = (a' : sA .fst) → sB (sA .snd .fst a') .fst
isSmallΠ sA sB .snd = equivΠ (sA .snd) (λ a' → sB (sA .snd .fst a') .snd)

-- Evidence that A is locally ℓ-small is the same as an ℓ-valued UARel on A.

module _ {ℓ ℓ'} {A : Type ℓ} where

  locallySmall→UARel : isLocally[ ℓ' ]Small A → UARel A ℓ'
  locallySmall→UARel lsA .UARel._≅_ x y = lsA x y .fst
  locallySmall→UARel lsA .UARel.ua x y = lsA x y .snd

  UARel→locallySmall : UARel A ℓ' → isLocally[ ℓ' ]Small A
  UARel→locallySmall 𝒮-A x y = (x A.≅ y ) , A.ua x y
    where module A = UARel 𝒮-A
