{-# OPTIONS --safe #-}
module Cubical.Modalities.Flat.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Modalities.Flat.Base

private
  variable
    @♭ ♭ℓ : Level
    ℓ ℓ' : Level

module ♭Sigma {@♭ ♭ℓ ♭ℓ' : Level} {@♭ A : Type ♭ℓ} (@♭ C : A → Type ♭ℓ') where
  ♭C : ♭ A → Type ♭ℓ'
  ♭C (u ^♭) = ♭ (C u)

  Σ♭→♭Σ : (Σ[ x ∈ ♭ A ] ♭C x) → ♭ (Σ[ x ∈ A ] C x)
  Σ♭→♭Σ ((u ^♭) , (v ^♭)) = (u , v) ^♭

  ♭Σ→Σ♭ : ♭ (Σ[ x ∈ A ] C x) → (Σ[ x ∈ ♭ A ] ♭C x)
  ♭Σ→Σ♭ ((u , v) ^♭) = (u ^♭) , (v ^♭)

  Σ♭≃♭Σ : (Σ[ x ∈ ♭ A ] ♭C x) ≃ ♭ (Σ[ x ∈ A ] C x)
  Σ♭≃♭Σ = isoToEquiv (iso Σ♭→♭Σ ♭Σ→Σ♭
          (λ { ((u , v) ^♭) → refl}) λ { ((u ^♭) , (v ^♭)) → refl})

module ♭Equalities {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ}  where
  {-
    Theorem 6.1 (Shulman's real cohesion)
     - done with a hack to avoid non-crisp interval variables
    I think, it should be justified semantically to use interval variables always as if they were crisp.
    If this is ever supported by agda, the following should be changed.
  -}

  private
    data _≡'_ {A : Type ℓ} : A → A → Type ℓ where
      refl' : {x : A} → x ≡' x

    ♭≡'→≡'♭ : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → ♭ (u ≡' v) → (u ^♭) ≡' (v ^♭)
    ♭≡'→≡'♭ u _ (refl' ^♭) = refl'

    ≡'♭→♭≡' : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → (u ^♭) ≡' (v ^♭) → ♭ (u ≡' v)
    ≡'♭→♭≡' u _ refl' = refl' ^♭

    ≡'♭≃♭≡' : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → (u ^♭) ≡' (v ^♭) ≃ ♭ (u ≡' v)
    ≡'♭≃♭≡' u v = isoToEquiv (iso (≡'♭→♭≡' u v) (♭≡'→≡'♭ u v) (λ {(refl' ^♭) → refl}) λ {refl' → refl})

    ♭≡'→♭≡ : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → ♭ (u ≡' v) → ♭ (u ≡ v)
    ♭≡'→♭≡ u v (refl' ^♭) = refl ^♭

    ≡'≃≡ : {A : Type ℓ} (x y : A) → (x ≡ y) ≃ (x ≡' y)
    ≡'≃≡ = fundamentalTheoremOfId _≡'_ (λ _ → refl') (λ z → (z , refl') , λ {(_ , refl') → refl})

    ♭≡' : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ}
       → (@♭ p : A ≡' B) → ♭ A ≡' ♭ B
    ♭≡' refl' = refl'

    ♭≃ : {@♭ ♭ℓ : Level} {@♭ A B : Type ♭ℓ} → (@♭ e : A ≃ B) → ♭ A ≃ ♭ B
    ♭≃ e = pathToEquiv ((fst (invEquiv (≡'≃≡ _ _))) (♭≡' ((fst (≡'≃≡ _ _)) (ua e))))

    ♭≡'≃♭≡ : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → ♭ (u ≡ v) ≃ ♭ (u ≡' v)
    ♭≡'≃♭≡ u v = ♭≃ (≡'≃≡ u v)

  ≡♭≃♭≡ : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → (u ^♭ ≡ v ^♭) ≃ ♭ (u ≡ v)
  ≡♭≃♭≡ u v = compEquiv (≡'≃≡ (u ^♭) (v ^♭)) (compEquiv (≡'♭≃♭≡' u v) (invEquiv (♭≡'≃♭≡ u v) ))

♭≡Comm : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A)
          → (u ^♭ ≡ v ^♭) ≃ ♭ (u ≡ v)
♭≡Comm {A = A} = ♭Equalities.≡♭≃♭≡ {A = A}
