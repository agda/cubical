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


    crispIdInduction' : {@♭ ♭ℓ ♭ℓ′ : Level} {@♭ B : Type ♭ℓ}
                        (@♭ C : (@♭ u v : B) (@♭ p : u ≡' v) → Type ♭ℓ′)
                      → (@♭ d : (@♭ u : B) → C u u refl')
                      → (@♭ u v : B) (@♭ p : u ≡' v)
                      → C u v p
    crispIdInduction' C d u _ refl' = d u

    crispIdInduction : {@♭ ♭ℓ ♭ℓ′ : Level} {@♭ B : Type ♭ℓ}
                       (@♭ C : (@♭ u v : B) (@♭ p : u ≡ v) → Type ♭ℓ′)
                       → (@♭ d : (@♭ u : B) → C u u refl)
                       → (@♭ u v : B) (@♭ p : u ≡ v)
                       → C u v p
    crispIdInduction {B = B} C d = {!crispIdInduction' C'!}
      where ≡'→≡ : {@♭ u v : B} (@♭ p : u ≡' v) → u ≡ v
            ≡'→≡ {u = u} {v = v} p = fst (invEquiv (≡'≃≡ u v)) p
            ≡→≡' : {@♭ u v : B} (@♭ p : u ≡ v) → u ≡' v
            ≡→≡' {u = u} {v = v} p = fst (≡'≃≡ u v) p

            C' : (@♭ u v : B) (@♭ p : u ≡' v) → Type _
            C' u v p = C u v (fst (invEquiv (≡'≃≡ u v)) p)

            C'→C : (@♭ u v : B) (@♭ p : u ≡' v) → C' u v p → C u v (≡'→≡ p)
            C'→C u v p c' = c'

            C→C' : (@♭ u v : B) (@♭ p : u ≡' v) → C u v (≡'→≡ p) → C' u v p
            C→C' u v p c = c

            d' : (@♭ u : B) → C' u u refl'
            d' u = {!≡'→≡ refl'!}

  ≡♭≃♭≡ : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → (u ^♭ ≡ v ^♭) ≃ ♭ (u ≡ v)
  ≡♭≃♭≡ u v = compEquiv (≡'≃≡ (u ^♭) (v ^♭)) (compEquiv (≡'♭≃♭≡' u v) (invEquiv (♭≡'≃♭≡ u v) ))

♭≡Comm : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A)
          → (u ^♭ ≡ v ^♭) ≃ ♭ (u ≡ v)
♭≡Comm {A = A} = ♭Equalities.≡♭≃♭≡ {A = A}

{-
  From Theorem 5.6 in Michael Shulman's real cohesion article.
-}
crispIdentityInduction : {@♭ ♭ℓ ♭ℓ′ : Level} {@♭ B : Type ♭ℓ}
  (@♭ C : (@♭ u v : B) (@♭ p : u ≡ v) → Type ♭ℓ′)
  → (@♭ d : (@♭ u : B) → C u u refl)
  → (@♭ u v : B) (@♭ p : u ≡ v)
  → C u v p
crispIdentityInduction {B = B} C d = {!!}
  where C♭ : {@♭ u v : B} → u ^♭ ≡ v ^♭ → Type _
        C♭ p = C _ _ {!J!}
