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

private variable
  {-
    Variable generalization mostly doesn't work for crisp contexts,
    so the crisp levels are not used too much.
  -}
  @♭ ♭ℓ ♭ℓ' : Level
  ℓ ℓ' : Level

crispPropRec : {@♭ ♭ℓ : Level} {@♭ P : Type ♭ℓ} {@♭ A : Type ♭ℓ}
               → isProp P → ((@♭ y : A) → P) → (@♭ x : ∥ A ∥₁) → P
crispPropRec Pprop f ∣ x ∣₁ = f x
crispPropRec Pprop f (squash₁ x y i) = Pprop (crispPropRec Pprop f x) (crispPropRec Pprop f y) i

module ♭Sigma {@♭ ♭ℓ ♭ℓ' : Level} (@♭ A : Type ♭ℓ) (@♭ C : A → Type ♭ℓ') where
  ♭C : ♭ A → Type ♭ℓ'
  ♭C (u ^♭) = ♭ (C u)

  Σ♭ : Type _
  Σ♭ = Σ (♭ A) ♭C

  Σ♭→♭Σ : (Σ[ x ∈ ♭ A ] ♭C x) → ♭ (Σ[ x ∈ A ] C x)
  Σ♭→♭Σ ((u ^♭) , (v ^♭)) = (u , v) ^♭

  ♭Σ→Σ♭ : ♭ (Σ[ x ∈ A ] C x) → (Σ[ x ∈ ♭ A ] ♭C x)
  ♭Σ→Σ♭ ((u , v) ^♭) = (u ^♭) , (v ^♭)

  Σ♭≃♭Σ : (Σ[ x ∈ ♭ A ] ♭C x) ≃ ♭ (Σ[ x ∈ A ] C x)
  Σ♭≃♭Σ = isoToEquiv (iso Σ♭→♭Σ ♭Σ→Σ♭
          (λ { ((u , v) ^♭) → refl}) λ { ((u ^♭) , (v ^♭)) → refl})

♭Family = ♭Sigma.♭C
Σ♭ = ♭Sigma.Σ♭
Σ♭≃♭Σ = ♭Sigma.Σ♭≃♭Σ

module ♭Equalities {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ}  where
  {-
    Theorem 6.1 (Shulman's real cohesion)
     - done with a hack to avoid non-crisp interval variables
    I think, it should be justified semantically to use interval variables always as if they were crisp.
    If this is ever supported by agda, the following should be changed.

    The final proof of the theorem '♭≡Comm' is below this module.
  -}

  private
    data _≡'_ {A : Type ℓ} : A → A → Type ℓ where
      refl' : {x : A} → x ≡' x

    subst' : {@♭ A : Type ♭ℓ} (@♭ B : A → Type ♭ℓ') {@♭ x y : A}
      → (@♭ p : x ≡' y) → (b : B x) → B y
    subst' _ refl' b = b

    ♭≡'→≡'♭ : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → ♭ (u ≡' v) → (u ^♭) ≡' (v ^♭)
    ♭≡'→≡'♭ u _ (refl' ^♭) = refl'

    ≡'♭→♭≡' : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → (u ^♭) ≡' (v ^♭) → ♭ (u ≡' v)
    ≡'♭→♭≡' u _ refl' = refl' ^♭

    ≡'♭≃♭≡' : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → (u ^♭) ≡' (v ^♭) ≃ ♭ (u ≡' v)
    ≡'♭≃♭≡' u v = isoToEquiv (iso (≡'♭→♭≡' u v) (♭≡'→≡'♭ u v) (λ {(refl' ^♭) → refl}) λ {refl' → refl})

    ♭≡'→♭≡ : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → ♭ (u ≡' v) → ♭ (u ≡ v)
    ♭≡'→♭≡ u v (refl' ^♭) = refl ^♭

    ≡≃≡' : {A : Type ℓ} (x y : A) → (x ≡ y) ≃ (x ≡' y)
    ≡≃≡' = fundamentalTheoremOfId _≡'_ (λ _ → refl') (λ z → (z , refl') , λ {(_ , refl') → refl})

    ≡'→≡ : {B : Type ℓ} {u v : B} (p : u ≡' v) → u ≡ v
    ≡'→≡ {u = u} {v = v} p = fst (invEquiv (≡≃≡' u v)) p

    ≡→≡' : {B : Type ℓ} {u v : B} (p : u ≡ v) → u ≡' v
    ≡→≡' {u = u} {v = v} p = fst (≡≃≡' u v) p

    →refl : {A : Type ℓ} (x : A) → (≡→≡' (refl {x = x})) ≡ refl'
    →refl x = fundamentalTheoremOfIdβ _≡'_ (λ _ → refl') (λ z → (z , refl') , λ {(_ , refl') → refl}) x

    →refl' : {A : Type ℓ} (x : A) → (≡'→≡ (refl' {x = x})) ≡ refl
    →refl' x =  ≡'→≡ (refl' {x = x})  ≡⟨ cong ≡'→≡ (sym (→refl x)) ⟩
                ≡'→≡ (≡→≡' refl)      ≡⟨ snd (isEquiv→hasRetract (snd (≡≃≡' x x))) refl ⟩
                refl ∎

    ♭≡' : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ}
       → (@♭ p : A ≡' B) → ♭ A ≡' ♭ B
    ♭≡' refl' = refl'

    ♭≃ : {@♭ ♭ℓ : Level} {@♭ A B : Type ♭ℓ} → (@♭ e : A ≃ B) → ♭ A ≃ ♭ B
    ♭≃ e = pathToEquiv ((fst (invEquiv (≡≃≡' _ _))) (♭≡' ((fst (≡≃≡' _ _)) (ua e))))

    ♭≡'≃♭≡ : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → ♭ (u ≡ v) ≃ ♭ (u ≡' v)
    ♭≡'≃♭≡ u v = ♭≃ (≡≃≡' u v)

  ≡♭≃♭≡ : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A) → (u ^♭ ≡ v ^♭) ≃ ♭ (u ≡ v)
  ≡♭≃♭≡ u v = compEquiv (≡≃≡' (u ^♭) (v ^♭)) (compEquiv (≡'♭≃♭≡' u v) (invEquiv (♭≡'≃♭≡ u v) ))

♭≡Comm : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (@♭ u v : A)
          → (u ^♭ ≡ v ^♭) ≃ ♭ (u ≡ v)
♭≡Comm {A = A} = ♭Equalities.≡♭≃♭≡ {A = A}


Fiber♭ : {@♭ ♭ℓ ♭ℓ' : Level}
        {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ'} (@♭ f : A → B) (@♭ u : B)
        → Type _
Fiber♭ f u = fiber (♭map f) (u ^♭)

♭Fiber : {@♭ ♭ℓ ♭ℓ' : Level}
        {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ'} (@♭ f : A → B) (@♭ u : B)
        → Type _
♭Fiber f u = ♭ (fiber f u)

♭PreservesFiber :
  {@♭ ♭ℓ ♭ℓ' : Level}
  {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ'} (@♭ f : A → B) (@♭ u : B)
  → (Fiber♭ f u) ≃ (♭Fiber f u)
♭PreservesFiber {♭ℓ' = ♭ℓ'} {A = A} f u =
  Fiber♭ f u                             ≃⟨ idEquiv _ ⟩
  Σ (♭ A) (λ y → (♭map f) y ≡ (u ^♭))   ≃⟨ patternMatchIn♭A ⟩
  Σ (♭ A) Path♭                         ≃⟨ _ , totalEquiv Path♭ ♭Path ♭≡CommMap ♭≡CommIsEquiv  ⟩
  Σ♭ _ (λ y → f y ≡ u)                   ≃⟨ Σ♭≃♭Σ _ (λ y → f y ≡ u) ⟩
  ♭Fiber f u ■
  where
    ♭Path : (x : ♭ A) → Type ♭ℓ'
    ♭Path = ♭Family A (λ v → (f v ≡ u))

    Path♭ : (x : ♭ A) → Type ♭ℓ'
    Path♭ (v ^♭) = (f v) ^♭ ≡ u ^♭

    ♭≡CommMap : (x : ♭ A) → Path♭ x → ♭Path x
    ♭≡CommMap (v ^♭) = fst (♭≡Comm (f v) u)

    ♭≡CommIsEquiv : (x : ♭ A) → isEquiv (♭≡CommMap x)
    ♭≡CommIsEquiv (v ^♭) = snd (♭≡Comm (f v) u)

    ♭Fiber→Fiber♭ : ♭Fiber f u → Fiber♭ f u
    ♭Fiber→Fiber♭ ((x , p) ^♭) = (x ^♭) , fst (invEquiv (♭≡Comm (f x) u)) (p ^♭)

    Fiber♭→♭Fiber : Fiber♭ f u → ♭Fiber f u
    Fiber♭→♭Fiber ((x ^♭) , p) = fst (Σ♭≃♭Σ _ (λ y → f y ≡ u)) ((x ^♭) , (fst (♭≡Comm (f x) u) p))

    patternMatchIn♭A : Σ (♭ A) (λ y → (♭map f) y ≡ (u ^♭)) ≃ Σ (♭ A) Path♭
    patternMatchIn♭A = isoToEquiv (iso to from toFrom fromTo)
      where
        to : Σ (♭ A) (λ y → (♭map f) y ≡ (u ^♭)) → Σ (♭ A) Path♭
        to ((v ^♭) , p) = (v ^♭) , p

        from : Σ (♭ A) Path♭ → Σ (♭ A) (λ y → (♭map f) y ≡ (u ^♭))
        from ((v ^♭) , p) = (v ^♭) , p

        toFrom : (x : _) → to (from x) ≡ x
        toFrom ((v ^♭) , p) = refl

        fromTo : (x : _) → from (to x) ≡ x
        fromTo ((v ^♭) , p) = refl
