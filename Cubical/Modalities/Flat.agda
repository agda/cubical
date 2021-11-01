{-# OPTIONS --safe #-}
module Cubical.Modalities.Flat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PropTrunc

{-
  In Mike Shulman's real cohesive homotopty type theory
  (see https://arxiv.org/pdf/1509.07584.pdf),
  a judgement of the form `x :: A` is read as `x is a crisp
  variable of type A`. In Agda a declaration `@♭ x : A` can
  be used in a way similar. It is only possible to declare a
  variable like that, if all variables appearing in `A` were
  also introduced in this way. If this is the case, we say
  that `A` is crisp.
-}

private
  variable
    @♭ ♭ℓ : Level
    ℓ ℓ' : Level

data ♭ (@♭ A : Type ♭ℓ) : Type ♭ℓ where
    _^♭ : (@♭ a : A) → ♭ A

counit : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} → ♭ A → A
counit (a ^♭) = a

♭map : {@♭ ♭ℓ ♭ℓ′ : Level} {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ′}
       → (@♭ f : A → B) → ♭ A → ♭ B
♭map f (a ^♭) = (f a) ^♭

♭-Induction : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (C : ♭ A → Type ℓ)
              → (f₀ : (@♭ u : A) → C (u ^♭))
              → (M : ♭ A)
              → (C M)
♭-Induction C f₀ (a ^♭) = f₀ a

{-
  Lemma 5.1 (Shulman's real cohesion)
-}
crisp♭-Induction : {@♭ ♭ℓ ♭ℓ' : Level} {@♭ A : Type ♭ℓ}
                   → (@♭ C : (@♭ x : ♭ A) → Type ♭ℓ')
                   → (@♭ N : (@♭ u : A) → C (u ^♭))
                   → (@♭ M : ♭ A) → C M
crisp♭-Induction C N (a ^♭) = N a

♭nat : {@♭ ♭ℓ ♭ℓ′ : Level} {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ′}
        → (@♭ f : A → B)
        → (x : ♭ A) → counit (♭map f x) ≡ f (counit x)
♭nat f (x ^♭) = refl

♭congCounit : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ}
        → (@♭ x y : A) → (p : ♭ (x ≡ y)) → x ^♭ ≡ y ^♭
♭congCounit x y (q ^♭) i = {!(q i) ^♭!}

isCrisplyDiscrete : {@♭ ♭ℓ : Level}
                    → (@♭ A : Type ♭ℓ) → Type ♭ℓ
isCrisplyDiscrete A = isEquiv (counit {A = A})

isDiscreteUnit : isCrisplyDiscrete Unit
isDiscreteUnit = snd (isoToEquiv (iso counit inv linv rinv))
  where
    inv = λ {tt → tt ^♭}
    linv = λ {tt → refl}
    rinv = λ {(tt ^♭) → refl}

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
    (done in a different way, avoiding (non-crisp) interval variables)
  -}
  Eq♭ : ♭ A → ♭ A → Type ♭ℓ
  Eq♭ (u ^♭) (v ^♭) = ♭ (u ^♭ ≡ v ^♭)

  Eq♭'' : (@♭ u : A) → (@♭ v : A) → Type ♭ℓ
  Eq♭'' u v = u ≡ v

  Eq♭' : ♭ A → ♭ A → Type ♭ℓ
  Eq♭' (u ^♭) (v ^♭) = ♭ (u ≡ v)

  reflEq♭ : (x : ♭ A) → Eq♭ x x
  reflEq♭ (u ^♭) = refl ^♭

  ΣEq≃♭Σ≡ : (@♭ u : A) → (Σ[ y ∈ ♭ A ] Eq♭' (u ^♭) y) ≃ ♭ (Σ[ y ∈ A ] u ≡ y)
  ΣEq≃♭Σ≡ u = let open ♭Sigma in {!Σ♭≃♭Σ (Eq♭'' u) !}

  Eq♭SigmaContr : (x : ♭ A) → isContr (Σ[ y ∈ ♭ A ] Eq♭ x y)
  Eq♭SigmaContr (u ^♭) = {!!}




private
  counitInvℕ : ℕ → ♭ ℕ
  counitInvℕ zero = zero ^♭
  counitInvℕ (suc x) = ♭map suc (counitInvℕ x)

  linvℕ : (n : ℕ) → counit (counitInvℕ n) ≡ n
  linvℕ zero = refl
  linvℕ (suc x) =
         counit (counitInvℕ (suc x))    ≡⟨ ♭nat suc (counitInvℕ x) ⟩
         suc (counit (counitInvℕ x))    ≡⟨ cong suc (linvℕ x) ⟩
         suc x ∎

  rinvℕ : (n : ♭ ℕ) → counitInvℕ (counit n) ≡ n
  rinvℕ (zero ^♭) = refl
  rinvℕ (suc a ^♭) =
              ♭map suc (counitInvℕ a)  ≡⟨ cong (♭map suc) (rinvℕ (a ^♭)) ⟩
              suc a ^♭ ∎

isDiscreteℕ : isCrisplyDiscrete ℕ
isDiscreteℕ = snd (isoToEquiv (iso counit counitInvℕ linvℕ rinvℕ))

isDiscreteℤ : isCrisplyDiscrete ℤ
isDiscreteℤ = snd (isoToEquiv (iso counit inv linv rinv))
  where
    inv = λ { (pos n) → ♭map pos (counitInvℕ n) ;
              (negsuc n) → ♭map negsuc (counitInvℕ n)}
    linv = λ { (pos n) →
                 counit (inv (pos n))          ≡⟨ ♭nat pos (counitInvℕ n) ⟩
                 pos (counit (counitInvℕ n))   ≡⟨ cong pos (linvℕ n) ⟩
                 (pos n) ∎ ;
               (negsuc n) →
                 counit (inv (negsuc n))         ≡⟨ ♭nat negsuc (counitInvℕ n) ⟩
                 negsuc (counit (counitInvℕ n))  ≡⟨ cong negsuc (linvℕ n) ⟩
                 negsuc n ∎}
    rinv = λ { (pos n ^♭) → cong (♭map pos) (rinvℕ (n ^♭)) ;
               (negsuc n ^♭) → cong (♭map negsuc) (rinvℕ (n ^♭))}

{-
  From the article
  https://arxiv.org/pdf/1908.08034.pdf
  by david Jaz Myers
-}

BAut : {ℓ : Level}
       → (X : Type ℓ) → X → Type ℓ
BAut X x = Σ[ y ∈ X ] ∥ y ≡ x ∥

♭BAut→BAut♭ : {@♭ ♭ℓ : Level}
            →  (@♭ X : Type ♭ℓ) (@♭ x : X)
            → ♭ (BAut X x) → BAut (♭ X) (x ^♭)
♭BAut→BAut♭ X x ((y , p) ^♭) = (y ^♭) ,
              PropTrunc.rec PropTrunc.isPropPropTrunc (λ p → ∣ {!cong _^♭ p!} ∣ ) p

BAutEquiv : {@♭ ♭ℓ : Level} (@♭ X : Type ♭ℓ)
            → _
BAutEquiv = {!!}
