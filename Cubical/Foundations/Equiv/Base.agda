{-# OPTIONS --safe #-}
module Cubical.Foundations.Equiv.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Core.Glue public
  using ( isEquiv ; equiv-proof ; _≃_ ; equivFun ; equivProof )

fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

-- Helper function for constructing equivalences from pairs (f,g) that cancel each other up to definitional
-- equality. For such (f,g), the result type simplifies to isContr (fiber f b).
strictContrFibers : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} (g : B → A) (b : B)
  → Σ[ t ∈ fiber f (f (g b)) ]
    ((t' : fiber f b) → Path (fiber f (f (g b))) t (g (f (t' .fst)) , cong (f ∘ g) (t' .snd)))
strictContrFibers {f = f} g b .fst = (g b , refl)
strictContrFibers {f = f} g b .snd (a , p) i = (g (p (~ i)) , λ j → f (g (p (~ i ∨ j))))

-- The identity equivalence
idIsEquiv : ∀ {ℓ} (A : Type ℓ) → isEquiv (idfun A)
idIsEquiv A .equiv-proof = strictContrFibers (idfun A)

idEquiv : ∀ {ℓ} (A : Type ℓ) → A ≃ A
idEquiv A .fst = idfun A
idEquiv A .snd = idIsEquiv A

-- the definition using Π-type
isEquiv' : ∀ {ℓ}{ℓ'}{A : Type ℓ}{B : Type ℓ'} → (A → B) → Type (ℓ-max ℓ ℓ')
isEquiv' {B = B} f = (y : B) → isContr (fiber f y)

-- Transport along a line of types A, constant on some extent φ, is an equivalence.
isEquivTransp : ∀ {ℓ : I → Level} (A : (i : I) → Type (ℓ i)) → ∀ (φ : I) → isEquiv (transp (λ j → A (φ ∨ j)) φ)
isEquivTransp A φ = u₁ where
  -- NB: The transport in question is the `coei→1` or `squeeze` operation mentioned
  -- at `Cubical.Foundations.CartesianKanOps` and
  -- https://1lab.dev/1Lab.Path.html#coei%E2%86%921
  coei→1 : A φ → A i1
  coei→1 = transp (λ j → A (φ ∨ j)) φ

  -- A line of types, interpolating between propositions:
  -- (k = i0): the identity function is an equivalence
  -- (k = i1): transport along A is an equivalence
  γ : (k : I) → Type _
  γ k = isEquiv (transp (λ j → A (φ ∨ (j ∧ k))) (φ ∨ ~ k))

  _ : γ i0 ≡ isEquiv (idfun (A φ))
  _ = refl

  _ : γ i1 ≡ isEquiv coei→1
  _ = refl

  -- We have proof that the identity function *is* an equivalence,
  u₀ : γ i0
  u₀ = idIsEquiv (A φ)

  -- and by transporting that evidence along γ, we prove that
  -- transporting along A is an equivalence, too.
  u₁ : γ i1
  u₁ = transp γ φ u₀

transpEquiv : ∀ {ℓ : I → Level} (A : (i : I) → Type (ℓ i)) → ∀ φ → A φ ≃ A i1
transpEquiv A φ .fst = transp (λ j → A (φ ∨ j)) φ
transpEquiv A φ .snd = isEquivTransp A φ
