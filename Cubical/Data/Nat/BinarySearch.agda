module Cubical.Data.Nat.BinarySearch where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Mod renaming (quotient_/_ to _/_ ; remainder_/_ to _%_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    P : ℕ → Type ℓ

open Minimal hiding (search ; →Least)

module IncreasingDec (dec : ∀ n → Dec (P n)) (P≤ : ∀ {m n} → m ≤ᵗ n → P m → P n) where

  mid : ℕ → ℕ → ℕ
  mid a Δ = Δ / 2 + suc a

  private
    ¬P> : ∀ {m n} → m <ᵗ n → ¬ P n → ¬ P m
    ¬P> {m} m<n ¬Pn = ¬Pn ∘_ $ P≤ $ <ᵗ-weaken {m} $ m<n

    sum≤gap/2+mid : ∀ {a} Δ → Δ + a ≤ᵗ Δ / 2 + mid a Δ
    sum≤gap/2+mid {a} Δ = ≤→≤ᵗ $
      subst (Δ + a ≤_) (sym $ +-assoc (Δ / 2) _ (suc a) ∙ +-suc _ a) (≤-+ʳ (≤1+/2+/2 Δ))

    -- lemma needed to pass termination checking
    ≤ᵗf : ∀ Δ' {f} → Δ' ≤ᵗ f → suc Δ' / 2 ≤ᵗ f
    ≤ᵗf Δ' {f} = <ᵗ≤ᵗ-trans {suc Δ' / 2} {suc Δ'} {suc f} (<→<ᵗ (quotient<id Δ' 0))

    helper : ∀ a Δ f → Δ ≤ᵗ f → ¬ (P a) → P (Δ + a) → Σ[ m ∈ ℕ ] Least P m
    helper a zero       f       _    ¬Pa Pa   = ⊥.rec (¬Pa Pa)
    helper a Δ@(suc Δ') (suc f) Δ'≤f ¬Pa PΔ+a with dec (suc a)
    ... | yes P1+a = suc a , P1+a , λ _ → (¬Pa ∘_) ∘ P≤
    ... | no ¬P1+a with dec (mid a Δ)
    ... | yes Pm =
      helper (suc a)   (Δ / 2) f (≤ᵗf Δ' Δ'≤f) ¬P1+a Pm
    ... | no ¬Pm =
      helper (mid a Δ) (Δ / 2) f (≤ᵗf Δ' Δ'≤f) ¬Pm   (P≤ (sum≤gap/2+mid Δ) PΔ+a)

  -- if for a : ℕ we know already know that ¬ P a, then we can start searching from there

  search[_,_] : ∀ a n → a ≤ n → ¬ P a → (Σ[ m ∈ ℕ ] Least P m) ⊎ (∀ m → m <ᵗ n → ¬ P m)
  search[ a , n ] (Δ , Δ+a≡n) ¬Pa with dec (Δ + a)
  ... | yes Pn = inl (helper a Δ Δ (≤ᵗ-refl Δ) ¬Pa Pn)
  ... | no ¬Pn = inr (λ _ → flip ¬P> (¬Pn ∘ subst P (sym Δ+a≡n)))

  →Least[_,_] : ∀ a n → a ≤ n → ¬ P a → P n → Σ ℕ (Least P)
  →Least[ a , n ] (Δ , Δ+a≡n) ¬Pa Pn =
    helper a Δ Δ (≤ᵗ-refl Δ) ¬Pa (subst P (sym Δ+a≡n) Pn)

  -- otherwise, we can start at zero, relying on the decidability of P 0

  search : ∀ n → (Σ[ m ∈ ℕ ] Least P m) ⊎ (∀ m → m <ᵗ n → ¬ P m)
  search n with dec 0
  ... | yes P0 = inl (0 , P0 , λ _ b _ → b)
  ... | no ¬P0 = search[ 0 , n ] zero-≤ ¬P0

  →Least : Σ _ P → Σ _ (Least P)
  →Least (n , Pn) with search n
  ... | inl least = least
  ... | inr ¬P<n  = n , Pn , ¬P<n

-- This can be applied to search for the biggest value such that
-- its image under an increasing function is below a given k : ℕ
module BiggestImage≤ (f : ℕ → ℕ) (inc : isIncreasing f) (f0=0 : f 0 ≡ 0) (k : ℕ) where
  open IncreasingDec
    ((k <ᵗ?_) ∘ f)
    (λ {m} {n} → flip (<ᵗ≤ᵗ-trans {k} {f m} {f n}) ∘ ≤→≤ᵇ ∘ inc ∘ ≤ᵇ→≤)
    public hiding (mid)

  private
    module withLeast where
      preimage : Σ ℕ (Least ((k <ᵗ_) ∘ f)) → ℕ
      preimage = predℕ ∘ fst

      <imageSuc : ∀ ΣLeast → k < f (suc (preimage ΣLeast))
      <imageSuc (zero  , k<f0  , _) = <≤-trans (<ᵗ→< k<f0) (inc zero-≤)
      <imageSuc (suc n , k<fsn , _) = <ᵗ→< k<fsn

      image≤ : ∀ ΣLeast → f (preimage ΣLeast) ≤ k
      image≤ (zero  , k<f0  , r<n→¬k<fsr) = subst (_≤ k) (sym f0=0) zero-≤
      image≤ (suc n , k<fsn , r<n→¬k<fsr) = <-asym' $ r<n→¬k<fsr n (<ᵗsuc {n}) ∘ <→<ᵗ

  module →Biggest[_,_] (a n : ℕ) (a≤n : a ≤ n) (fa≤k : f a ≤ᵗ k) (k<fn : k <ᵗ f n) where
    private
      ΣLeast : Σ ℕ (Least ((k <ᵗ_) ∘ f))
      ΣLeast = →Least[ a , n ] a≤n (flip (<ᵗ-asym {k} {f a}) (≤ᵗ→≤ fa≤k)) k<fn

    preimage : ℕ
    preimage = withLeast.preimage ΣLeast

    <imageSuc : k < f (suc preimage)
    <imageSuc = withLeast.<imageSuc ΣLeast

    image≤ : f preimage ≤ k
    image≤ = withLeast.image≤ ΣLeast

  module →Biggest (ΣP : Σ[ n ∈ ℕ ] k <ᵗ f n) where
    preimage : ℕ
    preimage = withLeast.preimage (→Least ΣP)

    <imageSuc : k < f (suc preimage)
    <imageSuc = withLeast.<imageSuc (→Least ΣP)

    image≤ : f preimage ≤ k
    image≤ = withLeast.image≤ (→Least ΣP)
