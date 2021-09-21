{-# OPTIONS --cubical #-}
module Cubical.Algebra.UpperNat.Base where
{-
  based on:
  https://github.com/DavidJaz/Cohesion/blob/master/UpperNaturals.agda

  and the slides here (for arithmetic operation):
  https://felix-cherubini.de/myers-slides-II.pdf
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Logic
open import Cubical.Functions.Embedding

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma

open import Cubical.HITs.Truncation
open import Cubical.HITs.PropositionalTruncation renaming (rec to propTruncRec)

private
  variable
    ℓ ℓ′ : Level

hProp₀ = hProp ℓ-zero

-- A propositional version of _≤_
_≤p_ : ℕ → ℕ → hProp₀
n ≤p m = (n ≤ m) , m≤n-isProp

isUpwardClosed : (s : ℕ → hProp₀) → Type₀
isUpwardClosed s = (n m : ℕ) → n ≤ m → fst (s n) → fst (s m)

isPropUpwardClosed : (N : ℕ → hProp₀) → isProp (isUpwardClosed N)
isPropUpwardClosed N =
  isPropΠ4 (λ _ m _ _ → snd (N m))

isSetℕ→Prop₀ : isSet (ℕ → hProp₀)
isSetℕ→Prop₀ = isOfHLevelΠ 2 λ _ → isSetHProp

{- The Upper Naturals
   An upper natural is an upward closed proposition on natural numbers.
   The interpretation is that an upper natural is a natural ``defined by its upper bounds'', in the
   sense that for the proposition N holding of a natural n means that n is an upper bound of N.
   The important bit about upper naturals is that they satisfy the well-ordering principle,
   constructively.

   Example Application:
   The degree of a (constructive!) polynomial may be defined as an upper natural:

     deg(∑_{i=0}^{n} aᵢ · Xⁱ) :≡ λ (k : ℕ) → ∀ (k ≤ i ≤ n) aₖ≡0
-}

ℕ↑ : Type₁
ℕ↑ = Σ[ s ∈ (ℕ → hProp₀)] isUpwardClosed s

isSetℕ↑ : isSet ℕ↑
isSetℕ↑ = isOfHLevelΣ 2 isSetℕ→Prop₀ λ s → isOfHLevelSuc 1 (isPropUpwardClosed s)

_isUpperBoundOf_ : ℕ → ℕ↑ → hProp₀
n isUpperBoundOf s = (fst s) n

_^↑ : ℕ → ℕ↑
n ^↑ = (n ≤p_) , isUpwardClosed≤p
  where
    isUpwardClosed≤p : {n : ℕ} → isUpwardClosed (n ≤p_)
    isUpwardClosed≤p = λ _ _ z z₁ → ≤-trans z₁ z

0↑ : ℕ↑
0↑ = 0 ^↑

1↑ : ℕ↑
1↑ = 1 ^↑

-- Infinity is defined to be the number with no upper bounds.
∞↑ : ℕ↑
∞↑ = (λ _ → false) , proof
  where false : hProp₀
        false = ⊥
        proof : isUpwardClosed (λ _ → false)
        proof = λ n m _ z → z

_+↑_ : ℕ↑ → ℕ↑ → ℕ↑
s +↑ l = seq , seqIsUpwardClosed
       where
         seq : ℕ → hProp₀
         seq n = (∃[ (a , b) ∈ ℕ × ℕ ] fst ((fst s a) ⊓ (fst l b) ⊓ ((a + b) ≤p n) )) ,
                 isPropPropTrunc
         seqIsUpwardClosed : isUpwardClosed seq
         seqIsUpwardClosed n m n≤m =
           propTruncRec
             isPropPropTrunc
             λ {((a , b) , wa , (wb , a+b≤n)) → ∣ (a , b) , wa , (wb , ≤-trans a+b≤n n≤m) ∣}

-- hasPropFibers→isEmbedding
ℕ↑Path : {s l : ℕ↑} → ((n : ℕ) → fst (fst s n) ≡ fst (fst l n)) → s ≡ l
ℕ↑Path {s = s} {l = l} pwPath = path
   where
     seqPath : fst s ≡ fst l
     seqPath i n = subtypePathReflection (λ A → isProp A , isPropIsProp)
                                         (fst s n)
                                         (fst l n)
                                         (pwPath n) i
     path : s ≡ l
     path = subtypePathReflection (λ s → isUpwardClosed s , isPropUpwardClosed s) s l seqPath

+↑Comm : (s l : ℕ↑) → s +↑ l ≡ l +↑ s
+↑Comm s l = ℕ↑Path λ n → cong fst (propPath n)
  where implication : (s l : ℕ↑) (n : ℕ) → fst (fst (s +↑ l) n) → fst (fst (l +↑ s) n)
        implication s l n = propTruncRec
                           isPropPropTrunc
                           (λ {((a , b) , wa , (wb , a+b≤n))
                             → ∣ (b , a) , wb , (wa , subst (λ k → fst (k ≤p n)) (+-comm a b) a+b≤n) ∣ })
        propPath : (n : ℕ) → fst (s +↑ l) n ≡ fst (l +↑ s) n
        propPath n = ⇒∶ implication s l n
                     ⇐∶ implication l s n

_·↑_ : ℕ↑ → ℕ↑ → ℕ↑
s ·↑ l = seq , seqIsUpwardClosed
       where
         seq : ℕ → hProp₀
         seq n = (∃[ (a , b) ∈ ℕ × ℕ ] fst ((fst s a) ⊓ (fst l b) ⊓ ((a · b) ≤p n) )) ,
                 isPropPropTrunc
         seqIsUpwardClosed : isUpwardClosed seq
         seqIsUpwardClosed n m n≤m =
           propTruncRec
             isPropPropTrunc
             λ {((a , b) , wa , (wb , a·b≤n)) → ∣ (a , b) , wa , (wb , ≤-trans a·b≤n n≤m) ∣}
