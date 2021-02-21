{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

module Cubical.Displayed.Countable where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Unit as Unit

open import Cubical.Codata.Conat as Conat
open import Cubical.Codata.Conat.Bounded as Conat

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary

open import Cubical.Displayed.Base
open import Cubical.Displayed.Properties

private
  variable
    ℓ : Level
    A : Type ℓ

Denumeration : Type ℓ → Type ℓ
Denumeration A = ℕ ≃ A

isDenumerable : Type ℓ → Type ℓ
isDenumerable A = ∥ ℕ ≃ A ∥

[_]-Listing : Conat → Type ℓ → Type ℓ
[ m ]-Listing A = Bounded m ≃ A

isCountable' : Type ℓ → Type ℓ
isCountable' A = ∥ Σ[ m ∈ Conat ] [ m ]-Listing A ∥

isCountable : Type ℓ → Type ℓ
isCountable A = Σ[ m ∈ Conat ] ∥ [ m ]-Listing A ∥

isCountableIsProp : isProp (isCountable A)
isCountableIsProp (m , l) (n , r)
    = ΣPathP (m≡n , isOfHLevel→isOfHLevelDep 1 (λ _ → squash) l r m≡n)
  where
  m≡n : m ≡ n
  m≡n = rec2 (IsSet.isSetConat m n)
          (λ e1 e2 → Bounded-inj m n (ua (compEquiv e1 (invEquiv e2))))
          l r

isCountable'→isCountable : isCountable' A → isCountable A
isCountable'→isCountable = PT.rec isCountableIsProp (map-snd ∣_∣)

CountableIndexing : Type ℓ → Type ℓ
CountableIndexing A = Σ[ f ∈ (ℕ → Maybe A) ] ∀ x → ∥ fiber f (just x) ∥

isCountablyIndexed : Type ℓ → Type ℓ
isCountablyIndexed A = ∥ CountableIndexing A ∥

Denumeration→[∞]-Listing : Denumeration A → [ ∞ ]-Listing A
Denumeration→[∞]-Listing = compEquiv Σ≺∞≃ℕ

[∞]-Listing→Denumeration : [ ∞ ]-Listing A → Denumeration A
[∞]-Listing→Denumeration = compEquiv (invEquiv Σ≺∞≃ℕ)

isDenumerable→isCountable : isDenumerable A → isCountable' A
isDenumerable→isCountable = map (_,_ ∞ ∘ Denumeration→[∞]-Listing)

Listing→CountableIndexing : ∀ m → [ m ]-Listing A → CountableIndexing A
Listing→CountableIndexing m l = (f , ∣_∣ ∘ fib)
  where
  ix : (n : ℕ) → Dec (n ≺ m) → Maybe _
  ix n (yes n≺m) = just (l .fst (n , n≺m))
  ix n (no _) = nothing

  f : ℕ → Maybe _
  f n = ix n (n ≺? m)

  fib : ∀ x → fiber f (just x)
  fib x with l .snd .equiv-proof x .fst
  ... | ((n , n≺m) , p) = n , cong (ix n) (≺?-yes n m n≺m) ∙ cong just p

isCountable→isCountablyIndexed : isCountable' A → isCountablyIndexed A
isCountable→isCountablyIndexed = map (uncurry Listing→CountableIndexing)

-- UA-Relations

isDenumerableᴰ : ∀ ℓ → DUARel (𝒮-type (Type ℓ)) isDenumerable _
isDenumerableᴰ ℓ
  = 𝒮ᴰ-subtype (𝒮-type (Type ℓ)) λ A → isDenumerable A , squash

isCountable'ᴰ : ∀ ℓ → DUARel (𝒮-type (Type ℓ)) isCountable' _
isCountable'ᴰ ℓ
  = 𝒮ᴰ-subtype (𝒮-type (Type ℓ)) λ A → isCountable' A , squash

isCountableᴰ : ∀ ℓ → DUARel (𝒮-type (Type ℓ)) isCountable _
isCountableᴰ ℓ
  = 𝒮ᴰ-subtype (𝒮-type (Type ℓ))
      λ A → isCountable A , isCountableIsProp

isCountablyIndexedᴰ : ∀ ℓ → DUARel (𝒮-type (Type ℓ)) isCountablyIndexed _
isCountablyIndexedᴰ ℓ
  = 𝒮ᴰ-subtype (𝒮-type (Type ℓ)) λ A → isCountablyIndexed A , squash
