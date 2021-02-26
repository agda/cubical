{-# OPTIONS --cubical --safe --no-import-sorts #-}

module Cubical.Displayed.Countable where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat.Lower as Nat
open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Unit as Unit

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

[_]-Listing : Mono → Type ℓ → Type ℓ
[ m ]-Listing A = Lower m ≃ A

isCountable' : Type ℓ → Type ℓ
isCountable' A = ∥ Σ[ m ∈ Mono ] [ m ]-Listing A ∥

isCountable : Type ℓ → Type ℓ
isCountable A = Σ[ m ∈ Mono ] ∥ [ m ]-Listing A ∥

isCountableIsProp : isProp (isCountable A)
isCountableIsProp (m , l) (n , r)
    = ΣPathP (m≡n , isOfHLevel→isOfHLevelDep 1 (λ _ → squash) l r m≡n)
  where
  m≡n : m ≡ n
  m≡n = rec2 (MonoIsSet m n)
          (λ e1 e2 → Lower-inj (ua (compEquiv e1 (invEquiv e2))))
          l r

isCountable'→isCountable : isCountable' A → isCountable A
isCountable'→isCountable = PT.rec isCountableIsProp (map-snd ∣_∣)

CountableIndexing : Type ℓ → Type ℓ
CountableIndexing A = Σ[ f ∈ (ℕ → Maybe A) ] ∀ x → ∥ fiber f (just x) ∥

isCountablyIndexed : Type ℓ → Type ℓ
isCountablyIndexed A = ∥ CountableIndexing A ∥

Denumeration→[∞]-Listing : Denumeration A → [ ∞ ]-Listing A
Denumeration→[∞]-Listing = compEquiv Lower∞≃ℕ

[∞]-Listing→Denumeration : [ ∞ ]-Listing A → Denumeration A
[∞]-Listing→Denumeration = compEquiv (invEquiv Lower∞≃ℕ)

isDenumerable→isCountable : isDenumerable A → isCountable' A
isDenumerable→isCountable = map (_,_ ∞ ∘ Denumeration→[∞]-Listing)

Listing→CountableIndexing : ∀ m → [ m ]-Listing A → CountableIndexing A
Listing→CountableIndexing {A = A} m (g , eg) = f , ∣_∣ ∘ fib
  where
  ix : (n : ℕ) → Dec (Bool→Type (m .fst n)) → Maybe A
  ix n (no _) = nothing
  ix n (yes mn) = just (g (n , mn))

  dbn : (n : ℕ) → Dec (Bool→Type (m .fst n))
  dbn n with m .fst n
  ... |  true = yes _
  ... | false = no (idfun ⊥)

  dyes : ∀ n → (mn : Bool→Type (m .fst n)) → dbn n ≡ yes mn
  dyes n mn with m .fst n
  ... | true = refl

  f : (n : ℕ) → Maybe A
  f n = ix n (dbn n)

  fib : ∀ x → fiber f (just x)
  fib x with eg .equiv-proof x .fst
  ... | ((n , mn) , p) = λ where
      .fst → n
      .snd → cong (ix n) (dyes n mn) ∙ cong just p

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
