{-

Inductive eliminators to establish properties of all finite sets directly

-}
{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.Induction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.SetTruncation as Set

open import Cubical.Data.Nat
  renaming (_+_ to _+ℕ_) hiding (elim)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum

open import Cubical.Data.Fin renaming (Fin to Finℕ)
open import Cubical.Data.SumFin
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.FinSet.Constructors

private
  variable
    ℓ ℓ' : Level

-- definitions mimicking that of natural numbers

module _
  {ℓ : Level} where

  𝟘 : FinSet ℓ
  𝟘 = ⊥* , 0 , ∣ uninhabEquiv Empty.rec* Empty.rec ∣

  𝟙 : FinSet ℓ
  𝟙 = Unit* , isContr→isFinSet (isContrUnit*)

  _+_ : FinSet ℓ → FinSet ℓ → FinSet ℓ
  X + Y = X .fst ⊎ Y .fst , isFinSet⊎ X Y

  -- 𝔽in can be seen as a universe polymorphic version of SumFin
  𝔽in : ℕ → FinSet ℓ
  𝔽in 0 = 𝟘
  𝔽in (suc n) = 𝟙 + 𝔽in n

  -- useful properties

  𝟘≃Empty : 𝟘 .fst ≃ ⊥
  𝟘≃Empty = uninhabEquiv rec* (λ x → x)

  𝟙≃Unit : 𝟙 .fst ≃ Unit
  𝟙≃Unit = isContr→≃Unit (isContrUnit*)

  * : {n : ℕ} → 𝔽in (suc n) .fst
  * = inl tt*

  𝔽in≃Fin : (n : ℕ) → 𝔽in n .fst ≃ Fin n
  𝔽in≃Fin 0 = 𝟘≃Empty
  𝔽in≃Fin (suc n) = ⊎-equiv 𝟙≃Unit (𝔽in≃Fin n)

  𝔽in≃Finℕ : (n : ℕ) → 𝔽in n .fst ≃ Finℕ n
  𝔽in≃Finℕ n = 𝔽in≃Fin n ⋆ SumFin≃Fin n

  -- 𝔽in preserves addition

  𝟘+X≡X : {X : FinSet ℓ} → 𝟘 + X ≡ X
  𝟘+X≡X {X = X} i .fst = ua (⊎-swap-≃ ⋆ ⊎-equiv (idEquiv (X .fst)) 𝟘≃Empty ⋆ ⊎-⊥-≃) i
  𝟘+X≡X {X = X} i .snd =
    isProp→PathP {B = λ i → isFinSet (𝟘+X≡X {X = X} i .fst)}
                 (λ _ → isPropIsFinSet) ((𝟘 + X) .snd) (X .snd) i

  𝔽in1≡𝟙 : 𝔽in 1 ≡ 𝟙
  𝔽in1≡𝟙 i .fst = ua (⊎-equiv (idEquiv (𝟙 .fst)) 𝟘≃Empty ⋆ ⊎-⊥-≃) i
  𝔽in1≡𝟙 i .snd =
    isProp→PathP {B = λ i → isFinSet (𝔽in1≡𝟙 i .fst)}
                 (λ _ → isPropIsFinSet) (𝔽in 1 .snd) (𝟙 .snd) i

  𝔽in+ : (m n : ℕ) → 𝔽in m + 𝔽in n ≡ 𝔽in (m +ℕ n)
  𝔽in+ 0 n = 𝟘+X≡X
  𝔽in+ (suc m) n i .fst = (ua (⊎-assoc-≃) ∙ (λ i → (𝟙 + 𝔽in+ m n i) .fst)) i
  𝔽in+ (suc m) n i .snd =
    isProp→PathP {B = λ i → isFinSet (𝔽in+ (suc m) n i .fst)}
                 (λ _ → isPropIsFinSet) ((𝔽in (suc m) + 𝔽in n) .snd) (𝔽in (suc m +ℕ n) .snd) i

-- every finite sets are merely equal to some 𝔽in

∣≡𝔽in∣ : (X : FinSet ℓ) → ∥ Σ[ n ∈ ℕ ] X ≡ 𝔽in n ∥
∣≡𝔽in∣ X = Prop.map (λ (n , p) → n , path X (n , p)) (isFinSet→isFinSet' (X .snd))
  where
    path : (X : FinSet ℓ) → ((n , _) : isFinOrd (X .fst)) → X ≡ 𝔽in n
    path X (n , p) i .fst = ua (p ⋆ invEquiv (𝔽in≃Fin n)) i
    path X (n , p) i .snd =
      isProp→PathP {B = λ i → isFinSet (path X (n , p) i .fst)}
                   (λ _ → isPropIsFinSet) (X .snd) (𝔽in n .snd) i

-- the eliminators

module _
  (P : FinSet ℓ → Type ℓ')
  (h : (X : FinSet ℓ) → isProp (P X)) where

  module _
    (p : (n : ℕ) → P (𝔽in n)) where

    elimProp : (X : FinSet ℓ) → P X
    elimProp X = Prop.rec (h X) (λ (n , q) → transport (λ i → P (q (~ i))) (p n)) (∣≡𝔽in∣ X)

  module _
    (p0 : P 𝟘)
    (p1 : {X : FinSet ℓ} → P X → P (𝟙 + X)) where

    elimProp𝔽in : (n : ℕ) → P (𝔽in n)
    elimProp𝔽in 0 = p0
    elimProp𝔽in (suc n) = p1 (elimProp𝔽in n)

    elimProp𝟙+ : (X : FinSet ℓ) → P X
    elimProp𝟙+ = elimProp elimProp𝔽in

  module _
    (p0 : P 𝟘)(p1 : P 𝟙)
    (p+ : {X Y : FinSet ℓ} → P X → P Y → P (X + Y)) where

    elimProp+ : (X : FinSet ℓ) → P X
    elimProp+ = elimProp𝟙+ p0 (λ p → p+ p1 p)
