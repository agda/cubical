{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.HomotopyGroups where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Data.Bool hiding (_≤_ ; _≥_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit

open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Truncation hiding (rec2 ; elim2)

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ : Level

-- Essentially proven as EH-π in Cubical.Homotopy.Loopspace
πGr-comm : (n : ℕ) (A : Pointed ℓ) → (a b : typ (πGr (suc n) A))
  → ·π (suc n) a b ≡ ·π (suc n) b a
πGr-comm n A = elim2 (λ _ _ → isSetPathImplicit) λ a b → cong ∣_∣₂ (EH n a b)

-- πAb n A = πₙ₊₂(A), as an abelian group
πAb : (n : ℕ) (A : Pointed ℓ) → AbGroup ℓ
πAb n A = Group→AbGroup (πGr (1 + n) A) (πGr-comm n A)

-- Corollary 7.3.13 in the HoTT book
ΩOfHLevelTrunc : (X : Pointed ℓ) (n : ℕ)
  → Ω (hLevelTrunc∙ (1 + n) X) ≡ hLevelTrunc∙ n (Ω X)
ΩOfHLevelTrunc X 0 = ua∙ (isoToEquiv (PathIdTruncIso 0)) refl
ΩOfHLevelTrunc X (suc n) =
  ua∙
  ( isoToEquiv (PathIdTruncIso (suc n)))
  ( cong ∣_∣ₕ (transportRefl refl))

ΩOfContrIsContr : (X : Pointed ℓ)
  → isContr (typ X) → isContr (typ (Ω X))
ΩOfContrIsContr X cntrX = isOfHLevelPath 0 cntrX (pt X) (pt X)

UnitGroupEquivUnit : GroupEquiv {ℓ-zero} {ℓ} UnitGroup₀ UnitGroup
UnitGroupEquivUnit =
  invGroupEquiv (contrGroupEquivUnit isContrUnit*)

UnitAbGroupEquiv : (G : AbGroup ℓ)
  → GroupEquiv {ℓ} {ℓ} (AbGroup→Group G) UnitGroup
  → AbGroupEquiv {ℓ} {ℓ} G UnitAbGroup
UnitAbGroupEquiv G (e , isHom-e) = e , isHom-e

-- Abelian homotopy groups of truncated spaces
Ω^OfHLevelTrunc : (X : Pointed ℓ) (n : ℕ)
  → isContr (typ ((Ω^ n) (hLevelTrunc∙ (1 + n) X)))
Ω^OfHLevelTrunc X zero =
  ∣ pt X ∣ₕ
  , (λ y → ( spoke (λ p → if p then ∣ pt X ∣ₕ else y) true) ⁻¹
            ∙ spoke (λ p → if p then ∣ pt X ∣ₕ else y) false)
Ω^OfHLevelTrunc X (suc n) =
  transport
  ( sym (λ i → isContr (typ ( ( flipΩPath n
                               ∙ cong (Ω^ n) (ΩOfHLevelTrunc X (1 + n)))
                               i))))
  ( Ω^OfHLevelTrunc (Ω X) n)

Ω^OfHLevelTrunc+ : (X : Pointed ℓ) (n k : ℕ)
  → isContr (typ ((Ω^ (k + n)) (hLevelTrunc∙ (1 + n) X)))
Ω^OfHLevelTrunc+ X n zero = Ω^OfHLevelTrunc X n
Ω^OfHLevelTrunc+ X n (suc k) =
  ΩOfContrIsContr
  ( (Ω^ (k + n)) (hLevelTrunc∙ (1 + n) X))
  ( Ω^OfHLevelTrunc+ X n k)

Ω^OfHLevelTrunc' : (X : Pointed ℓ) (n k : ℕ) → k ≥ n
  → isContr (typ ((Ω^ k) (hLevelTrunc∙ (1 + n) X)))
Ω^OfHLevelTrunc' X n k (x , p) =
 transport
 ( λ i → isContr (typ ((Ω^ (p i)) (hLevelTrunc∙ (suc n) X))))
 ( Ω^OfHLevelTrunc+ X n x)

πAbOfHLevelTrunc : (X : Pointed ℓ) (n k : ℕ) → k ≥ n
  → AbGroupEquiv {ℓ} {ℓ} (πAb k (hLevelTrunc∙ (3 + n) X)) UnitAbGroup
πAbOfHLevelTrunc X n k p =
  UnitAbGroupEquiv
  ( πAb k (hLevelTrunc∙ _ X))
  ( compGroupEquiv
    ( contrGroupEquivUnit
      ( isContr→isContrSetTrunc
        ( Ω^OfHLevelTrunc' X (2 + n) (2 + k) (≤-+ˡ p))))
    ( UnitGroupEquivUnit))

πAbOfHLevelTrunc' : (X : Pointed ℓ) (n k : ℕ) → k ≥ n
  → AbGroupEquiv {ℓ} {ℓ} (πAb (suc k) (hLevelTrunc∙ (3 + n) X)) UnitAbGroup
πAbOfHLevelTrunc' X n k p =
  πAbOfHLevelTrunc X n (1 + k) (≤-trans p ≤-sucℕ)
