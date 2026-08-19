module Cubical.Algebra.OrderedCommRing.Instances.Fast.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order as ℕ using () renaming (_≤_ to _≤ℕ_ ; _<_ to _<ℕ_)
import Cubical.Data.Nat.Order.Inductive as ℕ
open import Cubical.Data.Fast.Int as ℤ
  renaming (_+_ to _+ℤ_ ; _-_ to _-ℤ_; -_ to -ℤ_ ; _·_ to _·ℤ_)
open import Cubical.Data.Fast.Int.Order
  renaming (_<_ to _<ℤ_ ; _≤_ to _≤ℤ_)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Fast.Int

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Morphisms

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Fast.Int

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Fast.Int

open import Cubical.Relation.Binary
open BinaryRelation

open CommRingStr
open OrderedCommRingStr
open PseudolatticeStr
open StrictOrderStr

ℤOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
fst ℤOrderedCommRing = ℤ
0r  (snd ℤOrderedCommRing) = 0
1r  (snd ℤOrderedCommRing) = 1
_+_ (snd ℤOrderedCommRing) = _+ℤ_
_·_ (snd ℤOrderedCommRing) = _·ℤ_
-_  (snd ℤOrderedCommRing) = -ℤ_
_<_ (snd ℤOrderedCommRing) = _<ℤ_
_≤_ (snd ℤOrderedCommRing) = _≤ℤ_
isOrderedCommRing (snd ℤOrderedCommRing) = isOrderedCommRingℤ
  where
    open IsOrderedCommRing

    isOrderedCommRingℤ : IsOrderedCommRing 0 1 _+ℤ_ _·ℤ_ -ℤ_ _<ℤ_ _≤ℤ_
    isOrderedCommRingℤ .isCommRing      = ℤCommRing .snd .isCommRing
    isOrderedCommRingℤ .isPseudolattice = ℤ≤Pseudolattice .snd .is-pseudolattice
    isOrderedCommRingℤ .isStrictOrder   = ℤ<StrictOrder .snd .isStrictOrder
    isOrderedCommRingℤ .<-≤-weaken      = λ _ _ → <-weaken
    isOrderedCommRingℤ .≤≃¬>            = λ x y →
      propBiimpl→Equiv isProp≤ (isProp¬ (y <ℤ x))
        (λ x≤y y<x → isIrrefl< (≤<-trans x≤y y<x))
        isAsym'<
    isOrderedCommRingℤ .+MonoR≤         = λ _ _ _ → ≤-+o
    isOrderedCommRingℤ .+MonoR<         = λ _ _ _ → <-+o
    isOrderedCommRingℤ .posSum→pos∨pos  = λ _ _ → ∣_∣₁ ∘ 0<+ _ _
    isOrderedCommRingℤ .<-≤-trans       = λ _ _ _ → <≤-trans
    isOrderedCommRingℤ .≤-<-trans       = λ _ _ _ → ≤<-trans
    isOrderedCommRingℤ .·MonoR≤         = λ _ _ _ → 0≤o→≤-·o
    isOrderedCommRingℤ .·MonoR<         = λ _ _ _ → 0<o→<-·o
    isOrderedCommRingℤ .0<1             = zero-<possuc

private
  variable
    ℓ ℓ' : Level

module CanonicalMonoFromℤ (R : OrderedCommRing ℓ ℓ') where

  open CanonicalHomFromℤ (OrderedCommRing→CommRing R)
  open OrderedCommRingTheory R

  private
    module R where
      open OrderedCommRingStr (snd R) public
      open RingTheory (OrderedCommRing→Ring R) using (fromℕ ; fromℤ) public

  1≤fromℕsuc : ∀ n → R.1r R.≤ R.fromℕ (suc n)
  1≤fromℕsuc zero    = R.is-refl R.1r
  1≤fromℕsuc (suc n) =
    subst (R._≤ R.fromℕ (suc (suc n))) (R.+IdL R.1r) (+Mono≤ _ _ _ _ 0≤1 (1≤fromℕsuc n))

  0<fromℕsuc : ∀ n → R.0r R.< R.fromℕ (suc n)
  0<fromℕsuc n = R.<-≤-trans _ _ _ R.0<1 (1≤fromℕsuc n)

  0≤fromℕ : ∀ n → R.0r R.≤ R.fromℕ n
  0≤fromℕ zero    = R.is-refl R.0r
  0≤fromℕ (suc n) = R.<-≤-weaken _ _ (0<fromℕsuc n)

  fromℕ-pres≤ᵗ : ∀ m n → m ℕ.≤ᵗ n → R.fromℕ m R.≤ R.fromℕ n
  fromℕ-pres≤ᵗ zero          n             t = 0≤fromℕ n
  fromℕ-pres≤ᵗ (suc zero)    (suc n)       t = 1≤fromℕsuc n
  fromℕ-pres≤ᵗ (suc (suc m)) (suc (suc n)) t =
    +MonoL≤ _ _ _ (fromℕ-pres≤ᵗ (suc m) (suc n) t)

  fromℕ-pres≤ : ∀ m n → m ≤ℕ n → R.fromℕ m R.≤ R.fromℕ n
  fromℕ-pres≤ m n = fromℕ-pres≤ᵗ m n ∘ ℕ.≤→≤ᵇ

  fromℕ-pres<ᵗ : ∀ m n → m ℕ.<ᵗ n → R.fromℕ m R.< R.fromℕ n
  fromℕ-pres<ᵗ zero          (suc n)       t = 0<fromℕsuc n
  fromℕ-pres<ᵗ (suc zero)    (suc (suc n)) t = <SumLeftPos R.1r _ (0<fromℕsuc n)
  fromℕ-pres<ᵗ (suc (suc m)) (suc (suc n)) t =
    +MonoL< _ _ _ (fromℕ-pres<ᵗ (suc m) (suc n) t)

  fromℕ-pres< : ∀ m n → m <ℕ n → R.fromℕ m R.< R.fromℕ n
  fromℕ-pres< m n = fromℕ-pres<ᵗ m n ∘ ℕ.<→<ᵇ

  fromℤ-pres≤ : ∀ m n → m ≤ℤ n → R.fromℤ m R.≤ R.fromℤ n
  fromℤ-pres≤ (pos m)    (pos n)    (pos≤pos p)       = fromℕ-pres≤ᵗ m n p
  fromℤ-pres≤ (negsuc m) (pos n)    negsuc≤pos        =
    R.is-trans≤ _ _ _ (0≤→-≤0 _ (0≤fromℕ (suc m))) (0≤fromℕ n)
  fromℤ-pres≤ (negsuc m) (negsuc n) (negsuc≤negsuc p) =
    -Flip≤ _ _ (fromℕ-pres≤ᵗ (suc n) (suc m) p)

  fromℤ-pres< : ∀ m n → m <ℤ n → R.fromℤ m R.< R.fromℤ n
  fromℤ-pres< (pos m)    (pos n)    (pos<pos p)       = fromℕ-pres<ᵗ m n p
  fromℤ-pres< (negsuc m) (pos n)    negsuc<pos        =
    R.<-≤-trans _ _ _ (0<→-<0 _ (0<fromℕsuc m)) (0≤fromℕ n)
  fromℤ-pres< (negsuc m) (negsuc n) (negsuc<negsuc p) =
    -Flip< _ _ (fromℕ-pres<ᵗ (suc n) (suc m) p)

  fromℤ-reflect< : ∀ m n → R.fromℤ m R.< R.fromℤ n → m <ℤ n
  fromℤ-reflect< m n fm<fn with m ≟ n
  ... | lt m<n = m<n
  ... | eq m≡n = ⊥.rec (R.is-irrefl _ (subst (R._< _) (cong R.fromℤ m≡n) fm<fn))
  ... | gt m>n = ⊥.rec (R.is-asym _ _ fm<fn (fromℤ-pres< n m m>n))

  isOCRHomFromℤ : IsOrderedCommRingHom (snd ℤOrderedCommRing) R.fromℤ (snd R)
  isOCRHomFromℤ .IsOrderedCommRingHom.isCommRingHom = isHomFromℤ
  isOCRHomFromℤ .IsOrderedCommRingHom.pres≤         = fromℤ-pres≤
  isOCRHomFromℤ .IsOrderedCommRingHom.reflect<      = fromℤ-reflect<

  isOCRMonoFromℤ : IsOrderedCommRingMono (snd ℤOrderedCommRing) R.fromℤ (snd R)
  isOCRMonoFromℤ .IsOrderedCommRingMono.isOrderedCommRingHom = isOCRHomFromℤ
  isOCRMonoFromℤ .IsOrderedCommRingMono.pres<                = fromℤ-pres<

  fromℤOCR : OrderedCommRingHom ℤOrderedCommRing R
  fst fromℤOCR = R.fromℤ
  snd fromℤOCR = isOCRHomFromℤ

  fromℤOCRMono : OrderedCommRingMono ℤOrderedCommRing R
  fst fromℤOCRMono = R.fromℤ
  snd fromℤOCRMono = isOCRMonoFromℤ

  isUniqueFromℤOCR : (φ : OrderedCommRingHom ℤOrderedCommRing R)
                   → ∀ n → R.fromℤ n ≡ fst φ n
  isUniqueFromℤOCR = isUniqueFromℤ ∘ OrderedCommRingHom→CommRingHom

  isUniqueFromℤOCRMono : (φ : OrderedCommRingMono ℤOrderedCommRing R)
                       → ∀ n → R.fromℤ n ≡ fst φ n
  isUniqueFromℤOCRMono = isUniqueFromℤ ∘ OrderedCommRingMono→CommRingHom

  isContrHom[ℤOCR,-] : isContr (OrderedCommRingHom ℤOrderedCommRing R)
  fst isContrHom[ℤOCR,-] = fromℤOCR
  snd isContrHom[ℤOCR,-] = OrderedCommRingHom≡ ∘ funExt ∘ isUniqueFromℤOCR

  isContrMono[ℤOCR,-] : isContr (OrderedCommRingMono ℤOrderedCommRing R)
  fst isContrMono[ℤOCR,-] = fromℤOCRMono
  snd isContrMono[ℤOCR,-] = OrderedCommRingMono≡ ∘ funExt ∘ isUniqueFromℤOCRMono
