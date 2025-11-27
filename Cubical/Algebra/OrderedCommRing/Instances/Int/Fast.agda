module Cubical.Algebra.OrderedCommRing.Instances.Int.Fast where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Int.Fast as ℤ
  renaming (_+_ to _+ℤ_ ; _-_ to _-ℤ_; -_ to -ℤ_ ; _·_ to _·ℤ_)
open import Cubical.Data.Int.Fast.Order
  renaming (_<_ to _<ℤ_ ; _≤_ to _≤ℤ_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int.Fast

open import Cubical.Algebra.OrderedCommRing

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Int.Fast

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Int.Fast

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
    isOrderedCommRingℤ .<-≤-weaken      = λ x y → <-weaken {x} {y}
    isOrderedCommRingℤ .≤≃¬>            = λ x y →
      propBiimpl→Equiv (isProp≤ {x} {y}) (isProp¬ (y <ℤ x))
        (λ x≤y y<x → isIrrefl< (≤<-trans {x} {y} x≤y y<x))
        (λ ¬y<x → case x ≟ y return (λ _ → x ≤ℤ y) of λ {
          (lt x<y) → <-weaken {x} {y} x<y ;
          (eq x≡y) → subst (x ≤ℤ_) x≡y isRefl≤ ;
          (gt y<z) → ⊥.rec (¬y<x y<z) })
    isOrderedCommRingℤ .+MonoR≤         = λ x y z → ≤-+o {x} {y} {z}
    isOrderedCommRingℤ .+MonoR<         = λ x y z → <-+o {x} {y} {z}
    isOrderedCommRingℤ .posSum→pos∨pos  = λ _ _ → ∣_∣₁ ∘ 0<+ _ _
    isOrderedCommRingℤ .<-≤-trans       = λ x y z → <≤-trans {x} {y} {z}
    isOrderedCommRingℤ .≤-<-trans       = λ x y z → ≤<-trans {x} {y} {z}
    isOrderedCommRingℤ .·MonoR≤         = λ x y z → 0≤o→≤-·o {z} {x} {y}
    isOrderedCommRingℤ .·MonoR<         = λ x y z → 0<o→<-·o {z} {x} {y}
    isOrderedCommRingℤ .0<1             = isRefl≤
