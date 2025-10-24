module Cubical.Algebra.OrderedCommRing.Instances.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

import Cubical.Functions.Logic as L

open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Int as ℤ
  renaming (_+_ to _+ℤ_ ; _-_ to _-ℤ_; -_ to -ℤ_ ; _·_ to _·ℤ_)
open import Cubical.Data.Int.Order
  renaming (_<_ to _<ℤ_ ; _≤_ to _≤ℤ_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int

open import Cubical.Algebra.OrderedCommRing

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Int

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Int

open CommRingStr
open OrderedCommRingStr
open PseudolatticeStr
open StrictOrderStr

private
  lemma0<+ : ∀ x y → 0 <ℤ x +ℤ y → (0 <ℤ x) L.⊔′ (0 <ℤ y)
  lemma0<+ (pos zero)    (pos zero)    = ⊥.rec ∘ isIrrefl<
  lemma0<+ (pos zero)    (pos (suc n)) = ∣_∣₁ ∘ inr ∘ subst (0 <ℤ_) (sym $ pos0+ _)
  lemma0<+ (pos (suc m)) (pos n)       = λ _ → ∣ inl (suc-≤-suc zero-≤pos) ∣₁
  lemma0<+ (pos zero)    (negsuc n)    = ⊥.rec ∘ ¬pos≤negsuc ∘ subst (0 <ℤ_)
                                        (sym $ pos0+ (negsuc n))
  lemma0<+ (pos (suc m)) (negsuc n)    = λ _ → ∣ inl (suc-≤-suc zero-≤pos) ∣₁
  lemma0<+ (negsuc m)    (pos zero)    = ⊥.rec ∘ ¬pos≤negsuc
  lemma0<+ (negsuc m)    (pos (suc n)) = λ _ → ∣ inr (suc-≤-suc zero-≤pos) ∣₁
  lemma0<+ (negsuc m)    (negsuc n)    = ⊥.rec ∘ ¬pos≤negsuc ∘ subst (0 <ℤ_)
                                        (sym $ neg+ (suc m) (suc n))

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
        (λ ¬y<x → case x ≟ y return (λ _ → x ≤ℤ y) of λ {
          (lt x<y) → <-weaken x<y ;
          (eq x≡y) → subst (x ≤ℤ_) x≡y isRefl≤ ;
          (gt y<z) → ⊥.rec (¬y<x y<z) })
    isOrderedCommRingℤ .+MonoR≤         = λ _ _ z → ≤-+o {o = z}
    isOrderedCommRingℤ .+MonoR<         = λ _ _ z → <-+o {o = z}
    isOrderedCommRingℤ .posSum→pos∨pos  = lemma0<+
    isOrderedCommRingℤ .<-≤-trans       = λ _ _ _ → <≤-trans
    isOrderedCommRingℤ .≤-<-trans       = λ _ _ _ → ≤<-trans
    isOrderedCommRingℤ .·MonoR≤         = λ _ _ _ → 0≤o→≤-·o
    isOrderedCommRingℤ .·MonoR<         = λ _ _ _ → 0<o→<-·o
    isOrderedCommRingℤ .0<1             = isRefl≤
