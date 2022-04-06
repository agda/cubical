{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRing.CohomologyRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Properties
open import Cubical.Algebra.Ring

open import Cubical.Algebra.Direct-Sum.Base
open import Cubical.Algebra.AbGroup.Instances.Direct-Sum
open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.Polynomials.Multivariate.Properties

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level


-----------------------------------------------------------------------------
-- Lemma

ConstsubstCommSlice : {A : Type ℓ}
                   → (B : A → Type ℓ')
                   → (C : Type ℓ')
                   → (F : ∀ a → B a → C)
                   → {x y : A} (p : x ≡ y) (u : B x)
                   →  (F x u) ≡ F y (subst B p u)
ConstsubstCommSlice B C F p Bx = (sym (transportRefl (F _ Bx)) ∙ substCommSlice B (λ _ → C) F p Bx) 

-----------------------------------------------------------------------------
-- Definition Cohomology Ring


H*AbGr : (A : Type ℓ) → AbGroup ℓ
H*AbGr A = ⊕-AbGr ℕ (λ n → coHom n A) (λ n → snd (coHomGroup n A))

H* : (A : Type ℓ) → Type ℓ
H* A = fst (H*AbGr A)

module _ (A : Type ℓ) where

  open AbGroupStr (snd (H*AbGr A))
  open AbGroupTheory (H*AbGr A)
  
  _cup_ : H* A → H* A → H* A
  _cup_ = DS-Rec-Set.f ℕ (λ n → coHom n A) (λ n → snd (coHomGroup n A))
          (H* A → H* A)
          (λ f g p q i j x → is-set (f x) (g x) (λ X → p X x) (λ X → q X x) i j)
          -- elements
          (λ x → 0g)
          (λ n a → DS-Rec-Set.f ℕ _ _ (H* A) is-set
                    -- elements
                    0g
                    (λ m b → base (n +' m) (a ⌣ b))
                    _+_
                    -- equations
                    assoc
                    rid
                    comm
                    (λ m → (cong (base (n +' m)) (⌣-0ₕ n m a)) ∙ (base-neutral (n +' m)))
                    λ m b c → base-add (n +' m) (a ⌣ b) (a ⌣ c) ∙ cong (base (n +' m)) (sym (leftDistr-⌣ n m a b c)))
          (λ U V y → (U y) + (V y))
          -- equations
          (λ xs ys zs i y → assoc (xs y) (ys y) (zs y) i)
          (λ xs i y       → rid (xs y) i)
          (λ xs ys i y    → comm (xs y) (ys y) i)
          (λ n → funExt(
                  DS-Ind-Prop.f ℕ _ _ _ (λ _ → is-set _ _)
                  refl
                  (λ m b → cong (base (n +' m)) (0ₕ-⌣ n m b) ∙ base-neutral (n +' m))
                  λ {U V} ind-U ind-V → (cong₂ _+_ ind-U ind-V) ∙ (rid 0g)))
          λ n a b → funExt (
                     DS-Ind-Prop.f ℕ _ _ _ (λ _ → is-set _ _)
                     (rid 0g)
                     (λ m c → (base-add (n +' m) (a ⌣ c) (b ⌣ c)) ∙ (cong (base (n +' m)) (sym (rightDistr-⌣ n m a b c))))
                     λ {U V} ind-U ind-V → comm-4 _ _ _ _ ∙ cong₂ _+_ ind-U ind-V)

  1H* : H* A
  1H* = base 0 1⌣

  cup-assoc : (x y z : H* A) → x cup (y cup z) ≡ (x cup y) cup z
  cup-assoc = DS-Ind-Prop.f ℕ _ _ _
              (λ x p q i y z j → is-set _ _ (p y z) (q y z) i j)
              (λ y z → refl)
              (λ n a → DS-Ind-Prop.f ℕ _ _ _
                        (λ y p q i z j → is-set _ _ (p z) (q z) i j)
                        (λ z → refl)
                        (λ m b → DS-Ind-Prop.f ℕ _ _ _ (λ _ → is-set _ _)
                                  refl
                                  (λ k c → (cong (base (n +' (m +' k))) (assoc-⌣ n m k a b c))
                                             ∙ sym (ConstsubstCommSlice (λ n → coHom n A) (H* A) base (sym (+'-assoc n m k)) ((a ⌣ b) ⌣ c)))
                                  λ {U V} ind-U ind-V → cong₂ _+_ ind-U ind-V)
                        λ {U V} ind-U ind-V z → cong₂ _+_ (ind-U z) (ind-V z))
              λ {U V} ind-U ind-V y z → cong₂ _+_ (ind-U y z) (ind-V y z)

  cup-rid : (x : H* A) → x cup 1H* ≡ x
  cup-rid = DS-Ind-Prop.f ℕ _ _ _ (λ _ → is-set _ _)
            refl
            (λ n a → (cong (base (n +' 0)) (lUnit⌣ n a)) ∙ sym (ConstsubstCommSlice (λ n → coHom n A) (H* A) base (sym (n+'0 n)) a))
            λ {U V} ind-U ind-V → (cong₂ _+_ ind-U ind-V)

  cup-lid : (x : H* A) → 1H* cup x ≡ x
  cup-lid = DS-Ind-Prop.f ℕ _ _ _ (λ _ → is-set _ _)
            refl
            (λ n a → cong (base n) (rUnit⌣ n a))
            (λ {U V} ind-U ind-V → cong₂ _+_ ind-U ind-V)

  cup-rdistr : (x y z : H* A) → x cup (y + z) ≡ (x cup y) + (x cup z)
  cup-rdistr = DS-Ind-Prop.f ℕ _ _ _
               (λ x p q i y z j → is-set _ _ (p y z) (q y z) i j)
               (λ y z → sym (rid 0g))
               (λ n a y z → refl)
               λ {U V} ind-U ind-V y z → cong₂ _+_ (ind-U y z) (ind-V y z) ∙ comm-4 (U cup y) (U cup z) (V cup y) (V cup z)

  cup-ldistr : (x y z : H* A) → (x + y) cup z ≡ (x cup z) + (y cup z)
  cup-ldistr = λ x y z → refl

  H*R : Ring ℓ
  fst H*R = H* A
  RingStr.0r (snd H*R) = 0g
  RingStr.1r (snd H*R) = 1H*
  RingStr._+_ (snd H*R) = _+_
  RingStr._·_ (snd H*R) = _cup_
  RingStr.- snd H*R = -_
  RingStr.isRing (snd H*R) = makeIsRing is-set
                                        assoc rid (λ x → fst (inverse x)) comm
                                        cup-assoc cup-rid cup-lid cup-rdistr cup-ldistr

-----------------------------------------------------------------------------
-- Graded Comutative Ring

-- def -1^(nm) using Even or Odd
-- then transporting the proofs
-- +lemma get -1^ out 

  gradCommRing : (n m : ℕ) → (a : coHom n A) → (b : coHom m A) → (base n a) cup (base m b) ≡ (base m b) cup (base n a)
  gradCommRing = {!!}

