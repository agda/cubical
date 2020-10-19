{-

Eilenberg–Mac Lane type K(G, 1)

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.EilenbergMacLane1.Properties where

open import Cubical.HITs.EilenbergMacLane1.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base

open import Cubical.HITs.PropositionalTruncation as PropTrunc using (∥_∥; ∣_∣; squash)
open import Cubical.HITs.SetTruncation as SetTrunc using (∥_∥₂; ∣_∣₂; squash₂)

-- Type quotients

private
  variable
    ℓG ℓ : Level

module _ (G : Group {ℓG}) where

  open Group G

  elimEq : {B : EM₁ G → Type ℓ}
           (Bprop : (x : EM₁ G) → isProp (B x))
           {x y : EM₁ G}
           (eq : x ≡ y)
           (bx : B x)
           (by : B y) →
           PathP (λ i → B (eq i)) bx by
  elimEq {B = B} Bprop {x = x} =
    J (λ y eq → ∀ bx by → PathP (λ i → B (eq i)) bx by) (λ bx by → Bprop x bx by)

  elimProp : {B : EM₁ G → Type ℓ}
             → ((x : EM₁ G) → isProp (B x))
             → B embase
             → (x : EM₁ G)
             → B x
  elimProp Bprop b embase = b
  elimProp Bprop b (emloop g i) = elimEq Bprop (emloop g) b b i
  elimProp Bprop b (emcomp g h i j) =
    isSet→isSetDep (λ x → isProp→isSet (Bprop x))
    (emloop g) (emloop (g + h)) (λ j → embase) (emloop h) (emcomp g h)
    (λ i → elimEq Bprop (emloop g) b b i)
    (λ i → elimEq Bprop (emloop (g + h)) b b i)
    (λ j → b) (λ j → elimEq Bprop (emloop h) b b j) i j
  elimProp Bprop b (emsquash x y p q r s i j k) =
    isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (isProp→isSet (Bprop x)))
    _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (emsquash x y p q r s) i j k
    where
      g = elimProp Bprop b

  elimProp2 : {C : EM₁ G → EM₁ G → Type ℓ}
            → ((x y : EM₁ G) → isProp (C x y))
            → C embase embase
            → (x y : EM₁ G)
            → C x y
  elimProp2 Cprop c = elimProp (λ x → isPropΠ (λ y → Cprop x y))
                               (elimProp (λ y → Cprop embase y) c)

  elimSet : {B : EM₁ G → Type ℓ}
          → ((x : EM₁ G) → isSet (B x))
          → (b : B embase)
          → ((g : Carrier) → PathP (λ i → B (emloop g i)) b b)
          → (x : EM₁ G)
          → B x
  elimSet Bset b bloop embase = b
  elimSet Bset b bloop (emloop g i) = bloop g i
  elimSet Bset b bloop (emcomp g h i j) =
    isSet→isSetDep Bset (emloop g) (emloop (g + h)) (λ j → embase) (emloop h) (emcomp g h)
      (bloop g) (bloop (g + h)) refl (bloop h) i j
  elimSet Bset b bloop (emsquash x y p q r s i j k) =
    isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (Bset x))
      _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (emsquash x y p q r s) i j k
    where
      g = elimSet Bset b bloop

  elim : {B : EM₁ G → Type ℓ}
       → ((x : EM₁ G) → isGroupoid (B x))
       → (b : B embase)
       → (bloop : (g : Carrier) → PathP (λ i → B (emloop g i)) b b)
       → ((g h : Carrier) → SquareP (λ i j → B (emcomp g h i j))
            (bloop g) (bloop (g + h)) (λ j → b) (bloop h))
       → (x : EM₁ G)
       → B x
  elim Bgpd b bloop bcomp embase = b
  elim Bgpd b bloop bcomp (emloop g i) = bloop g i
  elim Bgpd b bloop bcomp (emcomp g h i j) = bcomp g h i j
  elim Bgpd b bloop bcomp (emsquash x y p q r s i j k) =
     isOfHLevel→isOfHLevelDep 3 Bgpd
      _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (emsquash x y p q r s) i j k 
    where
      g = elim Bgpd b bloop bcomp

  rec : {B : Type ℓ}
      → isGroupoid B
      → (b : B)
      → (bloop : Carrier → b ≡ b)
      → ((g h : Carrier) → Square (bloop g) (bloop (g + h)) refl (bloop h))
      → (x : EM₁ G)
      → B
  rec Bgpd = elim (λ _ → Bgpd)


  rec' : {B : Type ℓ}
      → isGroupoid B
      → (b : B)
      → (bloop : Carrier → b ≡ b)
      → ((g h : Carrier) → (bloop g) ∙ (bloop h) ≡ bloop (g + h))
      → (x : EM₁ G)
      → B
  rec' Bgpd b bloop p = rec Bgpd b bloop sq
    where
      module _ (g h : Carrier) where
        abstract
          sq : Square (bloop g) (bloop (g + h)) refl (bloop h)
          sq =
            transport (sym (Square≡doubleComp (bloop g) (bloop (g + h)) refl (bloop h)))
                      (refl ∙∙ bloop g ∙∙ bloop h
                        ≡⟨ doubleCompPath-elim refl (bloop g) (bloop h) ⟩
                      (refl ∙ bloop g) ∙ bloop h
                        ≡⟨ cong (_∙ bloop h) (sym (lUnit (bloop g))) ⟩
                      bloop g ∙ bloop h
                        ≡⟨ p g h ⟩
                      bloop (g + h) ∎)


