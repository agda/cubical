{-

Eilenberg–Mac Lane type K(G, 1)

-}

{-# OPTIONS --cubical --no-import-sorts  --lossy-unification #-}
module Cubical.HITs.EilenbergMacLane1.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Functions.Morphism

open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ⊥-rec) hiding (elim)

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup.Base

open import Cubical.HITs.EilenbergMacLane1.Base


private
  variable
    ℓG ℓ : Level

module _ ((G , str) : Group ℓG) where

  open GroupStr str

  elimGroupoid :
   {B : EM₁ (G , str) → Type ℓ}
          → ((x : EM₁ (G , str)) → isGroupoid (B x))
          → (b : B embase)
          → (bloop : ((g : G) → PathP (λ i → B (emloop g i)) b b))
          → ((g h : G) → PathP (λ i → PathP (λ j → B (emcomp g h j i))
                                 (bloop g i) (bloop (g · h) i)) (λ _ → b) (bloop h))
          → (x : EM₁ (G , str))
          → B x
  elimGroupoid Bgroup b bloop bcomp embase = b
  elimGroupoid Bgroup b bloop bcomp (emloop x i) = bloop x i
  elimGroupoid Bgroup b bloop bcomp (emcomp g h j i) = bcomp g h i j
  elimGroupoid {B = B} Bgroup b bloop bcomp (emsquash g h p q r s i j k) = help i j k
    where
    help : PathP (λ i → PathP (λ j → PathP (λ k → B (emsquash g h p q r s i j k))
                 (elimGroupoid Bgroup b bloop bcomp g)
                 (elimGroupoid Bgroup b bloop bcomp h))
                 (λ k → elimGroupoid Bgroup b bloop bcomp (p k))
                 λ k → elimGroupoid Bgroup b bloop bcomp (q k))
                 (λ j k → elimGroupoid Bgroup b bloop bcomp (r j k))
                 λ j k → elimGroupoid Bgroup b bloop bcomp (s j k)
    help = toPathP (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (Bgroup _) _ _) _ _ _ _)

  elimSet : {B : EM₁ (G , str) → Type ℓ}
          → ((x : EM₁ (G , str)) → isSet (B x))
          → (b : B embase)
          → ((g : G) → PathP (λ i → B (emloop g i)) b b)
          → (x : EM₁ (G , str))
          → B x
  elimSet Bset b bloop embase = b
  elimSet Bset b bloop (emloop g i) = bloop g i
  elimSet Bset b bloop (emcomp g h i j) =
    isSet→SquareP
      (λ i j → Bset (emcomp g h i j))
      (λ j → bloop g j) (λ j → bloop (g · h) j)
      (λ i → b) (λ i → bloop h i)
      i j
  elimSet Bset b bloop (emsquash x y p q r s i j k) =
    isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (Bset x))
      _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (emsquash x y p q r s) i j k
    where
      g = elimSet Bset b bloop

  elimProp : {B : EM₁ (G , str) → Type ℓ}
             → ((x : EM₁ (G , str)) → isProp (B x))
             → B embase
             → (x : EM₁ (G , str))
             → B x
  elimProp Bprop b x =
    elimSet
      (λ x → isProp→isSet (Bprop x))
      b
      (λ g → isProp→PathP (λ i → Bprop ((emloop g) i)) b b)
      x

  elimProp2 : {C : EM₁ (G , str) → EM₁ (G , str) → Type ℓ}
    → ((x y : EM₁ (G , str)) → isProp (C x y))
    → C embase embase
    → (x y : EM₁ (G , str))
    → C x y
  elimProp2 Cprop c =
    elimProp
      (λ x → isPropΠ (λ y → Cprop x y))
      (elimProp (λ y → Cprop embase y) c)

  elim : {B : EM₁ (G , str) → Type ℓ}
       → ((x : EM₁ (G , str)) → isGroupoid (B x))
       → (b : B embase)
       → (bloop : (g : G) → PathP (λ i → B (emloop g i)) b b)
       → ((g h : G) → SquareP (λ i j → B (emcomp g h i j))
            (bloop g) (bloop (g · h)) (λ j → b) (bloop h))
       → (x : EM₁ (G , str))
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
      → (bloop : G → b ≡ b)
      → ((g h : G) → Square (bloop g) (bloop (g · h)) refl (bloop h))
      → (x : EM₁ (G , str))
      → B
  rec Bgpd = elim (λ _ → Bgpd)

  rec' : {B : Type ℓ}
      → isGroupoid B
      → (b : B)
      → (bloop : G → b ≡ b)
      → ((g h : G) → bloop (g · h) ≡ bloop g ∙ bloop h)
      → (x : EM₁ (G , str))
      → B
  rec' Bgpd b bloop square =
    rec Bgpd b bloop
      (λ g h →  compPath→Square (withRefl g h))
    where withRefl : (g h : G)
                   → refl ∙ bloop (g · h) ≡ bloop g ∙ bloop h
          withRefl g h =
            refl ∙ bloop (g · h) ≡⟨ sym (lUnit (bloop (g · h))) ⟩
            bloop (g · h)        ≡⟨ square g h ⟩
            bloop g ∙ bloop h ∎
