{-
  This is mostly for convenience, when working with ideals
  (which are defined for general rings) in a commutative ring.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Ideal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Ring.Ideal renaming (IdealsIn to IdealsInRing)
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.RingSolver.ReflectionSolving

private
  variable
    ℓ : Level

IdealsIn : (R : CommRing ℓ) → Type _
IdealsIn R = IdealsInRing (CommRing→Ring R)

module _ (Ring@(R , str) : CommRing ℓ) where
  open CommRingStr str
  makeIdeal : (I : R → hProp ℓ)
              → (+-closed : {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I)
              → (0r-closed : 0r ∈ I)
              → (·-closedLeft : {x : R} → (r : R) → x ∈ I → r · x ∈ I)
              → IdealsIn (R , str)
  makeIdeal I +-closed 0r-closed ·-closedLeft = I ,
    (record
       { +-closed = +-closed
       ; -closed = λ x∈I → subst-∈ I (useSolver _)
                             (·-closedLeft (- 1r) x∈I)
       ; 0r-closed = 0r-closed
       ; ·-closedLeft = ·-closedLeft
       ; ·-closedRight = λ r x∈I →
                       subst-∈ I
                             (·-comm r _)
                             (·-closedLeft r x∈I)
       })
       where useSolver : (x : R) → - 1r · x ≡ - x
             useSolver = solve Ring


-- better?
module _ (R' : CommRing ℓ) where
 private R = fst R'
 open CommRingStr (snd R')
 open Sum (CommRing→Ring R')

 record isCommIdeal (I : ℙ R) : Type ℓ where
  constructor
   makeIsCommIdeal
  field
   +Closed : ∀ {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I
   contains0 : 0r ∈ I
   ·Closed : ∀ {x : R} (r : R) → x ∈ I → r · x ∈ I

 open isCommIdeal
 isPropIsCommIdeal : (I : ℙ R) → isProp (isCommIdeal I)
 +Closed (isPropIsCommIdeal I ici₁ ici₂ i) x∈I y∈I =
         I _ .snd (ici₁ .+Closed x∈I y∈I) (ici₂ .+Closed x∈I y∈I) i
 contains0 (isPropIsCommIdeal I ici₁ ici₂ i) = I 0r .snd (ici₁ .contains0) (ici₂ .contains0) i
 ·Closed (isPropIsCommIdeal I ici₁ ici₂ i) r x∈I =
         I _ .snd (ici₁ .·Closed r x∈I) (ici₂ .·Closed r x∈I) i

 CommIdeal : Type _
 CommIdeal = Σ[ I ∈ ℙ R ] isCommIdeal I

 ∑Closed : (I : CommIdeal) {n : ℕ} (V : FinVec R n)
         → (∀ i → V i ∈ fst I) → ∑ V ∈ fst I
 ∑Closed I {n = zero} _ _ = I .snd .contains0
 ∑Closed I {n = suc n} V h = I .snd .+Closed (h zero) (∑Closed I (V ∘ suc) (h ∘ suc))
