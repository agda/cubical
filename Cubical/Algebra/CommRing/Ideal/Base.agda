{-
  This is mostly for convenience, when working with ideals
  (which are defined for general rings) in a commutative ring.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Ideal.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset renaming ( _∈_ to _∈p_ ; _⊆_ to _⊆p_
                                                  ; subst-∈ to subst-∈p )

open import Cubical.Functions.Logic

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; tt)
                             renaming ( --zero to ℕzero ; suc to ℕsuc
                                        _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-assoc to +ℕ-assoc ; +-comm to +ℕ-comm
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)

open import Cubical.Data.FinData hiding (rec ; elim)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Ideal renaming (IdealsIn to IdealsInRing)
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ : Level

module CommIdeal (R' : CommRing ℓ) where
 private R = fst R'
 open CommRingStr (snd R')
 open Sum (CommRing→Ring R')
 open CommRingTheory R'
 open RingTheory (CommRing→Ring R')

 record isCommIdeal (I : ℙ R) : Type ℓ where
  constructor
   makeIsCommIdeal
  field
   +Closed : ∀ {x y : R} → x ∈p I → y ∈p I → (x + y) ∈p I
   contains0 : 0r ∈p I
   ·Closed : ∀ {x : R} (r : R) → x ∈p I → r · x ∈p I

  ·RClosed :  ∀ {x : R} (r : R) → x ∈p I → x · r ∈p I
  ·RClosed r x∈pI = subst-∈p I (·Comm _ _) (·Closed r x∈pI)

 open isCommIdeal
 isPropIsCommIdeal : (I : ℙ R) → isProp (isCommIdeal I)
 +Closed (isPropIsCommIdeal I ici₁ ici₂ i) x∈pI y∈pI =
         I _ .snd (ici₁ .+Closed x∈pI y∈pI) (ici₂ .+Closed x∈pI y∈pI) i
 contains0 (isPropIsCommIdeal I ici₁ ici₂ i) = I 0r .snd (ici₁ .contains0) (ici₂ .contains0) i
 ·Closed (isPropIsCommIdeal I ici₁ ici₂ i) r x∈pI =
         I _ .snd (ici₁ .·Closed r x∈pI) (ici₂ .·Closed r x∈pI) i

 CommIdeal : Type (ℓ-suc ℓ)
 CommIdeal = Σ[ I ∈ ℙ R ] isCommIdeal I

 isSetCommIdeal : isSet CommIdeal
 isSetCommIdeal = isSetΣSndProp isSetℙ isPropIsCommIdeal

 --inclusion and containment of ideals
 _⊆_ : CommIdeal → CommIdeal → Type ℓ
 I ⊆ J = I .fst ⊆p J .fst

 infix 5 _∈_
 _∈_ : R → CommIdeal → Type ℓ
 x ∈ I = x ∈p I .fst

 subst-∈ : (I : CommIdeal) {x y : R} → x ≡ y → x ∈ I → y ∈ I
 subst-∈ I = subst-∈p (I .fst)

 CommIdeal≡Char : {I J : CommIdeal} → I ⊆ J → J ⊆ I → I ≡ J
 CommIdeal≡Char I⊆J J⊆I = Σ≡Prop isPropIsCommIdeal (⊆-extensionality _ _ (I⊆J , J⊆I))

 -Closed : (I : CommIdeal) (x : R)
         → x ∈ I → (- x) ∈ I
 -Closed I x x∈I = subst (_∈ I) (solve! R') (·Closed (snd I) (- 1r) x∈I)

 ∑Closed : (I : CommIdeal) {n : ℕ} (V : FinVec R n)
         → (∀ i → V i ∈ I) → ∑ V ∈ I
 ∑Closed I {n = zero} _ _ = I .snd .contains0
 ∑Closed I {n = suc n} V h = I .snd .+Closed (h zero) (∑Closed I (V ∘ suc) (h ∘ suc))

 0Ideal : CommIdeal
 fst 0Ideal x = (x ≡ 0r) , is-set _ _
 +Closed (snd 0Ideal) x≡0 y≡0 = cong₂ (_+_) x≡0 y≡0 ∙ +IdR _
 contains0 (snd 0Ideal) = refl
 ·Closed (snd 0Ideal) r x≡0 = cong (r ·_) x≡0 ∙ 0RightAnnihilates _

 1Ideal : CommIdeal
 fst 1Ideal x = ⊤
 +Closed (snd 1Ideal) _ _ = lift tt
 contains0 (snd 1Ideal) = lift tt
 ·Closed (snd 1Ideal) _ _ = lift tt

 contains1Is1 : (I : CommIdeal) → 1r ∈ I → I ≡ 1Ideal
 contains1Is1 I 1∈I = CommIdeal≡Char (λ _ _ → lift tt)
   λ x _ → subst-∈ I (·IdR _) (I .snd .·Closed x 1∈I) -- x≡x·1 ∈ I

IdealsIn : (R : CommRing ℓ) → Type _
IdealsIn R = CommIdeal.CommIdeal R

module _ {R : CommRing ℓ} where
  open CommRingStr (snd R)
  open isIdeal
  open CommIdeal R
  open isCommIdeal
  makeIdeal : (I : fst R → hProp ℓ)
              → (+-closed : {x y : fst R} → x ∈p I → y ∈p I → (x + y) ∈p I)
              → (0r-closed : 0r ∈p I)
              → (·-closedLeft : {x : fst R} → (r : fst R) → x ∈p I → r · x ∈p I)
              → IdealsIn R
  fst (makeIdeal I +-closed 0r-closed ·-closedLeft) = I
  +Closed (snd (makeIdeal I +-closed 0r-closed ·-closedLeft)) = +-closed
  contains0 (snd (makeIdeal I +-closed 0r-closed ·-closedLeft)) = 0r-closed
  ·Closed (snd (makeIdeal I +-closed 0r-closed ·-closedLeft)) = ·-closedLeft


  CommIdeal→Ideal : IdealsIn R → IdealsInRing (CommRing→Ring R)
  fst (CommIdeal→Ideal I) = fst I
  +-closed (snd (CommIdeal→Ideal I)) = +Closed (snd I)
  -closed (snd (CommIdeal→Ideal I)) =  λ x∈pI → subst-∈p (fst I) (solve! R)
                                                           (·Closed (snd I) (- 1r) x∈pI)
  0r-closed (snd (CommIdeal→Ideal I)) = contains0 (snd I)
  ·-closedLeft (snd (CommIdeal→Ideal I)) = ·Closed (snd I)
  ·-closedRight (snd (CommIdeal→Ideal I)) = λ r x∈pI →
                                             subst-∈p (fst I)
                                                   (·Comm r _)
                                                   (·Closed (snd I) r x∈pI)

  Ideal→CommIdeal : IdealsInRing (CommRing→Ring R) → IdealsIn R
  fst (Ideal→CommIdeal I) = fst I
  +Closed (snd (Ideal→CommIdeal I)) = +-closed (snd I)
  contains0 (snd (Ideal→CommIdeal I)) = 0r-closed (snd I)
  ·Closed (snd (Ideal→CommIdeal I)) = ·-closedLeft (snd I)
