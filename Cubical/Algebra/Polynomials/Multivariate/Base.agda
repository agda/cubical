{-# OPTIONS --safe #-}
module Cubical.Algebra.Polynomials.Multivariate.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_)
open import Cubical.Data.Vec

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

private variable
  ℓ ℓ' : Level

module _ (A' : CommRing ℓ) where
  private
    A = fst A'
  open CommRingStr (snd A')

-----------------------------------------------------------------------------
-- Definition

  data Poly (n : ℕ) : Type ℓ where
    -- elements
    0P     : Poly n
    base   : (v : Vec ℕ n) → (a : A) → Poly n
    _poly+_  : (P : Poly n) → (Q : Poly n) → Poly n
      -- AbGroup eq
    poly+Assoc : (P Q R : Poly n) → P poly+ (Q poly+ R) ≡ (P poly+ Q) poly+ R
    poly+IdR   : (P : Poly n) → P poly+ 0P ≡ P
    poly+Comm  : (P Q : Poly n) → P poly+ Q ≡ Q poly+ P
      -- Base eq
    base-0P : (v : Vec ℕ n) → base v 0r ≡ 0P
    base-poly+     : (v : Vec ℕ n) → (a b : A) → (base v a) poly+ (base v b) ≡ base v (a + b)
      -- Set Trunc
    trunc : isSet(Poly n)

-----------------------------------------------------------------------------
-- Induction and Recursion

module _ (A' : CommRing ℓ) where
  private
    A = fst A'
  open CommRingStr (snd A')

  module Poly-Ind-Set
    -- types
    (n : ℕ)
    (F : (P : Poly A' n) → Type ℓ')
    (issd : (P : Poly A' n) → isSet (F P))
    -- elements
    (0P* : F 0P)
    (base* : (v : Vec ℕ n) → (a : A) → F (base v a))
    (_poly+*_ : {P Q : Poly A' n} → (PS : F P) → (QS : F Q) → F (P poly+ Q))
    -- AbGroup eq
    (poly+Assoc* : {P Q R : Poly A' n} → (PS : F P) → (QS : F Q) → (RS : F R)
                    → PathP (λ i → F (poly+Assoc P Q R i)) (PS poly+* (QS poly+* RS)) ((PS poly+* QS) poly+* RS))
    (poly+IdR*   : {P : Poly A' n} → (PS : F P) →
                   PathP (λ i → F (poly+IdR P i)) (PS poly+* 0P*) PS)
    (poly+Comm*  : {P Q : Poly A' n} → (PS : F P) → (QS : F Q)
                    → PathP (λ i → F (poly+Comm P Q i)) (PS poly+* QS) (QS poly+* PS))
    -- Base eq
    (base-0P* : (v : Vec ℕ n) → PathP (λ i → F (base-0P v i)) (base* v 0r) 0P*)
    (base-poly+*     : (v : Vec ℕ n) → (a b : A)
                     → PathP (λ i → F (base-poly+ v a b i)) ((base* v a) poly+* (base* v b)) (base* v (a + b)))
    where

    f : (P : Poly A' n) → F P
    f 0P = 0P*
    f (base v a) = base* v a
    f (P poly+ Q) = (f P) poly+* (f Q)
    f (poly+Assoc P Q R i) = poly+Assoc* (f P) (f Q) (f R) i
    f (poly+IdR P i) = poly+IdR* (f P) i
    f (poly+Comm P Q i) = poly+Comm* (f P) (f Q) i
    f (base-0P v i) = base-0P* v i
    f (base-poly+ v a b i) = base-poly+* v a b i
    f (trunc P Q p q i j) = isOfHLevel→isOfHLevelDep 2 issd  (f P) (f Q) (cong f p) (cong f q) (trunc P Q p q) i j


  module Poly-Rec-Set
    -- types
    (n  : ℕ)
    (B  : Type ℓ')
    (iss : isSet B)
    -- elements
    (0P*      : B)
    (base*    : (v : Vec ℕ n) → (a : A) → B)
    (_poly+*_ : B → B → B)
    -- AbGroup eq
    (poly+Assoc* : (PS QS RS : B) → (PS poly+* (QS poly+* RS)) ≡ ((PS poly+* QS) poly+* RS))
    (poly+IdR*   : (PS : B)       → (PS poly+* 0P*) ≡  PS)
    (poly+Comm*  : (PS QS : B)    → (PS poly+* QS) ≡ (QS poly+* PS))
    -- Base eq
    (base-0P* : (v : Vec ℕ n) → (base* v 0r) ≡  0P*)
    (base-poly+*     : (v : Vec ℕ n) → (a b : A) → ((base* v a) poly+* (base* v b)) ≡ (base* v (a + b)))
    where

    f : Poly A' n → B
    f = Poly-Ind-Set.f n (λ _ → B) (λ _ → iss) 0P* base* _poly+*_ poly+Assoc* poly+IdR* poly+Comm* base-0P* base-poly+*


  module Poly-Ind-Prop
    -- types
    (n : ℕ)
    (F : (P : Poly A' n) → Type ℓ')
    (ispd : (P : Poly A' n) → isProp (F P))
    -- elements
    (0P* : F 0P)
    (base* : (v : Vec ℕ n) → (a : A) → F (base v a))
    (_poly+*_ : {P Q : Poly A' n} → (PS : F P) → (QS : F Q) → F (P poly+ Q))
    where

    f : (P : Poly A' n) → F P
    f = Poly-Ind-Set.f n F (λ P → isProp→isSet (ispd P)) 0P* base* _poly+*_
          (λ {P Q R} PS QS RQ → toPathP (ispd _ (transport (λ i → F (poly+Assoc P Q R i)) _) _))
          (λ {P} PS           → toPathP (ispd _ (transport (λ i → F (poly+IdR P i))       _) _))
          (λ {P Q} PS QS      → toPathP (ispd _ (transport (λ i → F (poly+Comm P Q i))    _) _))
          (λ v                → toPathP (ispd _ (transport (λ i → F (base-0P v i))    _) _))
          (λ v a b            → toPathP (ispd _ (transport (λ i → F (base-poly+ v a b i))    _) _))


  module Poly-Rec-Prop
    -- types
    (n : ℕ)
    (B : Type ℓ')
    (isp : isProp B)
    -- elements
    (0P* : B)
    (base* : (v : Vec ℕ n) → (a : A) → B)
    (_poly+*_ : B → B → B)
    where

    f : Poly A' n → B
    f = Poly-Ind-Prop.f n (λ _ → B) (λ _ → isp) 0P* base* _poly+*_
