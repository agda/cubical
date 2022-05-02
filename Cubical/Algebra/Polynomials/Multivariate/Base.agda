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
    _Poly+_  : (P : Poly n) → (Q : Poly n) → Poly n
      -- AbGroup eq
    Poly+-assoc : (P Q R : Poly n) → P Poly+ (Q Poly+ R) ≡ (P Poly+ Q) Poly+ R
    Poly+-Rid   : (P : Poly n) → P Poly+ 0P ≡ P
    Poly+-comm  : (P Q : Poly n) → P Poly+ Q ≡ Q Poly+ P
      -- Base eq
    base-0P : (v : Vec ℕ n) → base v 0r ≡ 0P
    base-Poly+     : (v : Vec ℕ n) → (a b : A) → (base v a) Poly+ (base v b) ≡ base v (a + b)
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
    (_Poly+*_ : {P Q : Poly A' n} → (PS : F P) → (QS : F Q) → F (P Poly+ Q))
    -- AbGroup eq
    (Poly+-assoc* : {P Q R : Poly A' n} → (PS : F P) → (QS : F Q) → (RS : F R)
                    → PathP (λ i → F (Poly+-assoc P Q R i)) (PS Poly+* (QS Poly+* RS)) ((PS Poly+* QS) Poly+* RS))
    (Poly+-Rid*   : {P : Poly A' n} → (PS : F P) →
                   PathP (λ i → F (Poly+-Rid P i)) (PS Poly+* 0P*) PS)
    (Poly+-comm*  : {P Q : Poly A' n} → (PS : F P) → (QS : F Q)
                    → PathP (λ i → F (Poly+-comm P Q i)) (PS Poly+* QS) (QS Poly+* PS))
    -- Base eq
    (base-0P* : (v : Vec ℕ n) → PathP (λ i → F (base-0P v i)) (base* v 0r) 0P*)
    (base-Poly+*     : (v : Vec ℕ n) → (a b : A)
                     → PathP (λ i → F (base-Poly+ v a b i)) ((base* v a) Poly+* (base* v b)) (base* v (a + b)))
    where

    f : (P : Poly A' n) → F P
    f 0P = 0P*
    f (base v a) = base* v a
    f (P Poly+ Q) = (f P) Poly+* (f Q)
    f (Poly+-assoc P Q R i) = Poly+-assoc* (f P) (f Q) (f R) i
    f (Poly+-Rid P i) = Poly+-Rid* (f P) i
    f (Poly+-comm P Q i) = Poly+-comm* (f P) (f Q) i
    f (base-0P v i) = base-0P* v i
    f (base-Poly+ v a b i) = base-Poly+* v a b i
    f (trunc P Q p q i j) = isOfHLevel→isOfHLevelDep 2 issd  (f P) (f Q) (cong f p) (cong f q) (trunc P Q p q) i j


  module Poly-Rec-Set
    -- types
    (n  : ℕ)
    (B  : Type ℓ')
    (iss : isSet B)
    -- elements
    (0P*      : B)
    (base*    : (v : Vec ℕ n) → (a : A) → B)
    (_Poly+*_ : B → B → B)
    -- AbGroup eq
    (Poly+-assoc* : (PS QS RS : B) → (PS Poly+* (QS Poly+* RS)) ≡ ((PS Poly+* QS) Poly+* RS))
    (Poly+-Rid*   : (PS : B)       → (PS Poly+* 0P*) ≡  PS)
    (Poly+-comm*  : (PS QS : B)    → (PS Poly+* QS) ≡ (QS Poly+* PS))
    -- Base eq
    (base-0P* : (v : Vec ℕ n) → (base* v 0r) ≡  0P*)
    (base-Poly+*     : (v : Vec ℕ n) → (a b : A) → ((base* v a) Poly+* (base* v b)) ≡ (base* v (a + b)))
    where

    f : Poly A' n → B
    f = Poly-Ind-Set.f n (λ _ → B) (λ _ → iss) 0P* base* _Poly+*_ Poly+-assoc* Poly+-Rid* Poly+-comm* base-0P* base-Poly+*


  module Poly-Ind-Prop
    -- types
    (n : ℕ)
    (F : (P : Poly A' n) → Type ℓ')
    (ispd : (P : Poly A' n) → isProp (F P))
    -- elements
    (0P* : F 0P)
    (base* : (v : Vec ℕ n) → (a : A) → F (base v a))
    (_Poly+*_ : {P Q : Poly A' n} → (PS : F P) → (QS : F Q) → F (P Poly+ Q))
    where

    f : (P : Poly A' n) → F P
    f = Poly-Ind-Set.f n F (λ P → isProp→isSet (ispd P)) 0P* base* _Poly+*_
          (λ {P Q R} PS QS RQ → toPathP (ispd _ (transport (λ i → F (Poly+-assoc P Q R i)) _) _))
          (λ {P} PS           → toPathP (ispd _ (transport (λ i → F (Poly+-Rid P i))       _) _))
          (λ {P Q} PS QS      → toPathP (ispd _ (transport (λ i → F (Poly+-comm P Q i))    _) _))
          (λ v                → toPathP (ispd _ (transport (λ i → F (base-0P v i))    _) _))
          (λ v a b            → toPathP (ispd _ (transport (λ i → F (base-Poly+ v a b i))    _) _))


  module Poly-Rec-Prop
    -- types
    (n : ℕ)
    (B : Type ℓ')
    (isp : isProp B)
    -- elements
    (0P* : B)
    (base* : (v : Vec ℕ n) → (a : A) → B)
    (_Poly+*_ : B → B → B)
    where

    f : Poly A' n → B
    f = Poly-Ind-Prop.f n (λ _ → B) (λ _ → isp) 0P* base* _Poly+*_
