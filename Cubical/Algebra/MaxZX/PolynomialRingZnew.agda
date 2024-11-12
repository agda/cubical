{-# OPTIONS --cubical #-}

-- PolynomialRingZ.agda
module PolynomialRingZnew where

open import Agda.Primitive.Cubical
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.Polynomials.UnivariateList.Properties 
open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Data.Int.Properties
open import Cubical.Algebra.CommRing 
open import Cubical.Data.Int.Base renaming ( _+_ to _+ℤ_ ; _·_ to _·ℤ_; -_ to -ℤ_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_ ; isZero to isZeroℕ ; isEven to isEvenℕ ; isOdd to isOddℕ)
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Tactics.CommRingSolver
open import ExplMaxIdeal

{- record Inspect {A : Set} (x : A) : Set where
  constructor what
  field
      it : A
      it-eq : x ≡ it

inspect : ∀ {A : Set} (x : A) → Inspect x
inspect x = what x refl -}
  
-- ℤ is a commutative ring --

isCommRingℤ : IsCommRing (pos 0) (pos 1) _+ℤ_ _·ℤ_ -ℤ_
isCommRingℤ = makeIsCommRing
  isSetℤ
  +Assoc     
  (λ x → refl)     
  -Cancel     
  +Comm      
  ·Assoc     
  ·IdR
  ·DistR+
  ·Comm

ℤCommRingStr : CommRingStr ℤ
ℤCommRingStr = record
  { 0r = pos 0
  ; 1r = pos 1
  ; _+_ = _+ℤ_
  ; _·_ = _·ℤ_
  ; -_ = -ℤ_
  ; isCommRing = isCommRingℤ
  }

ℤCommRing : CommRing Agda.Primitive.lzero
ℤCommRing = ℤ , ℤCommRingStr

isZero : ℤ → Bool
isZero (pos n) = isZeroℕ n
isZero (ℤ.negsuc n) = false

-- Polynomial ring over ℤ is a commutative ring --

module PolyRingℤ = PolyModTheory ℤCommRing renaming (_Poly+_ to _+P_; Poly- to -P_; _Poly*_ to _·P_)
module PolyModℤ = PolyMod ℤCommRing
open PolyMod ℤCommRing

ℤ[X] : Type
ℤ[X] = Poly ℤCommRing

TestPolynom1 : ℤ[X]
TestPolynom1 = pos 3 ∷ pos 1 ∷ pos 1 ∷ []

isCommRingℤ[X] : IsCommRing [] (pos 1 ∷ []) PolyRingℤ._+P_ PolyRingℤ._·P_ PolyRingℤ.-P_
isCommRingℤ[X] = makeIsCommRing
  PolyModℤ.isSetPoly
  PolyRingℤ.Poly+Assoc
  (λ x → refl)     
  PolyRingℤ.Poly+Inverses     
  PolyRingℤ.Poly+Comm      
  PolyRingℤ.Poly*Associative     
  PolyRingℤ.Poly*Rid
  PolyRingℤ.Poly*LDistrPoly+
  PolyRingℤ.Poly*Commutative 

ℤ[X]CommRingStr : CommRingStr (Poly ℤCommRing)
ℤ[X]CommRingStr = record
  { 0r = []
  ; 1r =  pos 1 ∷ []
  ; _+_ = PolyRingℤ._+P_
  ; _·_ = PolyRingℤ._·P_
  ; -_ =  PolyRingℤ.-P_
  ; isCommRing = isCommRingℤ[X]
  }

ℤ[X]CommRing : CommRing Agda.Primitive.lzero
ℤ[X]CommRing = record
  { fst = Poly ℤCommRing
  ; snd = ℤ[X]CommRingStr
  }

