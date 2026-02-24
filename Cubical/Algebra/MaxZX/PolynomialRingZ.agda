{-# OPTIONS --cubical #-}

-- PolynomialRingZ.agda
module PolynomialRingZ where

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
open import Cubical.Data.Empty renaming (rec to ⊥-elim)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Tactics.CommRingSolver
open import Cubical.HITs.PropositionalTruncation.Base
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

open ExplMaxIdeal.ExplMaxIdeal ℓ-zero ℤ[X]CommRing


data 𝕌 : Set where
  u : 𝕌

X : ℤ[X]
X = pos 0 ∷ pos 1 ∷ []

isPos : ℕ → Bool
isPos (suc n) = true
isPos zero = false

suc≢zero : {n : ℕ} →  suc n ≡ 0 → ⊥
suc≢zero eq = true≢false (cong isPos eq)

possuc≢poszero : {n : ℕ} →  (pos (suc n)) ≡ (pos 0) → ⊥
possuc≢poszero {n} eq = true≢false (cong isPosSuc eq)
  where 
  isPosSuc : ℤ → Bool
  isPosSuc (pos zero) = false
  isPosSuc (pos (suc n)) = true
  isPosSuc (negsuc n) = true

negsuc≢poszero : {n : ℕ} →  negsuc n  ≡ (pos 0) → ⊥
negsuc≢poszero {n} eq = true≢false (cong isPosSuc eq)
  where 
  isPosSuc : ℤ → Bool
  isPosSuc (pos zero) = false
  isPosSuc (pos (suc n)) = true
  isPosSuc (negsuc n) = true
  
degSeq : (ℕ → ℤ) → ℕ → ℤ
degSeq f m with (f m)
degSeq f zero | pos zero = negsuc 0
degSeq f (suc m) | pos zero = degSeq f m
degSeq f m | pos (suc n) = pos m
degSeq f m | negsuc n = pos m

_≤ℕ_ : ℕ → ℕ → Bool
zero ≤ℕ m = true
suc n ≤ℕ zero = false
suc n ≤ℕ suc m = n ≤ℕ m

{- lemma1 : {m : ℕ} → (m ≤ℕ 0) ≡ true → m ≡ 0
lemma1 {zero} le = refl
lemma1 {suc m} le = ⊥-elim (true≢false (sym le))-}

degAux1 : (m : ℕ) → (p : ℤ[X]) →
       ((m₁ : ℕ) → true ≡ true → PolyMod.Poly→Fun (ℤ , ℤCommRingStr) p m₁ ≡ pos 0) →
       (if isZeroℕ m then pos zero else  PolyMod.Poly→Fun (ℤ , ℤCommRingStr) p (predℕ m)) ≡ pos 0
degAux1 zero p x = refl
degAux1 (suc m) p x = x m refl

degAux : (p : ℤ[X]) → Σ ℕ (λ n → ((m : ℕ) → (n ≤ℕ m ≡ true) → (Poly→Fun p m ≡ pos 0)) × ((n ≡ 0) ⊎ (Poly→Fun p (predℕ n) ≡ pos 0 → ⊥)))
degAux [] = 0 , (λ m le → refl) , inl refl
degAux (a ∷ p) with (degAux p)
degAux (pos zero ∷ p) | zero , (x , x₁) = 0 , ((λ m x₂ → degAux1 m p x)  , inl refl)
degAux (pos (suc n) ∷ p) | zero , (x , inl x₁) = 1 , ((λ m x₂ → lemma m x₂) , (inr possuc≢poszero))
  where
  lemma : (m : ℕ) → (1 ≤ℕ m) ≡ true → (if isZeroℕ m then pos (suc n) else PolyMod.Poly→Fun (ℤ , ℤCommRingStr) p (predℕ m)) ≡ pos 0
  lemma zero x₂ = ⊥-elim (true≢false (sym x₂))
  lemma (suc n) x₂ = x n refl
degAux (pos (suc n) ∷ p) | zero , (x , inr x₁) = 0 , ((λ m x₂ → ⊥-elim (x₁ (x zero refl))) , inl refl)
degAux (negsuc n ∷ p) | zero , (x , inl x₁) = 1 , ((λ m x₂ → lemma m x₂) , inr negsuc≢poszero)
 where
  lemma : (m : ℕ) → (1 ≤ℕ m) ≡ true → (if isZeroℕ m then (negsuc n) else PolyMod.Poly→Fun (ℤ , ℤCommRingStr) p (predℕ m)) ≡ pos 0
  lemma zero x₂ = ⊥-elim (true≢false (sym x₂))
  lemma (suc n) x₂ = x n refl
degAux (negsuc n ∷ p) | zero , (x , inr x₁) = 0 , ((λ m x₂ → ⊥-elim (x₁ (x zero refl))) , inl refl)
degAux (a ∷ p)            | suc fst₁ , (eq , inl x₁) = ⊥-elim (suc≢zero x₁)
degAux (pos n ∷ p)        | suc fst₁ , (eq , inr x₁) = suc (suc fst₁) , ((λ m x → lemma m x) , (inr x₁))
  where
  lemma : (m : ℕ) → ((suc (suc fst₁) ≤ℕ m) ≡ true) → (if isZeroℕ m then pos n else PolyMod.Poly→Fun (ℤ , ℤCommRingStr) p (predℕ m)) ≡ pos 0
  lemma zero x = ⊥-elim (true≢false (sym x))
  lemma (suc m) x = eq m x
degAux (negsuc n ∷ p)     | suc fst₁ , (eq , inr x₁) = suc (suc fst₁) , ((λ m x → lemma m x) , (inr x₁))
  where
  lemma : (m : ℕ) → ((suc (suc fst₁) ≤ℕ m) ≡ true) → (if isZeroℕ m then (negsuc n) else PolyMod.Poly→Fun (ℤ , ℤCommRingStr) p (predℕ m)) ≡ pos 0
  lemma zero x = ⊥-elim (true≢false (sym x))
  lemma (suc m) x = eq m x
degAux (drop0 i) = 0 , lemma i 
  where
  lemma : (i : I) → ((m : ℕ) → (0 ≤ℕ m ≡ true) → (Poly→Fun (drop0 i) m ≡ pos 0)) × ((0 ≡ 0) ⊎ (Poly→Fun (drop0 i) 0 ≡ pos 0 → ⊥))
  lemma i = (λ m x i₁ → subLemma i zero) , inl refl
    where
    subLemma : (λ n → if isZero n then pos 0 else pos 0) ≡ (λ _ → pos 0)
    subLemma i n = pos 0
    subLemma i n = pos 0

deg : ℤ[X] → ℕ
deg p = {!!}

_+P_ = PolyRingℤ._+P_
_·P_ = PolyRingℤ._·P_
-P_ = PolyRingℤ.-P_

LC : ℤ[X] → ℤ
LC [] = pos 0
LC (a ∷ p) = if isZero (LC p) then a else LC p  
LC (drop0 i) = pos 0

{- LCnegZero : (p : ℤ[X]) → (n : ℕ) → (deg p ≡ pos n) → Poly→Fun p n ≡ pos 0 → ⊥
LCnegZero [] n eq eq0r =  pos≢neg (sym eq)
LCnegZero (a ∷ p) zero eq eq0r = {!!}
LCnegZero (a ∷ p) (suc n) eq eq0r = {!!}
LCnegZero (drop0 i) n eq eq0r = {!!} -}

{- degToZero : (f : ℤ[X]) → deg f ≡ negsuc 0 → f ≡ []
degToZero [] eq = refl
degToZero (a ∷ f) eq with inspect (deg (a ∷ f)) 
... | what (pos zero) it-eq = {!!}
... | what (pos (suc n)) it-eq = {!!}
... | what (negsuc n) it-eq = {!!}
degToZero (drop0 i) eq = (λ i₁ →  (drop0 (primIMax i i₁))) -}

_≤ℤ_ : ℤ → ℤ → Bool
pos n ≤ℤ pos m = n ≤ℕ m
pos n ≤ℤ negsuc m = false
negsuc n ≤ℤ pos m = true
negsuc n ≤ℤ negsuc m = m ≤ℕ n

{- Lemma5a : (f : ℤ[X]) → pos 0 ≤ℤ deg ((X ·P f) +P (-P (pos 1 ∷ []))) ≡ true
Lemma5a [] = refl
Lemma5a (a ∷ f) = {!!}
Lemma5a (drop0 i) = {!!}

Lemma5 : (M : ℤ[X] → Bool) → (ν : R → R) →  WitnessNotMaximalIdeal M ν ⊎ Σ ℤ[X] (λ f → ((pos 0 ≤ℤ deg f) ≡ true) × (M f ≡ true))
Lemma5 M ν with inspect (M X)
... | what true it-eq = inr (X , (refl , it-eq))
... | what false it-eq with inspect (M ((X ·P (ν X)) +P (-P (pos 1 ∷ []))) )
... | what false it-eq₁ = inl (notMax X it-eq it-eq₁)
... | what true it-eq₁ = inr (((X ·P (ν X)) +P (-P (pos 1 ∷ []))) , ({!!} , it-eq₁)) -}

