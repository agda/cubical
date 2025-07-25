module Cubical.Algebra.Polynomials.UnivariateList.Base where

{-
Polynomials over commutative rings
==================================
-}

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _Nat+_; _·_ to _Nat·_) hiding (·-comm)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty.Base renaming (rec to ⊥rec )
open import Cubical.Data.Bool hiding (_≤_)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

------------------------------------------------------------------------------------

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

module _ (R' : CommRing ℓ) where
  private
    R = fst R'

  open CommRingStr (snd R')

  data Poly : Type ℓ where
    []    : Poly
    _∷_   : (a : R) → (p : Poly) → Poly
    drop0 : 0r ∷ [] ≡ []

  infixr 5 _∷_

  pattern [_] x = x ∷ []

module PolyMod (R' : CommRing ℓ) where
  private
    R = fst R'
  open CommRingStr (snd R') public

-------------------------------------------------------------------------------------------
-- First definition of a polynomial.
-- A polynomial a₁ +  a₂x + ... + aⱼxʲ of degree j is represented as a list [a₁, a₂, ...,aⱼ]
-- modulo trailing zeros.
-------------------------------------------------------------------------------------------
  module Elim (B      : Poly R' → Type ℓ')
              ([]*    : B [])
              (cons*  : (r : R) (p : Poly R') (b : B p) → B (r ∷ p))
              (drop0* : PathP (λ i → B (drop0 i)) (cons* 0r [] []*) []*) where

   f : (p : Poly R') → B p
   f [] = []*
   f (x ∷ p) = cons* x p (f p)
   f (drop0 i) = drop0* i

  -- Given a proposition (as type) ϕ ranging over polynomials, we prove it by:
  -- ElimProp.f ϕ ⌜proof for base case []⌝ ⌜proof for induction case a ∷ p⌝
  --           ⌜proof that ϕ actually is a proposition over the domain of polynomials⌝
  module _ (B : Poly R' → Type ℓ')
           ([]* : B [])
           (cons* : (r : R) (p : Poly R') (b : B p) → B (r ∷ p))
           (BProp : {p : Poly R'} → isProp (B p)) where
   ElimProp : (p : Poly R') → B p
   ElimProp = Elim.f B []* cons* (toPathP (BProp (transport (λ i → B (drop0 i)) (cons* 0r [] []*)) []*))


  module _ (B         : Poly R' → Poly R' → Type ℓ')
           ([][]*     : B [] [])
           (cons[]*   : (r : R) (p : Poly R') (b : B p []) → B (r ∷ p) [])
           ([]cons*   : (r : R) (p : Poly R') (b : B [] p) → B [] (r ∷ p))
           (conscons* : (r s : R) (p q : Poly R') (b : B p q) → B (r ∷ p) (s ∷ q))
           (BProp     : {p q : Poly R'} → isProp (B p q)) where

    elimProp2 : (p q : Poly R') → B p q
    elimProp2 =
      ElimProp
        (λ p → (q : Poly R') → B p q)
        (ElimProp (B []) [][]* (λ r p b → []cons* r p b) BProp)
        (λ r p b → ElimProp (λ q → B (r ∷ p) q) (cons[]* r p (b [])) (λ s q b' → conscons* r s p q (b q)) BProp)
        (isPropΠ (λ _ → BProp))

  module Rec (B : Type ℓ')
             ([]* : B)
             (cons* : R → B → B)
             (drop0* : cons* 0r []* ≡ []*)
             (Bset : isSet B) where
    f : Poly R' → B
    f = Elim.f (λ _ → B) []* (λ r p b → cons* r b) drop0*


  module RecPoly ([]* : Poly R') (cons* : R → Poly R' → Poly R') (drop0* : cons* 0r []* ≡ []*) where
    f : Poly R' → Poly R'
    f [] = []*
    f (a ∷ p) = cons* a (f p)
    f (drop0 i) = drop0* i



--------------------------------------------------------------------------------------------------
-- Second definition of a polynomial. The purpose of this second definition is to
-- facilitate the proof that the first definition is a set. The two definitions are
-- then shown to be equivalent.
-- A polynomial a₀ +  a₁x + ... + aⱼxʲ of degree j is represented as a function f
-- such that for i ∈ ℕ we have  f(i) = aᵢ if i ≤ j, and 0 for i > j
--------------------------------------------------------------------------------------------------

  PolyFun : Type ℓ
  PolyFun = Σ[ p ∈ (ℕ → R) ] (∃[ n ∈ ℕ ] ((m : ℕ) → n ≤ m → p m ≡ 0r))


  isSetPolyFun : isSet PolyFun
  isSetPolyFun = isSetΣSndProp (isSetΠ (λ x → is-set)) λ f x y → squash₁ x y


  --construction of the function that represents the polynomial
  Poly→Fun : Poly R' → (ℕ → R)
  Poly→Fun [] = (λ _ → 0r)
  Poly→Fun (a ∷ p) = (λ n → if isZero n then a else Poly→Fun p (predℕ n))
  Poly→Fun (drop0 i) = lemma i
    where
    lemma : (λ n → if isZero n then 0r else 0r) ≡ (λ _ → 0r)
    lemma i zero = 0r
    lemma i (suc n) = 0r


  Poly→Prf : (p : Poly R') → ∃[ n ∈ ℕ ] ((m : ℕ) → n ≤ m → (Poly→Fun p m ≡ 0r))
  Poly→Prf = ElimProp (λ p →  ∃[ n ∈ ℕ ] ((m : ℕ) → n ≤ m → (Poly→Fun p m ≡ 0r)))
                        ∣ 0 , (λ m ineq → refl) ∣₁
                        (λ r p → map ( λ (n , ineq) → (suc n) ,
                                       λ { zero h → ⊥rec (znots (sym (≤0→≡0 h))) ;
                                           (suc m) h → ineq m (pred-≤-pred h)
                                         }
                                     )
                        )
                        squash₁

  Poly→PolyFun : Poly R' → PolyFun
  Poly→PolyFun p = (Poly→Fun p) , (Poly→Prf p)

  -- this function corresponds to multiplication by the indeterminate X and
  -- is used to show that multiplication by X is injective on Poly R'
  shiftPolyFun : PolyFun → PolyFun
  fst (shiftPolyFun _) zero = 0r
  fst (shiftPolyFun (f , _)) (suc n) = f n
  snd (shiftPolyFun (f , f-vanishes)) =
    PT.rec
      isPropPropTrunc
      (λ (k , vanishes-at-k)
        → ∣ (suc k) ,
            (λ {zero → λ _ → refl;
                (suc m) → λ k+1≤m+1 → vanishes-at-k m (pred-≤-pred k+1≤m+1)
               })
          ∣₁)
      f-vanishes

  shiftPolyFunPrepends0 : (p : Poly R') → shiftPolyFun (Poly→PolyFun p) ≡ Poly→PolyFun (0r ∷ p)
  shiftPolyFunPrepends0 p =
    Σ≡Prop (λ _ → isPropPropTrunc)
            λ {i zero → 0r; i (suc n) → fst (Poly→PolyFun p) n}

----------------------------------------------------
-- Start of code by Anders Mörtberg and Evan Cavallo


  at0 : (ℕ → R) → R
  at0 f = f 0

  atS : (ℕ → R) → (ℕ → R)
  atS f n = f (suc n)

  polyEq : (p p' : Poly R') → Poly→Fun p ≡ Poly→Fun p' → p ≡ p'
  polyEq [] [] _ = refl
  polyEq [] (a ∷ p') α =
    sym drop0 ∙∙ cong₂ _∷_ (cong at0 α) (polyEq [] p' (cong atS α)) ∙∙ refl
  polyEq [] (drop0 j) α k =
    hcomp
      (λ l → λ
        { (j = i1) → drop0 l
        ; (k = i0) → drop0 l
        ; (k = i1) → drop0 (j ∧ l)
        })
      (is-set 0r 0r (cong at0 α) refl j k ∷ [])
  polyEq (a ∷ p) [] α =
    refl ∙∙ cong₂ _∷_ (cong at0 α) (polyEq p [] (cong atS α)) ∙∙ drop0
  polyEq (a ∷ p) (a₁ ∷ p') α =
    cong₂ _∷_ (cong at0 α) (polyEq p p' (cong atS α))
  polyEq (a ∷ p) (drop0 j) α k =
    hcomp -- filler
      (λ l → λ
        { (k = i0) → a ∷ p
        ; (k = i1) → drop0 (j ∧ l)
        ; (j = i0) → at0 (α k) ∷ polyEq p [] (cong atS α) k
        })
      (at0 (α k) ∷ polyEq p [] (cong atS α) k)
  polyEq (drop0 i) [] α k =
    hcomp
      (λ l → λ
        { (i = i1) → drop0 l
        ; (k = i0) → drop0 (i ∧ l)
        ; (k = i1) → drop0 l
        })
      (is-set 0r 0r (cong at0 α) refl i k ∷ [])
  polyEq (drop0 i) (a ∷ p') α k =
    hcomp -- filler
      (λ l → λ
        { (k = i0) → drop0 (i ∧ l)
        ; (k = i1) → a ∷ p'
        ; (i = i0) → at0 (α k) ∷ polyEq [] p' (cong atS α) k
        })
      (at0 (α k) ∷ polyEq [] p' (cong atS α) k)
  polyEq (drop0 i) (drop0 j) α k =
    hcomp
      (λ l → λ
        { (k = i0) → drop0 (i ∧ l)
        ; (k = i1) → drop0 (j ∧ l)
        ; (i = i0) (j = i0) → at0 (α k) ∷ []
        ; (i = i1) (j = i1) → drop0 l
        })
      (is-set 0r 0r (cong at0 α) refl (i ∧ j) k ∷ [])


  PolyFun→Poly+ : (q : PolyFun) → Σ[ p ∈ Poly R' ] Poly→Fun p ≡ q .fst
  PolyFun→Poly+ (f , pf) = rec lem (λ x → rem1 f (x .fst) (x .snd) ,
                                               funExt (rem2 f (fst x) (snd x))
                                   ) pf
    where
    lem : isProp (Σ[ p ∈ (Poly R')] Poly→Fun p ≡ f)
    lem (p , α) (p' , α') =
      ΣPathP (polyEq p p' (α ∙ sym α'), isProp→PathP (λ i → (isSetΠ λ _ → is-set) _ _) _ _)

    rem1 : (p : ℕ → R) (n : ℕ) → ((m : ℕ) → n ≤ m → p m ≡ 0r) → Poly R'
    rem1 p zero h = []
    rem1 p (suc n) h = p 0 ∷ rem1 (λ x → p (suc x)) n (λ m x → h (suc m) (suc-≤-suc x))

    rem2 : (f : ℕ → R) (n : ℕ) → (h : (m : ℕ) → n ≤ m → f m ≡ 0r) (m : ℕ) →
                                                                 Poly→Fun (rem1 f n h) m ≡ f m
    rem2 f zero h m = sym (h m zero-≤)
    rem2 f (suc n) h zero = refl
    rem2 f (suc n) h (suc m) = rem2 (λ x → f (suc x)) n (λ k p → h (suc k) (suc-≤-suc p)) m

  PolyFun→Poly : PolyFun → Poly R'
  PolyFun→Poly q = PolyFun→Poly+ q .fst

  PolyFun→Poly→PolyFun : (p : Poly R') → PolyFun→Poly (Poly→PolyFun p) ≡ p
  PolyFun→Poly→PolyFun p = polyEq _ _ (PolyFun→Poly+ (Poly→PolyFun p) .snd)



--End of code by Mörtberg and Cavallo
-------------------------------------

  isSetPoly : isSet (Poly R')
  isSetPoly = isSetRetract Poly→PolyFun
                           PolyFun→Poly
                           PolyFun→Poly→PolyFun
                           isSetPolyFun
