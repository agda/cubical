module Cubical.HITs.S2.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.S1.Base
open import Cubical.HITs.S2.Base
open import Cubical.HITs.Susp

open import Cubical.Homotopy.Loopspace

S²ToSetElim : ∀ {ℓ} {A : S² → Type ℓ}
           → ((x : S²) → isSet (A x))
           → A base
           → (x : S²) → A x
S²ToSetElim set b base = b
S²ToSetElim set b (surf i j) =
  isOfHLevel→isOfHLevelDep 2 set b b {a0 = refl} {a1 = refl} refl refl surf i j

-- Wedge connectivity lemmas for S² (binary maps 2-groupoids)
wedgeconFunS² : ∀ {ℓ} {P : S² → S² → Type ℓ}
         → ((x y : _) → isOfHLevel 4 (P x y))
         → (l : ((x : S²) → P x base))
         → (r : (x : S²) → P base x)
         → l base ≡ r base
         → (x y : _) → P x y
wedgeconFunS² {P = P} hlev l r p base y = r y
wedgeconFunS² {P = P} hlev l r p (surf i i₁) y = help y i i₁
  where
  help : (y : S²) → SquareP (λ i j → P (surf i j) y)
                     (λ _ → r y) (λ _ → r y)
                     (λ _ → r y) λ _ → r y
  help =
    S²ToSetElim (λ _ → isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (hlev _ _) _ _) _ _)
               λ w j → hcomp (λ k → λ { (j = i0) → p k
                                        ; (j = i1) → p k
                                        ; (w = i0) → p k
                                        ; (w = i1) → p k})
                              (l (surf w j))

wedgeconFunS²Id : ∀ {ℓ} {P : S² → S² → Type ℓ}
         → (h : ((x y : _) → isOfHLevel 4 (P x y)))
         → (l : ((x : S²) → P x base))
         → (r : (x : S²) → P base x)
         → (p : l base ≡ r base)
         → (x : S²) → wedgeconFunS² h l r p x base ≡ l x
wedgeconFunS²Id h l r p base = sym p
wedgeconFunS²Id h l r p (surf i j) k =
  hcomp (λ w → λ {(i = i0) → p (~ k ∧ w)
                 ; (i = i1) → p (~ k ∧ w)
                 ; (j = i0) → p (~ k ∧ w)
                 ; (j = i1) → p (~ k ∧ w)
                 ; (k = i1) → l (surf i j)})
        (l (surf i j))

S¹×S¹→S² : S¹ → S¹ → S²
S¹×S¹→S² base y = base
S¹×S¹→S² (loop i) base = base
S¹×S¹→S² (loop i) (loop j) = surf i j

invS² : S² → S²
invS² base = base
invS² (surf i j) = surf j i

invS²∘invS²≡id : (x : _) → invS² (invS² x) ≡ x
invS²∘invS²≡id base = refl
invS²∘invS²≡id (surf i i₁) = refl

invS²Iso : Iso S² S²
Iso.fun invS²Iso = invS²
Iso.inv invS²Iso = invS²
Iso.rightInv invS²Iso = invS²∘invS²≡id
Iso.leftInv invS²Iso = invS²∘invS²≡id

S¹×S¹→S²-anticomm : (x y : S¹) → invS² (S¹×S¹→S² x y) ≡ S¹×S¹→S² y x
S¹×S¹→S²-anticomm base base = refl
S¹×S¹→S²-anticomm base (loop i) = refl
S¹×S¹→S²-anticomm (loop i) base = refl
S¹×S¹→S²-anticomm (loop i) (loop i₁) = refl

toSuspPresInvS² : (x : S²) → toSusp S²∙ (invS² x) ≡ sym (toSusp S²∙ x)
toSuspPresInvS² base =
  rCancel (merid base) ∙∙ refl ∙∙ cong sym (sym (rCancel (merid base)))
toSuspPresInvS² (surf i j) k r =
  hcomp (λ l → λ {(i = i0) → cc l k r
                 ; (i = i1) → cc l k r
                 ; (j = i0) → cc l k r
                 ; (j = i1) → cc l k r
                 ; (k = i0) → l1-fill j i r (~ l)
                 ; (k = i1) → l1-fill i j (~ r) (~ l)
                 ; (r = i0) → north
                 ; (r = i1) → north})
        (l1≡l2 k j i r)
  where
  cc : Cube {A = Susp S²} _ _ _ _ _ _
  cc = doubleCompPath-filler
        (rCancel (merid base)) refl (cong sym (sym (rCancel (merid base))))

  l1-fill : (i j k r : I) → Susp S²
  l1-fill i j k r =
    hfill (λ r →  λ {(i = i0) → rCancel (merid base) r k
                 ; (i = i1) → rCancel (merid base) r k
                 ; (j = i0) → rCancel (merid base) r k
                 ; (j = i1) → rCancel (merid base) r k
                 ; (k = i0) → north
                 ; (k = i1) → north})
          (inS (toSusp S²∙ (surf i j) k))
          r

  l1 : (Ω^ 3) (Susp∙ S²) .fst
  l1 i j k = l1-fill i j k i1

  l2 : (Ω^ 3) (Susp∙ S²) .fst
  l2 i j k = l1 j i (~ k)

  sym≡cong-sym-refl : ∀ {ℓ} {A : Type ℓ} {x : A} → sym≡cong-sym (λ _ _ → x) ≡ refl
  sym≡cong-sym-refl {x = x} = transportRefl (λ _ _ _ → x)

  l1≡l2 : l1 ≡ l2
  l1≡l2 = sym (sym≡flipSquare (λ i j → l1 j i))
        ∙ ((λ _ i j k → l1 j (~ i) k)
        ∙ λ r i j k →
          hcomp (λ l →  λ {(i = i0) → north
                 ; (i = i1) → north
                 ; (j = i0) → sym≡cong-sym-refl {x = north} r (~ l) i k
                 ; (j = i1) → sym≡cong-sym-refl {x = north} r (~ l) i k
                 ; (k = i0) → north
                 ; (k = i1) → north
                 ; (r = i0) → sym≡cong-sym (λ i k → l1 j i k) (~ l) i k
                 ; (r = i1) → l2 i j k})
                (l2 i j k))


S¹×S¹→S²-sym : (x y : S¹) → toSusp S²∙ (S¹×S¹→S² x y) ≡ sym (toSusp S²∙ (S¹×S¹→S² y x))
S¹×S¹→S²-sym x y =
  cong sym (sym (toSuspPresInvS²  (S¹×S¹→S² x y)))
  ∙ cong (sym ∘ toSusp S²∙) (S¹×S¹→S²-anticomm x y)
