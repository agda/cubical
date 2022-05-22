{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.RingStructure.CohomologyRingFun where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.NProd
open import Cubical.Algebra.Ring

open import Cubical.Algebra.DirectSum.DirectSumFun.Base
open import Cubical.Algebra.AbGroup.Instances.DirectSumFun
open import Cubical.Algebra.DirectSum.Equiv-DSHIT-DSFun

open import Cubical.HITs.SetTruncation as ST

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity

private variable
  ℓ ℓ' : Level

open Iso


-----------------------------------------------------------------------------
-- Notation

module intermediate-def where
  H*Fun-AbGr : (A : Type ℓ) → AbGroup ℓ
  H*Fun-AbGr A = ⊕Fun-AbGr (λ n → coHom n A) (λ n → snd (coHomGroup n A))

  H*Fun : (A : Type ℓ) → Type ℓ
  H*Fun A = fst (H*Fun-AbGr A)

module CupRingProperties (A : Type ℓ) where
  open intermediate-def
  open AbGroupStr (snd (H*Fun-AbGr A))
  open AbGroupTheory

  private
    G : (n : ℕ) → Type ℓ
    G = λ n → coHom n A
    Gstr : (n : ℕ) → AbGroupStr (G n)
    Gstr n = snd (coHomGroup n A)


  open AbGroupStr (snd (NProd-AbGroup G Gstr)) using ()
      renaming
    ( 0g       to 0Fun
    ; _+_      to _+Fun_
    ; -_       to -Fun_
    ; assoc    to +FunAssoc
    ; identity to +FunIdR×IdL
    ; inverse  to +FunInvR×InvL
    ; comm     to +FunComm
    ; is-set   to isSetFun)

  private
    Fun : (G : (n : ℕ) → Type ℓ) → (Gstr : (n : ℕ) → AbGroupStr (G n)) → Type ℓ
    Fun G Gstr = fst (NProd-AbGroup G Gstr)

    +FunIdR : (x : Fun G Gstr) → x +Fun 0Fun ≡ x
    +FunIdR = λ x → fst (+FunIdR×IdL x)

    +FunIdL : (x : Fun G Gstr) → 0Fun +Fun x  ≡ x
    +FunIdL = λ x → snd (+FunIdR×IdL x)

    -- +FunInvR : (x : Fun G Gstr) → x +Fun (-Fun x) ≡ 0Fun
    -- +FunInvR = λ x → fst (+FunInvR×InvL x)

    -- +FunInvL : (x : Fun G Gstr) → (-Fun x) +Fun x ≡ 0Fun
    -- +FunInvL = λ x → snd (+FunInvR×InvL x)


-----------------------------------------------------------------------------
-- Definition of the cup product

  -- Underlying function
  eqSameFiber : {i n : ℕ} → (i ≤ n) → i +' (n ∸ i) ≡ n
  eqSameFiber {zero} {zero} r = refl
  eqSameFiber {zero} {suc n} r = refl
  eqSameFiber {suc i} {zero} r = ⊥.rec (¬-<-zero r)
  eqSameFiber {suc i} {suc n} r = +'≡+ (suc i) (suc n ∸ suc i)
                                  ∙ cong suc (sym (+'≡+ i (n ∸ i)))
                                  ∙ cong suc (eqSameFiber (pred-≤-pred r))

  sumFun : (i n : ℕ) → (i ≤ n) → (f g : (n : ℕ) → coHom n A) → coHom n A
  sumFun zero n r f g = subst (λ X → coHom X A) (eqSameFiber r) (f 0 ⌣ g n)
  sumFun (suc i) n r f g = subst (λ X → coHom X A) (eqSameFiber r) ((f (suc i)) ⌣ (g (n ∸ (suc i))))
                           +ₕ sumFun i n (≤-trans ≤-sucℕ r) f g

  _cupFun_ : (f g : (n : ℕ) → coHom n A) → (n : ℕ) → coHom n A
  _cupFun_ f g n = sumFun n n ≤-refl f g

  -- Proof that it is an almost null sequence
  -- cupAn : (f g : (n : ℕ) → coHom n A) → AlmostNull G Gstr f → AlmostNull G Gstr g → AlmostNull G Gstr (f cupFun g)
  -- cupAn f g (k , nf) (l , ng) = (k +n l) , λ n r → {!!}
  --   {- proof for sumFun i n ≤-refl f g -> apply on n (for rec call)
  --      i ≤ n & n > k+l
  --      Case analysis :
  --      k     < suc i -> 0 + rec-call
  --      suc i ≤ k     -> n - (suc i) > k+l - k = l -> ok + rec-call
  --   -}


-----------------------------------------------------------------------------
-- Requiered lemma for mapping the product

  -- lemma for 0 case
  substCoHom0 : {n m : ℕ} → (p : n ≡ m) → subst (λ X → coHom X A) p (0ₕ n) ≡ 0ₕ m
  substCoHom0 {n} {m} p = J (λ m p → subst (λ X → coHom X A) p (0ₕ n) ≡ 0ₕ m)
                          (transportRefl _) p

  cupFunAnnihilL : (f : (n : ℕ) → coHom n A) → 0Fun cupFun f ≡ 0Fun
  cupFunAnnihilL f = funExt (λ n → sumF0 n n ≤-refl)
    where
    sumF0 : (i n : ℕ) → (r : i ≤ n) → sumFun i n r 0Fun f ≡ 0ₕ n
    sumF0 zero n r = cong (subst (λ X → coHom X A) (eqSameFiber r)) (0ₕ-⌣ _ _ _)
                     ∙ substCoHom0 (eqSameFiber r)
    sumF0 (suc i) n r = cong₂ _+ₕ_
                              (cong (subst (λ X → coHom X A) (eqSameFiber r)) (0ₕ-⌣ _ _ _))
                              (sumF0 i n (≤-trans ≤-sucℕ r))
                        ∙ rUnitₕ n _
                        ∙ substCoHom0 (eqSameFiber r)


  cupFunAnnihilR : (f : (n : ℕ) → (G n)) → f cupFun 0Fun ≡ 0Fun
  cupFunAnnihilR f = funExt (λ n → sumF0 n n ≤-refl)
    where
    sumF0 : (i n : ℕ) → (r : i ≤ n) → sumFun i n r f 0Fun ≡ 0ₕ n
    sumF0 zero n r = cong (subst (λ X → coHom X A) (eqSameFiber r)) (⌣-0ₕ _ _ _)
                     ∙ substCoHom0 (eqSameFiber r)
    sumF0 (suc i) n r = cong₂ _+ₕ_
                              (cong (subst (λ X → coHom X A) (eqSameFiber r)) (⌣-0ₕ _ _ _))
                              (sumF0 i n (≤-trans ≤-sucℕ r))
                        ∙ rUnitₕ n _
                        ∙ substCoHom0 (eqSameFiber r)


  -- lemma for +
  substCoHom+ : {n m : ℕ} → (p : n ≡ m) → (x y : coHom n A) →
                subst (λ X → coHom X A) p (x +ₕ y) ≡ subst (λ X → coHom X A) p x +ₕ subst (λ X → coHom X A) p y
  substCoHom+ {n} {m} p x y = J (λ m p → subst (λ X → coHom X A) p (x +ₕ y) ≡ subst (λ X → coHom X A) p x +ₕ subst (λ X → coHom X A) p y)
                                (transportRefl _ ∙ sym (cong₂ _+ₕ_ (transportRefl _) (transportRefl _)))
                                p


  cupFunDistR : (f g h : (n : ℕ) → coHom n A) → f cupFun (g +Fun h) ≡ (f cupFun g) +Fun (f cupFun h)
  cupFunDistR f g h = funExt (λ n → sumFAssoc n n ≤-refl)
   where
   sumFAssoc : (i n : ℕ) → (r : i ≤ n) → sumFun i n r f (g +Fun h) ≡ (sumFun i n r f g) +ₕ (sumFun i n r f h)
   sumFAssoc zero n r = cong (subst (λ X → coHom X A) (eqSameFiber r)) (leftDistr-⌣ _ _ _ _ _)
                        ∙ substCoHom+ _ _ _
   sumFAssoc (suc i) n r = cong (λ X → X +ₕ (sumFun i n (≤-trans ≤-sucℕ r) f (g +Fun h)))
                                (cong (subst (λ X → coHom X A) (eqSameFiber r)) (leftDistr-⌣ _ _ _ _ _))
                           ∙ cong₂ _+ₕ_ (substCoHom+ (eqSameFiber r) _ _) (sumFAssoc i n (≤-trans ≤-sucℕ r))
                           ∙ comm-4 (coHomGroup n A) _ _ _ _

  cupFunDistL : (f g h : (n : ℕ) → coHom n A) → (f +Fun g) cupFun h ≡ (f cupFun h) +Fun (g cupFun h)
  cupFunDistL f g h = funExt (λ n → sumFAssoc n n ≤-refl)
   where
   sumFAssoc : (i n : ℕ) → (r : i ≤ n) → sumFun i n r (f +Fun g) h ≡ (sumFun i n r f h) +ₕ (sumFun i n r g h)
   sumFAssoc zero n r = cong (subst (λ X → coHom X A) (eqSameFiber r)) (rightDistr-⌣ _ _ _ _ _)
                        ∙ substCoHom+ _ _ _
   sumFAssoc (suc i) n r = cong (λ X → X +ₕ (sumFun i n (≤-trans ≤-sucℕ r) (f +Fun g) h))
                                (cong (subst (λ X → coHom X A) (eqSameFiber r)) (rightDistr-⌣ _ _ _ _ _))
                           ∙ cong₂ _+ₕ_ (substCoHom+ (eqSameFiber r) _ _) (sumFAssoc i n (≤-trans ≤-sucℕ r))
                           ∙ comm-4 (coHomGroup n A) _ _ _ _
