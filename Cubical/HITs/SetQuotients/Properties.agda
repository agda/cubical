{-

Set quotients:

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.SetQuotients.Properties where

open import Cubical.HITs.SetQuotients.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

open import Cubical.HITs.PropositionalTruncation as PropTrunc using (∥_∥; ∣_∣; squash)
open import Cubical.HITs.SetTruncation as SetTrunc using (∥_∥₂; ∣_∣₂; squash₂)

-- Type quotients

private
  variable
    ℓ : Level
    A : Type ℓ
    R : A → A → Type ℓ
    B : A / R → Type ℓ
    C : A / R → A / R → Type ℓ
    D : A / R → A / R → A / R → Type ℓ

elimEq/ : (Bprop : (x : A / R ) → isProp (B x))
          {x y : A / R}
          (eq : x ≡ y)
          (bx : B x)
          (by : B y) →
          PathP (λ i → B (eq i)) bx by
elimEq/ {B = B} Bprop {x = x} =
  J (λ y eq → ∀ bx by → PathP (λ i → B (eq i)) bx by) (λ bx by → Bprop x bx by)

elimProp : ((x : A / R ) → isProp (B x))
         → ((a : A) → B ( [ a ]))
         → (x : A / R)
         → B x
elimProp Bprop f [ x ] = f x
elimProp Bprop f (squash/ x y p q i j) =
  isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (Bprop x))
    (g x) (g y) (cong g p) (cong g q) (squash/ x y p q) i j
    where
    g = elimProp Bprop f
elimProp Bprop f (eq/ a b r i) = elimEq/ Bprop (eq/ a b r) (f a) (f b) i

elimProp2 : ((x y : A / R ) → isProp (C x y))
          → ((a b : A) → C [ a ] [ b ])
          → (x y : A / R)
          → C x y
elimProp2 Cprop f = elimProp (λ x → isPropΠ (λ y → Cprop x y))
                             (λ x → elimProp (λ y → Cprop [ x ] y) (f x))

elimProp3 : ((x y z : A / R ) → isProp (D x y z))
          → ((a b c : A) → D [ a ] [ b ] [ c ])
          → (x y z : A / R)
          → D x y z
elimProp3 Dprop f = elimProp (λ x → isPropΠ2 (λ y z → Dprop x y z))
                             (λ x → elimProp2 (λ y z → Dprop [ x ] y z) (f x))

-- lemma 6.10.2 in hott book
[]surjective : (x : A / R) → ∃[ a ∈ A ] [ a ] ≡ x
[]surjective = elimProp (λ x → squash) (λ a → ∣ a , refl ∣)

elim : {B : A / R → Type ℓ}
     → ((x : A / R) → isSet (B x))
     → (f : (a : A) → (B [ a ]))
     → ((a b : A) (r : R a b) → PathP (λ i → B (eq/ a b r i)) (f a) (f b))
     → (x : A / R)
     → B x
elim Bset f feq [ a ] = f a
elim Bset f feq (eq/ a b r i) = feq a b r i
elim Bset f feq (squash/ x y p q i j) =
  isOfHLevel→isOfHLevelDep 2 Bset
              (g x) (g y) (cong g p) (cong g q) (squash/ x y p q) i j
    where
      g = elim Bset f feq

rec : {B : Type ℓ}
      (Bset : isSet B)
      (f : A → B)
      (feq : (a b : A) (r : R a b) → f a ≡ f b)
    → A / R → B
rec Bset f feq [ a ] = f a
rec Bset f feq (eq/ a b r i) = feq a b r i
rec Bset f feq (squash/ x y p q i j) = Bset (g x) (g y) (cong g p) (cong g q) i j
  where
  g = rec Bset f feq

rec2 : {B : Type ℓ} (Bset : isSet B)
       (f : A → A → B) (feql : (a b c : A) (r : R a b) → f a c ≡ f b c)
                       (feqr : (a b c : A) (r : R b c) → f a b ≡ f a c)
    → A / R → A / R → B
rec2 Bset f feql feqr = rec (isSetΠ (λ _ → Bset))
                            (λ a → rec Bset (f a) (feqr a))
                            (λ a b r → funExt (elimProp (λ _ → Bset _ _)
                                              (λ c → feql a b c r)))

setQuotUniversal : {B : Type ℓ} (Bset : isSet B) →
                   (A / R → B) ≃ (Σ[ f ∈ (A → B) ] ((a b : A) → R a b → f a ≡ f b))
setQuotUniversal Bset = isoToEquiv (iso intro out outRightInv outLeftInv)
  where
  intro = λ g →  (λ a → g [ a ]) , λ a b r i → g (eq/ a b r i)
  out = λ h → elim (λ x → Bset) (fst h) (snd h)

  outRightInv : ∀ h → intro (out h) ≡ h
  outRightInv h = refl

  outLeftInv : ∀ g → out (intro g) ≡ g
  outLeftInv = λ g → funExt (λ x → PropTrunc.elim {P = λ sur → out (intro g) x ≡ g x}
    (λ sur → Bset (out (intro g) x) (g x))
    (λ sur → cong (out (intro g)) (sym (snd sur)) ∙ (cong g (snd sur))) ([]surjective x)
    )

open BinaryRelation

effective : (Rprop : isPropValued R) (Requiv : isEquivRel R) (a b : A) → [ a ] ≡ [ b ] → R a b
effective {A = A} {R = R} Rprop (equivRel R/refl R/sym R/trans) a b p = transport aa≡ab (R/refl _)
  where
    helper : A / R → hProp _
    helper =
      rec isSetHProp (λ c → (R a c , Rprop a c))
                     (λ c d cd → Σ≡Prop (λ _ → isPropIsProp)
                                        (hPropExt (Rprop a c) (Rprop a d)
                                                  (λ ac → R/trans _ _ _ ac cd) (λ ad → R/trans _ _ _ ad (R/sym _ _ cd))))

    aa≡ab : R a a ≡ R a b
    aa≡ab i = helper (p i) .fst

isEquivRel→isEffective : isPropValued R → isEquivRel R → isEffective R
isEquivRel→isEffective {R = R} Rprop Req a b = isoToIsEquiv (iso out intro out-intro intro-out)
  where
    intro : [ a ] ≡ [ b ] → R a b
    intro = effective Rprop Req a b

    out : R a b → [ a ] ≡ [ b ]
    out = eq/ a b

    intro-out : ∀ x → intro (out x) ≡ x
    intro-out ab = Rprop a b _ _

    out-intro : ∀ x → out (intro x) ≡ x
    out-intro eq = squash/ _ _ _ _

discreteSetQuotients : Discrete A → isPropValued R → isEquivRel R → (∀ a₀ a₁ → Dec (R a₀ a₁)) → Discrete (A / R)
discreteSetQuotients {A = A} {R = R} Adis Rprop Req Rdec =
  elim (λ a₀ → isSetΠ (λ a₁ → isProp→isSet (isPropDec (squash/ a₀ a₁))))
    discreteSetQuotients' discreteSetQuotients'-eq
  where
    discreteSetQuotients' : (a : A) (y : A / R) → Dec ([ a ] ≡ y)
    discreteSetQuotients' a₀ = elim (λ a₁ → isProp→isSet (isPropDec (squash/ [ a₀ ] a₁))) dis dis-eq
      where
        dis : (a₁ : A) → Dec ([ a₀ ] ≡ [ a₁ ])
        dis a₁ with Rdec a₀ a₁
        ... | (yes p) = yes (eq/ a₀ a₁ p)
        ... | (no ¬p) = no λ eq → ¬p (effective Rprop Req a₀ a₁ eq )

        dis-eq : (a b : A) (r : R a b) →
          PathP (λ i → Dec ([ a₀ ] ≡ eq/ a b r i)) (dis a) (dis b)
        dis-eq a b ab = J (λ b ab → ∀ k → PathP (λ i → Dec ([ a₀ ] ≡ ab i)) (dis a) k)
                          (λ k → isPropDec (squash/ _ _) _  _) (eq/ a b ab) (dis b)

    discreteSetQuotients'-eq : (a b : A) (r : R a b) →
      PathP (λ i → (y : A / R) → Dec (eq/ a b r i ≡ y))
            (discreteSetQuotients' a) (discreteSetQuotients' b)
    discreteSetQuotients'-eq a b ab =
      J (λ b ab → ∀ k → PathP (λ i → (y : A / R) → Dec (ab i ≡ y))
                              (discreteSetQuotients' a) k)
        (λ k → funExt (λ x → isPropDec (squash/ _ _) _ _)) (eq/ a b ab) (discreteSetQuotients' b)
