{-

Type quotients:

-}

{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SetQuotients.Properties where

open import Cubical.HITs.SetQuotients.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HAEquiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetTruncation

-- Type quotients

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    R : A → A → Type ℓ'
    B : A / R → Type ℓ''

elimEq/ : (Bprop : (x : A / R ) → isProp (B x))
          {x y : A / R}
          (eq : x ≡ y)
          (bx : B x)
          (by : B y) →
          PathP (λ i → B (eq i)) bx by
elimEq/ {B = B} Bprop {x = x} =
  J (λ y eq → ∀ bx by → PathP (λ i → B (eq i)) bx by) (λ bx by → Bprop x bx by)


elimTypeQuotientsProp : ((x : A / R ) → isProp (B x)) →
                       (f : (a : A) → B ( [ a ])) →
                       (x : A / R) → B x
elimTypeQuotientsProp Bprop f [ x ] = f x
elimTypeQuotientsProp Bprop f (squash/ x y p q i j) =
  elimSquash₀ (λ x → isProp→isType (Bprop x)) (squash/ x y p q)
              (g x) (g y) (cong g p) (cong g q) i j
    where
    g = elimTypeQuotientsProp Bprop f
elimTypeQuotientsProp Bprop f (eq/ a b r i) = elimEq/ Bprop (eq/ a b r) (f a) (f b) i

-- lemma 6.10.2 in hott book
-- TODO: defined truncated Sigma as ∃
[]surjective : (x : A / R) → ∥ Σ[ a ∈ A ] [ a ] ≡ x ∥
[]surjective = elimTypeQuotientsProp (λ x → squash) (λ a → ∣ a , refl ∣)

elimTypeQuotients : {B : A / R → Type ℓ} →
                   (Bset : (x : A / R) → isType (B x)) →
                   (f : (a : A) → (B [ a ])) →
                   (feq : (a b : A) (r : R a b) →
                          PathP (λ i → B (eq/ a b r i)) (f a) (f b)) →
                   (x : A / R) → B x
elimTypeQuotients Bset f feq [ a ] = f a
elimTypeQuotients Bset f feq (eq/ a b r i) = feq a b r i
elimTypeQuotients Bset f feq (squash/ x y p q i j) =
  elimSquash₀ Bset (squash/ x y p q)
              (g x) (g y) (cong g p) (cong g q) i j
    where
      g = elimTypeQuotients Bset f feq


setQuotUniversal : {B : Type ℓ} (Bset : isType B) →
                   (A / R → B) ≃ (Σ[ f ∈ (A → B) ] ((a b : A) → R a b → f a ≡ f b))
setQuotUniversal Bset = isoToEquiv (iso intro elim elimRightInv elimLeftInv)
  where
  intro = λ g →  (λ a → g [ a ]) , λ a b r i → g (eq/ a b r i)
  elim = λ h → elimTypeQuotients (λ x → Bset) (fst h) (snd h)

  elimRightInv : ∀ h → intro (elim h) ≡ h
  elimRightInv h = refl

  elimLeftInv : ∀ g → elim (intro g) ≡ g
  elimLeftInv = λ g → funExt (λ x → elimPropTrunc {P = λ sur → elim (intro g) x ≡ g x}
    (λ sur → Bset (elim (intro g) x) (g x))
    (λ sur → cong (elim (intro g)) (sym (snd sur)) ∙ (cong g (snd sur))) ([]surjective x)
    )

open BinaryRelation

effective : (Rprop : isPropValued R) (Requiv : isEquivRel R) (a b : A) → [ a ] ≡ [ b ] → R a b
effective {A = A} {R = R} Rprop (EquivRel R/refl R/sym R/trans) a b p = transport aa≡ab (R/refl _)
  where
    helper : A / R → hProp
    helper = elimTypeQuotients (λ _ → isTypeHProp) (λ c → (R a c , Rprop a c))
                              (λ c d cd → ΣProp≡ (λ _ → isPropIsProp)
                                                 (ua (PropEquiv→Equiv (Rprop a c) (Rprop a d)
                                                                      (λ ac → R/trans _ _ _ ac cd) (λ ad → R/trans _ _ _ ad (R/sym _ _ cd)))))

    aa≡ab : R a a ≡ R a b
    aa≡ab i = fst (helper (p i))

isEquivRel→isEffective : isPropValued R → isEquivRel R → isEffective R
isEquivRel→isEffective {R = R} Rprop Req a b = isoToEquiv (iso intro elim intro-elim elim-intro)
  where
    intro : [ a ] ≡ [ b ] → R a b
    intro = effective Rprop Req a b

    elim : R a b → [ a ] ≡ [ b ]
    elim = eq/ a b

    intro-elim : ∀ x → intro (elim x) ≡ x
    intro-elim ab = Rprop a b _ _

    elim-intro : ∀ x → elim (intro x) ≡ x
    elim-intro eq = squash/ _ _ _ _

discreteTypeQuotients : Discrete A → isPropValued R → isEquivRel R → (∀ a₀ a₁ → Dec (R a₀ a₁)) → Discrete (A / R)
discreteTypeQuotients {A = A} {R = R} Adis Rprop Req Rdec =
 elimTypeQuotients ((λ a₀ → isTypePi (λ a₁ → isProp→isType (isPropDec (squash/ a₀ a₁)))))
                  discreteTypeQuotients' discreteTypeQuotients'-eq
  where
    discreteTypeQuotients' : (a : A) (y : A / R) → Dec ([ a ] ≡ y)
    discreteTypeQuotients' a₀ = elimTypeQuotients ((λ a₁ → isProp→isType (isPropDec (squash/ [ a₀ ] a₁)))) dis dis-eq
      where
        dis : (a₁ : A) → Dec ([ a₀ ] ≡ [ a₁ ])
        dis a₁ with Rdec a₀ a₁
        ... | (yes p) = yes (eq/ a₀ a₁ p)
        ... | (no ¬p) = no λ eq → ¬p (effective Rprop Req a₀ a₁ eq )

        dis-eq : (a b : A) (r : R a b) →
          PathP (λ i → Dec ([ a₀ ] ≡ eq/ a b r i)) (dis a) (dis b)
        dis-eq a b ab = J (λ b ab → ∀ k → PathP (λ i → Dec ([ a₀ ] ≡ ab i)) (dis a) k)
                          (λ k → isPropDec (squash/ _ _) _  _) (eq/ a b ab) (dis b)

    discreteTypeQuotients'-eq : (a b : A) (r : R a b) →
      PathP (λ i → (y : A / R) → Dec (eq/ a b r i ≡ y))
            (discreteTypeQuotients' a) (discreteTypeQuotients' b)
    discreteTypeQuotients'-eq a b ab =
      J (λ b ab → ∀ k → PathP (λ i → (y : A / R) → Dec (ab i ≡ y))
                              (discreteTypeQuotients' a) k)
        (λ k → funExt (λ x → isPropDec (squash/ _ _) _ _)) (eq/ a b ab) (discreteTypeQuotients' b)
