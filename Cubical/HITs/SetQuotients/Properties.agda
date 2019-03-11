{-

This file contains:

- Properties about set quotieents

-}

{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SetQuotients.Properties where

open import Cubical.HITs.SetQuotients.Base

open import Cubical.Core.Prelude
open import Cubical.Core.PropositionalTruncation
open import Cubical.HITs.SetTruncation
open import Cubical.Core.Glue
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Nat.Base
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat.Properties
open import Cubical.Foundations.HAEquiv


Σ≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
     {x y : Σ A B}  →
     Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y)) ≃
     (x ≡ y)
Σ≡ {A = A} {B = B} {x} {y} = (isoToEquiv (iso intro elim intro-elim elim-intro ))
  where
    intro : Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y)) → x ≡ y
    intro eq = λ i → (fst eq i) , (snd eq i)

    elim : x ≡ y → Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y ))
    elim eq = (λ i → fst (eq i)) , λ i → snd (eq i)

    intro-elim : ∀ eq → intro (elim eq) ≡ eq
    intro-elim eq = refl

    elim-intro : ∀ eq → elim (intro eq) ≡ eq
    elim-intro eq = refl

ΣProp≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
         {x y : Σ A B}  → (∀ a → isProp (B a)) →
         fst x ≡ fst y → x ≡ y
ΣProp≡ {B = B} {x = x} {y = y} Bprop eq = fst Σ≡ (eq , J (λ b eq → ∀ k → PathP (λ i → B (eq i)) (snd x) k) (λ k → Bprop (fst x) _ _) eq (snd y))

PropEquiv→Equiv : ∀ {ℓ} {A B : Set ℓ} (Aprop : isProp A) (Bprop : isProp B) (f : A → B) (g : B → A) → (A ≃ B)
PropEquiv→Equiv Aprop Bprop f g = isoToEquiv (iso f g (λ b → Bprop (f (g b)) b) λ a → Aprop (g (f a)) a)

isPropIsOfHLevel : ∀ {ℓ} {A : Set ℓ} (n : ℕ) → (isProp (isOfHLevel n A))
isPropIsOfHLevel zero = isPropIsContr
isPropIsOfHLevel (suc n) = isOfHLevel1→isProp (hLevelPi 1 (λ _ → hLevelPi 1 (λ _ → isProp→IsOfHLevel1 (isPropIsOfHLevel n))))

HLevel≡ : ∀ {ℓ} {n} {A : Set ℓ} {B : Set ℓ} → {hA : isOfHLevel n A} {hB : isOfHLevel n B} → (A ≡ B) ≃ ((A , hA) ≡ (B , hB))
HLevel≡ {n = n} {A = A} {B = B} {hA} {hB} = isoToEquiv (iso intro elim intro-elim elim-intro)
  where
    intro : A ≡ B → (A , hA) ≡ (B , hB)
    intro eq = ΣProp≡ (λ A → isPropIsOfHLevel n) eq

    elim : (A , hA) ≡ (B , hB) → A ≡ B
    elim = cong fst

    intro-elim : ∀ x → intro (elim x) ≡ x
    intro-elim eq = cong (fst Σ≡) (ΣProp≡ (λ e →
      J (λ B e →
           ∀ k → (x y : PathP (λ i → isOfHLevel n (e i)) hA k) → x ≡ y)
        (λ k → isProp→isSet (isPropIsOfHLevel n) _ _) e hB) refl)

    elim-intro : ∀ x → elim (intro x) ≡ x
    elim-intro eq = refl

hLevelSigma : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} n
  → (isOfHLevel n A)
  → ((a : A) → isOfHLevel n (B a))
  → isOfHLevel n (Σ[ a ∈ A ] B a)
hLevelSigma 0 Ah Bh = isContrSigma Ah Bh
hLevelSigma {B = B} (suc n) Ah Bh x y = subst (isOfHLevel n) (ua Σ≡) sub-lemma
  where
  sub-lemma : isOfHLevel n (Σ (fst x ≡ fst y) λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y))
  sub-lemma = hLevelSigma n (Ah (fst x) (fst y)) (λ a≡ → J
    (λ ay a≡ → ∀ by → isOfHLevel n (PathP (λ i → B (a≡ i)) (snd x) by))
    (λ by → Bh (fst x) (snd x) by) a≡ (snd y) )

raiseHLevel : ∀ {ℓ} {A : Set ℓ} (n : ℕ) (hA : isOfHLevel n A) → isOfHLevel (suc n) A
raiseHLevel zero hA = isProp→IsOfHLevel1 (isContr→isProp hA)
raiseHLevel (suc n) hA = λ x y → raiseHLevel n (hA x y)

liftHLevel : ∀ {ℓ} {A : Set ℓ} {n : ℕ} (m : ℕ) (hA : isOfHLevel n A) → isOfHLevel (m + n) A
liftHLevel zero hA = hA
liftHLevel {n = n} (suc m) hA = raiseHLevel (m + n) (liftHLevel m hA)

hLevel≃ : ∀ {ℓ} n → {A B : Set ℓ} (hA : isOfHLevel n A) (hB : isOfHLevel n B) →
  isOfHLevel n (A ≃ B)
hLevel≃ zero {A = A} {B = B} hA hB = A≃B , contr
  where
  A≃B : A ≃ B
  A≃B = isoToEquiv (iso (λ _ → fst hB) (λ _ → fst hA) (snd hB ) (snd hA))

  contr : (y : A ≃ B) → A≃B ≡ y
  contr y = ΣProp≡ isPropIsEquiv (funExt (λ a → snd hB (fst y a)))

hLevel≃ (suc n) {A = A} {B = B} hA hB = hLevelSigma (suc n) (hLevelPi (suc n) (λ _ → hB)) (λ a → subst (λ n → isOfHLevel n (isEquiv a)) eq (liftHLevel n (isProp→IsOfHLevel1 (isPropIsEquiv a))))
  where
    eq : n + 1 ≡ 1 + n
    eq = +-comm n 1

hLevelRespectEquiv : ∀ {ℓ ℓ'} → {A : Set ℓ}  {B : Set ℓ'} → (n : ℕ) → A ≃ B → isOfHLevel n A → isOfHLevel n B
hLevelRespectEquiv zero eq hA = (fst eq (fst hA)) , (λ b →  (cong (fst eq) (snd hA (fst (fst (equiv-proof (snd eq) b))))) ∙ (snd (fst (equiv-proof (snd eq) b))))
hLevelRespectEquiv {A = A} {B = B} (suc n) eq hA x y = hLevelRespectEquiv n (invEquiv (congEquiv eq')) (hA _ _)
  where
    eq' : B ≃ A
    eq' = invEquiv eq

hLevel≡ : ∀ {ℓ} n → {A B : Set ℓ} (hA : isOfHLevel n A) (hB : isOfHLevel n B) →
  isOfHLevel n (A ≡ B)
hLevel≡ {ℓ} n {A} {B} hA hB = hLevelRespectEquiv n (invEquiv univalence) (hLevel≃ n hA hB)

hLevelHLevel : ∀ {ℓ} n → isOfHLevel (suc n) (HLevel {ℓ = ℓ} n)
hLevelHLevel n x y = subst (λ e → isOfHLevel n e) (ua HLevel≡) (hLevel≡ n (snd x) (snd y))

hProp≃HLevel1 : ∀ {ℓ} → hProp {ℓ} ≃ HLevel {ℓ} 1
hProp≃HLevel1 {ℓ} = isoToEquiv (iso intro elim intro-elim elim-intro)
  where
    intro : hProp {ℓ} → HLevel {ℓ} 1
    intro h = (fst h) , (isProp→IsOfHLevel1 (snd h))

    elim : HLevel 1 → hProp
    elim h = (fst h) , (isOfHLevel1→isProp (snd h))

    intro-elim : ∀ h → intro (elim h) ≡ h
    intro-elim h = ΣProp≡ (λ _ → isPropIsOfHLevel 1) refl

    elim-intro : ∀ h → elim (intro h) ≡ h
    elim-intro h = ΣProp≡ (λ _ → isPropIsProp) refl

isSetHProp : ∀ {ℓ} → isSet (hProp {ℓ = ℓ})
isSetHProp = isOfHLevel2→isSet (subst (λ X → isOfHLevel 2 X) (ua (invEquiv hProp≃HLevel1)) (hLevelHLevel 1))

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Set ℓ
    R : A → A → Set ℓ'
    B : A / R → Set ℓ''

elimEq/ : (Bprop : (x : A / R ) → isProp (B x))
          {x y : A / R}
          (eq : x ≡ y)
          (bx : B x)
          (by : B y) → 
          PathP (λ i → B (eq i)) bx by
elimEq/ {B = B} Bprop {x = x} =
  J (λ y eq → ∀ bx by → PathP (λ i → B (eq i)) bx by) (λ bx by → Bprop x bx by)


elimSetQuotientsProp : ((x : A / R ) → isProp (B x)) →
                       (f : (a : A) → B ( [ a ])) →
                       (x : A / R) → B x
elimSetQuotientsProp Bprop f [ x ] = f x
elimSetQuotientsProp Bprop f (squash/ x y p q i j) =
  elimSquash₀ (λ x → isProp→isSet (Bprop x)) (squash/ x y p q)
              (g x) (g y) (cong g p) (cong g q) i j
    where
    g = elimSetQuotientsProp Bprop f
elimSetQuotientsProp Bprop f (eq/ a b r i) = elimEq/ Bprop (eq/ a b r) (f a) (f b) i

-- lemma 6.10.2 in hott book
-- TODO: defined truncated Sigma as ∃
[]surjective : (x : A / R) → ∥ Σ[ a ∈ A ] [ a ] ≡ x ∥
[]surjective = elimSetQuotientsProp (λ x → squash) (λ a → ∣ a , refl ∣)

elimSetQuotients : {B : A / R → Set ℓ} →
                   (Bset : (x : A / R) → isSet (B x)) →
                   (f : (a : A) → (B [ a ])) →
                   (feq : (a b : A) (r : R a b) →
                          PathP (λ i → B (eq/ a b r i)) (f a) (f b)) →
                   (x : A / R) → B x
elimSetQuotients Bset f feq [ a ] = f a
elimSetQuotients Bset f feq (eq/ a b r i) = feq a b r i
elimSetQuotients Bset f feq (squash/ x y p q i j) =
  elimSquash₀ Bset (squash/ x y p q)
              (g x) (g y) (cong g p) (cong g q) i j
    where
      g = elimSetQuotients Bset f feq


setQuotUniversal : {B : Set ℓ} (Bset : isSet B) →
                   (A / R → B) ≃ (Σ[ f ∈ (A → B) ] ((a b : A) → R a b → f a ≡ f b))
setQuotUniversal Bset = isoToEquiv (iso intro elim elimRightInv elimLeftInv)
  where
  intro = λ g →  (λ a → g [ a ]) , λ a b r i → g (eq/ a b r i)
  elim = λ h → elimSetQuotients (λ x → Bset) (fst h) (snd h)

  elimRightInv : ∀ h → intro (elim h) ≡ h
  elimRightInv h = refl

  elimLeftInv : ∀ g → elim (intro g) ≡ g
  elimLeftInv = λ g → funExt (λ x → elimPropTrunc {P = λ sur → elim (intro g) x ≡ g x}
    (λ sur → Bset (elim (intro g) x) (g x))
    (λ sur → cong (elim (intro g)) (sym (snd sur)) ∙ (cong g (snd sur))) ([]surjective x)
    )

reflect : (Rprop : BinaryRelation.isProp R) (Requiv : BinaryRelation.isEquiv R) (a b : A) → [ a ] ≡ [ b ] → R a b
reflect {ℓ} {ℓ'} {A = A} {R = R} Rprop (BinaryRelation.Equiv R/refl R/sym R/trans) a b p = transport aa≡ab R/refl
  where
    helper : A / R → hProp
    helper = elimSetQuotients (λ _ → isSetHProp) (λ c → (R a c , Rprop a c)) λ c d cd → ΣProp≡ (λ _ → isPropIsProp) (ua (PropEquiv→Equiv (Rprop a c) (Rprop a d) (λ ac → R/trans ac cd) (λ ad → R/trans ad (R/sym cd))))

    aa≡ab : R a a ≡ R a b
    aa≡ab i = fst (helper (p i))

isEquiv→isEffective : BinaryRelation.isProp R → BinaryRelation.isEquiv R → BinaryRelation.isEffective R
isEquiv→isEffective {R = R} Rprop Req a b = isoToEquiv (iso intro elim intro-elim elim-intro)
  where
    intro : [ a ] ≡ [ b ] → R a b
    intro = reflect Rprop Req a b

    elim : R a b → [ a ] ≡ [ b ]
    elim = eq/ a b

    intro-elim : ∀ x → intro (elim x) ≡ x
    intro-elim ab = Rprop a b _ _

    elim-intro : ∀ x → elim (intro x) ≡ x
    elim-intro eq = squash/ _ _ _ _

discreteSetQuotients : Discrete A → BinaryRelation.isProp R → BinaryRelation.isEquiv R → (∀ a₀ a₁ → Dec (R a₀ a₁)) → Discrete (A / R)
discreteSetQuotients {A = A} {R = R} Adis Rprop Req Rdec = elimSetQuotients ((λ a₀ → isSetPi (λ a₁ → isProp→isSet (isPropDec (squash/ a₀ a₁))))) discreteSetQuotients' discreteSetQuotients'-eq
  where
    discreteSetQuotients' : (a : A) (y : A / R) → Dec ([ a ] ≡ y)
    discreteSetQuotients' a₀ = elimSetQuotients ((λ a₁ → isProp→isSet (isPropDec (squash/ [ a₀ ] a₁)))) dis dis-eq
      where
        dis : (a₁ : A) → Dec ([ a₀ ] ≡ [ a₁ ])
        dis a₁ with Rdec a₀ a₁
        ... | (yes p) = yes (eq/ a₀ a₁ p)
        ... | (no ¬p) = no λ eq → ¬p (reflect Rprop Req a₀ a₁ eq )

        dis-eq : (a b : A) (r : R a b) →
          PathP (λ i → Dec ([ a₀ ] ≡ eq/ a b r i)) (dis a) (dis b)
        dis-eq a b ab = J (λ b ab → ∀ k → PathP (λ i → Dec ([ a₀ ] ≡ ab i)) (dis a) k) (λ k → isPropDec (squash/ _ _) _  _) (eq/ a b ab)
                          (dis b)
        
    discreteSetQuotients'-eq : (a b : A) (r : R a b) →
      PathP (λ i → (y : A / R) → Dec (eq/ a b r i ≡ y))
      (discreteSetQuotients' a) (discreteSetQuotients' b)
    discreteSetQuotients'-eq a b ab = J
                                        (λ b ab →
                                           ∀ k →
                                           PathP (λ i → (y : A / R) → Dec (ab i ≡ y))
                                           (discreteSetQuotients' a) k)
                                        (λ k → funExt (λ x → isPropDec (squash/ _ _) _ _)) (eq/ a b ab) (discreteSetQuotients' b)
