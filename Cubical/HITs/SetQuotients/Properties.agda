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
    eq = +-sym n 1

hLevelRespectEquiv : ∀ {ℓ ℓ'} → {A : Set ℓ}  {B : Set ℓ'} → (n : ℕ) → A ≃ B → isOfHLevel n A → isOfHLevel n B
hLevelRespectEquiv zero eq hA = (fst eq (fst hA)) , (λ b → compPath (cong (fst eq) (snd hA (fst (fst (equiv-proof (snd eq) b))))) (snd (fst (equiv-proof (snd eq) b))))
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
    R : A → A → hProp {ℓ = ℓ'}
    B : A / R → Set ℓ''

elimEq/ : ((x : A / R ) → isProp (B x)) →
          {x y : A / R} →
          (eq : x ≡ y) →
          (bx : B x) →
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

elimSetQuotients : (Bset : (x : A / R) → isSet (B x)) → 
                   (f : (a : A) → (B [ a ])) →
                   (feq : (a b : A) (r : fst (R a b)) →
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
                   (A / R → B) ≃ (Σ[ f ∈ (A → B) ] ((a b : A) → fst (R a b) → f a ≡ f b))
setQuotUniversal Bset = isoToEquiv (iso intro elim elimRightInv elimLeftInv)
  where
  intro = λ g →  (λ a → g [ a ]) , λ a b r i → g (eq/ a b r i)
  elim = λ h → elimSetQuotients (λ x → Bset) (fst h) (snd h)

  elimRightInv : ∀ h → intro (elim h) ≡ h
  elimRightInv h = refl

  elimLeftInv : ∀ g → elim (intro g) ≡ g
  elimLeftInv = λ g → funExt (λ x → elimPropTrunc {P = λ sur → elim (intro g) x ≡ g x}
    (λ sur → Bset (elim (intro g) x) (g x))
    (λ sur → compPath (cong (elim (intro g)) (sym (snd sur))) (cong g (snd sur))) ([]surjective x)
    )

reflect : ∀ {ℓ ℓ'} {A : Set ℓ} {R : A → A → hProp {ℓ = ℓ'}} (equiv : BinaryRelation.isEquiv R) (a b : A) → [ a ] ≡ [ b ] → fst (R a b)
reflect {ℓ} {ℓ'} {A = A} {R = R} (BinaryRelation.Equiv R/refl R/sym R/trans) a b p = transport aa≡ab R/refl
  where
    helper : A / R → hProp
    helper = elimSetQuotients (λ _ → isSetHProp) (λ c → R a c) λ c d cd → ΣProp≡ (λ _ → isPropIsProp) (ua (PropEquiv→Equiv (snd (R a c)) (snd (R a d)) (λ ac → R/trans ac cd) (λ ad → R/trans ad (R/sym cd))))

    aa≡ab : fst (R a a) ≡ fst (R a b)
    aa≡ab i = fst (helper (p i))

isEquiv→isEffective : BinaryRelation.isEquiv R → BinaryRelation.isEffective R
isEquiv→isEffective {R = R} Req a b = isoToEquiv (iso intro elim intro-elim elim-intro)
  where
    intro : [ a ] ≡ [ b ] → fst (R a b)
    intro = reflect Req a b

    elim : fst (R a b) → [ a ] ≡ [ b ]
    elim = eq/ a b

    intro-elim : ∀ x → intro (elim x) ≡ x
    intro-elim ab = snd (R a b) _ _

    elim-intro : ∀ x → elim (intro x) ≡ x
    elim-intro eq = squash/ _ _ _ _

discreteSetQuotients : Discrete A → BinaryRelation.isEquiv R → (∀ a₀ a₁ → Dec (fst (R a₀ a₁))) → Discrete (A / R)
discreteSetQuotients {A = A} {R = R} Adis Req Rdec = elimSetQuotients ((λ a₀ → isSetPi (λ a₁ → isProp→isSet (isPropDec (squash/ a₀ a₁))))) discreteSetQuotients' discreteSetQuotients'-eq
  where
    discreteSetQuotients' : (a : A) (y : A / R) → Dec ([ a ] ≡ y)
    discreteSetQuotients' a₀ = elimSetQuotients ((λ a₁ → isProp→isSet (isPropDec (squash/ [ a₀ ] a₁)))) dis dis-eq
      where
        dis : (a₁ : A) → Dec ([ a₀ ] ≡ [ a₁ ])
        dis a₁ with Rdec a₀ a₁
        ... | (yes p) = yes (eq/ a₀ a₁ p)
        ... | (no ¬p) = no λ eq → ¬p (reflect Req a₀ a₁ eq )

        dis-eq : (a b : A) (r : fst (R a b)) →
          PathP (λ i → Dec ([ a₀ ] ≡ eq/ a b r i)) (dis a) (dis b)
        dis-eq a b ab = J (λ b ab → ∀ k → PathP (λ i → Dec ([ a₀ ] ≡ ab i)) (dis a) k) (λ k → isPropDec (squash/ _ _) _  _) (eq/ a b ab)
                          (dis b)
        
    discreteSetQuotients'-eq : (a b : A) (r : fst (R a b)) →
      PathP (λ i → (y : A / R) → Dec (eq/ a b r i ≡ y))
      (discreteSetQuotients' a) (discreteSetQuotients' b)
    discreteSetQuotients'-eq a b ab = J
                                        (λ b ab →
                                           ∀ k →
                                           PathP (λ i → (y : A / R) → Dec (ab i ≡ y))
                                           (discreteSetQuotients' a) k)
                                        (λ k → funExt (λ x → isPropDec (squash/ _ _) _ _)) (eq/ a b ab) (discreteSetQuotients' b)
{- 


something : ∀ {ℓ} {A B : Set ℓ} {n : ℕ} {pa : isOfHLevel n A} {pb : isOfHLevel n B} → isOfHLevel n ((A , pa) ≡ (B , pb))
something = {!!}







something0 : ∀ {ℓ} {A B : Set ℓ} (n : ℕ) (ha : isOfHLevel n A) (hb : isOfHLevel n B)  → ((A , ha) ≡ (B , hb)) ≡ (A ≡ B)
something0 {A = A} {B = B} n ha hb  = ua (isoToEquiv (iso intro elim intro-elim elim-intro))
  where
    intro : (A , ha) ≡ (B , hb) → A ≡ B
    intro eq = cong fst eq

    elim :  A ≡ B → (A , ha) ≡ (B , hb)
    elim eq i = (eq i , J (λ B eq → (ha : isOfHLevel n A) (hb : isOfHLevel n B) → PathP (λ i → isOfHLevel n (eq i)) ha hb) (λ ha hb → isPropIsOfHLevel n ha hb) eq ha hb i) 

    elim-intro : (eq : (A , ha) ≡ (B , hb)) → elim (intro eq) ≡ eq
    elim-intro eq = cong {!transport (Σ≡ (A , ha) (B , hb))!} {!!}

    intro-elim : (eq : A ≡ B) → intro (elim eq) ≡ eq
    intro-elim  eq = refl



hPropEquiv→Equiv : ∀ {ℓ} {A B : hProp {ℓ = ℓ}} (f : fst A ≃ fst B) → (A ≡ B)
hPropEquiv→Equiv {ℓ} {A} {B} eq = fst Σ≡ (eq0 ,  eq1)
    where
      eq0 : fst A ≡ fst B
      eq0 = (ua (PropEquiv→Equiv (snd A) (snd B) (fst eq) (invEq eq)))

      eq1 : PathP (λ i → isProp (eq0 i)) (snd A) (snd B)
      eq1 = J (λ b eq → ∀ k → PathP (λ i → isProp (eq i)) (snd A) k) (isPropIsProp (snd A)) eq0 (snd B)


hLevel≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (n : ℕ) (hA : isOfHLevel n A) (hB : isOfHLevel n B) → isOfHLevel n (A ≃ B)
hLevel≃ {A = A} {B = B}  zero hA hB = 
  let
    f : A → B
    f _ = fst hB
    isEquivF : isEquiv f
    isEquivF = (record { equiv-proof = λ y → ((fst hA) , (snd hB y)) , (λ z → λ i → (snd hA (fst z) i , isProp→isSet(isContr→isProp hB) (fst hB) y (snd hB y) (snd z) i)) })
  in 
    (f , isEquivF) , (λ y →
    let
      eq : (λ _ → fst hB) ≡ fst y
      eq = funExt (λ a → snd hB (fst y a))
    in fst Σ≡ (eq , J (λ g eq → ∀ y → PathP (λ i → isEquiv (eq i)) isEquivF (snd y)) (λ y → isPropIsEquiv f _ _)
                            eq {!y!}))

hLevel≃ (suc n) hA hB = hLevelSigma (suc n) (hLevelPi (suc n) (λ _ → hB)) (λ a → subst (λ n → isOfHLevel n (isEquiv a)) (sucN≡n+1 n)  (liftHLevel n (isProp→IsOfHLevel1 (isPropIsEquiv a))))
  where
    sucN≡n+1 : ∀ n → n + 1 ≡ suc n 
    sucN≡n+1 n = +-sym n 1

app-equiv : ∀ {ℓ ℓ'} → {A : Set ℓ} → {B : Set ℓ'} → (e : A ≃ B) → (a0 a1 : A) → (a0 ≡ a1) ≃ (fst e a0 ≡ fst e a1)
app-equiv e a0 a1  = (cong (fst e)) , (record { equiv-proof = λ e' → {!!} })



hLevel≡ : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} (n : ℕ) (hA : isOfHLevel n A) (hB : isOfHLevel n B) → isOfHLevel n (A ≡ B)
hLevel≡ n hA hB = subst (λ eq → isOfHLevel n eq) (sym (ua {!univalence!})) {!!}

hLevelHLevel : ∀ {ℓ} (n : ℕ) → isOfHLevel (suc n) (HLevel n)
hLevelHLevel n = {!!}

hProp≃1types : ∀ {ℓ} → hProp ≃ HLevel 1
hProp≃1types = isoToEquiv (iso {!intro!} {!!} {!!} {!!})
  where
    intro : hProp → HLevel 1
    intro hp = (fst hp) , (isProp→IsOfHLevel1 (snd hp))

    elim : HLevel 1 → hProp
    elim hl = (fst hl), isOfHLevel1→isProp (snd hl)

    intro-elim : ∀ hl → intro (elim hl) ≡ hl
    intro-elim hl = fst Σ≡ (refl , isPropIsOfHLevel 1 _ _)

    elim-intro : ∀ hp → elim (intro hp) ≡ hp
    elim-intro hp = fst Σ≡ (refl , funExt λ a → funExt (λ b → refl))

isSetHProp : isSet hProp
isSetHProp = isOfHLevel2→isSet (subst (λ t → isOfHLevel 2 t) (sym (ua hProp≃1types)) (hLevelHLevel 1))

isSetSigma : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
  → (isSet A)
  → ((x : A) → isSet (B x))
  → isSet (Σ A B)
isSetSigma Aset Bset = isOfHLevel2→isSet (hLevelSigma 2 (isSet→isOfHLevel2 Aset) (λ a → isSet→isOfHLevel2 (Bset a)))

module _ {ℓ ℓ' : Level} (A : Set ℓ) (R : A → A → hProp {ℓ = ℓ'}) where

  isEquivClassOf : {ℓ'' : Level} (P : A → hProp {ℓ = ℓ''}) → Set (ℓ-max (ℓ-max ℓ ℓ'') ℓ')
  isEquivClassOf P = ∥ (Σ[ a ∈ A ] ((b : A) → fst (R a b) ≃ fst (P b) )) ∥

  _∥_ : {ℓ'' : Level} → Set (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ''))
  _∥_ {ℓ'' = ℓ''} = Σ[ P ∈ (A → hProp {ℓ = ℓ''}) ] isEquivClassOf P

  ⟦_⟧ : A → _∥_
  ⟦ a ⟧ = (R a) , ∣ a , (λ b → transportEquiv refl)  ∣

  isSet∥ : isSet _∥_
  isSet∥ = isSetSigma (isSetPi (λ _ → isSetHProp)) λ _ → isProp→isSet squash

  module _ (Rer : isEquivRelation R) where
    R-eq : (a b : A) (r : fst (R a b)) → ∀ c → fst (R a c) ≡ fst (R b c)
    R-eq a b r c = ua (PropEquiv→Equiv ((snd (fst (⟦ a ⟧) c))) (snd (fst (⟦ b ⟧) c))
              (λ ac → isEquivRelation.trans Rer b a c (isEquivRelation.sym Rer a b r) ac )
              (λ bc → isEquivRelation.trans Rer a b c r bc))

    ⟦⟧-eq : (a b : A) (r : fst (R a b)) → (⟦ a ⟧) ≡ (⟦ b ⟧)
    ⟦⟧-eq a b r = ΣProp≡ (λ P → squash) (funExt (λ c → ΣProp≡ (λ _ → isPropIsProp) (R-eq a b r c)))

    f : A / R → _∥_
    f = elimSetQuotients (λ _ → isSet∥) ⟦_⟧ ⟦⟧-eq

    f[]≡⟦⟧ : ∀ a → f [ a ] ≡ ⟦ a ⟧
    f[]≡⟦⟧ a = refl

    surjective⟦⟧ : (y : _∥_) → ∥ (Σ[ a ∈ A ] ⟦ a ⟧ ≡ y) ∥
    surjective⟦⟧ y = elimPropTrunc {P = λ z → ∥ (Σ[ a ∈ A ] ⟦ a ⟧ ≡ y) ∥} (λ z → squash ) (λ z → ∣ (fst z) , ΣProp≡ (λ a → squash) (funExt (λ b → hPropEquiv→Equiv (snd z b))) ∣ ) (snd y)

    surjectiveF : (y : _∥_) → Σ[ x ∈ A / R ] f x ≡ y
    surjectiveF y = {!!}

    isEquivF : isEquiv f
    isEquivF = record { equiv-proof = λ y → ({!snd y!} , {!!}) , {!!} }

    /≃∥ : (A / R) ≃ _∥_
    /≃∥ = (f , isEquivF)

    discrete∥ : Discrete A → (∀ a0 a1 → Dec (fst (R a0 a1))) → Discrete _∥_
    discrete∥ Adis Rdec y0 y1 = elimPropTrunc {P = λ _ → Dec (y0 ≡ y1)} (λ _ → isPropDec (isSet∥ y0 y1)) (λ z0 → elimPropTrunc {P = λ _ → Dec (y0 ≡ y1)} (λ _ → isPropDec (isSet∥ y0 y1)) (λ z1 → helper z0 z1) (snd y1)) (snd y0)
      where
      helper : ∀ z0 z1 → Dec (y0 ≡ y1)
      helper (a0 , eq0) (a1 , eq1) with (Rdec a0 a1)
      ... | yes r = yes (ΣProp≡ (λ P → squash) (funExt (λ b → ΣProp≡ (λ _ → isPropIsProp)
        (fst (fst y0 b) ≡⟨ sym (ua (eq0 b))  ⟩
        (fst (R a0 b) ≡⟨ R-eq a0 a1 r b ⟩
        fst (R a1 b) ≡⟨ ua (eq1 b) ⟩
        fst (fst y1 b) ∎ )))))
      ... | no nr = no (λ eq → {!!})


-}
