{-

Set quotients:

-}

{-# OPTIONS --safe #-}
module Cubical.HITs.SetQuotients.Properties where

open import Cubical.HITs.SetQuotients.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

open import Cubical.HITs.TypeQuotients as TypeQuot using (_/ₜ_ ; [_] ; eq/)
open import Cubical.HITs.PropositionalTruncation as PropTrunc using (∥_∥ ; ∣_∣ ; squash)
open import Cubical.HITs.SetTruncation as SetTrunc using (∥_∥₂ ; ∣_∣₂ ; squash₂
                                                              ; isSetSetTrunc)


private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    R : A → A → Type ℓ
    B : A / R → Type ℓ
    C : A / R → A / R → Type ℓ
    D : A / R → A / R → A / R → Type ℓ

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
elimProp Bprop f (eq/ a b r i) = isProp→PathP (λ i → Bprop ((eq/ a b r) i)) (f a) (f b) i

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

-- sometimes more convenient:
elimContr : (∀ (a : A) → isContr (B [ a ]))
          → (x : A / R) → B x
elimContr Bcontr = elimProp (elimProp (λ _ → isPropIsProp) λ _ → isContr→isProp (Bcontr _))
                             λ _ → Bcontr _ .fst

elimContr2 : (∀ (a b : A) → isContr (C [ a ] [ b ]))
           → (x y : A / R) → C x y
elimContr2 Ccontr = elimContr λ _ → isOfHLevelΠ 0
                   (elimContr λ _ → inhProp→isContr (Ccontr _ _) isPropIsContr)

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

-- the recursor for maps into groupoids:
-- i.e. for any type A with a binary relation R and groupoid B,
-- we can construct a map A / R → B from a map A → B satisfying the conditions
-- (i)   ∀ (a b : A) → R a b → f a ≡ f b
-- (ii)  ∀ (a b : A) → isProp (f a ≡ f b)

-- We start by proving that we can recover the set-quotient
-- by set-truncating the (non-truncated type quotient)
typeQuotSetTruncIso : Iso (A / R) ∥ A /ₜ R ∥₂
Iso.fun typeQuotSetTruncIso = rec isSetSetTrunc (λ a → ∣ [ a ] ∣₂)
                                                 λ a b r → cong ∣_∣₂ (eq/ a b r)
Iso.inv typeQuotSetTruncIso = SetTrunc.rec squash/ (TypeQuot.rec [_] eq/)
Iso.rightInv typeQuotSetTruncIso = SetTrunc.elim (λ _ → isProp→isSet (squash₂ _ _))
                                  (TypeQuot.elimProp (λ _ → squash₂ _ _) λ _ → refl)
Iso.leftInv typeQuotSetTruncIso = elimProp (λ _ → squash/ _ _) λ _ → refl

module rec→Gpd {A : Type ℓ} {R : A → A → Type ℓ'} {B : Type ℓ''} (Bgpd : isGroupoid B)
               (f : A → B)
               (feq : ∀ (a b : A) → R a b → f a ≡ f b)
               (fprop : ∀ (a b : A) → isProp (f a ≡ f b)) where

 fun : A / R → B
 fun = f₁ ∘ f₂
  where
  f₁ : ∥ A /ₜ R ∥₂ → B
  f₁ = SetTrunc.rec→Gpd.fun Bgpd f/ congF/Const
   where
   f/ : A /ₜ R → B
   f/ = TypeQuot.rec f feq
   congF/Const : (a b : A /ₜ R) (p q : a ≡ b) → cong f/ p ≡ cong f/ q
   congF/Const = TypeQuot.elimProp2 (λ _ _ → isPropΠ2 λ _ _ → Bgpd _ _ _ _)
                                     λ a b p q → fprop a b (cong f/ p) (cong f/ q)

  f₂ : A / R → ∥ A /ₜ R ∥₂
  f₂ = Iso.fun typeQuotSetTruncIso


setQuotUniversalIso : {B : Type ℓ} (Bset : isSet B)
                    → Iso (A / R → B) (Σ[ f ∈ (A → B) ] ((a b : A) → R a b → f a ≡ f b))
Iso.fun (setQuotUniversalIso Bset) g = (λ a → g [ a ]) , λ a b r i → g (eq/ a b r i)
Iso.inv (setQuotUniversalIso Bset) h = elim (λ x → Bset) (fst h) (snd h)
Iso.rightInv (setQuotUniversalIso Bset) h = refl
Iso.leftInv (setQuotUniversalIso Bset) g =
 funExt (λ x → PropTrunc.elim (λ sur → Bset (out (intro g) x) (g x))
        (λ sur → cong (out (intro g)) (sym (snd sur)) ∙ (cong g (snd sur))) ([]surjective x))
     where
     intro = Iso.fun (setQuotUniversalIso Bset)
     out = Iso.inv (setQuotUniversalIso Bset)

setQuotUniversal : {B : Type ℓ} (Bset : isSet B) →
                   (A / R → B) ≃ (Σ[ f ∈ (A → B) ] ((a b : A) → R a b → f a ≡ f b))
setQuotUniversal Bset = isoToEquiv (setQuotUniversalIso Bset)

open BinaryRelation

setQuotUnaryOp : (-_ : A → A)
               → (∀ a a' → R a a' → R (- a) (- a'))
               → (A / R → A / R)
setQuotUnaryOp -_ h = Iso.inv (setQuotUniversalIso squash/) ((λ a → [ - a ]) , λ a b x → eq/ _ _ (h _ _ x))

-- characterisation of binary functions/operations on set-quotients
setQuotUniversal2Iso : {B : Type ℓ} (Bset : isSet B) → isRefl R
                 → Iso (A / R → A / R → B)
                       (Σ[ _∗_ ∈ (A → A → B) ] ((a a' b b' : A) → R a a' → R b b' → a ∗ b ≡ a' ∗ b'))
Iso.fun (setQuotUniversal2Iso {A = A} {R = R} {B = B} Bset isReflR) _∗/_ = _∗_ , h
   where
   _∗_ = λ a b → [ a ] ∗/ [ b ]
   h : (a a' b b' : A) → R a a' → R b b' → a ∗ b ≡ a' ∗ b'
   h a a' b b' ra rb = cong (_∗/ [ b ]) (eq/ _ _ ra) ∙ cong ([ a' ] ∗/_) (eq/ _ _ rb)
Iso.inv (setQuotUniversal2Iso {A = A} {R = R} {B = B} Bset isReflR) (_∗_ , h) =
   rec2 Bset _∗_ hleft hright
        where
        hleft : ∀ a b c → R a b → (a ∗ c) ≡ (b ∗ c)
        hleft _ _ c r = h _ _ _ _ r (isReflR c)
        hright : ∀ a b c → R b c → (a ∗ b) ≡ (a ∗ c)
        hright a _ _ r = h _ _ _ _ (isReflR a) r
Iso.rightInv (setQuotUniversal2Iso {A = A} {R = R} {B = B} Bset isReflR) (_∗_ , h) =
   Σ≡Prop (λ _ → isPropΠ4 λ _ _ _ _ → isPropΠ2 λ _ _ → Bset _ _) refl
Iso.leftInv (setQuotUniversal2Iso {A = A} {R = R} {B = B} Bset isReflR) _∗/_ =
   funExt₂ (elimProp2 (λ _ _ → Bset _ _) λ _ _ → refl)

setQuotUniversal2 : {B : Type ℓ} (Bset : isSet B) → isRefl R
                  → (A / R → A / R → B)
                  ≃ (Σ[ _∗_ ∈ (A → A → B) ] ((a a' b b' : A) → R a a' → R b b' → a ∗ b ≡ a' ∗ b'))
setQuotUniversal2 Bset isReflR = isoToEquiv (setQuotUniversal2Iso Bset isReflR)

-- corollary for binary operations
-- TODO: prove truncated inverse for effective relations
setQuotBinOp : isRefl R
             → (_∗_ : A → A → A)
             → (∀ a a' b b' → R a a' → R b b' → R (a ∗ b) (a' ∗ b'))
             → (A / R → A / R → A / R)
setQuotBinOp isReflR _∗_ h = Iso.inv (setQuotUniversal2Iso squash/ isReflR)
                             ((λ a b → [ a ∗ b ]) , λ _ _ _ _ ra rb → eq/ _ _ (h _ _ _ _ ra rb))

setQuotSymmBinOp : isRefl R → isTrans R
                 → (_∗_ : A → A → A)
                 → (∀ a b → a ∗ b ≡ b ∗ a)
                 → (∀ a a' b → R a a' → R (a ∗ b) (a' ∗ b))
                 → (A / R → A / R → A / R)
setQuotSymmBinOp {A = A} {R = R} isReflR isTransR _∗_ ∗-symm h = setQuotBinOp isReflR _∗_ h'
  where
  h' : ∀ a a' b b' → R a a' → R b b' → R (a ∗ b) (a' ∗ b')
  h' a a' b b' ra rb = isTransR _ _ _ (h a a' b ra)
                               (transport (λ i → R (∗-symm b a' i) (∗-symm b' a' i)) (h b b' a' rb))


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

isEquivRel→effectiveIso : isPropValued R → isEquivRel R → (a b : A) → Iso ([ a ] ≡ [ b ]) (R a b)
Iso.fun (isEquivRel→effectiveIso {R = R} Rprop Req a b) = effective Rprop Req a b
Iso.inv (isEquivRel→effectiveIso {R = R} Rprop Req a b) = eq/ a b
Iso.rightInv (isEquivRel→effectiveIso {R = R} Rprop Req a b) _ = Rprop a b _ _
Iso.leftInv (isEquivRel→effectiveIso {R = R} Rprop Req a b) _ = squash/ _ _ _ _

isEquivRel→isEffective : isPropValued R → isEquivRel R → isEffective R
isEquivRel→isEffective Rprop Req a b = isoToIsEquiv (invIso (isEquivRel→effectiveIso Rprop Req a b))

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


-- Quotienting by the truncated relation is equivalent to quotienting by untruncated relation
truncRelIso : Iso (A / R) (A / (λ a b → ∥ R a b ∥))
Iso.fun truncRelIso = rec squash/ [_] λ _ _ r → eq/ _ _ ∣ r ∣
Iso.inv truncRelIso = rec squash/ [_] λ _ _ → PropTrunc.rec (squash/ _ _) λ r → eq/ _ _ r
Iso.rightInv truncRelIso = elimProp (λ _ → squash/ _ _) λ _ → refl
Iso.leftInv truncRelIso = elimProp (λ _ → squash/ _ _) λ _ → refl

truncRelEquiv : A / R ≃ A / (λ a b → ∥ R a b ∥)
truncRelEquiv = isoToEquiv truncRelIso

-- Using this we can obtain a useful characterization of
-- path-types for equivalence relations (not prop-valued)
-- and their quotients

isEquivRel→TruncIso : isEquivRel R → (a b : A) → Iso ([ a ] ≡ [ b ])  ∥ R a b ∥
isEquivRel→TruncIso {A = A} {R = R} Req a b = compIso (isProp→Iso (squash/ _ _) (squash/ _ _)
                                   (cong (Iso.fun truncRelIso)) (cong (Iso.inv truncRelIso)))
                      (isEquivRel→effectiveIso  (λ _ _ → PropTrunc.isPropPropTrunc) ∥R∥eq a b)
 where
 open isEquivRel
 ∥R∥eq : isEquivRel  λ a b → ∥ R a b ∥
 reflexive ∥R∥eq a = ∣ reflexive Req a ∣
 symmetric ∥R∥eq a b = PropTrunc.map (symmetric Req a b)
 transitive ∥R∥eq a b c = PropTrunc.map2 (transitive Req a b c)
