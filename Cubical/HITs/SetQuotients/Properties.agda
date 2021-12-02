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
    A B C : Type ℓ
    R S T : A → A → Type ℓ

elimProp : {P : A / R → Type ℓ}
  → (∀ x → isProp (P x))
  → (∀ a → P [ a ])
  → ∀ x → P x
elimProp prop f [ x ] = f x
elimProp prop f (squash/ x y p q i j) =
  isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (prop x))
    (g x) (g y) (cong g p) (cong g q) (squash/ x y p q) i j
    where
    g = elimProp prop f
elimProp prop f (eq/ a b r i) =
  isProp→PathP (λ i → prop (eq/ a b r i)) (f a) (f b) i

elimProp2 : {P : A / R → B / S → Type ℓ}
  → (∀ x y → isProp (P x y))
  → (∀ a b → P [ a ] [ b ])
  → ∀ x y → P x y
elimProp2 prop f =
  elimProp (λ x → isPropΠ (prop x)) λ a →
  elimProp (prop [ a ]) (f a)

elimProp3 : {P : A / R → B / S → C / T → Type ℓ}
  → (∀ x y z → isProp (P x y z))
  → (∀ a b c → P [ a ] [ b ] [ c ])
  → ∀ x y z → P x y z
elimProp3 prop f =
  elimProp (λ x → isPropΠ2 (prop x)) λ a →
  elimProp2 (prop [ a ]) (f a)

-- sometimes more convenient:
elimContr : {P : A / R → Type ℓ}
  → (∀ a → isContr (P [ a ]))
  → ∀ x → P x
elimContr contr =
  elimProp (elimProp (λ _ → isPropIsProp) λ _ → isContr→isProp (contr _)) λ _ →
  contr _ .fst

elimContr2 : {P : A / R → B / S → Type ℓ}
  → (∀ a b → isContr (P [ a ] [ b ]))
  → ∀ x y → P x y
elimContr2 contr =
  elimContr λ _ →
  isOfHLevelΠ 0 (elimContr λ _ → inhProp→isContr (contr _ _) isPropIsContr)

-- lemma 6.10.2 in hott book
[]surjective : (x : A / R) → ∃[ a ∈ A ] [ a ] ≡ x
[]surjective = elimProp (λ x → squash) (λ a → ∣ a , refl ∣)

elim : {P : A / R → Type ℓ}
  → (∀ x → isSet (P x))
  → (f : (a : A) → (P [ a ]))
  → ((a b : A) (r : R a b) → PathP (λ i → P (eq/ a b r i)) (f a) (f b))
  → ∀ x → P x
elim set f feq [ a ] = f a
elim set f feq (eq/ a b r i) = feq a b r i
elim set f feq (squash/ x y p q i j) =
  isOfHLevel→isOfHLevelDep 2 set
    (g x) (g y) (cong g p) (cong g q) (squash/ x y p q) i j
  where
  g = elim set f feq

rec : isSet B
  → (f : A → B)
  → ((a b : A) (r : R a b) → f a ≡ f b)
  → A / R → B
rec set f feq [ a ] = f a
rec set f feq (eq/ a b r i) = feq a b r i
rec set f feq (squash/ x y p q i j) = set (g x) (g y) (cong g p) (cong g q) i j
  where
  g = rec set f feq

rec2 : isSet C
  → (f : A → B → C)
  → (∀ a b c → R a b → f a c ≡ f b c)
  → (∀ a b c → S b c → f a b ≡ f a c)
  → A / R → B / S → C
rec2 set f feql feqr =
  rec (isSetΠ (λ _ → set))
    (λ a → rec set (f a) (feqr a))
    (λ a b r → funExt (elimProp (λ _ → set _ _) (λ c → feql a b c r)))

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

module rec→Gpd {B : Type ℓ''} (Bgpd : isGroupoid B)
  (f : A → B)
  (feq : ∀ (a b : A) → R a b → f a ≡ f b)
  (fprop : ∀ (a b : A) → isProp (f a ≡ f b))
  where

  fun : A / R → B
  fun = f₁ ∘ f₂
    where
    f₁ : ∥ A /ₜ R ∥₂ → B
    f₁ = SetTrunc.rec→Gpd.fun Bgpd f/ congF/Const
      where
      f/ : A /ₜ R → B
      f/ = TypeQuot.rec f feq

      congF/Const : (a b : A /ₜ R) (p q : a ≡ b) → cong f/ p ≡ cong f/ q
      congF/Const =
        TypeQuot.elimProp2
          (λ _ _ → isPropΠ2 λ _ _ → Bgpd _ _ _ _)
          (λ a b p q → fprop a b (cong f/ p) (cong f/ q))

    f₂ : A / R → ∥ A /ₜ R ∥₂
    f₂ = Iso.fun typeQuotSetTruncIso


setQuotUniversalIso : isSet B
  → Iso (A / R → B) (Σ[ f ∈ (A → B) ] ((a b : A) → R a b → f a ≡ f b))
Iso.fun (setQuotUniversalIso Bset) g = (λ a → g [ a ]) , λ a b r i → g (eq/ a b r i)
Iso.inv (setQuotUniversalIso Bset) h = rec Bset (fst h) (snd h)
Iso.rightInv (setQuotUniversalIso Bset) h = refl
Iso.leftInv (setQuotUniversalIso Bset) g =
 funExt λ x →
 PropTrunc.rec
   (Bset (out (intro g) x) (g x))
   (λ sur → cong (out (intro g)) (sym (snd sur)) ∙ (cong g (snd sur)))
   ([]surjective x)
 where
 intro = Iso.fun (setQuotUniversalIso Bset)
 out = Iso.inv (setQuotUniversalIso Bset)

setQuotUniversal : isSet B
  → (A / R → B) ≃ (Σ[ f ∈ (A → B) ] ((a b : A) → R a b → f a ≡ f b))
setQuotUniversal Bset = isoToEquiv (setQuotUniversalIso Bset)

open BinaryRelation

setQuotUnaryOp : (-_ : A → A)
  → (∀ a a' → R a a' → R (- a) (- a'))
  → (A / R → A / R)
setQuotUnaryOp -_ h = rec squash/ (λ a → [ - a ]) (λ a b x → eq/ _ _ (h _ _ x))

-- characterisation of binary functions/operations on set-quotients
setQuotUniversal2Iso : isSet C → isRefl R → isRefl S
  → Iso (A / R → B / S → C)
        (Σ[ _∗_ ∈ (A → B → C) ] (∀ a a' b b' → R a a' → S b b' → a ∗ b ≡ a' ∗ b'))
Iso.fun (setQuotUniversal2Iso {R = R} {S = S} Bset isReflR isReflS) _∗/_ = _∗_ , h
  where
  _∗_ = λ a b → [ a ] ∗/ [ b ]

  h : ∀ a a' b b' → R a a' → S b b' → a ∗ b ≡ a' ∗ b'
  h a a' b b' r s = cong (_∗/ [ b ]) (eq/ _ _ r) ∙ cong ([ a' ] ∗/_) (eq/ _ _ s)
Iso.inv (setQuotUniversal2Iso {R = R} {S = S} Bset isReflR isReflS) (_∗_ , h) =
  rec2 Bset _∗_ hleft hright
  where
  hleft : ∀ a a' b → R a a' → (a ∗ b) ≡ (a' ∗ b)
  hleft _ _ b r = h _ _ _ _ r (isReflS b)

  hright : ∀ a b b' → S b b' → (a ∗ b) ≡ (a ∗ b')
  hright a _ _ r = h _ _ _ _ (isReflR a) r
Iso.rightInv (setQuotUniversal2Iso Bset isReflR isReflS) (_∗_ , h) =
   Σ≡Prop (λ _ → isPropΠ4 λ _ _ _ _ → isPropΠ2 λ _ _ → Bset _ _) refl
Iso.leftInv (setQuotUniversal2Iso Bset isReflR isReflS) _∗/_ =
   funExt₂ (elimProp2 (λ _ _ → Bset _ _) λ _ _ → refl)

setQuotUniversal2 : isSet C → isRefl R → isRefl S
  → (A / R → B / S → C)
  ≃ (Σ[ _∗_ ∈ (A → B → C) ] (∀ a a' b b' → R a a' → S b b' → a ∗ b ≡ a' ∗ b'))
setQuotUniversal2 Bset isReflR isReflS =
  isoToEquiv (setQuotUniversal2Iso Bset isReflR isReflS)

-- corollary for binary operations
-- TODO: prove truncated inverse for effective relations
setQuotBinOp : isRefl R → isRefl S
  → (_∗_ : A → B → C)
  → (∀ a a' b b' → R a a' → S b b' → T (a ∗ b) (a' ∗ b'))
  → (A / R → B / S → C / T)
setQuotBinOp isReflR isReflS _∗_ h =
  rec2 squash/ (λ a b → [ a ∗ b ])
    (λ _ _ _ r → eq/ _ _ (h _ _ _ _ r (isReflS _)))
    (λ _ _ _ s → eq/ _ _ (h _ _ _ _ (isReflR _) s))

setQuotSymmBinOp : isRefl R → isTrans R
  → (_∗_ : A → A → A)
  → (∀ a b → R (a ∗ b) (b ∗ a))
  → (∀ a a' b → R a a' → R (a ∗ b) (a' ∗ b))
  → (A / R → A / R → A / R)
setQuotSymmBinOp {A = A} {R = R} isReflR isTransR _∗_ ∗Rsymm h =
  setQuotBinOp isReflR isReflR _∗_ h'
  where
  h' : ∀ a a' b b' → R a a' → R b b' → R (a ∗ b) (a' ∗ b')
  h' a a' b b' ra rb =
    isTransR _ _ _ (h a a' b ra)
      (isTransR _ _ _ (∗Rsymm a' b)
        (isTransR _ _ _ (h b b' a' rb) (∗Rsymm b' a')))

effective : (Rprop : isPropValued R) (Requiv : isEquivRel R)
  → (a b : A) → [ a ] ≡ [ b ] → R a b
effective {A = A} {R = R} Rprop (equivRel R/refl R/sym R/trans) a b p =
  transport aa≡ab (R/refl _)
  where
    helper : A / R → hProp _
    helper =
      rec isSetHProp
        (λ c → (R a c , Rprop a c))
        (λ c d cd →
          Σ≡Prop (λ _ → isPropIsProp)
            (hPropExt (Rprop a c) (Rprop a d)
              (λ ac → R/trans _ _ _ ac cd)
              (λ ad → R/trans _ _ _ ad (R/sym _ _ cd))))

    aa≡ab : R a a ≡ R a b
    aa≡ab i = helper (p i) .fst

isEquivRel→effectiveIso : isPropValued R → isEquivRel R
  → (a b : A) → Iso ([ a ] ≡ [ b ]) (R a b)
Iso.fun (isEquivRel→effectiveIso {R = R} Rprop Req a b) = effective Rprop Req a b
Iso.inv (isEquivRel→effectiveIso {R = R} Rprop Req a b) = eq/ a b
Iso.rightInv (isEquivRel→effectiveIso {R = R} Rprop Req a b) _ = Rprop a b _ _
Iso.leftInv (isEquivRel→effectiveIso {R = R} Rprop Req a b) _ = squash/ _ _ _ _

isEquivRel→isEffective : isPropValued R → isEquivRel R → isEffective R
isEquivRel→isEffective Rprop Req a b =
  isoToIsEquiv (invIso (isEquivRel→effectiveIso Rprop Req a b))

discreteSetQuotients : Discrete A → isPropValued R → isEquivRel R
  → (∀ a₀ a₁ → Dec (R a₀ a₁))
  → Discrete (A / R)
discreteSetQuotients {A = A} {R = R} Adis Rprop Req Rdec =
  elim (λ a₀ → isSetΠ (λ a₁ → isProp→isSet (isPropDec (squash/ a₀ a₁))))
    discreteSetQuotients' discreteSetQuotients'-eq
  where
  discreteSetQuotients' : (a : A) (y : A / R) → Dec ([ a ] ≡ y)
  discreteSetQuotients' a₀ =
    elim (λ a₁ → isProp→isSet (isPropDec (squash/ [ a₀ ] a₁))) dis dis-eq
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

isEquivRel→TruncIso : isEquivRel R → (a b : A) → Iso ([ a ] ≡ [ b ]) ∥ R a b ∥
isEquivRel→TruncIso {A = A} {R = R} Req a b =
  compIso
    (isProp→Iso (squash/ _ _) (squash/ _ _)
      (cong (Iso.fun truncRelIso)) (cong (Iso.inv truncRelIso)))
    (isEquivRel→effectiveIso (λ _ _ → PropTrunc.isPropPropTrunc) ∥R∥eq a b)
  where
  open isEquivRel
  ∥R∥eq : isEquivRel λ a b → ∥ R a b ∥
  reflexive ∥R∥eq a = ∣ reflexive Req a ∣
  symmetric ∥R∥eq a b = PropTrunc.map (symmetric Req a b)
  transitive ∥R∥eq a b c = PropTrunc.map2 (transitive Req a b c)

-- quotienting by 'logically equivalent' relations gives the same quotient
relBiimpl→TruncIso : ({a b : A} → R a b → S a b) → ({a b : A} → S a b → R a b) → Iso (A / R) (A / S)
Iso.fun (relBiimpl→TruncIso R→S S→R) = rec squash/ [_] λ _ _ Rab → eq/ _ _ (R→S Rab)
Iso.inv (relBiimpl→TruncIso R→S S→R) = rec squash/ [_] λ _ _ Sab → eq/ _ _ (S→R Sab)
Iso.rightInv (relBiimpl→TruncIso R→S S→R) = elimProp (λ _ → squash/ _ _) λ _ → refl
Iso.leftInv (relBiimpl→TruncIso R→S S→R) = elimProp (λ _ → squash/ _ _) λ _ → refl
