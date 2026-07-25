{-

Set quotients:

-}

module Cubical.HITs.SetQuotients.Properties where

open import Cubical.HITs.SetQuotients.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

open import Cubical.HITs.TypeQuotients as TypeQuot using (_/ₜ_ ; [_] ; eq/)
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  using (∥_∥₁ ; ∣_∣₁ ; squash₁) renaming (rec to propRec)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetTruncation as SetTrunc
  using (∥_∥₂ ; ∣_∣₂ ; squash₂ ; isSetSetTrunc)


private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C Q : Type ℓ
    R S T W : A → A → Type ℓ

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

elimProp4 : {P : A / R → B / S → C / T → Q / W → Type ℓ}
  → (∀ x y z t → isProp (P x y z t))
  → (∀ a b c d → P [ a ] [ b ] [ c ] [ d ])
  → ∀ x y z t → P x y z t
elimProp4 prop f =
  elimProp (λ x → isPropΠ3 (prop x)) λ a →
  elimProp3 (prop [ a ]) (f a)

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
[]surjective = elimProp (λ x → squash₁) (λ a → ∣ a , refl ∣₁)

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
rec2 {_} {C} {_} {A} {_} {B} {_} {R} {_} {S} set f feql feqr = fun
  where
    fun₀ : A → B / S → C
    fun₀ a [ b ] = f a b
    fun₀ a (eq/ b c r i) = feqr a b c r i
    fun₀ a (squash/ x y p q i j) = isSet→SquareP (λ _ _ → set)
      (λ _ → fun₀ a x)
      (λ _ → fun₀ a y)
      (λ i → fun₀ a (p i))
      (λ i → fun₀ a (q i)) j i

    toPath : ∀ (a b : A) (x : R a b) (y : B / S) → fun₀ a y ≡ fun₀ b y
    toPath a b rab = elimProp (λ _ → set _ _) λ c → feql a b c rab

    fun : A / R → B / S → C
    fun [ a ] y = fun₀ a y
    fun (eq/ a b r i) y = toPath a b r y i
    fun (squash/ x y p q i j) z = isSet→SquareP (λ _ _ → set)
      (λ _ → fun x z)
      (λ _ → fun y z)
      (λ i → fun (p i) z)
      (λ i → fun (q i) z) j i

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
Iso.sec typeQuotSetTruncIso = SetTrunc.elim (λ _ → isProp→isSet (squash₂ _ _))
                                  (TypeQuot.elimProp (λ _ → squash₂ _ _) λ _ → refl)
Iso.ret typeQuotSetTruncIso = elimProp (λ _ → squash/ _ _) λ _ → refl

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
Iso.sec (setQuotUniversalIso Bset) h = refl
Iso.ret (setQuotUniversalIso Bset) g =
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
Iso.sec (setQuotUniversal2Iso Bset isReflR isReflS) (_∗_ , h) =
   Σ≡Prop (λ _ → isPropΠ4 λ _ _ _ _ → isPropΠ2 λ _ _ → Bset _ _) refl
Iso.ret (setQuotUniversal2Iso Bset isReflR isReflS) _∗/_ =
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
Iso.sec (isEquivRel→effectiveIso {R = R} Rprop Req a b) _ = Rprop a b _ _
Iso.ret (isEquivRel→effectiveIso {R = R} Rprop Req a b) _ = squash/ _ _ _ _

isEquivRel→isEffective : isPropValued R → isEquivRel R → isEffective R
isEquivRel→isEffective Rprop Req a b =
  isoToIsEquiv (invIso (isEquivRel→effectiveIso Rprop Req a b))

-- Quotienting by the truncated relation is equivalent to quotienting by untruncated relation
truncRelIso : Iso (A / R) (A / (λ a b → ∥ R a b ∥₁))
Iso.fun truncRelIso = rec squash/ [_] λ _ _ r → eq/ _ _ ∣ r ∣₁
Iso.inv truncRelIso = rec squash/ [_] λ _ _ → PropTrunc.rec (squash/ _ _) λ r → eq/ _ _ r
Iso.sec truncRelIso = elimProp (λ _ → squash/ _ _) λ _ → refl
Iso.ret truncRelIso = elimProp (λ _ → squash/ _ _) λ _ → refl

truncRelEquiv : A / R ≃ A / (λ a b → ∥ R a b ∥₁)
truncRelEquiv = isoToEquiv truncRelIso

-- Using this we can obtain a useful characterization of
-- path-types for equivalence relations (not prop-valued)
-- and their quotients

isEquivRel→TruncIso : isEquivRel R → (a b : A) → Iso ([ a ] ≡ [ b ]) ∥ R a b ∥₁
isEquivRel→TruncIso {A = A} {R = R} Req a b =
  compIso
    (isProp→Iso (squash/ _ _) (squash/ _ _)
      (cong (Iso.fun truncRelIso)) (cong (Iso.inv truncRelIso)))
    (isEquivRel→effectiveIso (λ _ _ → PropTrunc.isPropPropTrunc) ∥R∥eq a b)
  where
  open isEquivRel
  ∥R∥eq : isEquivRel λ a b → ∥ R a b ∥₁
  reflexive ∥R∥eq a = ∣ reflexive Req a ∣₁
  symmetric ∥R∥eq a b = PropTrunc.map (symmetric Req a b)
  transitive ∥R∥eq a b c = PropTrunc.map2 (transitive Req a b c)

discreteSetQuotients : isEquivRel R
  → (∀ a₀ a₁ → Dec (R a₀ a₁))
  → Discrete (A / R)
discreteSetQuotients {A = A} {R = R} Req Rdec =
  elimProp2
    (λ _ _ → isPropDec (squash/ _ _))
    λ _ _ → EquivPresDec
              (isoToEquiv (invIso (isEquivRel→TruncIso Req _ _)))
              (Dec∥∥ (Rdec _ _))

-- quotienting by 'logically equivalent' relations gives the same quotient
relBiimpl→TruncIso : ({a b : A} → R a b → S a b) → ({a b : A} → S a b → R a b) → Iso (A / R) (A / S)
Iso.fun (relBiimpl→TruncIso R→S S→R) = rec squash/ [_] λ _ _ Rab → eq/ _ _ (R→S Rab)
Iso.inv (relBiimpl→TruncIso R→S S→R) = rec squash/ [_] λ _ _ Sab → eq/ _ _ (S→R Sab)
Iso.sec (relBiimpl→TruncIso R→S S→R) = elimProp (λ _ → squash/ _ _) λ _ → refl
Iso.ret (relBiimpl→TruncIso R→S S→R) = elimProp (λ _ → squash/ _ _) λ _ → refl

descendMapPath : {M : Type ℓ} (f g : A / R → M) (isSetM : isSet M)
               → ((x : A) → f [ x ] ≡ g [ x ])
               → f ≡ g
descendMapPath f g isSetM path i x =
  propRec
    (isSetM (f x) (g x))
    (λ {(x' , p) →
                        f x        ≡⟨ cong f (sym p) ⟩
                        f [ x' ]   ≡⟨ path x' ⟩
                        g [ x' ]   ≡⟨ cong g p ⟩
                        g x   ∎ })
    ([]surjective x)
    i

-- If we have a function sending each element of A to its
-- canonical representative under R, we can obtain A/R more
-- simply as the set of fixed points of R.

CanonicalReprs : (A → A) → Type _
CanonicalReprs {A = A} r = Σ[ x ∈ A ] r x ≡ x

-- Lemma 6.10.8 in HoTT Book: set quotients via canonical representatives
module _ (isSetA : isSet A)
  (r : A → A)
  (ridem : (a : A) → r (r a) ≡ r a)
  (r≃R : (a b : A) → (r a ≡ r b) ≃ R a b)
  where

  canonicalReprsUniversalIso : isSet B →
    Iso (CanonicalReprs r → B) (Σ[ f ∈ (A → B) ] ((a b : A) → R a b → f a ≡ f b))
  Iso.fun (canonicalReprsUniversalIso isSetB) g =
    (λ a → g (r a , ridem a)) ,
    λ a b Rab → cong g (Σ≡Prop (λ _ → isSetA _ _) (invEq (r≃R a b) Rab))
  Iso.inv (canonicalReprsUniversalIso isSetB) (f , R→f) (c , rc≡c) = f c
  Iso.sec (canonicalReprsUniversalIso isSetB) (f , R→f) =
    Σ≡Prop (λ _ → isPropΠ3 λ _ _ _ → isSetB _ _)
      (funExt λ a → R→f (r a) a (equivFun (r≃R (r a) a) (ridem a)))
  Iso.ret (canonicalReprsUniversalIso isSetB) g =
    funExt λ (c , rc≡c) → cong g (Σ≡Prop (λ _ → isSetA _ _) rc≡c)

  canonicalReprsUniversal : isSet B →
    (CanonicalReprs r → B) ≃ (Σ[ f ∈ (A → B) ] ((a b : A) → R a b → f a ≡ f b))
  canonicalReprsUniversal isSetB = isoToEquiv (canonicalReprsUniversalIso isSetB)

  private
    isSetCR : isSet (CanonicalReprs r)
    isSetCR = isSetΣSndProp isSetA (λ _ → isSetA _ _)

  equivQuotCRIso : Iso (A / R) (CanonicalReprs r)
  Iso.fun equivQuotCRIso = invEq (setQuotUniversal isSetCR)
    (equivFun (canonicalReprsUniversal isSetCR) (idfun _))
  Iso.inv equivQuotCRIso (c , _) = [ c ]
  Iso.sec equivQuotCRIso = funExt⁻ (retEq (canonicalReprsUniversal isSetCR) (idfun _))
  Iso.ret equivQuotCRIso = funExt⁻
    (descendMapPath _ (idfun _) squash/ (λ a → eq/ _ _ (equivFun (r≃R (r a) a) (ridem a))))

  equivQuotCR : (A / R) ≃ (CanonicalReprs r)
  equivQuotCR = isoToEquiv equivQuotCRIso

quotSurjectionEquiv : isSet B
  → (p : A → B) → isSurjection p
  → (A / (λ x y → p x ≡ p y)) ≃ B
quotSurjectionEquiv isSetB p surj = fun , isEmbedding×isSurjection→isEquiv (funEmb , funSurj)
  where
  fun = rec isSetB p (λ _ _ q → q)

  funEmb : isEmbedding fun
  funEmb = injEmbedding isSetB (elimProp2 {P = λ x y → fun x ≡ fun y → x ≡ y}
    (λ _ _ → isPropΠ λ _ → squash/ _ _) eq/ _ _)

  funSurj : isSurjection fun
  funSurj = leftFactorSurjective [_] fun surj

-- Corollary 6.10.10 in HoTT Book
quotRetractEquiv : isSet B
  → (p : A → B) → (s : B → A) → retract s p
  → (A / (λ x y → p x ≡ p y)) ≃ B
quotRetractEquiv isSetB p s ret = quotSurjectionEquiv isSetB p (section→isSurjection ret)

-- Every set is equivalent to its quotient by _≡_.
ER≡ : (A : Type ℓ) → isEquivRel ((_≡_) {ℓ = ℓ} {A})
ER≡ {ℓ} A = equivRel (λ a i → a) (λ a b x i → x (~ i)) λ a b c x y i → (x ∙ y) i

≡-quotEquiv : isSet A → A ≃ (A / _≡_)
≡-quotEquiv isSetA .fst = [_]
≡-quotEquiv isSetA .snd = isEmbedding×isSurjection→isEquiv ([]embedding , []surjective)
  where
  []embedding : isEmbedding [_]
  []embedding = injEmbedding squash/ (effective (λ _ _ → isSetA _ _) (ER≡ _) _ _)


-- An Isomorphism/R: An Isomorphism but up to equivalence R instead of equality _≡_:
module _  {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ} (ER : isEquivRel R) where

  retract/R : (f : A → B) → (g : B → A) → Type ℓ
  retract/R f g = ∀ a → R (g (f a)) a

record Iso/R  (A : Type ℓ) (B : Type ℓ') {R : A → A → Type ℓ} (ER : isEquivRel R) : Type (ℓ-max ℓ ℓ') where
  --no-eta-equality
  constructor iso/R
  field
    fun/R : A → B
    inv/R : B → A
    leftInv/R  : retract/R ER fun/R inv/R

open Iso/R

-- R has an dual:
R* : {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} {iso/r : Iso/R A B {R} ER} → B → B → Type ℓ
R* {ℓ}{ℓ'}{A}{B}{R}{ER} {iso/r} b b' = R (iso/r .inv/R b) (iso/r .inv/R b')

section/R : {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} {iso/r : Iso/R A B {R} ER} → Type (ℓ-max ℓ ℓ')
section/R {iso/r = iso/r} = ∀ b → R* {iso/r = iso/r} (iso/r .fun/R (iso/r .inv/R b)) b

retract/R→section/R : {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} {iso/r : Iso/R A B {R} ER} →
  section/R {iso/r = iso/r}
retract/R→section/R {R = R} {equivRel reflexive symmetric transitive} {iso/r = iso/r} b = iso/r .leftInv/R (iso/r .inv/R b)

-- Iso/R is a RelIso
Iso/R→RelIso : {A : Type ℓ} {A' : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} → (iso/r : Iso/R A A' {R} ER) → RelIso {A = A} R {A' = A'} (R* {iso/r = iso/r})
Iso/R→RelIso (iso/R fun/R₁ inv/R₁ leftInv/R₁) = reliso fun/R₁ inv/R₁ (λ a' → leftInv/R₁ (inv/R₁ a')) leftInv/R₁

-- A 'natural' isomorphism/R when A ≡ B:
iso/R-A≡B : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R} → (AB : A ≡ B) → Iso/R A B ER
iso/R-A≡B {ℓ} {A}{B}{R} ER@{equivRel reflexive symmetric transitive} AB .fun/R = λ z → transport AB z
iso/R-A≡B {ℓ} {A}{B}{R} ER@{equivRel reflexive symmetric transitive} AB .inv/R = λ z → transport (sym AB) z
iso/R-A≡B {ℓ} {A}{B}{R} ER@{equivRel reflexive symmetric transitive} AB .leftInv/R a = step1 (iso/R-A≡B {ℓ} {A}{B}{R}{ER} AB .inv/R (iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB .fun/R a)) a help
  where
    help : transport (sym AB) (transport AB a) ≡ a
    help = transport⁻Transport AB a
    step1 : ∀ x y → x ≡ y → R x y
    step1 x y xy = subst (R x) xy (reflexive x)

R→R* : {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} → {iso/r : Iso/R A B {R} ER}{a a' : A}
  → R a a' → R* {iso/r = iso/r} (iso/r .fun/R a) (iso/r .fun/R a')
R→R* {ℓ}{ℓ'}{A}{B}{R} {ER} {iso/r} raa' =
  ER .isEquivRel.transitive (iso/r .inv/R (iso/r .fun/R _)) _ (iso/r .inv/R (iso/r .fun/R _))
  (ER .isEquivRel.transitive (iso/r .inv/R (iso/r .fun/R _)) _ _ (iso/r .leftInv/R _) raa')
  (ER .isEquivRel.symmetric (iso/r .inv/R (iso/r .fun/R _)) _ (iso/r .leftInv/R _))

R*→R : {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} → {iso/r : Iso/R A B {R} ER}{b b' : B} →
  R* {iso/r = iso/r} b b' → R (iso/r .inv/R b) (iso/r .inv/R b')
R*→R z = z

-- That Iso/R is a generalised isomorphism, by setting the equivalence
-- relation on A to _≡_ and assuming that inv/R has an inverse inv/R⁻¹,
-- ie by assuming it is 1-to-1:
iso/R→≡→Iso : {A : Type ℓ} {B : Type ℓ'} →
  (iso/r : Iso/R {ℓ}{ℓ'} A B {R = (_≡_) {ℓ}{A}} (ER≡ A)) → (inv/R⁻¹ : A → B) → (∀ b → inv/R⁻¹ (iso/r .inv/R b) ≡ b) → Iso A B
iso/R→≡→Iso {ℓ}{ℓ'}{A}{B} iso/r@(iso/R fun/R₁ inv/R₁ leftInv/R₁) inv/R⁻¹ invertible = iso fun/R₁ inv/R₁ section' leftInv/R₁
  where
    sectionR : section/R {ℓ}{ℓ'}{A}{B}{_≡_}{ER≡ A}{iso/r}
    sectionR = retract/R→section/R {iso/r = iso/r}
    step1 : ∀ b → (inv/R₁ (fun/R₁ (inv/R₁ b))) ≡ (inv/R₁ b)
    step1 b = R*→R {iso/r = iso/r} (sectionR b)
    step2 : ∀ b → inv/R⁻¹ (inv/R₁ (fun/R₁ (inv/R₁ b))) ≡ inv/R⁻¹ (inv/R₁ b)
    step2 b = cong (λ u → inv/R⁻¹ u) (step1 b)
    step3 : ∀ b → inv/R⁻¹ (inv/R₁ b) ≡ b
    step3 b = invertible b
    step4 : ∀ b → inv/R⁻¹ (inv/R₁ (fun/R₁ (inv/R₁ b))) ≡ fun/R₁ (inv/R₁ b)
    step4 b = invertible (fun/R₁ (inv/R₁ b))
    section' : ∀ b → fun/R₁ (inv/R₁ b) ≡ b
    section' b = (sym (step4 b) ∙ step2 b) ∙ step3 b

-- R* is an equivalence relation:
isEquivRelR* : (A : Type ℓ) (B : Type ℓ') {R : A → A → Type ℓ} {ER : isEquivRel R} → (iso/r : Iso/R A B ER) → isEquivRel (R* {iso/r = iso/r})
isEquivRelR* A B {R} {ER} iso/r = equivRel
  (λ a → ER .isEquivRel.reflexive (iso/r .inv/R a))
  (λ a b → ER .isEquivRel.symmetric (iso/r .inv/R a) (iso/r .inv/R b))
  (λ a b c → ER .isEquivRel.transitive (iso/r .inv/R a) (iso/r .inv/R b) (iso/r .inv/R c))

-- There is an induced isomorphism/R with respect to R*:
iso/R→Iso/R* : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R} →
  (iso/r : Iso/R A B {R} ER) →
           Iso/R B A {R = R* {iso/r = iso/r}} (isEquivRelR* A B iso/r)
iso/R→Iso/R* iso/r = iso/R (iso/r .inv/R) (iso/r .fun/R) (λ a → iso/r .leftInv/R (iso/r .inv/R a))

-- The propositionality of R implies the propositionality of R*:
isPropR→IsPropR* : {A : Type ℓ} {B : Type ℓ'} {R : A → A → Type ℓ}{ER : isEquivRel R} → (iso/r : Iso/R {ℓ} A B {R} ER)
  → (∀ a a' → isProp (R a a')) → (∀ b b' → isProp ((R* {iso/r = iso/r}) b b'))
isPropR→IsPropR* iso/r ispRxy x y = ispRxy (iso/r .inv/R x) (iso/r .inv/R y)

-- An example of duality:
isPropR→IsPropR** : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R} → (iso/r : Iso/R {ℓ} A B {R} ER)
  → (∀ x y → isProp (R x y)) → (∀ x y → isProp (R* {R = R* {iso/r = iso/r}} {iso/r = iso/R→Iso/R* iso/r} x y))
isPropR→IsPropR** {ℓ} {A} {B} {R} {equivRel reflexive symmetric transitive} iso/r x y ispRxy = λ x' y'
  → x (iso/r .inv/R (iso/r .fun/R y)) (iso/r .inv/R (iso/r .fun/R ispRxy)) x' y'

R**→R :  {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER}
  → ∀ x y → (R* {R = R* {iso/r = iso/r}} {iso/r = iso/R→Iso/R* iso/r} x y → R x y)
R**→R {ℓ} {A} {B} {R} {equivRel reflexive symmetric transitive} {iso/R f g leftInv/R₁} x y =
  λ z → transitive x (g (f y)) y
        (transitive x (g (f x)) (g (f y))
        (symmetric (g (f x)) x (leftInv/R₁ x)) z) (leftInv/R₁ y)

R→R** :  {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER}
  → ∀ x y → (R x y → R* {R = R* {iso/r = iso/r}} {iso/r = iso/R→Iso/R* iso/r} x y)
R→R** {ℓ} {A} {B} {R} {equivRel reflexive symmetric transitive} {iso/R f g leftInv/R₁} x y =
  λ z → transitive (g (f x)) y (g (f y))
        (transitive (g (f x)) x y (leftInv/R₁ x) z)
        (symmetric (g (f y)) y (leftInv/R₁ y))

R*-IsProp-Def1 : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER}
  {isp : ∀ x y → isProp (R x y)} → ∀ x y → (R* {R = R* {iso/r = iso/r}} {iso/r = iso/R→Iso/R* iso/r} x y) ≡ (R x y)
R*-IsProp-Def1 {ℓ} {A} {B} {R} {equivRel reflexive symmetric transitive} {iso/r@(iso/R f g leftInv/R₁)} {isp} x y =
  isoToPath (iso (R**→R {iso/r = iso/r} x y) (R→R** {iso/r = iso/r} x y)
  (λ rxy → isp x y (R**→R {iso/r = iso/r} x y (R→R** {iso/r = iso/r} x y rxy)) rxy)
  λ rgf → isp (g (f x)) (g (f y)) (R→R** {iso/r = iso/r} x y (R**→R {iso/r = iso/r} x y rgf)) rgf)

-- An isProp duality proof:
R**≡R : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER}
  {isp : ∀ x y → isProp (R x y)} → (R* {R = R* {iso/r = iso/r}} {iso/r = iso/R→Iso/R* iso/r}) ≡ R
R**≡R {ℓ} {A} {B} {R} ER@{equivRel reflexive symmetric transitive} {iso/r@(iso/R f g leftInv/R₁)} {isp} i x y = help x y i
   where
     isp' : isProp (R x y)
     isp' = isp x y
     help : (x' y' : A) → R* {R = R* {iso/r = iso/r}} {ER = isEquivRelR* A B {ER = ER}
       (iso/R f g leftInv/R₁)} {iso/r = iso/R g f λ a → leftInv/R₁ (g a)} x' y' ≡ R x' y'
     help = R*-IsProp-Def1 {iso/r = iso/r}{isp}

-- A few more R* identity lemmas:
R*≡Rinv :  {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R A B {R} ER} →
 ∀ b b' → R* {ℓ}{ℓ}{A}{B}{R}{ER}{iso/r} b b' ≡ R (iso/r .inv/R b) (iso/r .inv/R b')
R*≡Rinv b b' = refl

R*≡λttHlp :  {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{AB : A ≡ B} →
  ∀ b b' → R* {iso/r = iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB} b b' ≡ (R (transport (sym AB) b) (transport (sym AB) b'))
R*≡λttHlp {ℓ}{A}{B}{R}{ER} {AB} b b' = isoToPath (iso (λ z → z) (λ z → z) (λ b₁ i → b₁) λ a i → a)
  where
    iso/r = iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB
    defR* : R* {iso/r = iso/r} b b' ≡  R (iso/r .inv/R b) (iso/r .inv/R b')
    defR* = refl

R*≡λR :  {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R A B {R} ER} →
  R* {iso/r = iso/r} ≡ (λ b b' → R (iso/r .inv/R b) (iso/r .inv/R b'))
R*≡λR {ℓ}{A}{B}{R}{ER}{iso/r} = λ i b b' → R*≡Rinv {ℓ}{A}{B}{R}{ER}{iso/r} b b' i

R*≡λtt :  {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{AB : A ≡ B} →
  R* {iso/r = iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB} ≡ (λ b b' → R (transport (sym AB) b) (transport (sym AB) b'))
R*≡λtt {ℓ}{A}{B}{R}{ER}{AB} = λ i b b' → R*≡λttHlp {ℓ}{A}{B}{R}{ER}{AB} b b' i

-- Definitions, functions and lemmas concerning A/R as a set quotient:
A/R→B/R* : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER} →
  (aᵣ : A / R) → B / R* {iso/r = iso/r}
A/R→B/R* {ℓ} {A} {B} {R} {ER} {iso/r} [ a ] =  _/_.[ iso/r .fun/R  a ]
A/R→B/R* {ℓ} {A} {B} {R} {ER} {iso/r} (eq/ a a' r i) = _/_.eq/ (iso/r .fun/R a) (iso/r .fun/R a') (R→R* {iso/r = iso/r} r) i
A/R→B/R* {ℓ} {A} {B} {R} {ER} {iso/r} (squash/ a a' p q i j) = squash/ (A/R→B/R* {iso/r = iso/r} a) (A/R→B/R* {iso/r = iso/r} a')
  (cong (λ u → A/R→B/R* {iso/r = iso/r} u) p) (cong (λ u → A/R→B/R* {iso/r = iso/r} u) q) i j

B/R*→A/R : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER} →
  (bᵣ : B / R* {iso/r = iso/r}) → A / R
B/R*→A/R {ℓ} {A}{B}{R}{ER}{iso/r} [ b ] =  _/_.[ iso/r .inv/R  b ]
B/R*→A/R {ℓ} {A}{B}{R}{ER}{iso/r} (eq/ b b' r i) = eq/ (iso/r .inv/R b) (iso/r .inv/R b') r i
B/R*→A/R {ℓ} {A}{B}{R}{ER}{iso/r} (squash/ b b' p q i j) =
  squash/ (B/R*→A/R {iso/r = iso/r} b) (B/R*→A/R {iso/r = iso/r} b')
  (cong (λ u → B/R*→A/R {iso/r = iso/r} u) p) (cong (λ u → B/R*→A/R {iso/r = iso/r} u) q) i j

raa'→[a]≡[a'] : {ℓ : Level} {A : Type ℓ} {R : A → A → Type ℓ} {a a' : A} → R a a' → (_≡_) {ℓ} {A / R} (_/_.[ a ]) (_/_.[ a' ])
raa'→[a]≡[a'] {ℓ} {A} {R} {a} {a'} raa' = _/_.eq/ a a' raa'

∥f∥₁-map : {A : Type ℓ} {B : Type ℓ'} → (f : A → B) → ∥ A ∥₁ → ∥ B ∥₁
∥f∥₁-map {ℓ} {ℓ'} {A} {B} f A' = A' >>= λ a → return (f a)

extrapolate[] : {ℓ : Level} {A : Type ℓ} {R : A → A → Type ℓ} →
  (f : (A / R) → (A / R)) → (∀ (a : A) → f [ a ] ≡ [ a ]) → ∀ (aᵣ : A / R) → ∥ f aᵣ ≡ aᵣ ∥₁
extrapolate[] {ℓ} {A} {R} f fa aᵣ = ∥f∥₁-map (λ z → z .snd) goal
                  where
                    a[] : ∀ (aᵣ : A / R) → ∥ A ∥₁
                    a[] aᵣ = ∥f∥₁-map fst ([]surjective aᵣ)
                    a[]* : ∥ Σ A (λ a → [ a ] ≡ aᵣ) ∥₁
                    a[]* = []surjective aᵣ
                    step1 : Σ A (λ a → [ a ] ≡ aᵣ) → Σ A (λ a → f [ a ] ≡ aᵣ)
                    step1 (fst₁ , snd₁) = fst₁ , ((fa fst₁) ∙ snd₁)
                    step2 : Σ A (λ a → [ a ] ≡ aᵣ) → Σ A (λ a → f aᵣ ≡ f [ a ])
                    step2 (fst₁ , snd₁) = fst₁ , (sym (cong f snd₁))
                    stepf :  Σ A (λ a → [ a ] ≡ aᵣ) → Σ A (λ a → f aᵣ ≡ aᵣ)
                    stepf (fst₁ , snd₁) = fst₁ , (snd (step2 (fst₁ , snd₁))) ∙ (snd (step1 (fst₁ , snd₁)))
                    goal : ∥ Σ A (λ a → f aᵣ ≡ aᵣ) ∥₁
                    goal = ∥f∥₁-map stepf a[]*

isoA/R-B/R'Hlp3 : {ℓ : Level} {A : Type ℓ} {R : A → A → Type ℓ} →
  (f : (A / R) → (A / R)) → (∀ (a : A) → f [ a ] ≡ [ a ]) → ∀ (aᵣ : A / R) → f aᵣ ≡ aᵣ
isoA/R-B/R'Hlp3 {ℓ} {A} {R} f fid aᵣ = propRec (squash/ (f aᵣ) aᵣ) (λ u → u) (extrapolate[] {ℓ}{A}{R} f fid aᵣ)

isoA/R-B/R'Hlp1 : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}
  → (iso/r : Iso/R {ℓ} A B {R} ER) → (aᵣ : A / R)
  → (B/R*→A/R {iso/r = iso/r} (A/R→B/R* {iso/r = iso/r} aᵣ)) ≡ aᵣ
isoA/R-B/R'Hlp1 {ℓ} {A} {B} {R} ER@{equivRel rf sm trns} iso/r@(iso/R f g rgfa≡a) aᵣ =
  step2 (λ x → B/R*→A/R {iso/r = iso/r} (A/R→B/R* {iso/r = iso/r} x)) (λ a → step1 a) aᵣ
    where
      help1 : ∀ (a : A) → R (g (f a)) a
      help1 a = rgfa≡a a
      step1 : ∀ (a : A) → [ g (f a) ] ≡ [ a ]
      step1 a = raa'→[a]≡[a'] (help1 a)
      step2 : (f' : (A / R) → (A / R)) → (∀ (a : A) → f' [ a ] ≡ [ a ]) → ∀ (aᵣ : A / R) → f' aᵣ ≡ aᵣ
      step2 f' x aᵣ i = isoA/R-B/R'Hlp3 f' x aᵣ i

isoA/R-B/R'Hlp2 : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}
  → (iso/r : Iso/R {ℓ} A B {R} ER) → (bᵣ : B / R* {iso/r = iso/r})
  → (A/R→B/R* {iso/r = iso/r} (B/R*→A/R {iso/r = iso/r} bᵣ)) ≡ bᵣ
isoA/R-B/R'Hlp2 {ℓ} {A} {B} {R} ER@{equivRel rf sm trns} iso/r@(iso/R f g rgfa≡a) bᵣ =
  step2 (λ x → A/R→B/R* {iso/r = iso/r} (B/R*→A/R {iso/r = iso/r} x)) (λ b → step1 b) bᵣ
    where
      help1 : ∀ (a : A) → R (g (f a)) a
      help1 a = rgfa≡a a
      help2 : ∀ (b : B) → (R* {iso/r = iso/r} (f (g b))) b
      help2 = λ b → rgfa≡a (g b)
      step1 : ∀ (b : B) → (_≡_) {A = B / R* {iso/r = iso/r}} [ f (g b) ] [ b ]
      step1 b =  raa'→[a]≡[a'] (help2 b)
      step2 : (g' : (B / R* {iso/r = iso/r}) → (B / R* {iso/r = iso/r})) → (∀ (b : B) → g' [ b ] ≡ [ b ]) →
        ∀ (bᵣ : B / R* {iso/r = iso/r}) → g' bᵣ ≡ bᵣ
      step2 g' x bᵣ i = isoA/R-B/R'Hlp3 g' x bᵣ i

-- An important set quotient isomorphism:
isoA/R-B/R' : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER} →
  Iso (A / R) (B / R* {iso/r = iso/r})
isoA/R-B/R' {ℓ}{A}{B}{R}{ER}{iso/r} = iso (A/R→B/R* {iso/r = iso/r})
  (B/R*→A/R {iso/r = iso/r}) (λ b → isoA/R-B/R'Hlp2 iso/r b) λ a → isoA/R-B/R'Hlp1 iso/r a

-- An important set quotient equality lemma:
quotientEqualityLemma : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{ER : isEquivRel R}{iso/r : Iso/R {ℓ} A B {R} ER}
                 → A / R ≡ B / (R* {iso/r = iso/r})
quotientEqualityLemma {ℓ} {A}{B}{R}{ER}{iso/r} = isoToPath (isoA/R-B/R' {ℓ}{A}{B}{R}{ER}{iso/r})

-- Another set quotient equality lemma relying on Rel R and Rel R' propositionality:
A/R≡A/R'Hlp : {A : Type ℓ} → {R R' : A → A → Type ℓ} →
  (ispR : ∀ a a' → isProp (R a a')) →
  (ispR' : ∀ a a' → isProp (R' a a')) →
  (RR' : ∀ a a' → R a a' → R' a a') → (R'R : ∀ a a' → R' a a' → R a a') → A / R ≡ A / R'
A/R≡A/R'Hlp {ℓ} {A}{R}{R'} ispR ispR' RR' R'R = cong (λ u → A / u) R≡R'
  where
    Rxy≡R'xy : ∀ x y → R x y ≡ R' x y
    Rxy≡R'xy x y = isoToPath (iso (RR' x y) (R'R x y)
      (λ b → ispR' x y (RR' x y (R'R x y b)) b) (λ a → ispR x y (R'R x y (RR' x y a)) a))
    R≡R' : R ≡ R'
    R≡R' = funExt (λ x → funExt (λ y → Rxy≡R'xy x y))

-- A simpler version:
quotientRule : {A : Type ℓ} → {R R' : A → A → Type ℓ} → (RR' : R ≡ R') → A / R ≡ A / R'
quotientRule {ℓ} {A}{R}{R'} RR' i = A / (RR' i)

A/R≡A/R'Hlp2 : {A : Type ℓ} → {R R' : A → A → Type ℓ} →
  (RR' : ∀ a a' → (R a a' → R' a a')) → (R'R : ∀ a a' → (R' a a' → R a a')) → A / (λ a b → ∥ R a b ∥₁) ≡ A / (λ a b → ∥ R' a b ∥₁)
A/R≡A/R'Hlp2 {ℓ} {A}{R}{R'} RR' R'R = A/R≡A/R'Hlp (λ a a' → PropTrunc.isPropPropTrunc) (λ a a' → PropTrunc.isPropPropTrunc) (λ a a' raa' → ∥f∥₁-map (RR' a a') raa') (λ a a' r'aa' → ∥f∥₁-map (R'R a a') r'aa')

-- The propositional truncation of R makes no difference to the resulting quotient,
-- and so we have the following quotient equality lemma:
truncRel≡ : {A : Type ℓ}{R : A → A → Type ℓ} → (A / R) ≡ (A / (λ a b → ∥ R a b ∥₁))
truncRel≡ {ℓ}{A}{R} = isoToPath truncRelIso

-- A stronger quotient equality lemma based on the preceding, consistent with intuition:
A/R≡A/R' : {A : Type ℓ} → {R R' : A → A → Type ℓ} →
  (RR' : ∀ a a' → (R a a' → R' a a')) → (R'R : ∀ a a' → (R' a a' → R a a')) → A / R ≡ A / R'
A/R≡A/R' {ℓ} {A}{R}{R'} RR' R'R = truncRel≡ ∙ (A/R≡A/R'Hlp2 RR' R'R) ∙ sym truncRel≡

-- We can also obtain the following quotient equality lemmas:
quotientEqualityLemma2 : {A B : Type ℓ}{R : A → A → Type ℓ}{ER : isEquivRel R} →
  (AB : A ≡ B) → (A / R) ≡ (B / λ b b' → R (transport (sym AB) b) (transport (sym AB) b'))
quotientEqualityLemma2 {ℓ}{A}{B}{R}{ER} AB = quotientEqualityLemma {iso/r = iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB}
  where
    lemma : (A / R) ≡ (B / R* {iso/r = iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB})
    lemma = quotientEqualityLemma {iso/r = iso/R-A≡B {ℓ}{A}{B}{R}{ER} AB}

quotientEqualityLemma3 : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{R' : B → B → Type ℓ}
                 {ER : isEquivRel R} →
                 (iso/r : Iso/R {ℓ} A B {R} ER) →
                 (R'→R* : ∀ b b' → (R' b b' → R* {iso/r = iso/r} b b')) →
                 (R*→R' : ∀ b b' → (R* {iso/r = iso/r} b b' → R' b b')) →
                 A / R ≡ B / R'
quotientEqualityLemma3 {ℓ} {A}{B}{R}{R'}{ER} iso/r R'→R* R*→R' = step1 ∙ A/R≡A/R' R*→R' R'→R*
  where
    step1 : (A / R) ≡ (B / R* {iso/r = iso/r})
    step1 = quotientEqualityLemma {ℓ}{A}{B}{R}{ER}{iso/r}

quotientEqualityLemma4 : {A : Type ℓ} {B : Type ℓ} {R : A → A → Type ℓ}{R' : B → B → Type ℓ}
                 {ER : isEquivRel R} →
                 (iso/r : Iso/R {ℓ} A B {R} ER) →
                 (R'→Rinv : ∀ b b' → (R' b b' → R (iso/r .inv/R b) (iso/r .inv/R b'))) →
                 (Rinv→R' : ∀ b b' → (R (iso/r .inv/R b) (iso/r .inv/R b') → R' b b')) →
                 A / R ≡ B / R'
quotientEqualityLemma4 {ℓ} {A}{B}{R}{R'}{ER} iso/r R'→R R→R' =
  step1 ∙ A/R≡A/R' (λ b b' z → R→R' b b' z) (λ b b' x → R'→R b b' x)
    where
      help :  ∀ b b' → R* {ℓ}{ℓ}{A}{B}{R}{ER}{iso/r} b b' ≡ R (iso/r .inv/R b) (iso/r .inv/R b')
      help b b' = refl
      step1 : (A / R) ≡ (B / R* {iso/r = iso/r})
      step1 = quotientEqualityLemma {ℓ}{A}{B}{R}{ER}{iso/r}
