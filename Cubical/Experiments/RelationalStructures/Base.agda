{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.RelationalStructures.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Relation.ZigZag.Base
open import Cubical.HITs.SetQuotients

-- lemmas to move or inline

_◁_ : ∀ {ℓ} {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ : A i1}
  → a₀ ≡ a₀' → PathP A a₀' a₁ → PathP A a₀ a₁
(p ◁ q) i =
  hcomp (λ j → λ {(i = i0) → p (~ j); (i = i1) → q i1}) (q i)

_▷_ : ∀ {ℓ} {A : I → Type ℓ} {a₀ : A i0} {a₁ a₁' : A i1}
  → PathP A a₀ a₁ → a₁ ≡ a₁' → PathP A a₀ a₁'
(p ▷ q) i =
  hcomp (λ j → λ {(i = i0) → p i0; (i = i1) → q j}) (p i)

_/set_ : ∀ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') → hSet (ℓ-max ℓ ℓ')
A /set R = A / R , squash/

setUA : ∀ {ℓ} (A B : hSet ℓ) (e : A .fst ≃ B .fst) → A ≡ B
setUA A B e i = (ua e i , t i)
  where
  abstract
    t : PathP (λ i → isSet (ua e i)) (A .snd) (B .snd)
    t = isProp→PathP (λ _ → isPropIsSet) _ _

adjustPathPByProp : ∀ {ℓ ℓ'} {A : I → Type ℓ} (B : (i : I) → A i → Type ℓ')
  {a₀ : A i0} {a₁ : A i1} {b₀ : B i0 a₀} {b₁ : B i1 a₁}
  {p q : PathP A a₀ a₁}
  → (∀ i → isProp (A i)) -- isSet would be enough
  → PathP (λ i → B i (p i)) b₀ b₁
  → PathP (λ i → B i (q i)) b₀ b₁
adjustPathPByProp B {b₀ = b₀} {b₁} {p} {q} propA =
  subst (λ r → PathP (λ i → B i (r i)) b₀ b₁) (isOfHLevelPathP 1 propA _ _ p q)

ua→ : ∀ {ℓ ℓ'} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁} {B : (i : I) → Type ℓ'}
  {f₀ : A₀ → B i0} {f₁ : A₁ → B i1}
  → ((a : A₀) → PathP (λ i → B i) (f₀ a) (f₁ (e .fst a)))
  → PathP (λ i → ua e i → B i) f₀ f₁
ua→ {e = e} {f₀ = f₀} {f₁} h i a =
  hcomp
    (λ j → λ
      { (i = i0) → f₀ a
      ; (i = i1) → f₁ (lem a j)
      })
    (h (transp (λ j → ua e (~ j ∧ i)) (~ i) a) i)
  where
  lem : ∀ a₁ → e .fst (transport⁻ (ua e) a₁) ≡ a₁
  lem a₁ = sym (transportRefl _) ∙ transportTransport⁻ (ua e) a₁

-- main event

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level

open isBisimulation

--------------------------------------------------------------------------------
-- Prop-valued relations
--------------------------------------------------------------------------------

PropValuedRel : (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
PropValuedRel A B ℓ' =
  Σ[ R ∈ (A → B → Type ℓ') ] ∀ a b → isProp (R a b)

quotientPropValued : {A : Type ℓ} (R : A → A → Type ℓ)
  → PropValuedRel A (A / R) ℓ
quotientPropValued R .fst a b = [ a ] ≡ b
quotientPropValued R .snd a = squash/ [ a ]

Bisimulation→PropValued : {A B : Type ℓ} {ℓ' : Level}
  → Bisimulation A B ℓ' → PropValuedRel A B ℓ'
Bisimulation→PropValued (R , bisim) .fst = R
Bisimulation→PropValued (R , bisim) .snd = bisim .prop

--------------------------------------------------------------------------------
-- Definition of standard notion of structure
--------------------------------------------------------------------------------

SetWithStr : (ℓ : Level) (S : hSet ℓ → hSet ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
SetWithStr ℓ S = Σ[ X ∈ hSet ℓ ] S X .fst

set : {S : hSet ℓ → Type ℓ'} → (Σ[ X ∈ hSet ℓ ] S X) → hSet ℓ
set XS = XS .fst

typ : {S : hSet ℓ → Type ℓ'} → (Σ[ X ∈ hSet ℓ ] S X) → Type ℓ
typ (X , s) = X .fst

StrRel : (S : hSet ℓ → hSet ℓ') (ℓ'' : Level) → Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓ'')) ℓ')
StrRel {ℓ} S ℓ'' =
  (A B : hSet ℓ) (R : PropValuedRel (A .fst) (B .fst) ℓ)
  → PropValuedRel (S A .fst) (S B .fst) ℓ''

QuoStructure : (S : hSet ℓ → hSet ℓ') (ρ : StrRel S ℓ'')
  (A : SetWithStr ℓ S) (R : typ A → typ A → Type ℓ)
  → Type (ℓ-max ℓ' ℓ'')
QuoStructure S ρ A R =
  Σ (S (typ A /set R) .fst) (ρ (A .fst) (typ A /set R) (quotientPropValued R) .fst (A .snd))

record Descends (S : hSet ℓ → hSet ℓ') (ρ : StrRel S ℓ'')
  (A B : SetWithStr ℓ S) (R : Bisimulation (typ A) (typ B) ℓ) : Type (ℓ-max ℓ' ℓ'')
  where
  private
    module E = Bisim→Equiv R

  field
    quoᴸ : isContr (QuoStructure S ρ A E.Rᴸ)
    quoᴿ : isContr (QuoStructure S ρ B E.Rᴿ)
    path :
      PathP (λ i → S (setUA (typ A /set E.Rᴸ) (typ B /set E.Rᴿ) E.Thm i) .fst)
        (quoᴸ .fst .fst)
        (quoᴿ .fst .fst)

open Descends

isSNRS : (S : hSet ℓ → hSet ℓ') → StrRel S ℓ'' → Type _
isSNRS {ℓ} S ρ =
  {A B : SetWithStr ℓ S} (R : Bisimulation (typ A) (typ B) ℓ)
  → ρ (A .fst) (B .fst) (Bisimulation→PropValued R) .fst (A .snd) (B .snd)
  → Descends S ρ A B R

-- Two cool lemmas

coolLemmaᴸ : {S : hSet ℓ → hSet ℓ₁} (ρ : StrRel S ℓ₁') (θ : isSNRS S ρ)
  {X Y : hSet ℓ} (R : Bisimulation (X .fst) (Y .fst) ℓ)
  {x₀ x₁ : S X .fst} {y₀ y₁ : S Y .fst}
  (code₀₀ : ρ X Y (Bisimulation→PropValued R) .fst x₀ y₀)
  (code₁₁ : ρ X Y (Bisimulation→PropValued R) .fst x₁ y₁)
  → ρ X Y (Bisimulation→PropValued R) .fst x₀ y₁
  → θ _ code₀₀ .quoᴸ .fst .fst ≡ θ _ code₁₁ .quoᴸ .fst .fst
coolLemmaᴸ {S = S} ρ θ R {x₀} {x₁} {y₀} {y₁} code₀₀ code₁₁ code₀₁ =
  cong fst (θ R code₀₀ .quoᴸ .snd (θ R code₀₁ .quoᴸ .fst))
  ∙ lem
    (symP (θ R code₀₁ .path))
    (symP (θ R code₁₁ .path))
    (cong fst (θ R code₀₁ .quoᴿ .snd (θ R code₁₁ .quoᴿ .fst)))
  where
  lem : ∀ {ℓ} {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ a₁' : A i1}
    → PathP A a₀ a₁
    → PathP A a₀' a₁'
    → a₀ ≡ a₀'
    → a₁ ≡ a₁'
  lem {A = A} p₀ p₁ q i =
    comp A (λ k → λ {(i = i0) → p₀ k; (i = i1) → p₁ k}) (q i)

coolLemmaᴿ : {S : hSet ℓ → hSet ℓ₁} (ρ : StrRel S ℓ₁') (θ : isSNRS S ρ)
  {X Y : hSet ℓ} (R : Bisimulation (X .fst) (Y .fst) ℓ)
  {x₀ x₁ : S X .fst} {y₀ y₁ : S Y .fst}
  (code₀₀ : ρ X Y (Bisimulation→PropValued R) .fst x₀ y₀)
  (code₁₁ : ρ X Y (Bisimulation→PropValued R) .fst x₁ y₁)
  → ρ X Y (Bisimulation→PropValued R) .fst x₁ y₀
  → θ _ code₀₀ .quoᴿ .fst .fst ≡ θ _ code₁₁ .quoᴿ .fst .fst
coolLemmaᴿ {S = S} ρ θ R {x₀} {x₁} {y₀} {y₁} code₀₀ code₁₁ code₁₀ =
  cong fst (θ R code₀₀ .quoᴿ .snd (θ R code₁₀ .quoᴿ .fst))
  ∙ lem
    (θ R code₁₀ .path)
    (θ R code₁₁ .path)
    (cong fst (θ R code₁₀ .quoᴸ .snd (θ R code₁₁ .quoᴸ .fst)))
  where
  lem : ∀ {ℓ} {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ a₁' : A i1}
    → PathP A a₀ a₁
    → PathP A a₀' a₁'
    → a₀ ≡ a₀'
    → a₁ ≡ a₁'
  lem {A = A} p₀ p₁ q i =
    comp A (λ k → λ {(i = i0) → p₀ k; (i = i1) → p₁ k}) (q i)

--------------------------------------------------------------------------------
-- Structure combinators
--------------------------------------------------------------------------------

-- Constant structure

module _ (A : hSet ℓ') where

  constant-structure : hSet ℓ → hSet ℓ'
  constant-structure _ = A

  constant-rel : StrRel {ℓ = ℓ} constant-structure ℓ'
  constant-rel _ _ _ .fst a₀ a₁ = a₀ ≡ a₁
  constant-rel _ _ _ .snd = A .snd

  isSNRSConstant : isSNRS {ℓ = ℓ} constant-structure constant-rel
  isSNRSConstant _ _ .quoᴸ = isContrSingl _
  isSNRSConstant _ _ .quoᴿ = isContrSingl _
  isSNRSConstant _ r .path = r

-- Variable structure

pointed-structure : hSet ℓ → hSet ℓ
pointed-structure X = X

pointed-rel : StrRel pointed-structure ℓ
pointed-rel _ _ R .fst x y = R .fst x y
pointed-rel _ _ R .snd = R .snd

isSNRSPointed : isSNRS {ℓ = ℓ} pointed-structure pointed-rel
isSNRSPointed _ _ .quoᴸ = isContrSingl _
isSNRSPointed _ _ .quoᴿ = isContrSingl _
isSNRSPointed {A = _ , x} {_ , y} R r .path =
  equivFun (compEquiv R≃Rᴿ (compEquiv effEquiv (invEquiv (ua-ungluePath-Equiv E.Thm)))) r
  where
  module E = Bisim→Equiv R
  module S = isBisimulation (R .snd)

  effEquiv : E.Rᴿ (S.fwd x) y ≃ Path (_ / E.Rᴿ) [ S.fwd x ] [ y ]
  effEquiv .fst = eq/ (S.fwd x) y
  effEquiv .snd =
    isEquivRel→isEffective
      (λ _ _ → S.prop _ _)
      (bisim→EquivRel (invBisim R) .snd)
      (S.fwd x)
      y

  R≃Rᴿ : R .fst x y ≃ E.Rᴿ (S.fwd x) y
  R≃Rᴿ =
    isPropEquiv→Equiv
      (S.prop x y)
      (S.prop (S.bwd y) (S.fwd x))
      (λ r → S.zigzag (S.bwdRel y) r (S.fwdRel x))
      (λ s → S.zigzag (S.fwdRel x) s (S.bwdRel y))

-- Product of structures

module _ where

  join-structure :
    (hSet ℓ → hSet ℓ₁)
    → (hSet ℓ → hSet ℓ₂)
    → hSet ℓ → hSet (ℓ-max ℓ₁ ℓ₂)
  join-structure S₁ S₂ X .fst = S₁ X .fst × S₂ X .fst
  join-structure S₁ S₂ X .snd = isSet× (S₁ X .snd) (S₂ X .snd)

  join-rel :
    (S₁ : hSet ℓ → hSet ℓ₁) {ℓ₁' : Level} (ρ₁ : StrRel S₁ ℓ₁')
    (S₂ : hSet ℓ → hSet ℓ₂) {ℓ₂' : Level} (ρ₂ : StrRel S₂ ℓ₂')
    → StrRel (join-structure S₁ S₂) (ℓ-max ℓ₁' ℓ₂')
  join-rel S₁ ρ₁ S₂ ρ₂ X Y R .fst (s₁ , s₂) (t₁ , t₂) =
    ρ₁ X Y R .fst s₁ t₁
    × ρ₂ X Y R .fst s₂ t₂
  join-rel S₁ ρ₁ S₂ ρ₂ X Y R .snd (s₁ , s₂) (t₁ , t₂) =
    isProp× (ρ₁ X Y R .snd s₁ t₁) (ρ₂ X Y R .snd s₂ t₂)

  isSNRSJoin :
    {S₁ : hSet ℓ → hSet ℓ₁} {ℓ₁' : Level} {ρ₁ : StrRel S₁ ℓ₁'}
    {S₂ : hSet ℓ → hSet ℓ₂} {ℓ₂' : Level} {ρ₂ : StrRel S₂ ℓ₂'}
    → isSNRS S₁ ρ₁ → isSNRS S₂ ρ₂
    → isSNRS (join-structure S₁ S₂) (join-rel S₁ ρ₁ S₂ ρ₂)
  isSNRSJoin θ₁ θ₂ _ (code₁ , code₂) .quoᴸ .fst .fst =
    θ₁ _ code₁ .quoᴸ .fst .fst , θ₂ _ code₂ .quoᴸ .fst .fst
  isSNRSJoin θ₁ θ₂ _ (code₁ , code₂) .quoᴸ .fst .snd =
    θ₁ _ code₁ .quoᴸ .fst .snd , θ₂ _ code₂ .quoᴸ .fst .snd
  isSNRSJoin θ₁ θ₂ R (code₁ , code₂) .quoᴸ .snd (p , α) j =
    ( ( θ₁ R code₁ .quoᴸ .snd (p .fst ,  α .fst) j .fst
      , θ₂ R code₂ .quoᴸ .snd (p .snd ,  α .snd) j .fst
      )
    , ( θ₁ _ code₁ .quoᴸ .snd (p .fst , α .fst) j .snd
      , θ₂ _ code₂ .quoᴸ .snd (p .snd , α .snd) j .snd
      )
    )
  isSNRSJoin θ₁ θ₂ _ (code₁ , code₂) .quoᴿ .fst .fst =
    θ₁ _ code₁ .quoᴿ .fst .fst , θ₂ _ code₂ .quoᴿ .fst .fst
  isSNRSJoin θ₁ θ₂ _ (code₁ , code₂) .quoᴿ .fst .snd =
    θ₁ _ code₁ .quoᴿ .fst .snd , θ₂ _ code₂ .quoᴿ .fst .snd
  isSNRSJoin θ₁ θ₂ R (code₁ , code₂) .quoᴿ .snd (p , α) j =
    ( ( θ₁ R code₁ .quoᴿ .snd (p .fst ,  α .fst) j .fst
      , θ₂ R code₂ .quoᴿ .snd (p .snd ,  α .snd) j .fst
      )
    , ( θ₁ _ code₁ .quoᴿ .snd (p .fst , α .fst) j .snd
      , θ₂ _ code₂ .quoᴿ .snd (p .snd , α .snd) j .snd
      )
    )
  isSNRSJoin {S₁ = S₁} {S₂ = S₂} θ₁ θ₂ _ (code₁ , code₂) .path =
    equivFun ΣPathP≃PathPΣ
      ( adjustPathPByProp (λ i z → S₁ (_ , z) .fst) (λ _ → isPropIsSet) (θ₁ _ code₁ .path)
      , adjustPathPByProp (λ i z → S₂ (_ , z) .fst) (λ _ → isPropIsSet) (θ₂ _ code₂ .path)
      )

-- Parameterized structure

module _ {ℓ ℓ₁ ℓ₂} (A : Type ℓ) where

  parameterized-structure :
     (A → hSet ℓ₁ → hSet ℓ₂)
     → hSet ℓ₁ → hSet (ℓ-max ℓ ℓ₂)
  parameterized-structure S X .fst = (a : A) → (S a X .fst)
  parameterized-structure S X .snd = isSetΠ λ a → S a X .snd

  parameterized-rel : (S : A → hSet ℓ₁ → hSet ℓ₂) {ℓ₃ : Level}
    → (∀ a → StrRel (S a) ℓ₃)
    → StrRel (parameterized-structure S) (ℓ-max ℓ ℓ₃)
  parameterized-rel S ρ X Y R .fst s t =
    (a : A) → ρ a X Y R .fst (s a) (t a)
  parameterized-rel S ρ X Y R .snd s t =
    isPropΠ λ a → ρ a X Y R .snd (s a) (t a)

  isSNRSParameterized : {S : A → hSet ℓ₁ → hSet ℓ₂} {ℓ₃ : Level}
    (ρ : ∀ a → StrRel (S a) ℓ₃)
    → (∀ a → isSNRS (S a) (ρ a))
    → isSNRS (parameterized-structure S) (parameterized-rel S ρ)
  isSNRSParameterized ρ θ _ code .quoᴸ .fst .fst a = θ a _ (code a) .quoᴸ .fst .fst
  isSNRSParameterized ρ θ _ code .quoᴸ .fst .snd a = θ a _ (code a) .quoᴸ .fst .snd
  isSNRSParameterized ρ θ R code .quoᴸ .snd (f , h) j .fst a = θ a R (code a) .quoᴸ .snd (f a , h a) j .fst
  isSNRSParameterized ρ θ _ code .quoᴸ .snd (f , h) j .snd a = θ a _ (code a) .quoᴸ .snd (f a , h a) j .snd
  isSNRSParameterized ρ θ _ code .quoᴿ .fst .fst a = θ a _ (code a) .quoᴿ .fst .fst
  isSNRSParameterized ρ θ _ code .quoᴿ .fst .snd a = θ a _ (code a) .quoᴿ .fst .snd
  isSNRSParameterized ρ θ R code .quoᴿ .snd (f , h) j .fst a = θ a R (code a) .quoᴿ .snd (f a , h a) j .fst
  isSNRSParameterized ρ θ _ code .quoᴿ .snd (f , h) j .snd a = θ a _ (code a) .quoᴿ .snd (f a , h a) j .snd
  isSNRSParameterized {S = S} ρ θ R code .path =
    funExt λ a →
    adjustPathPByProp (λ i z → S a (_ , z) .fst) (λ _ → isPropIsSet) (θ a R (code a) .path)

module _  {ℓ ℓ₁} where

  unaryFun-structure : (hSet ℓ → hSet ℓ₁) → hSet ℓ → hSet (ℓ-max ℓ ℓ₁)
  unaryFun-structure S X .fst = X .fst → S X .fst
  unaryFun-structure S X .snd = isSetΠ λ _ → S X .snd

  unaryFun-rel : (S : hSet ℓ → hSet ℓ₁) {ℓ₁' : Level}
    → StrRel S ℓ₁' → StrRel (unaryFun-structure S) (ℓ-max ℓ ℓ₁')
  unaryFun-rel S ρ X Y R .fst f g =
    {x : X .fst} {y : Y .fst}
    → R .fst x y
    → ρ X Y R .fst (f x) (g y)
  unaryFun-rel S ρ X Y R .snd f g =
    isPropImplicitΠ λ x →
    isPropImplicitΠ λ y →
    isPropΠ λ _ → ρ X Y R .snd (f x) (g y)

  isSNRSUnaryFun : {S : hSet ℓ → hSet ℓ₁} {ℓ₁' : Level} (ρ : StrRel S ℓ₁')
    → isSNRS S ρ
    → isSNRS (unaryFun-structure S) (unaryFun-rel S ρ)
  isSNRSUnaryFun {S = S} ρ θ {X , f} {Y , g} (R , bis) code .quoᴸ .fst =
    str , λ p → subst (λ y → ρ _ _ _ .fst _ (str y)) p (θ _ _ .quoᴸ .fst .snd)
    where
    str : _
    str [ x ] = θ (R , bis) (code (bis .fwdRel x)) .quoᴸ .fst .fst
    str (eq/ x₀ x₁ r i) =
      coolLemmaᴸ ρ θ (R , bis)
        (code (bis .fwdRel x₀))
        (code (bis .fwdRel x₁))
        (code r)
        i
    str (squash/ _ _ p q j i) =
      S _ .snd _ _ (cong str p) (cong str q) j i
  isSNRSUnaryFun {S = S} ρ θ (R , bis) code .quoᴸ .snd (f' , h) =
    Σ≡Prop
      (λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropΠ λ _ → ρ _ _ _ .snd _ _)
      (funExt
        (elimProp
          (λ _ → S _ .snd _ _)
          (λ x → cong fst (θ _ _ .quoᴸ .snd (f' [ x ] , h refl)))))
  isSNRSUnaryFun {S = S} ρ θ (R , bis) code .quoᴿ .fst =
    str , λ p → subst (λ y → ρ _ _ _ .fst _ (str y)) p (θ _ _ .quoᴿ .fst .snd)
    where
    str : _
    str [ y ] = θ (R , bis) (code (bis .bwdRel y)) .quoᴿ .fst .fst
    str (eq/ y₀ y₁ r i) =
      coolLemmaᴿ ρ θ (R , bis)
        (code (bis .bwdRel y₀))
        (code (bis .bwdRel y₁))
        (code r)
        i
    str (squash/ _ _ p q j i) =
      S _ .snd _ _ (cong str p) (cong str q) j i
  isSNRSUnaryFun {S = S} ρ θ _ code .quoᴿ .snd (g' , h) =
    Σ≡Prop
      (λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropΠ λ _ → ρ _ _ _ .snd _ _)
      (funExt
        (elimProp
          (λ _ → S _ .snd _ _)
          (λ y → cong fst (θ _ _ .quoᴿ .snd (g' [ y ] , h refl)))))
  isSNRSUnaryFun {S = S} ρ θ (_ , bis) code .path =
    ua→
      (elimProp
        (λ _ → isOfHLevelPathP' 1 (λ i → S _ .snd) _ _)
        (λ x →
          θ _ (code (bis .fwdRel x)) .path
          ▷ cong fst
            (θ _ (code (bis .fwdRel x)) .quoᴿ .snd
              (θ _ (code (bis .bwdRel (bis .fwd x))) .quoᴿ .fst))))
