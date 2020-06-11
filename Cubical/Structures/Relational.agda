{-# OPTIONS --cubical #-}
module Cubical.Structures.Relational where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Data.Sigma
open import Cubical.Relation.ZigZag.Base
open import Cubical.Relation.Binary
open import Cubical.HITs.SetQuotients

-- lemmas to move

J' : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A}
  (P : ∀ y → x ≡ y → Type ℓ') (d : P x refl)
  (y : A) (p : x ≡ y) → P y p
J' P d y p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

_/set_ : ∀ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') → hSet (ℓ-max ℓ ℓ')
A /set R = A / R , squash/

setUA : ∀ {ℓ} (A B : hSet ℓ) (e : A .fst ≃ B .fst) → A ≡ B
setUA A B e = Σ≡Prop (λ _ → isPropIsSet) (ua e)

postulate -- TODO
  helper : ∀ {ℓ ℓ'} {A : I → Type ℓ} (B : (i : I) → A i → Type ℓ')
    {a₀ : A i0} {a₁ : A i1} {b₀ : B i0 a₀} {b₁ : B i1 a₁}
    {p q : PathP A a₀ a₁}
    → isProp (A i0) -- isSet would be enough
    → PathP (λ i → B i (p i)) b₀ b₁ ≃ PathP (λ i → B i (q i)) b₀ b₁

postulate -- TODO
  ua→ : ∀ {ℓ ℓ'} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁} {B : (i : I) → Type ℓ'}
    {f₀ : A₀ → B i0} {f₁ : A₁ → B i1}
    → ((a : A₀) → PathP (λ i → B i) (f₀ a) (f₁ (e .fst a)))
    → PathP (λ i → ua e i → B i) f₀ f₁

-- main event

private
  variable
    ℓ ℓ' : Level

open isBisimulation

-- Suitable relations

record isSuitable {A B : Type ℓ} (R : A → B → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    zigzag : isZigZagComplete R
    prop : ∀ a b → isProp (R a b)

SuitableRel : (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
SuitableRel A B ℓ' =
  Σ[ R ∈ (A → B → Type ℓ') ] isSuitable R

open isSuitable

quotientSuitable : {A : Type ℓ} (R : A → A → Type ℓ)
  → SuitableRel A (A / R) ℓ
quotientSuitable R .fst a b = [ a ] ≡ b
quotientSuitable R .snd .zigzag r₀ r₁ r₂ = r₀ ∙ sym r₁ ∙ r₂
quotientSuitable R .snd .prop a = squash/ [ a ]

isBisimulation→isSuitable : {A B : Type ℓ} {R : A → B → Type ℓ'}
  → isBisimulation R → isSuitable R
isBisimulation→isSuitable bisim .zigzag = bisim .zigzag
isBisimulation→isSuitable bisim .prop = bisim .prop

Bisimulation→Suitable : {A B : Type ℓ} {ℓ' : Level}
  → Bisimulation A B ℓ' → SuitableRel A B ℓ'
Bisimulation→Suitable (R , bisim) = R , isBisimulation→isSuitable bisim

-- Definition of standard notion of structure

SetWithStr : (ℓ : Level) (S : hSet ℓ → hSet ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
SetWithStr ℓ S = Σ[ X ∈ hSet ℓ ] S X .fst

set : {S : hSet ℓ → Type ℓ'} → (Σ[ X ∈ hSet ℓ ] S X) → hSet ℓ
set XS = XS .fst

typ : {S : hSet ℓ → Type ℓ'} → (Σ[ X ∈ hSet ℓ ] S X) → Type ℓ
typ XS = XS .fst .fst

StrRel : (S : hSet ℓ → hSet ℓ') (ℓ'' : Level) → Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓ'')) ℓ')
StrRel {ℓ} S ℓ'' =
  (A B : hSet ℓ) (R : SuitableRel (A .fst) (B .fst) ℓ) → SuitableRel (S A .fst) (S B .fst) ℓ''

record Descends (S : hSet ℓ → hSet ℓ') {ℓ'' : Level} (ρ : StrRel S ℓ'')
  (A B : SetWithStr ℓ S) (R : Bisimulation (typ A) (typ B) ℓ) : Type (ℓ-max ℓ' ℓ'')
  where
  private
    module E = Bisim→Equiv R

  field
    strᴸ : S (typ A /set E.Rᴸ) .fst
    matchᴸ : ρ (A .fst) (typ A /set E.Rᴸ) (quotientSuitable E.Rᴸ) .fst (A .snd) strᴸ

    strᴿ : S (typ B /set E.Rᴿ) .fst
    matchᴿ : ρ (B .fst) (typ B /set E.Rᴿ) (quotientSuitable E.Rᴿ) .fst (B .snd) strᴿ

    path : PathP (λ i → S (setUA (typ A /set E.Rᴸ) (typ B /set E.Rᴿ) E.Thm i) .fst) strᴸ strᴿ

open Descends

isSNRS : (S : hSet ℓ → hSet ℓ') {ℓ'' : Level} → StrRel S ℓ'' → Type _
isSNRS {ℓ} S ρ =
  (A B : SetWithStr ℓ S) (R : Bisimulation (typ A) (typ B) ℓ)
  → ρ (A .fst) (B .fst) (Bisimulation→Suitable R) .fst (A .snd) (B .snd)
  → Descends S ρ A B R

-- constant

module _ {ℓ : Level} (A : hSet ℓ') where

  constant-structure : hSet ℓ → hSet ℓ'
  constant-structure _ = A

  constant-rel : StrRel constant-structure ℓ'
  constant-rel _ _ _ .fst a₀ a₁ = a₀ ≡ a₁
  constant-rel _ _ _ .snd .zigzag r₀ r₁ r₂ = r₀ ∙ sym r₁ ∙ r₂
  constant-rel _ _ _ .snd .prop = A .snd

  isSNRSConstant : isSNRS constant-structure constant-rel
  isSNRSConstant (_ , a₀) (_ , a₁) _ _ .strᴸ = a₀
  isSNRSConstant (_ , a₀) (_ , a₁) _ _ .matchᴸ = refl
  isSNRSConstant (_ , a₀) (_ , a₁) _ _ .strᴿ = a₁
  isSNRSConstant (_ , a₀) (_ , a₁) _ _ .matchᴿ = refl
  isSNRSConstant (_ , a₀) (_ , a₁) _ r .path = r

-- pointed

pointed-structure : hSet ℓ → hSet ℓ
pointed-structure X = X

pointed-rel : StrRel pointed-structure ℓ
pointed-rel _ _ R .fst x y = R .fst x y
pointed-rel _ _ R .snd .zigzag = R .snd .zigzag
pointed-rel _ _ R .snd .prop = R .snd .prop

isSNRSPointed : isSNRS {ℓ = ℓ} pointed-structure pointed-rel
isSNRSPointed (_ , x) (_ , y) _ _ .strᴸ = [ x ]
isSNRSPointed (_ , x) (_ , y) _ _ .matchᴸ = refl
isSNRSPointed (_ , x) (_ , y) _ _ .strᴿ = [ y ]
isSNRSPointed (_ , x) (_ , y) _ _ .matchᴿ = refl
isSNRSPointed (_ , x) (_ , y) R r .path =
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

-- join

module _ {ℓ₁ ℓ₂} where

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
  join-rel S₁ ρ₁ S₂ ρ₂ X Y R .snd .zigzag r₀ r₁ r₂ =
    ( ρ₁ X Y R .snd .zigzag (r₀ .fst) (r₁ .fst) (r₂ .fst)
    , ρ₂ X Y R .snd .zigzag (r₀ .snd) (r₁ .snd) (r₂ .snd)
    )
  join-rel S₁ ρ₁ S₂ ρ₂ X Y R .snd .prop (s₁ , s₂) (t₁ , t₂) =
    isProp× (ρ₁ X Y R .snd .prop s₁ t₁) (ρ₂ X Y R .snd .prop s₂ t₂)

  isSNRSJoin :
    {S₁ : hSet ℓ → hSet ℓ₁} {ℓ₁' : Level} {ρ₁ : StrRel S₁ ℓ₁'}
    {S₂ : hSet ℓ → hSet ℓ₂} {ℓ₂' : Level} {ρ₂ : StrRel S₂ ℓ₂'}
    → isSNRS S₁ ρ₁ → isSNRS S₂ ρ₂
    → isSNRS (join-structure S₁ S₂) (join-rel S₁ ρ₁ S₂ ρ₂)
  isSNRSJoin θ₁ θ₂ (_ , s₁ , s₂) (_ , t₁ , t₂) R (code₁ , code₂) .strᴸ =
    θ₁ (_ , s₁) (_ , t₁) R code₁ .strᴸ , θ₂ (_ , s₂) (_ , t₂) R code₂ .strᴸ
  isSNRSJoin θ₁ θ₂ (_ , s₁ , s₂) (_ , t₁ , t₂) R (code₁ , code₂) .matchᴸ =
    θ₁ (_ , s₁) (_ , t₁) R code₁ .matchᴸ , θ₂ (_ , s₂) (_ , t₂) R code₂ .matchᴸ
  isSNRSJoin θ₁ θ₂ (_ , s₁ , s₂) (_ , t₁ , t₂) R (code₁ , code₂) .strᴿ =
    θ₁ (_ , s₁) (_ , t₁) R code₁ .strᴿ , θ₂ (_ , s₂) (_ , t₂) R code₂ .strᴿ
  isSNRSJoin θ₁ θ₂ (_ , s₁ , s₂) (_ , t₁ , t₂) R (code₁ , code₂) .matchᴿ =
    θ₁ (_ , s₁) (_ , t₁) R code₁ .matchᴿ , θ₂ (_ , s₂) (_ , t₂) R code₂ .matchᴿ
  isSNRSJoin {S₁ = S₁} {S₂ = S₂} θ₁ θ₂ (_ , s₁ , s₂) (_ , t₁ , t₂) R (code₁ , code₂) .path =
    equivFun ΣPathP≃PathPΣ
      ( equivFun (helper (λ i z → S₁ (_ , z) .fst) isPropIsSet)
        (θ₁ (_ , s₁) (_ , t₁) R code₁ .path)
      , equivFun (helper (λ i z → S₂ (_ , z) .fst) isPropIsSet)
        (θ₂ (_ , s₂) (_ , t₂) R code₂ .path)
      )

-- parameterized

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
  parameterized-rel S ρ X Y R .snd .zigzag r₀ r₁ r₂ a =
    ρ a X Y R .snd .zigzag (r₀ a) (r₁ a) (r₂ a)
  parameterized-rel S ρ X Y R .snd .prop s t =
    isPropΠ λ a → ρ a X Y R .snd .prop (s a) (t a)

  isSNRSParameterized : {S : A → hSet ℓ₁ → hSet ℓ₂} {ℓ₃ : Level}
    (ρ : ∀ a → StrRel (S a) ℓ₃)
    → (∀ a → isSNRS (S a) (ρ a))
    → isSNRS (parameterized-structure S) (parameterized-rel S ρ)
  isSNRSParameterized ρ θ (_ , s) (_ , t) R code .strᴸ a = θ a (_ , s a) (_ , t a) R (code a) .strᴸ
  isSNRSParameterized ρ θ (_ , s) (_ , t) R code .matchᴸ a = θ a (_ , s a) (_ , t a) R (code a) .matchᴸ
  isSNRSParameterized ρ θ (_ , s) (_ , t) R code .strᴿ a = θ a (_ , s a) (_ , t a) R (code a) .strᴿ
  isSNRSParameterized ρ θ (_ , s) (_ , t) R code .matchᴿ a = θ a (_ , s a) (_ , t a) R (code a) .matchᴿ
  isSNRSParameterized {S = S} ρ θ (_ , s) (_ , t) R code .path =
    funExt λ a →
    equivFun (helper (λ i z → S a (_ , z) .fst) isPropIsSet)
      (θ a (_ , s a) (_ , t a) R (code a) .path)

-- X ↦ X → X
-- TODO: generalize to (X ↦ X → S X) for another structure S

module _ where

  unaryFun-structure : hSet ℓ → hSet ℓ
  unaryFun-structure X .fst = X .fst → X .fst
  unaryFun-structure X .snd = isSetΠ λ _ → X .snd

  unaryFun-rel : StrRel unaryFun-structure ℓ
  unaryFun-rel X Y R .fst f g =
    (x : X .fst) (y : Y .fst)
    → R .fst x y
    → R .fst (f x) (g y)
  unaryFun-rel X Y R .snd .zigzag {f} {g} {f'} {g'} r₀ r₁ r₂ x y r =
    R .snd .zigzag (r₀ x y r) (r₁ x y r) (r₂ x y r)
  unaryFun-rel X Y R .snd .prop f g =
    isPropΠ3 λ x y _ → R .snd .prop (f x) (g y)

  isSNRSUnaryFun : isSNRS {ℓ = ℓ} unaryFun-structure unaryFun-rel
  isSNRSUnaryFun (X , f) (Y , g) (R , bis) code .strᴸ = str
    where
    str : _
    str [ x ] = [ f x ]
    str (eq/ x₀ x₁ r i) =
      eq/ (f x₀) (f x₁)
        (bis .zigzag
          (code x₀ (bis .fwd x₁) r)
          (code x₁ (bis .fwd x₁) (bis .fwdRel x₁))
          (bis .fwdRel (f x₁)))
        i
    str (squash/ x₀ x₁ p q j i) = squash/ _ _ (cong str p) (cong str q) j i
  isSNRSUnaryFun (_ , f) (_ , g) (_ , bis) _ .matchᴸ x = J' _ refl
  isSNRSUnaryFun (_ , f) (_ , g) (_ , bis) code .strᴿ = str
    where
    str : _
    str [ y ] = [ g y ]
    str (eq/ y₀ y₁ r i) =
      eq/ (g y₀) (g y₁)
        (bis .zigzag
          (bis .bwdRel (g y₁))
          (code (bis .bwd y₁) y₁ (bis .bwdRel y₁))
          (code (bis .bwd y₁) y₀ r))
        i
    str (squash/ y₀ y₁ p q j i) = squash/ _ _ (cong str p) (cong str q) j i
  isSNRSUnaryFun (_ , f) (_ , g) (_ , bis) _ .matchᴿ y = J' _ refl
  isSNRSUnaryFun (X , f) (Y , g) (_ , bis) code .path =
    ua→
      (elimProp
        (λ _ → isOfHLevelPathP' 1 (λ i → setUA (X .fst /set E.Rᴸ) (Y .fst /set E.Rᴿ) E.Thm i .snd) _ _)
        (λ x → ua-gluePath _
          (eq/ (bis .fwd (f x)) (g (bis .fwd x))
            (bis .zigzag
              (bis .bwdRel (g (bis .fwd x)))
              (code x (bis .fwd x) (bis .fwdRel x))
              (bis .fwdRel (f x))))))
    where
    module E = Bisim→Equiv (_ , bis)
