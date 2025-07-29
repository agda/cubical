{-# OPTIONS --safe #-}

module Cubical.Algebra.MndContainer.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Algebra.MndContainer.Base
open import Cubical.Data.Containers.Set.Base
open import Cubical.Data.Unit
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Sum

private
  variable
    ℓs ℓp ℓ ℓ' ℓ'' : Level

open MndContainer
open IsMndContainer

State : (S : hSet ℓ) → SetCon {ℓ} {ℓ}
State (S , setS) = (S → S) ◁ (λ _ → S) & isSetΠ (λ _ → setS) & setS

JustOrNothing : Bool* {ℓ} → Type ℓ'
JustOrNothing (lift false) = ⊥* 
JustOrNothing (lift true) = Unit*

isSetJustOrNothing : ∀ {ℓ ℓ'} → {s : Bool* {ℓ}} → isSet {ℓ'} (JustOrNothing {ℓ} {ℓ'} s)
isSetJustOrNothing {_} {_} {lift false} x = rec* x
isSetJustOrNothing {_} {_} {lift true} = isSetUnit*

Maybe : SetCon {ℓs} {ℓp}
Maybe {ℓs} {ℓp} = Bool* {ℓs} ◁ JustOrNothing {ℓs} {ℓp} & isSetBool* & (λ {s} → isSetJustOrNothing {_} {_} {s})

LOrR : {A : Type ℓ} {B : Type ℓ'} → A ⊎ B → Type ℓ''
LOrR (inl a) = Unit*
LOrR (inr b) = ⊥*

isSetLOrR : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {x : A ⊎ B} → isSet {ℓ''} (LOrR x)
isSetLOrR {_} {_} {_} {A} {B} {inl a} = isSetUnit*
isSetLOrR {_} {_} {_} {A} {B} {inr b} x = rec* x

-- Examples of monadic containers

ReaderM : (A : hSet ℓp) → MndContainer {ℓs} {ℓp} (Unit* ◁ (λ _ → fst A) & isSetUnit* & snd A)
ι (ReaderM A) = tt*
σ (ReaderM A) _ _ = tt*
pr₁ (ReaderM A) _ _ p = p
pr₂ (ReaderM A) _ _ p = p
unit-l (isMndContainer (ReaderM A)) tt* = refl
unit-r (isMndContainer (ReaderM A)) tt* = refl
assoc (isMndContainer (ReaderM A)) tt* _ _ = refl
pr-unit-r (isMndContainer (ReaderM A)) = refl
pr-unit-l (isMndContainer (ReaderM A)) = refl
pr-mul₁ (isMndContainer (ReaderM A)) = refl
pr-mul₁₂ (isMndContainer (ReaderM A)) = refl
pr-mul₂₂ (isMndContainer (ReaderM A)) = refl

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.Instances.Nat
open MonoidStr
open IsMonoid

WriterM : (A : hSet ℓs) (mon : MonoidStr (fst A)) → MndContainer {ℓs} {ℓp} (fst A ◁ const Unit* & snd A & isSetUnit*)
ι (WriterM A mon) = mon .ε
σ (WriterM A mon) a b = (mon ._·_) a (b tt*)
pr₁ (WriterM A mon) _ _ tt* = tt*
pr₂ (WriterM A mon) _ _ tt* = tt*
unit-l (isMndContainer (WriterM A mon)) a = mon .·IdL a
unit-r (isMndContainer (WriterM A mon)) a = mon .·IdR a
assoc (isMndContainer (WriterM A mon)) a b c = mon .·Assoc a (b tt*) (c tt* tt*)
pr-unit-r (isMndContainer (WriterM A mon)) i tt* = tt*
pr-unit-l (isMndContainer (WriterM A mon)) i tt* = tt*
pr-mul₁ (isMndContainer (WriterM A mon)) i tt* = tt*
pr-mul₁₂ (isMndContainer (WriterM A mon)) i tt* = tt*
pr-mul₂₂ (isMndContainer (WriterM A mon)) i tt* = tt*

StreamM : MndContainer {ℓs} {ℓ-zero} (Unit* ◁ const ℕ & isSetUnit* & isSetℕ)
StreamM = ReaderM (ℕ , isSetℕ)

StateM : (S : hSet ℓs) → MndContainer {ℓs} {ℓs} (State S)
ι (StateM S) s = s
σ (StateM S) f g s = g s (f s)
pr₁ (StateM S) _ _ s = s
pr₂ (StateM S) f _ s = f s
unit-l (isMndContainer (StateM S)) f = refl
unit-r (isMndContainer (StateM S)) f = refl
assoc (isMndContainer (StateM S)) f g h = refl
pr-unit-r (isMndContainer (StateM S)) = refl
pr-unit-l (isMndContainer (StateM S)) = refl
pr-mul₁ (isMndContainer (StateM S)) = refl
pr-mul₁₂ (isMndContainer (StateM S)) = refl
pr-mul₂₂ (isMndContainer (StateM S)) = refl

MaybeM : MndContainer {ℓs} {ℓp} Maybe
ι MaybeM = true*
σ MaybeM (lift true) f = f tt*
σ MaybeM (lift false) f = false*
pr₁ MaybeM (lift true) _ _ = tt*
pr₂ MaybeM (lift true) _ p = p
pr₂ MaybeM (lift false) _ ()
unit-l (isMndContainer MaybeM) a = refl
unit-r (isMndContainer MaybeM) (lift true) = refl
unit-r (isMndContainer MaybeM) (lift false) = refl
assoc (isMndContainer MaybeM) (lift true) b c = refl
assoc (isMndContainer MaybeM) (lift false) b c = refl
pr-unit-r (isMndContainer MaybeM) {lift true} i tt* = tt*
pr-unit-l (isMndContainer MaybeM) {lift true} i p = p
pr-mul₁ (isMndContainer MaybeM)  {lift true} {b} {c} i = λ _ → tt*
pr-mul₁₂ (isMndContainer MaybeM) {lift true} {b} {c} i p' = pr₁ MaybeM (b tt*) (c tt*) p'
pr-mul₂₂ (isMndContainer MaybeM) {lift true} {b} {c} i p' = pr₂ MaybeM (b tt*) (c tt*) p'

-- Note: MaybeM is also special case of CoproductM when E = ⊤

CoproductM : ∀ {ℓs ℓs'} (E : hSet ℓs) →
             MndContainer {ℓ-max ℓs ℓs'} {ℓs'} ((Unit* {ℓs'} ⊎ (fst E)) ◁ LOrR & (isSet⊎ isSetUnit* (snd E)) & isSetLOrR)
ι (CoproductM E) = inl tt*
σ (CoproductM E) (inl tt*) f = f tt*
σ (CoproductM E) (inr e) f = inr e
pr₁ (CoproductM E) (inl tt*) _ _ = tt*
pr₂ (CoproductM E) (inl tt*) _ y = y
unit-l (isMndContainer (CoproductM E)) _ = refl
unit-r (isMndContainer (CoproductM E)) (inl tt*) = refl
unit-r (isMndContainer (CoproductM E)) (inr e) = refl
assoc (isMndContainer (CoproductM E)) (inl tt*) b c = refl
assoc (isMndContainer (CoproductM E)) (inr e) b c = refl
pr-unit-r (isMndContainer (CoproductM E)) {inl tt*} i tt* = tt*
pr-unit-l (isMndContainer (CoproductM E)) = refl
pr-mul₁ (isMndContainer (CoproductM E)) {inl tt*} = refl
pr-mul₁ (isMndContainer (CoproductM E)) {inr e} i ()
pr-mul₁₂ (isMndContainer (CoproductM E)) {inl tt*} = refl
pr-mul₁₂ (isMndContainer (CoproductM E)) {inr e} i ()
pr-mul₂₂ (isMndContainer (CoproductM E)) {inl tt*} = refl
pr-mul₂₂ (isMndContainer (CoproductM E)) {inr e} i ()

