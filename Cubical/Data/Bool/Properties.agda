{-# OPTIONS --safe #-}
module Cubical.Data.Bool.Properties where

open import Cubical.Core.Everything

open import Cubical.Functions.Involution

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function

open import Cubical.Data.Sum hiding (elim)
open import Cubical.Data.Bool.Base
open import Cubical.Data.Empty hiding (elim)
open import Cubical.Data.Empty as Empty hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; isPropUnit)

open import Cubical.HITs.PropositionalTruncation hiding (elim; rec)

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    A : Type ℓ

elim : ∀ {ℓ} {A : Bool → Type ℓ}
  → A true
  → A false
  → (b : Bool) → A b
elim t f false = f
elim t f true  = t

notnot : ∀ x → not (not x) ≡ x
notnot true  = refl
notnot false = refl

notIso : Iso Bool Bool
Iso.fun notIso = not
Iso.inv notIso = not
Iso.rightInv notIso = notnot
Iso.leftInv notIso = notnot

notIsEquiv : isEquiv not
notIsEquiv = involIsEquiv {f = not} notnot

notEquiv : Bool ≃ Bool
notEquiv = involEquiv {f = not} notnot

notEq : Bool ≡ Bool
notEq = involPath {f = not} notnot

private
  -- This computes to false as expected
  nfalse : Bool
  nfalse = transp (λ i → notEq i) i0 true

  -- Sanity check
  nfalsepath : nfalse ≡ false
  nfalsepath = refl

K-Bool
  : (P : {b : Bool} → b ≡ b → Type ℓ)
  → (∀{b} → P {b} refl)
  → ∀{b} → (q : b ≡ b) → P q
K-Bool P Pr {false} = J (λ{ false q → P q ; true _ → Lift ⊥ }) Pr
K-Bool P Pr {true}  = J (λ{ true q → P q ; false _ → Lift ⊥ }) Pr

isSetBool : isSet Bool
isSetBool a b = J (λ _ p → ∀ q → p ≡ q) (K-Bool (refl ≡_) refl)

true≢false : ¬ true ≡ false
true≢false p = subst (λ b → if b then Bool else ⊥) p true

false≢true : ¬ false ≡ true
false≢true p = subst (λ b → if b then ⊥ else Bool) p true

¬true→false : (x : Bool) → ¬ x ≡ true → x ≡ false
¬true→false false _ = refl
¬true→false true p = Empty.rec (p refl)

¬false→true : (x : Bool) → ¬ x ≡ false → x ≡ true
¬false→true false p = Empty.rec (p refl)
¬false→true true _ = refl

not≢const : ∀ x → ¬ not x ≡ x
not≢const false = true≢false
not≢const true  = false≢true

-- or properties
or-zeroˡ : ∀ x → true or x ≡ true
or-zeroˡ _ = refl

or-zeroʳ : ∀ x → x or true ≡ true
or-zeroʳ false = refl
or-zeroʳ true  = refl

or-identityˡ : ∀ x → false or x ≡ x
or-identityˡ _ = refl

or-identityʳ : ∀ x → x or false ≡ x
or-identityʳ false = refl
or-identityʳ true  = refl

or-comm      : ∀ x y → x or y ≡ y or x
or-comm false false = refl
or-comm false true  = refl
or-comm true  false = refl
or-comm true  true  = refl

or-assoc     : ∀ x y z → x or (y or z) ≡ (x or y) or z
or-assoc false y z = refl
or-assoc true  y z = refl

or-idem      : ∀ x → x or x ≡ x
or-idem false = refl
or-idem true  = refl

-- and properties
and-zeroˡ : ∀ x → false and x ≡ false
and-zeroˡ _ = refl

and-zeroʳ : ∀ x → x and false ≡ false
and-zeroʳ false = refl
and-zeroʳ true  = refl

and-identityˡ : ∀ x → true and x ≡ x
and-identityˡ _ = refl

and-identityʳ : ∀ x → x and true ≡ x
and-identityʳ false = refl
and-identityʳ true  = refl

and-comm      : ∀ x y → x and y ≡ y and x
and-comm false false = refl
and-comm false true  = refl
and-comm true  false = refl
and-comm true  true  = refl

and-assoc     : ∀ x y z → x and (y and z) ≡ (x and y) and z
and-assoc false y z = refl
and-assoc true  y z = refl

and-idem      : ∀ x → x and x ≡ x
and-idem false = refl
and-idem true  = refl

-- xor properties
⊕-identityʳ : ∀ x → x ⊕ false ≡ x
⊕-identityʳ false = refl
⊕-identityʳ true = refl

⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
⊕-comm false false = refl
⊕-comm false true  = refl
⊕-comm true  false = refl
⊕-comm true  true  = refl

⊕-assoc : ∀ x y z → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
⊕-assoc false y z = refl
⊕-assoc true false z = refl
⊕-assoc true true z = notnot z

not-⊕ˡ : ∀ x y → not (x ⊕ y) ≡ not x ⊕ y
not-⊕ˡ false y = refl
not-⊕ˡ true  y = notnot y

⊕-invol : ∀ x y → x ⊕ (x ⊕ y) ≡ y
⊕-invol false x = refl
⊕-invol true  x = notnot x

isEquiv-⊕ : ∀ x → isEquiv (x ⊕_)
isEquiv-⊕ x = involIsEquiv (⊕-invol x)

⊕-Path : ∀ x → Bool ≡ Bool
⊕-Path x = involPath {f = x ⊕_} (⊕-invol x)

⊕-Path-refl : ⊕-Path false ≡ refl
⊕-Path-refl = isInjectiveTransport refl

¬transportNot : ∀(P : Bool ≡ Bool) b → ¬ (transport P (not b) ≡ transport P b)
¬transportNot P b eq = not≢const b sub
  where
  sub : not b ≡ b
  sub = subst {A = Bool → Bool} (λ f → f (not b) ≡ f b)
          (λ i c → transport⁻Transport P c i) (cong (transport⁻ P) eq)

module BoolReflection where
  data Table (A : Type₀) (P : Bool ≡ A) : Type₀ where
    inspect : (b c : A)
            → transport P false ≡ b
            → transport P true ≡ c
            → Table A P

  table : ∀ P → Table Bool P
  table = J Table (inspect false true refl refl)

  reflLemma : (P : Bool ≡ Bool)
         → transport P false ≡ false
         → transport P true ≡ true
         → transport P ≡ transport (⊕-Path false)
  reflLemma P ff tt i false = ff i
  reflLemma P ff tt i true = tt i

  notLemma : (P : Bool ≡ Bool)
         → transport P false ≡ true
         → transport P true ≡ false
         → transport P ≡ transport (⊕-Path true)
  notLemma P ft tf i false = ft i
  notLemma P ft tf i true  = tf i

  categorize : ∀ P → transport P ≡ transport (⊕-Path (transport P false))
  categorize P with table P
  categorize P | inspect false true p q
    = subst (λ b → transport P ≡ transport (⊕-Path b)) (sym p) (reflLemma P p q)
  categorize P | inspect true false p q
    = subst (λ b → transport P ≡ transport (⊕-Path b)) (sym p) (notLemma P p q)
  categorize P | inspect false false p q
    = Empty.rec (¬transportNot P false (q ∙ sym p))
  categorize P | inspect true true p q
    = Empty.rec (¬transportNot P false (q ∙ sym p))

  ⊕-complete : ∀ P → P ≡ ⊕-Path (transport P false)
  ⊕-complete P = isInjectiveTransport (categorize P)

  ⊕-comp : ∀ p q → ⊕-Path p ∙ ⊕-Path q ≡ ⊕-Path (q ⊕ p)
  ⊕-comp p q = isInjectiveTransport (λ i x → ⊕-assoc q p x i)

  open Iso

  reflectIso : Iso Bool (Bool ≡ Bool)
  reflectIso .fun = ⊕-Path
  reflectIso .inv P = transport P false
  reflectIso .leftInv = ⊕-identityʳ
  reflectIso .rightInv P = sym (⊕-complete P)

  reflectEquiv : Bool ≃ (Bool ≡ Bool)
  reflectEquiv = isoToEquiv reflectIso

_≤_ : Bool → Bool → Type
true ≤ false = ⊥
_ ≤ _ = Unit

_≥_ : Bool → Bool → Type
false ≥ true = ⊥
_ ≥ _ = Unit

isProp≤ : ∀ b c → isProp (b ≤ c)
isProp≤  true false = isProp⊥
isProp≤  true  true = isPropUnit
isProp≤ false false = isPropUnit
isProp≤ false  true = isPropUnit

isProp≥ : ∀ b c → isProp (b ≥ c)
isProp≥ false  true = isProp⊥
isProp≥  true  true = isPropUnit
isProp≥ false false = isPropUnit
isProp≥  true false = isPropUnit

isProp-Bool→Type : ∀ b → isProp (Bool→Type b)
isProp-Bool→Type false = isProp⊥
isProp-Bool→Type true = isPropUnit

isPropDep-Bool→Type : isPropDep Bool→Type
isPropDep-Bool→Type = isOfHLevel→isOfHLevelDep 1 isProp-Bool→Type

IsoBool→∙ : ∀ {ℓ} {A : Pointed ℓ} → Iso ((Bool , true) →∙ A) (typ A)
Iso.fun IsoBool→∙ f = fst f false
fst (Iso.inv IsoBool→∙ a) false = a
fst (Iso.inv (IsoBool→∙ {A = A}) a) true = pt A
snd (Iso.inv IsoBool→∙ a) = refl
Iso.rightInv IsoBool→∙ a = refl
Iso.leftInv IsoBool→∙ (f , p) =
  ΣPathP ((funExt (λ { false → refl ; true → sym p}))
        , λ i j → p (~ i ∨ j))

-- import here to avoid conflicts
open import Cubical.Data.Unit

-- relation to hProp

BoolProp≃BoolProp* : {a : Bool} → Bool→Type a ≃ Bool→Type* {ℓ} a
BoolProp≃BoolProp* {a = true} = Unit≃Unit*
BoolProp≃BoolProp* {a = false} = uninhabEquiv Empty.rec Empty.rec*

Bool→TypeInj : (a b : Bool) → Bool→Type a ≃ Bool→Type b → a ≡ b
Bool→TypeInj true true _ = refl
Bool→TypeInj true false p = Empty.rec (p .fst tt)
Bool→TypeInj false true p = Empty.rec (invEq p tt)
Bool→TypeInj false false _ = refl

Bool→TypeInj* : (a b : Bool) → Bool→Type* {ℓ} a ≃ Bool→Type* {ℓ} b → a ≡ b
Bool→TypeInj* true true _ = refl
Bool→TypeInj* true false p = Empty.rec* (p .fst tt*)
Bool→TypeInj* false true p = Empty.rec* (invEq p tt*)
Bool→TypeInj* false false _ = refl

isPropBool→Type : {a : Bool} → isProp (Bool→Type a)
isPropBool→Type {a = true} = isPropUnit
isPropBool→Type {a = false} = isProp⊥

isPropBool→Type* : {a : Bool} → isProp (Bool→Type* {ℓ} a)
isPropBool→Type* {a = true} = isPropUnit*
isPropBool→Type* {a = false} = isProp⊥*

DecBool→Type : {a : Bool} → Dec (Bool→Type a)
DecBool→Type {a = true} = yes tt
DecBool→Type {a = false} = no (λ x → x)

DecBool→Type* : {a : Bool} → Dec (Bool→Type* {ℓ} a)
DecBool→Type* {a = true} = yes tt*
DecBool→Type* {a = false} = no (λ (lift x) → x)

Dec→DecBool : {P : Type ℓ} → (dec : Dec P) → P → Bool→Type (Dec→Bool dec)
Dec→DecBool (yes p) _ = tt
Dec→DecBool (no ¬p) q = Empty.rec (¬p q)

DecBool→Dec : {P : Type ℓ} → (dec : Dec P) → Bool→Type (Dec→Bool dec) → P
DecBool→Dec (yes p) _ = p

Dec≃DecBool : {P : Type ℓ} → (h : isProp P)(dec : Dec P) → P ≃ Bool→Type (Dec→Bool dec)
Dec≃DecBool h dec = propBiimpl→Equiv h isPropBool→Type (Dec→DecBool dec) (DecBool→Dec dec)

Bool≡BoolDec : {a : Bool} → a ≡ Dec→Bool (DecBool→Type {a = a})
Bool≡BoolDec {a = true} = refl
Bool≡BoolDec {a = false} = refl

Dec→DecBool* : {P : Type ℓ} → (dec : Dec P) → P → Bool→Type* {ℓ} (Dec→Bool dec)
Dec→DecBool* (yes p) _ = tt*
Dec→DecBool* (no ¬p) q = Empty.rec (¬p q)

DecBool→Dec* : {P : Type ℓ} → (dec : Dec P) → Bool→Type* {ℓ} (Dec→Bool dec) → P
DecBool→Dec* (yes p) _ = p

Dec≃DecBool* : {P : Type ℓ} → (h : isProp P)(dec : Dec P) → P ≃ Bool→Type* {ℓ} (Dec→Bool dec)
Dec≃DecBool* h dec = propBiimpl→Equiv h isPropBool→Type* (Dec→DecBool* dec) (DecBool→Dec* dec)

Bool≡BoolDec* : {a : Bool} → a ≡ Dec→Bool (DecBool→Type* {ℓ} {a = a})
Bool≡BoolDec* {a = true} = refl
Bool≡BoolDec* {a = false} = refl

Bool→Type× : (a b : Bool) → Bool→Type (a and b) → Bool→Type a × Bool→Type b
Bool→Type× true true _ = tt , tt
Bool→Type× true false p = Empty.rec p
Bool→Type× false true p = Empty.rec p
Bool→Type× false false p = Empty.rec p

Bool→Type×' : (a b : Bool) → Bool→Type a × Bool→Type b → Bool→Type (a and b)
Bool→Type×' true true _ = tt
Bool→Type×' true false (_ , p) = Empty.rec p
Bool→Type×' false true (p , _) = Empty.rec p
Bool→Type×' false false (p , _) = Empty.rec p

Bool→Type×≃ : (a b : Bool) → Bool→Type a × Bool→Type b ≃ Bool→Type (a and b)
Bool→Type×≃ a b =
  propBiimpl→Equiv (isProp× isPropBool→Type isPropBool→Type) isPropBool→Type
    (Bool→Type×' a b) (Bool→Type× a b)

Bool→Type⊎ : (a b : Bool) → Bool→Type (a or b) → Bool→Type a ⊎ Bool→Type b
Bool→Type⊎ true true _ = inl tt
Bool→Type⊎ true false _ = inl tt
Bool→Type⊎ false true _ = inr tt
Bool→Type⊎ false false p = Empty.rec p

Bool→Type⊎' : (a b : Bool) → Bool→Type a ⊎ Bool→Type b → Bool→Type (a or b)
Bool→Type⊎' true true _ = tt
Bool→Type⊎' true false _ = tt
Bool→Type⊎' false true _ = tt
Bool→Type⊎' false false (inl p) = Empty.rec p
Bool→Type⊎' false false (inr p) = Empty.rec p

PropBoolP→P : (dec : Dec A) → Bool→Type (Dec→Bool dec) → A
PropBoolP→P (yes p) _ = p

P→PropBoolP : (dec : Dec A) → A → Bool→Type (Dec→Bool dec)
P→PropBoolP (yes p) _ = tt
P→PropBoolP (no ¬p) = ¬p

Bool≡ : Bool → Bool → Bool
Bool≡ true true = true
Bool≡ true false = false
Bool≡ false true = false
Bool≡ false false = true

Bool≡≃ : (a b : Bool) → (a ≡ b) ≃ Bool→Type (Bool≡ a b)
Bool≡≃ true true = isContr→≃Unit (inhProp→isContr refl (isSetBool _ _))
Bool≡≃ true false = uninhabEquiv true≢false Empty.rec
Bool≡≃ false true = uninhabEquiv false≢true Empty.rec
Bool≡≃ false false = isContr→≃Unit (inhProp→isContr refl (isSetBool _ _))
open Iso

-- Bool is equivalent to bi-point type

Iso-⊤⊎⊤-Bool : Iso (Unit ⊎ Unit) Bool
Iso-⊤⊎⊤-Bool .fun (inl tt) = true
Iso-⊤⊎⊤-Bool .fun (inr tt) = false
Iso-⊤⊎⊤-Bool .inv true = inl tt
Iso-⊤⊎⊤-Bool .inv false = inr tt
Iso-⊤⊎⊤-Bool .leftInv (inl tt) = refl
Iso-⊤⊎⊤-Bool .leftInv (inr tt) = refl
Iso-⊤⊎⊤-Bool .rightInv true = refl
Iso-⊤⊎⊤-Bool .rightInv false = refl

¬IsoUnitBool : ¬ Iso Unit Bool
¬IsoUnitBool isom = true≢false
 (isOfHLevelRetractFromIso 1 (invIso isom) isPropUnit true false) 

separatedBool : Separated Bool
separatedBool = Discrete→Separated _≟_

elim𝟚< : ∀ (a b c : Bool) → ¬ a ≡ b → ¬ a ≡ c → ¬ (b ≡ c) → ⊥ 
elim𝟚< false false c x x₁ x₂ = x refl
elim𝟚< false true false x x₁ x₂ = x₁ refl
elim𝟚< false true true x x₁ x₂ = x₂ refl
elim𝟚< true false false x x₁ x₂ = x₂ refl
elim𝟚< true false true x x₁ x₂ = x₁ refl
elim𝟚< true true c x x₁ x₂ = x refl

elim𝟚<fromIso : Iso A Bool → ∀ (a b c : A) → ¬ a ≡ b → ¬ a ≡ c → ¬ (b ≡ c) → ⊥
elim𝟚<fromIso isom _ _ _ a≢b a≢c b≢c =
  elim𝟚< _ _ _
    (a≢b ∘ isoFunInjective isom _ _ )
    (a≢c ∘ isoFunInjective isom _ _ )
    (b≢c ∘ isoFunInjective isom _ _ ) 
 where
 open Iso isom
