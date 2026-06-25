module Cubical.Data.Unit.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Relation.Nullary

open import Cubical.Data.Empty renaming (elim to ⊥-elim; elim* to ⊥*-elim)
open import Cubical.Data.Nat
open import Cubical.Data.Unit.Base
open import Cubical.Data.Prod.Base
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Reflection.StrictEquiv

open Iso

private
  variable
    ℓ ℓ' : Level

terminal : (A : Type ℓ) → A → Unit
terminal A x = tt

isContrUnit : isContr Unit
isContrUnit = tt , λ {tt → refl}

isPropUnit : isProp Unit
isPropUnit _ _ i = tt -- definitionally equal to: isContr→isProp isContrUnit

isSetUnit : isSet Unit
isSetUnit = isProp→isSet isPropUnit

isOfHLevelUnit : (n : HLevel) → isOfHLevel n Unit
isOfHLevelUnit n = isContr→isOfHLevel n isContrUnit

module _ (A : Type ℓ) where
  UnitToType≃ : (Unit → A) ≃ A
  unquoteDef UnitToType≃ = defStrictEquiv UnitToType≃ (λ f → f _) const

UnitToTypePath : ∀ {ℓ} (A : Type ℓ) → (Unit → A) ≡ A
UnitToTypePath A = ua (UnitToType≃ A)

module _ (A : Unit → Type ℓ) where

  open Iso

  ΠUnitIso : Iso ((x : Unit) → A x) (A tt)
  fun ΠUnitIso f = f tt
  inv ΠUnitIso a tt = a
  sec ΠUnitIso a = refl
  ret ΠUnitIso f = refl

  ΠUnit : ((x : Unit) → A x) ≃ A tt
  ΠUnit = isoToEquiv ΠUnitIso

module _ (A : Unit* {ℓ} → Type ℓ') where

  open Iso

  ΠUnit*Iso : Iso ((x : Unit*) → A x) (A tt*)
  fun ΠUnit*Iso f = f tt*
  inv ΠUnit*Iso a tt* = a
  sec ΠUnit*Iso a = refl
  ret ΠUnit*Iso f = refl

  ΠUnit* : ((x : Unit*) → A x) ≃ A tt*
  ΠUnit* = isoToEquiv ΠUnit*Iso

fiberUnitIso : {A : Type ℓ} → Iso (fiber (λ (a : A) → tt) tt) A
fun fiberUnitIso = fst
inv fiberUnitIso a = a , refl
sec fiberUnitIso _ = refl
ret fiberUnitIso _ = refl

isContr→Iso2 : {A : Type ℓ} {B : Type ℓ'} → isContr A → Iso (A → B) B
fun (isContr→Iso2 iscontr) f = f (fst iscontr)
inv (isContr→Iso2 iscontr) b _ = b
sec (isContr→Iso2 iscontr) _ = refl
ret (isContr→Iso2 iscontr) f = funExt λ x → cong f (snd iscontr x)

diagonal-unit : Unit ≡ Unit × Unit
diagonal-unit = isoToPath (iso (λ x → tt , tt) (λ x → tt) (λ {(tt , tt) i → tt , tt}) λ {tt i → tt})

fibId : (A : Type ℓ) → (fiber (λ (x : A) → tt) tt) ≡ A
fibId A = ua e
  where
  unquoteDecl e = declStrictEquiv e fst (λ a → a , refl)

isContr→≃Unit : {A : Type ℓ} → isContr A → A ≃ Unit
isContr→≃Unit contr = isoToEquiv (iso (λ _ → tt) (λ _ → fst contr) (λ _ → refl) λ _ → snd contr _)

isContr→≡Unit : {A : Type₀} → isContr A → A ≡ Unit
isContr→≡Unit contr = ua (isContr→≃Unit contr)

isContrUnit* : ∀ {ℓ} → isContr (Unit* {ℓ})
isContrUnit* = tt* , λ _ → refl

isPropUnit* : ∀ {ℓ} → isProp (Unit* {ℓ})
isPropUnit* _ _ = refl

isSetUnit* : ∀ {ℓ} → isSet (Unit* {ℓ})
isSetUnit* _ _ _ _ = refl

isOfHLevelUnit* : ∀ {ℓ} (n : HLevel) → isOfHLevel n (Unit* {ℓ})
isOfHLevelUnit* zero = tt* , λ _ → refl
isOfHLevelUnit* (suc zero) _ _ = refl
isOfHLevelUnit* (suc (suc zero)) _ _ _ _ _ _ = tt*
isOfHLevelUnit* (suc (suc (suc n))) = isOfHLevelPlus 3 (isOfHLevelUnit* n)

Unit≃Unit* : ∀ {ℓ} → Unit ≃ Unit* {ℓ}
Unit≃Unit* = invEquiv (isContr→≃Unit isContrUnit*)

isContr→≃Unit* : {A : Type ℓ} → isContr A → A ≃ Unit* {ℓ'}
isContr→≃Unit* contr = compEquiv (isContr→≃Unit contr) Unit≃Unit*

isContr→≡Unit* : {A : Type ℓ} → isContr A → A ≡ Unit*
isContr→≡Unit* contr = ua (isContr→≃Unit* contr)

-- J for pointed propositions
JPointedProp : ∀ {ℓ ℓ'} {B : (A : Type ℓ') (a : A) (isPr : isProp A) → Type ℓ}
  → B Unit* tt* isPropUnit*
  → (A : Type ℓ') (a : A) (isPr : isProp A) → B A a isPr
JPointedProp {ℓ' = ℓ'} {B = B} ind A a isPr =
  transport (λ i → B (P (~ i) .fst) (coh i) (P (~ i) .snd)) ind
  where
  A* : TypeOfHLevel ℓ' 1
  A* = A , isPr

  P : A* ≡ (Unit* , isPropUnit*)
  P = Σ≡Prop (λ _ → isPropIsProp)
        (ua (propBiimpl→Equiv isPr isPropUnit* (λ _ → tt*) λ _ → a))

  coh : PathP (λ i → (P (~ i) .fst)) tt* a
  coh = toPathP refl

⊥≢Unit : ¬ ⊥ ≡ Unit
⊥≢Unit ⊥≡Unit = ⊥-elim {A = λ _ → ⊥} (transport⁻ ⊥≡Unit tt)

⊥*≢Unit* : ¬ (⊥* {ℓ} :> Type ℓ) ≡ (Unit* {ℓ} :> Type ℓ)
⊥*≢Unit* ⊥≡Unit = ⊥*-elim {A = λ _ → ⊥} (transport⁻ ⊥≡Unit (lift tt))

Unit≢⊥ : ¬ Unit ≡ ⊥
Unit≢⊥ Unit≡⊥ = ⊥-elim {A = λ _ → ⊥} (transport Unit≡⊥ tt)

Unit*≢⊥* : ¬ (Unit* {ℓ} :> Type ℓ) ≡ (⊥* {ℓ} :> Type ℓ)
Unit*≢⊥* Unit≡⊥ = ⊥*-elim {A = λ _ → ⊥} (transport Unit≡⊥ (lift tt))
