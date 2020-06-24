{-

Definition of what it means to be a notion of relational structure

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.RelationalStructure where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients.Base
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.ZigZag.Base

open BinaryRelation

private
  variable
    ℓ ℓ' ℓ'' : Level

-- A set structure is a structure that takes sets to sets
record SetStructure (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    struct : Type ℓ → Type ℓ'
    set : ∀ {A} → isSet A → isSet (struct A)

open SetStructure public

-- A notion of structured relation for a structure S assigns a relation on S X and S Y to every relation on X
-- and Y. We require the output to be proposition-valued when the input is proposition-valued.
record StrRel (S : Type ℓ → Type ℓ') (ℓ'' : Level) : Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓ'')) ℓ') where
  field
    rel : ∀ {A B} (R : Rel A B ℓ) → Rel (S A) (S B) ℓ''
    prop : ∀ {A B R} → (∀ a b → isProp (R a b)) → ∀ s t → isProp (rel {A} {B} R s t)

open StrRel public

-- Given a type A and relation R, a quotient structure is a structure on the set quotient A/R such that
-- the graph of [_] : A → A/R is a structured relation
InducedQuotientStr : (S : Type ℓ → Type ℓ') (ρ : StrRel S ℓ'')
  (A : TypeWithStr ℓ S) (R : Rel (typ A) (typ A) ℓ)
  → Type (ℓ-max ℓ' ℓ'')
InducedQuotientStr S ρ A R =
  Σ (S (typ A / R)) (ρ .rel (λ a b → [ a ] ≡ b) (A .snd))

-- A bisimulation R between a pair of structured types A, B /descends to the quotients/ when the induced
-- equivalence relations Rᴸ and Rᴿ on A and B induce structures on A/Rᴸ and B/Rᴿ and there is a path
-- between these structures over the equivalence A/Rᴸ ≃ B/Rᴿ
record BisimDescends (S : Type ℓ → Type ℓ') (ρ : StrRel S ℓ'')
  (A B : TypeWithStr ℓ S) (R : Bisimulation (typ A) (typ B) ℓ) : Type (ℓ-max ℓ' ℓ'')
  where
  private
    module E = Bisim→Equiv R

  field
    quoᴸ : InducedQuotientStr S ρ A E.Rᴸ
    quoᴿ : InducedQuotientStr S ρ B E.Rᴿ
    path : PathP (λ i → S (ua E.Thm i)) (quoᴸ .fst) (quoᴿ .fst)

open BisimDescends

-- A notion of structured relations is standard when
-- (a) Given a structured type A and equivalence relation R, there is at most one quotient structure on A/R
-- (b) Any bisimulation descends to the quotients if and only if it is structured
record isUnivalentRel (S : SetStructure ℓ ℓ') (ρ : StrRel (S .struct) ℓ'') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
  where
  field
    propQuo : {A : TypeWithStr ℓ (S .struct)}
      (R : Σ[ R ∈ (typ A → typ A → Type ℓ) ] isEquivRel R)
      → isProp (InducedQuotientStr (S .struct) ρ A (R .fst))
    descends : {A B : TypeWithStr ℓ (S .struct)}
      (R : Bisimulation (typ A) (typ B) ℓ)
      → (ρ .rel (R .fst) (A .snd) (B .snd) → BisimDescends (S .struct) ρ A B R)
      × (BisimDescends (S .struct) ρ A B R → ρ .rel (R .fst) (A .snd) (B .snd))

  descendsEquiv : {A B : TypeWithStr ℓ (S .struct)}
    (R : Bisimulation (typ A) (typ B) ℓ)
    → ρ .rel (R .fst) (A .snd) (B .snd) ≃ BisimDescends (S .struct) ρ A B R
  descendsEquiv R =
    isPropEquiv→Equiv
      (ρ .prop (R .snd .isBisimulation.prop) _ _)
      isPropDescends
      (descends R .fst)
      (descends R .snd)
    where
    module E = Bisim→Equiv R

    isPropDescends : (d₀ d₁ : BisimDescends (S .struct) ρ _ _ R) → d₀ ≡ d₁
    isPropDescends d₀ d₁ j .quoᴸ = propQuo (bisim→EquivRel R) (d₀ .quoᴸ) (d₁ .quoᴸ) j
    isPropDescends d₀ d₁ j .quoᴿ = propQuo (bisim→EquivRel (invBisim R)) (d₀ .quoᴿ) (d₁ .quoᴿ) j
    isPropDescends d₀ d₁ j .path =
      isProp→PathP
        {B = λ j →
          PathP (λ i → S .struct (ua E.Thm i))
          (isPropDescends d₀ d₁ j .quoᴸ .fst)
          (isPropDescends d₀ d₁ j .quoᴿ .fst)}
        (λ i → isOfHLevelPathP' 1 (S .set squash/) _ _)
        (d₀ .path) (d₁ .path)
        j

