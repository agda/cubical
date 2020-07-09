{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv

Rel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Rel A B ℓ' = A → B → Type ℓ'

PropRel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
PropRel A B ℓ' = Σ[ R ∈ Rel A B ℓ' ] ∀ a b → isProp (R a b)

idPropRel : ∀ {ℓ} (A : Type ℓ) → PropRel A A ℓ
idPropRel A .fst a a' = ∥ a ≡ a' ∥
idPropRel A .snd _ _ = squash

invPropRel : ∀ {ℓ ℓ'} {A B : Type ℓ}
  → PropRel A B ℓ' → PropRel B A ℓ'
invPropRel R .fst b a = R .fst a b
invPropRel R .snd b a = R .snd a b

compPropRel : ∀ {ℓ ℓ' ℓ''} {A B C : Type ℓ}
  → PropRel A B ℓ' → PropRel B C ℓ'' → PropRel A C (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
compPropRel R S .fst a c = ∥ Σ[ b ∈ _ ] (R .fst a b × S .fst b c) ∥
compPropRel R S .snd _ _ = squash

graphRel : ∀ {ℓ} {A B : Type ℓ} → (A → B) → Rel A B ℓ
graphRel f a b = f a ≡ b

module BinaryRelation {ℓ ℓ' : Level} {A : Type ℓ} (_R_ : Rel A A ℓ') where
  isRefl : Type (ℓ-max ℓ ℓ')
  isRefl = (a : A) → a R a

  isSym : Type (ℓ-max ℓ ℓ')
  isSym = (a b : A) → a R b → b R a

  isTrans : Type (ℓ-max ℓ ℓ')
  isTrans = (a b c : A)  → a R b → b R c → a R c

  record isEquivRel : Type (ℓ-max ℓ ℓ') where
    constructor equivRel
    field
      reflexive : isRefl
      symmetric : isSym
      transitive : isTrans

  isPropValued : Type (ℓ-max ℓ ℓ')
  isPropValued = (a b : A) → isProp (a R b)

  isEffective : Type (ℓ-max ℓ ℓ')
  isEffective =
    (a b : A) → isEquiv (eq/ {R = _R_} a b)

  module _ (a : A) where
    -- the total space corresponding to the binary relation w.r.t. a
    Rel→TotalSpace : Type (ℓ-max ℓ ℓ')
    Rel→TotalSpace = Σ[ a' ∈ A ] (a R a')

  -- the statement that the total space is contractible at any a
  contrTotalSpace : Type (ℓ-max ℓ ℓ')
  contrTotalSpace = (a : A) → isContr (Rel→TotalSpace a)

  -- assume a reflexive binary relation
  module _ (ρ : isRefl) where
    -- identity is the least reflexive relation
    ≡→R : {a a' : A} → a ≡ a' → a R a'
    ≡→R {a} {a'} p = subst (λ z → a R z) p (ρ a)

    -- what it means for a reflexive binary relation to be univalent
    isUnivalent : Type (ℓ-max ℓ ℓ')
    isUnivalent = (a a' : A) → isEquiv (≡→R {a} {a'})

    -- helpers for contrTotalSpace→isUnivalent
    private
      module _ (a : A) where
        -- wrapper for ≡→R
        f = λ (a' : A) (p : a ≡ a') → ≡→R {a} {a'} p

        -- the corresponding total map that univalence
        -- of R will be reduced to
        totf : singl a → Σ[ a' ∈ A ] (a R a')
        totf (a' , p) = (a' , f a' p)

    -- if the total space corresponding to R is contractible
    -- then R is univalent
    -- because the singleton at a is also contractible
    contrTotalSpace→isUnivalent : contrTotalSpace → isUnivalent
    contrTotalSpace→isUnivalent c a
      = fiberEquiv (λ a' → a ≡ a')
                   (λ a' → a R a')
                   (f a)
                   (snd (isPropEquiv→Equiv (isContr→isProp (isContrSingl a))
                                           (isContr→isProp (c a))
                                           (totf a)
                                           (λ _ → fst (isContrSingl a))))

    -- converse map. proof idea:
    -- equivalences preserve contractability,
    -- singletons are contractible
    -- and by the univalence assumption the total map is an equivalence
    isUnivalent→contrTotalSpace : isUnivalent → contrTotalSpace
    isUnivalent→contrTotalSpace u a
      = isOfHLevelRespectEquiv 0
                               (totf a , totalEquiv (a ≡_)
                                                    (a R_)
                                                    (f a)
                                                    λ a' → u a a')
                               (isContrSingl a)


EquivRel : ∀ {ℓ} (A : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
EquivRel A ℓ' = Σ[ R ∈ Rel A A ℓ' ] BinaryRelation.isEquivRel R

EquivPropRel : ∀ {ℓ} (A : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
EquivPropRel A ℓ' = Σ[ R ∈ PropRel A A ℓ' ] BinaryRelation.isEquivRel (R .fst)

