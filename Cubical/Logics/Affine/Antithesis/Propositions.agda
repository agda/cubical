{-- Defines the type of antithesis propositions as in Affine Logic for Constructive Mathematics (https://arxiv.org/abs/1805.07518) --}
{-# OPTIONS --safe #-}

module Cubical.Logics.Affine.Antithesis.Propositions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Functions.Logic as Logic
open import Cubical.Reflection.RecordEquiv
open import Cubical.Relation.Binary.Order.Poset

private variable
  ℓ ℓ' : Level

record ±Prop ℓ : Type (ℓ-suc ℓ) where
  constructor make±Prop
  field
    _⁺ : hProp ℓ
    _⁻ : hProp ℓ
    is-disjoint : ⟨ _⁺ ⇒ _⁻ ⇒ Logic.⊥ ⟩

unquoteDecl ±PropIsoΣ = declareRecordIsoΣ ±PropIsoΣ (quote ±Prop)

isSet±Prop : isSet (±Prop ℓ)
isSet±Prop = isOfHLevelRetractFromIso 2 ±PropIsoΣ $ 
  isSetΣ isSetHProp λ _⁺ →
  isSetΣSndProp isSetHProp λ _⁻ → 
  isProp⟨⟩ (_⁺ ⇒ _⁻ ⇒ Logic.⊥)

open ±Prop

private variable
  P Q R S : ±Prop ℓ

record _⊢_ (P : ±Prop ℓ) (Q : ±Prop ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor make⊢
  field
    to  : ⟨ P ⁺ ⇒ Q ⁺ ⟩
    fro : ⟨ Q ⁻ ⇒ P ⁻ ⟩

unquoteDecl ⊢IsoΣ = declareRecordIsoΣ ⊢IsoΣ (quote _⊢_)

isProp⊢ : isProp (P ⊢ Q)
isProp⊢ {P = P} {Q = Q} = isOfHLevelRetractFromIso 1 ⊢IsoΣ $ isProp× (isProp→ (isProp⟨⟩ (Q ⁺))) (isProp→ (isProp⟨⟩ (P ⁻)))

open _⊢_

±PropExt : P ⊢ Q → Q ⊢ P → P ≡ Q
±PropExt P⊢Q Q⊢P = isoFunInjective ±PropIsoΣ _ _ $ curry ΣPathP (⇔toPath (P⊢Q  .to) (Q⊢P  .to)) $
  curry ΣPathP (⇔toPath (Q⊢P .fro) (P⊢Q .fro)) (isProp→PathP (λ i → isPropΠ2 λ _ _ → isProp⊥) _ _)

⊢refl : P ⊢ P
⊢refl = make⊢ (idfun _) (idfun _)

⊢trans : P ⊢ Q → Q ⊢ R → P ⊢ R
⊢trans P⊢Q Q⊢R = make⊢ (Q⊢R .to ∘ P⊢Q .to) (P⊢Q .fro ∘ Q⊢R .fro)

⊢IsPoset : IsPoset {ℓ' = ℓ} _⊢_
⊢IsPoset = isposet isSet±Prop (λ _ _ → isProp⊢) (λ _ → ⊢refl) (λ _ _ _ → ⊢trans) (λ _ _ → ±PropExt)
