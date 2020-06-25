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
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Trunc
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.ZigZag.Base

open BinaryRelation

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

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
  Σ[ s ∈ S (typ A / R) ] ρ .rel (graphRel [_]) (A .snd) s

-- A structured equivalence relation R on a structured type A should induce a structure on A/R
InducesQuotientStr : (S : Type ℓ → Type ℓ') (ρ : StrRel S ℓ'') → Type _
InducesQuotientStr {ℓ = ℓ} S ρ =
  (A : TypeWithStr ℓ S) (R : EquivPropRel (typ A) ℓ)
  → ρ .rel (R .fst .fst) (A .snd) (A .snd)
  → ∃![ s ∈ S (typ A / R .fst .fst) ] ρ .rel (graphRel [_]) (A .snd) s

-- The inverse of a structured relation should be structured
isSymmetricStrRel : {S : Type ℓ → Type ℓ'} (ρ : StrRel S ℓ'') → Type _
isSymmetricStrRel {ℓ = ℓ} {S = S} ρ =
  {X Y : Type ℓ} (R : PropRel X Y ℓ)
  {sx : S X} {sy : S Y}
  → ρ .rel (R .fst) sx sy
  → ρ .rel (invPropRel R .fst) sy sx

-- The composite of structured relations should be structured
isTransitiveStrRel : {S : Type ℓ → Type ℓ'} (ρ : StrRel S ℓ'') → Type _
isTransitiveStrRel {ℓ = ℓ} {S = S} ρ =
  {X Y Z : Type ℓ}
  (R₀ : PropRel X Y ℓ) (R₁ : PropRel Y Z ℓ)
  {sx : S X} {sy : S Y} {sz : S Z}
  → ρ .rel (R₀ .fst) sx sy
  → ρ .rel (R₁ .fst) sy sz
  → ρ .rel (compPropRel R₀ R₁ .fst) sx sz

record SuitableStrRel (S : Type ℓ → Type ℓ') (ρ : StrRel S ℓ'') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
  where
  field
    quo : InducesQuotientStr S ρ
    symmetric : isSymmetricStrRel ρ
    transitive : isTransitiveStrRel ρ

open SuitableStrRel

-- We can also ask for a notion of structured relations to agree with some notion of structured equivalences.
StrRelMatchesEquiv : {S : Type ℓ → Type ℓ'}
  → StrRel S ℓ'' → StrEquiv S ℓ''' → Type _
StrRelMatchesEquiv {S = S} ρ ι =
  (A B : TypeWithStr _ S) (e : typ A ≃ typ B) →
  ρ .rel (graphRel (e .fst)) (A .snd) (B .snd) ≃ ι A B e

-- Given a suitable notion of structured relation, if we have a structured quasi equivalence relation R
-- between structured types A and B, we get induced structures on the quotients A/(R ∙ R⁻¹) and B/(R⁻¹ ∙ R),
-- and the induced equivalence e : A/(R ∙ R⁻¹) ≃ B/(R⁻¹ ∙ R) is structured with respect to those quotient
-- structures.

quotientPropRel : ∀ {ℓ} {A : Type ℓ} (R : Rel A A ℓ) → PropRel A (A / R) ℓ
quotientPropRel R .fst a t = [ a ] ≡ t
quotientPropRel R .snd _ _ = squash/ _ _

record QERDescends (S : Type ℓ → Type ℓ') (ρ : StrRel S ℓ'')
  (A B : TypeWithStr ℓ S) (R : QuasiEquivRel (typ A) (typ B) ℓ) : Type (ℓ-max ℓ' ℓ'')
  where
  private
    module E = QER→Equiv R

  field
    quoᴸ : InducedQuotientStr S ρ A E.Rᴸ
    quoᴿ : InducedQuotientStr S ρ B E.Rᴿ
    rel : ρ .rel (graphRel (E.Thm .fst)) (quoᴸ .fst) (quoᴿ .fst)

open QERDescends
open isQuasiEquivRel

structuredQER→structuredEquiv : {S : Type ℓ → Type ℓ'} (ρ : StrRel S ℓ'')
  (θ : SuitableStrRel S ρ)
  (A B : TypeWithStr ℓ S) (R : QuasiEquivRel (typ A) (typ B) ℓ)
  → ρ .rel (R .fst .fst) (A .snd) (B .snd)
  → QERDescends S ρ A B R
structuredQER→structuredEquiv ρ θ (X , s) (Y , t) R r .quoᴸ =
  θ .quo (X , s) (QER→EquivRel R)
    (subst (λ R' → ρ .rel R' s s) correction
      (θ .transitive (R .fst) (invPropRel (R .fst)) r (θ .symmetric (R .fst) r)))
    .fst
  where
  correction : compPropRel (R .fst) (invPropRel (R .fst)) .fst ≡ QER→EquivRel R .fst .fst
  correction =
    funExt₂ λ x₀ x₁ →
      (hPropExt squash (R .fst .snd _ _)
        (Trunc.rec (R .fst .snd _ _) (λ {(y , r , r') → R .snd .zigzag r r' (R .snd .fwdRel _)}))
        (λ r → ∣ _ , r , R .snd .fwdRel _ ∣))

structuredQER→structuredEquiv ρ θ (X , s) (Y , t) R r .quoᴿ =
  θ .quo (Y , t) (QER→EquivRel (invQER R))
    (subst (λ R' → ρ .rel R' t t) correction
      (θ .transitive (invPropRel (R .fst)) (R .fst) (θ .symmetric (R .fst) r) r))
    .fst
  where
  correction : compPropRel (invPropRel (R .fst)) (R .fst) .fst ≡ QER→EquivRel (invQER R) .fst .fst
  correction =
    funExt₂ λ y₀ y₁ →
      (hPropExt squash (R .fst .snd _ _)
        (Trunc.rec (R .fst .snd _ _) (λ {(x , r , r') → R .snd .zigzag (R .snd .bwdRel _) r' r}))
        (λ r → ∣ _ , r , R .snd .bwdRel _ ∣))

structuredQER→structuredEquiv ρ θ (X , s) (Y , t) R r .rel =
  subst (λ R' → ρ .rel R' (quol .fst) (quor .fst)) correction
    (θ .transitive (compPropRel (invPropRel (quotientPropRel E.Rᴸ)) (R .fst)) (quotientPropRel E.Rᴿ)
      (θ .transitive (invPropRel (quotientPropRel E.Rᴸ)) (R .fst)
        (θ .symmetric (quotientPropRel E.Rᴸ) (quol .snd))
        r)
      (quor .snd))
  where
  module E = QER→Equiv R
  quol = structuredQER→structuredEquiv ρ θ (X , s) (Y , t) R r .quoᴸ
  quor = structuredQER→structuredEquiv ρ θ (X , s) (Y , t) R r .quoᴿ
  [R] = compPropRel (compPropRel (invPropRel (quotientPropRel E.Rᴸ)) (R .fst)) (quotientPropRel E.Rᴿ)

  correction : [R] .fst ≡ graphRel (E.Thm .fst)
  correction =
    funExt₂ λ qx qy →
      (hPropExt squash (squash/ _ _)
        (Trunc.rec (squash/ _ _)
          (λ {(y , qr , py) →
            Trunc.rec
              (squash/ _ _)
              (λ {(x , px , r) →
                cong (E.Thm .fst) (sym px)
                ∙ eq/ (R .snd .fwd x) y (R .snd .zigzag (R .snd .bwdRel y) r (R .snd .fwdRel x))
                ∙ py})
              qr}))
        (elimProp
          {B = λ qx →
            E.Thm .fst qx ≡ qy → [R] .fst qx qy}
          (λ _ → isPropΠ λ _ → squash)
          (λ x p → ∣ _ , ∣ _ , refl , R .snd .fwdRel x ∣ , p ∣)
          qx))
