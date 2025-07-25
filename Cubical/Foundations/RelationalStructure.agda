{-

Definition of what it means to be a notion of relational structure

-}
module Cubical.Foundations.RelationalStructure where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
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
open isEquivRel
open isQuasiEquivRel

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

-- A notion of structured relation for a structure S assigns a relation on S X and S Y to every relation on X
-- and Y. We require the output to be proposition-valued when the input is proposition-valued.
StrRel : (S : Type ℓ → Type ℓ') (ℓ'' : Level) → Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓ'')) ℓ')
StrRel {ℓ = ℓ} S ℓ'' = ∀ {A B} (R : Rel A B ℓ) → Rel (S A) (S B) ℓ''

-- Given a type A and relation R, a quotient structure is a structure on the set quotient A/R such that
-- the graph of [_] : A → A/R is a structured relation
InducedQuotientStr : (S : Type ℓ → Type ℓ') (ρ : StrRel S ℓ'')
  (A : TypeWithStr ℓ S) (R : Rel (typ A) (typ A) ℓ)
  → Type (ℓ-max ℓ' ℓ'')
InducedQuotientStr S ρ A R =
  Σ[ s ∈ S (typ A / R) ] ρ (graphRel [_]) (A .snd) s

-- A structured equivalence relation R on a structured type A should induce a structure on A/R
InducesQuotientStr : (S : Type ℓ → Type ℓ') (ρ : StrRel S ℓ'') → Type _
InducesQuotientStr {ℓ = ℓ} S ρ =
  (A : TypeWithStr ℓ S) (R : EquivPropRel (typ A) ℓ)
  → ρ (R .fst .fst) (A .snd) (A .snd)
  → ∃![ s ∈ S (typ A / R .fst .fst) ] ρ (graphRel [_]) (A .snd) s

-- The identity should be a structured relation
isReflexiveStrRel : {S : Type ℓ → Type ℓ'} (ρ : StrRel S ℓ'') → Type _
isReflexiveStrRel {ℓ = ℓ} {S = S} ρ =
  {X : Type ℓ} → (s : S X) → ρ (idPropRel X .fst) s s

-- The inverse of a structured relation should be structured
isSymmetricStrRel : {S : Type ℓ → Type ℓ'} (ρ : StrRel S ℓ'') → Type _
isSymmetricStrRel {ℓ = ℓ} {S = S} ρ =
  {X Y : Type ℓ} (R : PropRel X Y ℓ)
  {sx : S X} {sy : S Y}
  → ρ (R .fst) sx sy
  → ρ (invPropRel R .fst) sy sx

-- The composite of structured relations should be structured
isTransitiveStrRel : {S : Type ℓ → Type ℓ'} (ρ : StrRel S ℓ'') → Type _
isTransitiveStrRel {ℓ = ℓ} {S = S} ρ =
  {X Y Z : Type ℓ}
  (R : PropRel X Y ℓ) (R' : PropRel Y Z ℓ)
  {sx : S X} {sy : S Y} {sz : S Z}
  → ρ (R .fst) sx sy
  → ρ (R' .fst) sy sz
  → ρ (compPropRel R R' .fst) sx sz

-- The type of structures on a set should be a set
preservesSetsStr : (S : Type ℓ → Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
preservesSetsStr S = ∀ {X} → isSet X → isSet (S X)

-- The type of structures on a prop-valued relation should be a prop
preservesPropsStrRel : {S : Type ℓ → Type ℓ'} (ρ : StrRel S ℓ'') → Type _
preservesPropsStrRel {ℓ = ℓ} {S = S} ρ =
  {X Y : Type ℓ} {R : Rel X Y ℓ}
  → (∀ x y → isProp (R x y))
  → (sx : S X) (sy : S Y)
  → isProp (ρ R sx sy)

record SuitableStrRel (S : Type ℓ → Type ℓ') (ρ : StrRel S ℓ'') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
  where
  field
    quo : InducesQuotientStr S ρ
    symmetric : isSymmetricStrRel ρ
    transitive : isTransitiveStrRel ρ
    set : preservesSetsStr S
    prop : preservesPropsStrRel ρ

open SuitableStrRel public

quotientPropRel : ∀ {ℓ} {A : Type ℓ} (R : Rel A A ℓ) → PropRel A (A / R) ℓ
quotientPropRel R .fst a t = [ a ] ≡ t
quotientPropRel R .snd _ _ = squash/ _ _

-- We can also ask for a notion of structured relations to agree with some notion of structured equivalences.

StrRelMatchesEquiv : {S : Type ℓ → Type ℓ'}
  → StrRel S ℓ'' → StrEquiv S ℓ''' → Type _
StrRelMatchesEquiv {S = S} ρ ι =
  (A B : TypeWithStr _ S) (e : typ A ≃ typ B) →
  ρ (graphRel (e .fst)) (A .snd) (B .snd) ≃ ι A B e

-- Additional conditions for a "positive" notion of structured relation

isDetransitiveStrRel : {S : Type ℓ → Type ℓ'} (ρ : StrRel S ℓ'') → Type _
isDetransitiveStrRel {ℓ = ℓ} {S = S} ρ =
  {X Y Z : Type ℓ}
  (R : PropRel X Y ℓ) (R' : PropRel Y Z ℓ)
  {sx : S X} {sz : S Z}
  → ρ (compPropRel R R' .fst) sx sz
  → ∃[ sy ∈ S Y ] ρ (R .fst) sx sy × ρ (R' .fst) sy sz

record StrRelAction {S : Type ℓ → Type ℓ'} (ρ : StrRel S ℓ'')
  : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max ℓ' ℓ''))
  where
  field
    actStr : ∀ {X Y} → (X → Y) → S X → S Y
    actStrId : ∀ {X} (s : S X) → actStr (idfun X) s ≡ s
    actRel : ∀ {X₀ Y₀ X₁ Y₁} {f : X₀ → X₁} {g : Y₀ → Y₁}
      {R₀ : X₀ → Y₀ → Type ℓ} {R₁ : X₁ → Y₁ → Type ℓ}
      → (∀ x y → R₀ x y → R₁ (f x) (g y))
      → ∀ sx sy → ρ R₀ sx sy → ρ R₁ (actStr f sx) (actStr g sy)

open StrRelAction public

strRelQuotientComparison : {S : Type ℓ → Type ℓ'} {ρ : StrRel S ℓ''}
  (θ : SuitableStrRel S ρ) (α : StrRelAction ρ)
  {X : Type ℓ} (R : EquivPropRel X ℓ)
  → (S X / ρ (R .fst .fst)) → S (X / R .fst .fst)
strRelQuotientComparison θ α R [ s ] = α .actStr [_] s
strRelQuotientComparison {ρ = ρ} θ α R (eq/ s t r i) =
  (sym leftEq ∙ rightEq) i
  where
  ρs : ρ (R .fst .fst) s s
  ρs =
    subst (λ R' → ρ R' s s)
      (funExt₂ λ x x' →
        hPropExt squash₁ (R .fst .snd x x')
          (Trunc.rec (R .fst .snd x x')
            (λ {(_ , r , r') → R .snd .transitive _ _ _ r (R .snd .symmetric _ _ r')}))
          (λ r → ∣ x' , r , R .snd .reflexive x' ∣₁))
      (θ .transitive (R .fst) (invPropRel (R .fst)) r (θ .symmetric (R .fst) r))

  leftEq : θ .quo (_ , s) R ρs .fst .fst ≡ α .actStr [_] s
  leftEq =
    cong fst
      (θ .quo (_ , s) R ρs .snd
        ( α .actStr [_] s
        , subst
          (λ s' → ρ (graphRel [_]) s' (α .actStr [_] s))
          (α .actStrId s)
          (α .actRel eq/ s s ρs)
        ))

  rightEq : θ .quo (_ , s) R ρs .fst .fst ≡ α .actStr [_] t
  rightEq =
    cong fst
      (θ .quo (_ , s) R ρs .snd
        ( α .actStr [_] t
        , subst
          (λ s' → ρ (graphRel [_]) s' (α .actStr [_] t))
          (α .actStrId s)
          (α .actRel eq/ s t r)
        ))
strRelQuotientComparison θ α R (squash/ _ _ p q i j) =
  θ .set squash/ _ _
    (cong (strRelQuotientComparison θ α R) p)
    (cong (strRelQuotientComparison θ α R) q)
    i j

record PositiveStrRel {S : Type ℓ → Type ℓ'} {ρ : StrRel S ℓ''} (θ : SuitableStrRel S ρ)
  : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max ℓ' ℓ''))
  where
  field
    act : StrRelAction ρ
    reflexive : isReflexiveStrRel ρ
    detransitive : isDetransitiveStrRel ρ
    quo : {X : Type ℓ} (R : EquivPropRel X ℓ) → isEquiv (strRelQuotientComparison θ act R)

open PositiveStrRel public

posRelReflexive : {S : Type ℓ → Type ℓ'} {ρ : StrRel S ℓ''} {θ : SuitableStrRel S ρ}
  → PositiveStrRel θ
  → {X : Type ℓ} (R : EquivPropRel X ℓ)
  → (s : S X) → ρ (R .fst .fst) s s
posRelReflexive {ρ = ρ} σ R s =
  subst
    (uncurry (ρ (R .fst .fst)))
    (ΣPathP (σ .act .actStrId s , σ .act .actStrId s))
    (σ .act .actRel
      (λ x y →
        Trunc.rec (R .fst .snd _ _)
          (λ p → subst (R .fst .fst x) p (R .snd .reflexive x)))
      s s
      (σ .reflexive s))

-- Given a suitable notion of structured relation, if we have a structured quasi equivalence relation R
-- between structured types A and B, we get induced structures on the quotients A/(R ∙ R⁻¹) and B/(R⁻¹ ∙ R),
-- and the induced equivalence e : A/(R ∙ R⁻¹) ≃ B/(R⁻¹ ∙ R) is structured with respect to those quotient
-- structures.

record QERDescends (S : Type ℓ → Type ℓ') (ρ : StrRel S ℓ'')
  (A B : TypeWithStr ℓ S) (R : QuasiEquivRel (typ A) (typ B) ℓ) : Type (ℓ-max ℓ' ℓ'')
  where
  private
    module E = QER→Equiv R

  field
    quoᴸ : InducedQuotientStr S ρ A E.Rᴸ
    quoᴿ : InducedQuotientStr S ρ B E.Rᴿ
    rel : ρ (graphRel (E.Thm .fst)) (quoᴸ .fst) (quoᴿ .fst)

open QERDescends

structuredQER→structuredEquiv : {S : Type ℓ → Type ℓ'} {ρ : StrRel S ℓ''}
  (θ : SuitableStrRel S ρ)
  (A B : TypeWithStr ℓ S) (R : QuasiEquivRel (typ A) (typ B) ℓ)
  → ρ (R .fst .fst) (A .snd) (B .snd)
  → QERDescends S ρ A B R
structuredQER→structuredEquiv {ρ = ρ} θ (X , s) (Y , t) R r .quoᴸ =
  θ .quo (X , s) (QER→EquivRel R)
    (θ .transitive (R .fst) (invPropRel (R .fst)) r (θ .symmetric (R .fst) r))
    .fst

structuredQER→structuredEquiv {ρ = ρ} θ (X , s) (Y , t) R r .quoᴿ =
  θ .quo (Y , t) (QER→EquivRel (invQER R))
    (θ .transitive (invPropRel (R .fst)) (R .fst) (θ .symmetric (R .fst) r) r)
    .fst

structuredQER→structuredEquiv {ρ = ρ} θ (X , s) (Y , t) R r .rel =
  subst (λ R' → ρ R' (quol .fst) (quor .fst)) correction
    (θ .transitive (compPropRel (invPropRel (quotientPropRel E.Rᴸ)) (R .fst)) (quotientPropRel E.Rᴿ)
      (θ .transitive (invPropRel (quotientPropRel E.Rᴸ)) (R .fst)
        (θ .symmetric (quotientPropRel E.Rᴸ) (quol .snd))
        r)
      (quor .snd))
  where
  module E = QER→Equiv R
  quol = structuredQER→structuredEquiv {ρ = ρ} θ (X , s) (Y , t) R r .quoᴸ
  quor = structuredQER→structuredEquiv {ρ = ρ} θ (X , s) (Y , t) R r .quoᴿ
  [R] = compPropRel (compPropRel (invPropRel (quotientPropRel E.Rᴸ)) (R .fst)) (quotientPropRel E.Rᴿ)

  correction : [R] .fst ≡ graphRel (E.Thm .fst)
  correction =
    funExt₂ λ qx qy →
      (hPropExt squash₁ (squash/ _ _)
        (Trunc.rec (squash/ _ _)
          (λ {(y , qr , py) →
            Trunc.rec
              (squash/ _ _)
              (λ {(x , px , r) →
                (cong (E.Thm .fst) (sym px)
                ∙ E.relToFwd≡ r)
                ∙ py})
              qr}))
        (elimProp {P = λ qx → E.Thm .fst qx ≡ qy → [R] .fst qx qy}
          (λ _ → isPropΠ λ _ → squash₁)
          (λ x →
            elimProp {P = λ qy → E.Thm .fst [ x ] ≡ qy → [R] .fst [ x ] qy}
              (λ _ → isPropΠ λ _ → squash₁)
              (λ y p → ∣ _ , ∣ _ , refl , E.fwd≡ToRel p ∣₁ , refl ∣₁)
              qy)
          qx))
