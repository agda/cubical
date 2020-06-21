{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.RelationalStructures.Base where

open import Cubical.Foundations.Everything
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Relation.ZigZag.Base
open import Cubical.Relation.Binary
open import Cubical.HITs.SetQuotients

open import Cubical.Structures.Constant
open import Cubical.Structures.Pointed
open import Cubical.Structures.Parameterized
open import Cubical.Structures.NAryOp

open import Cubical.Foundations.SIP

private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level

open isBisimulation
open BinaryRelation

--------------------------------------------------------------------------------
-- Definition of standard notion of structure
--------------------------------------------------------------------------------

record SetStructure (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    struct : Type ℓ → Type ℓ'
    set : ∀ {A} → isSet A → isSet (struct A)

open SetStructure public

record StrRel (S : Type ℓ → Type ℓ')(ℓ'' : Level) : Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓ'')) ℓ') where
  field
    rel : (A B : Type ℓ) (R : Rel A B ℓ) → Rel (S A) (S B) ℓ''
    prop : ∀ {A} {B} {R} → (∀ a b → isProp (R a b)) → ∀ s t → isProp (rel A B R s t)

open StrRel public

QuoStructure : (S : Type ℓ → Type ℓ') (ρ : StrRel S ℓ'')
  (A : TypeWithStr ℓ S) (R : Rel (typ A) (typ A) ℓ)
  → Type (ℓ-max ℓ' ℓ'')
QuoStructure S ρ A R =
  Σ (S (typ A / R)) (ρ .rel (typ A) (typ A / R) (λ a b → [ a ] ≡ b) (A .snd))

isPropQuotientStructure : {S : Type ℓ → Type ℓ'} (ρ : StrRel S ℓ'')
  → Type (ℓ-max (ℓ-suc ℓ) (ℓ-max ℓ' ℓ''))
isPropQuotientStructure {ℓ = ℓ} {S = S} ρ =
  (A : TypeWithStr ℓ S) (R : typ A → typ A → Type ℓ)
  → isEquivRel R
  → isProp (QuoStructure S ρ A R)

record BisimDescends (S : Type ℓ → Type ℓ') (ρ : StrRel S ℓ'')
  (A B : TypeWithStr ℓ S) (R : Bisimulation (typ A) (typ B) ℓ) : Type (ℓ-max ℓ' ℓ'')
  where
  private
    module E = Bisim→Equiv R

  field
    quoᴸ : isContr (QuoStructure S ρ A E.Rᴸ)
    quoᴿ : isContr (QuoStructure S ρ B E.Rᴿ)
    path : PathP (λ i → S (ua E.Thm i)) (quoᴸ .fst .fst) (quoᴿ .fst .fst)

open BisimDescends public

isSNRS : (S : SetStructure ℓ ℓ') → StrRel (S .struct) ℓ'' → Type _
isSNRS {ℓ} S ρ =
  {A B : TypeWithStr ℓ (S .struct)} (R : Bisimulation (typ A) (typ B) ℓ)
  → ρ .rel (A .fst) (B .fst) (R .fst) (A .snd) (B .snd)
  → BisimDescends (S .struct) ρ A B R

--------------------------------------------------------------------------------
-- Two lemmas that get used later on
--------------------------------------------------------------------------------

private
  quoᴸ-coherence : (S : SetStructure ℓ ℓ₁) (ρ : StrRel (S .struct) ℓ₁') (θ : isSNRS S ρ)
    {X Y : Type ℓ} (R : Bisimulation X Y ℓ)
    {x₀ x₁ : S .struct X} {y₀ y₁ : S .struct Y}
    (code₀₀ : ρ .rel X Y (R .fst) x₀ y₀)
    (code₁₁ : ρ .rel X Y (R .fst) x₁ y₁)
    → ρ .rel X Y (R .fst) x₀ y₁
    → θ _ code₀₀ .quoᴸ .fst .fst ≡ θ _ code₁₁ .quoᴸ .fst .fst
  quoᴸ-coherence S ρ θ R {x₀} {x₁} {y₀} {y₁} code₀₀ code₁₁ code₀₁ =
    cong fst (θ R code₀₀ .quoᴸ .snd (θ R code₀₁ .quoᴸ .fst))
    ∙ lem
      (symP (θ R code₀₁ .path))
      (symP (θ R code₁₁ .path))
      (cong fst (θ R code₀₁ .quoᴿ .snd (θ R code₁₁ .quoᴿ .fst)))
    where
    lem : {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ a₁' : A i1}
      → PathP A a₀ a₁
      → PathP A a₀' a₁'
      → a₀ ≡ a₀'
      → a₁ ≡ a₁'
    lem {A = A} p₀ p₁ q i =
      comp A (λ k → λ {(i = i0) → p₀ k; (i = i1) → p₁ k}) (q i)

  quoᴿ-coherence : (S : SetStructure ℓ ℓ₁) (ρ : StrRel (S .struct) ℓ₁') (θ : isSNRS S ρ)
    {X Y : Type ℓ} (R : Bisimulation X Y ℓ)
    {x₀ x₁ : S .struct X} {y₀ y₁ : S .struct Y}
    (code₀₀ : ρ .rel X Y (R .fst) x₀ y₀)
    (code₁₁ : ρ .rel X Y (R .fst) x₁ y₁)
    → ρ .rel X Y (R .fst) x₁ y₀
    → θ _ code₀₀ .quoᴿ .fst .fst ≡ θ _ code₁₁ .quoᴿ .fst .fst
  quoᴿ-coherence S ρ θ R {x₀} {x₁} {y₀} {y₁} code₀₀ code₁₁ code₁₀ =
    cong fst (θ R code₀₀ .quoᴿ .snd (θ R code₁₀ .quoᴿ .fst))
    ∙ lem
      (θ R code₁₀ .path)
      (θ R code₁₁ .path)
      (cong fst (θ R code₁₀ .quoᴸ .snd (θ R code₁₁ .quoᴸ .fst)))
    where
    lem : {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ a₁' : A i1}
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

module _ (A : hSet ℓ₀) where

  constant-setStructure : SetStructure ℓ ℓ₀
  constant-setStructure .struct = constant-structure (A .fst)
  constant-setStructure .set _ = A .snd

  constant-rel : StrRel {ℓ = ℓ} (constant-setStructure .struct) ℓ₀
  constant-rel .rel _ _ _ a₀ a₁ = a₀ ≡ a₁
  constant-rel .prop _ = A .snd

  isPropQuoStructureConstant : isPropQuotientStructure {ℓ = ℓ} constant-rel
  isPropQuoStructureConstant (X , a) R e = isContr→isProp (isContrSingl _)

  isSNRSConstant : isSNRS {ℓ = ℓ} constant-setStructure constant-rel
  isSNRSConstant _ _ .quoᴸ = isContrSingl _
  isSNRSConstant _ _ .quoᴿ = isContrSingl _
  isSNRSConstant _ r .path = r

-- Variable structure

pointed-setStructure : SetStructure ℓ ℓ
pointed-setStructure .struct = pointed-structure
pointed-setStructure .set setX = setX

pointed-rel : StrRel pointed-structure ℓ
pointed-rel .rel _ _ R = R
pointed-rel .prop propR = propR

isPropQuoStructurePointed : isPropQuotientStructure {ℓ = ℓ} pointed-rel
isPropQuoStructurePointed (X , x) R e = isContr→isProp (isContrSingl _)

isSNRSPointed : isSNRS {ℓ = ℓ} pointed-setStructure pointed-rel
isSNRSPointed _ _ .quoᴸ = isContrSingl _
isSNRSPointed _ _ .quoᴿ = isContrSingl _
isSNRSPointed {A = _ , x} {_ , y} R r .path =
  ua-gluePath (Bisim→Equiv.Thm R) (eq/ (S.fwd x) y (S.zigzag (S.bwdRel y) r (S.fwdRel x)))
  where
  module S = isBisimulation (R .snd)

-- Product of structures

join-setStructure : SetStructure ℓ ℓ₁ → SetStructure ℓ ℓ₂ → SetStructure ℓ (ℓ-max ℓ₁ ℓ₂)
join-setStructure S₁ S₂ .struct X = S₁ .struct X × S₂ .struct X
join-setStructure S₁ S₂ .set setX = isSet× (S₁ .set setX) (S₂ .set setX)

join-rel :
  {S₁ : Type ℓ → Type ℓ₁} (ρ₁ : StrRel S₁ ℓ₁')
  {S₂ : Type ℓ → Type ℓ₂} (ρ₂ : StrRel S₂ ℓ₂')
  → StrRel (join-structure S₁ S₂) (ℓ-max ℓ₁' ℓ₂')
join-rel ρ₁ ρ₂ .rel X Y R (s₁ , s₂) (t₁ , t₂) =
  ρ₁ .rel X Y R s₁ t₁
  × ρ₂ .rel X Y R s₂ t₂
join-rel ρ₁ ρ₂ .prop propR (s₁ , s₂) (t₁ , t₂) =
  isProp× (ρ₁ .prop propR s₁ t₁) (ρ₂ .prop propR s₂ t₂)

isPropQuoStructureJoin :
  {S₁ : Type ℓ → Type ℓ₁} (ρ₁ : StrRel S₁ ℓ₁')
  {S₂ : Type ℓ → Type ℓ₂} (ρ₂ : StrRel S₂ ℓ₂')
  → isPropQuotientStructure ρ₁
  → isPropQuotientStructure ρ₂
  → isPropQuotientStructure (join-rel ρ₁ ρ₂)
isPropQuoStructureJoin ρ₁ ρ₂ q₁ q₂ (X , (s₁ , s₂)) R e (t , r) (t' , r') =
  equivFun ΣPath≃PathΣ
    ( equivFun ΣPath≃PathΣ
      ( cong fst (q₁ (X , s₁) R e (t .fst , r .fst) (t' .fst , r' .fst))
      , cong fst (q₂ (X , s₂) R e (t .snd , r .snd) (t' .snd , r' .snd))
      )
    , isProp→PathP (λ _ → join-rel ρ₁ ρ₂ .prop (λ _ _ → squash/ _ _) _ _) _ _
    )

isSNRSJoin :
  (S₁ : SetStructure ℓ ℓ₁) {ρ₁ : StrRel (S₁ .struct) ℓ₁'}
  (S₂ : SetStructure ℓ ℓ₂) {ρ₂ : StrRel (S₂ .struct) ℓ₂'}
  → isSNRS S₁ ρ₁ → isSNRS S₂ ρ₂
  → isSNRS (join-setStructure S₁ S₂) (join-rel ρ₁ ρ₂)
isSNRSJoin _ _ θ₁ θ₂ _ (code₁ , code₂) .quoᴸ .fst .fst =
  θ₁ _ code₁ .quoᴸ .fst .fst , θ₂ _ code₂ .quoᴸ .fst .fst
isSNRSJoin _ _ θ₁ θ₂ _ (code₁ , code₂) .quoᴸ .fst .snd =
  θ₁ _ code₁ .quoᴸ .fst .snd , θ₂ _ code₂ .quoᴸ .fst .snd
isSNRSJoin _ _ θ₁ θ₂ R (code₁ , code₂) .quoᴸ .snd (p , α) j =
  ( ( θ₁ R code₁ .quoᴸ .snd (p .fst ,  α .fst) j .fst
    , θ₂ R code₂ .quoᴸ .snd (p .snd ,  α .snd) j .fst
    )
  , ( θ₁ _ code₁ .quoᴸ .snd (p .fst , α .fst) j .snd
    , θ₂ _ code₂ .quoᴸ .snd (p .snd , α .snd) j .snd
    )
  )
isSNRSJoin _ _ θ₁ θ₂ _ (code₁ , code₂) .quoᴿ .fst .fst =
  θ₁ _ code₁ .quoᴿ .fst .fst , θ₂ _ code₂ .quoᴿ .fst .fst
isSNRSJoin _ _ θ₁ θ₂ _ (code₁ , code₂) .quoᴿ .fst .snd =
  θ₁ _ code₁ .quoᴿ .fst .snd , θ₂ _ code₂ .quoᴿ .fst .snd
isSNRSJoin _ _ θ₁ θ₂ R (code₁ , code₂) .quoᴿ .snd (p , α) j =
  ( ( θ₁ R code₁ .quoᴿ .snd (p .fst ,  α .fst) j .fst
    , θ₂ R code₂ .quoᴿ .snd (p .snd ,  α .snd) j .fst
    )
  , ( θ₁ _ code₁ .quoᴿ .snd (p .fst , α .fst) j .snd
    , θ₂ _ code₂ .quoᴿ .snd (p .snd , α .snd) j .snd
    )
  )
isSNRSJoin _ _ θ₁ θ₂ _ (code₁ , code₂) .path =
  equivFun ΣPathP≃PathPΣ (θ₁ _ code₁ .path , θ₂ _ code₂ .path)

-- Parameterized structure

module _ (A : Type ℓ₀) where

  parameterized-setStructure : (A → SetStructure ℓ ℓ₁) → SetStructure ℓ (ℓ-max ℓ₀ ℓ₁)
  parameterized-setStructure S .struct X = (a : A) → (S a .struct X)
  parameterized-setStructure S .set setX = isSetΠ λ a → S a .set setX

  parameterized-rel : {S : A → Type ℓ → Type ℓ₁} {ℓ₁' : Level}
    → (∀ a → StrRel (S a) ℓ₁')
    → StrRel (parameterized-structure A S) (ℓ-max ℓ₀ ℓ₁')
  parameterized-rel ρ .rel X Y R s t =
    (a : A) → ρ a .rel X Y R (s a) (t a)
  parameterized-rel ρ .prop propR s t =
    isPropΠ λ a → ρ a .prop propR (s a) (t a)

  isSNRSParameterized : (S : A → SetStructure ℓ ℓ₁) {ℓ₁' : Level}
    (ρ : ∀ a → StrRel (S a .struct) ℓ₁')
    → (∀ a → isSNRS (S a) (ρ a))
    → isSNRS (parameterized-setStructure S) (parameterized-rel ρ)
  isSNRSParameterized _ ρ θ _ code .quoᴸ .fst .fst a = θ a _ (code a) .quoᴸ .fst .fst
  isSNRSParameterized _ ρ θ _ code .quoᴸ .fst .snd a = θ a _ (code a) .quoᴸ .fst .snd
  isSNRSParameterized _ ρ θ R code .quoᴸ .snd (f , h) j .fst a = θ a R (code a) .quoᴸ .snd (f a , h a) j .fst
  isSNRSParameterized _ ρ θ _ code .quoᴸ .snd (f , h) j .snd a = θ a _ (code a) .quoᴸ .snd (f a , h a) j .snd
  isSNRSParameterized _ ρ θ _ code .quoᴿ .fst .fst a = θ a _ (code a) .quoᴿ .fst .fst
  isSNRSParameterized _ ρ θ _ code .quoᴿ .fst .snd a = θ a _ (code a) .quoᴿ .fst .snd
  isSNRSParameterized _ ρ θ R code .quoᴿ .snd (f , h) j .fst a = θ a R (code a) .quoᴿ .snd (f a , h a) j .fst
  isSNRSParameterized _ ρ θ _ code .quoᴿ .snd (f , h) j .snd a = θ a _ (code a) .quoᴿ .snd (f a , h a) j .snd
  isSNRSParameterized _ ρ θ R code .path = funExt λ a → θ a R (code a) .path

-- Variable assumption

unaryFun-setStructure : SetStructure ℓ ℓ₁ → SetStructure ℓ (ℓ-max ℓ ℓ₁)
unaryFun-setStructure S .struct X = X → S .struct X
unaryFun-setStructure S .set setX = isSetΠ λ _ → S .set setX

unaryFun-rel : {S : Type ℓ → Type ℓ₁} {ℓ₁' : Level}
  → StrRel S ℓ₁' → StrRel (nAryFun-structure 1 S) (ℓ-max ℓ ℓ₁')
unaryFun-rel ρ .rel X Y R f g =
  {x : X} {y : Y} → R x y → ρ .rel X Y R (f x) (g y)
unaryFun-rel ρ .prop propR f g =
  isPropImplicitΠ λ x →
  isPropImplicitΠ λ y →
  isPropΠ λ _ → ρ .prop propR (f x) (g y)

isPropQuoStructureUnaryFun : (S : SetStructure ℓ ℓ₁) (ρ : StrRel (S .struct) ℓ₁')
  → isPropQuotientStructure ρ
  → isPropQuotientStructure (unaryFun-rel ρ)
isPropQuoStructureUnaryFun S ρ q (X , f) R e (t , c) (t' , c') =
  equivFun ΣPath≃PathΣ
    ( funExt
      (elimProp
        (λ _ → S .set squash/ _ _)
        (λ x → cong fst (q (X , f x) R e (t [ x ] , c refl) (t' [ x ] , c' refl))))
    , isProp→PathP (λ _ → unaryFun-rel ρ .prop (λ _ _ → squash/ _ _) _ _) _ _
    )

isSNRSUnaryFun : (S : SetStructure ℓ ℓ₁) (ρ : StrRel (S .struct) ℓ₁')
  → isSNRS S ρ
  → isSNRS (unaryFun-setStructure S) (unaryFun-rel ρ)
isSNRSUnaryFun S ρ θ {X , f} {Y , g} (R , bis) code .quoᴸ .fst =
  f₀ , λ p → subst (λ y → ρ .rel _ _ _ _ (f₀ y)) p (θ _ _ .quoᴸ .fst .snd)
  where
  f₀ : _
  f₀ [ x ] = θ (R , bis) (code (bis .fwdRel x)) .quoᴸ .fst .fst
  f₀ (eq/ x₀ x₁ r i) =
    quoᴸ-coherence S ρ θ (R , bis)
      (code (bis .fwdRel x₀))
      (code (bis .fwdRel x₁))
      (code r)
      i
  f₀ (squash/ _ _ p q j i) =
    S .set squash/ _ _ (cong f₀ p) (cong f₀ q) j i
isSNRSUnaryFun S ρ θ (R , bis) code .quoᴸ .snd (f' , h) =
  Σ≡Prop
    (λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropΠ λ _ →
      ρ .prop (λ _ _ → squash/ _ _) _ _)
    (funExt
      (elimProp
        (λ _ → S .set squash/ _ _)
        (λ x → cong fst (θ _ _ .quoᴸ .snd (f' [ x ] , h refl)))))
isSNRSUnaryFun S ρ θ (R , bis) code .quoᴿ .fst =
  g₀ , λ p → subst (λ y → ρ .rel _ _ _ _ (g₀ y)) p (θ _ _ .quoᴿ .fst .snd)
  where
  g₀ : _
  g₀ [ y ] = θ (R , bis) (code (bis .bwdRel y)) .quoᴿ .fst .fst
  g₀ (eq/ y₀ y₁ r i) =
    quoᴿ-coherence S ρ θ (R , bis)
      (code (bis .bwdRel y₀))
      (code (bis .bwdRel y₁))
      (code r)
      i
  g₀ (squash/ _ _ p q j i) =
    S .set squash/ _ _ (cong g₀ p) (cong g₀ q) j i
isSNRSUnaryFun S ρ θ _ code .quoᴿ .snd (g' , h) =
  Σ≡Prop
    (λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropΠ λ _ →
      ρ .prop (λ _ _ → squash/ _ _) _ _)
    (funExt
      (elimProp
        (λ _ → S .set squash/ _ _)
        (λ y → cong fst (θ _ _ .quoᴿ .snd (g' [ y ] , h refl)))))
isSNRSUnaryFun S ρ θ (R , bis) code .path =
  ua→
    (elimProp
      (λ _ → isOfHLevelPathP' 1
        (λ i → S .set (subst isSet (λ j → ua E.Thm (i ∧ j)) squash/))
        _ _)
      (λ x →
        θ _ (code (bis .fwdRel x)) .path
        ▷ quoᴿ-coherence S ρ θ (R , bis) _ _ (code (bis .bwdRel (bis .fwd x)))))
  where
  module E = Bisim→Equiv (R , bis)
