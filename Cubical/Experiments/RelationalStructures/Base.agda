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
open BisimDescends
open isSNRS

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
    → θ .descends R .fst code₀₀ .quoᴸ  .fst ≡ θ .descends R .fst code₁₁ .quoᴸ .fst
  quoᴸ-coherence S ρ θ R {x₀} {x₁} {y₀} {y₁} code₀₀ code₁₁ code₀₁ =
    cong fst
      (θ .propQuo (bisim→EquivRel R)
        (θ .descends R .fst code₀₀ .quoᴸ)
        (θ .descends R .fst code₀₁ .quoᴸ))
    ∙ lem
      (symP (θ .descends R .fst code₀₁ .path))
      (symP (θ .descends R .fst code₁₁ .path))
      (cong fst
        (θ .propQuo (bisim→EquivRel (invBisim R))
          (θ .descends R .fst code₀₁ .quoᴿ)
          (θ .descends R .fst code₁₁ .quoᴿ)))
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
    → θ .descends R .fst code₀₀ .quoᴿ .fst ≡ θ .descends R .fst code₁₁ .quoᴿ .fst
  quoᴿ-coherence S ρ θ R {x₀} {x₁} {y₀} {y₁} code₀₀ code₁₁ code₁₀ =
    cong fst
      (θ .propQuo (bisim→EquivRel (invBisim R))
        (θ .descends R .fst code₀₀ .quoᴿ)
        (θ .descends R .fst code₁₀ .quoᴿ))
    ∙ lem
      (θ .descends R .fst code₁₀ .path)
      (θ .descends R .fst code₁₁ .path)
      (cong fst
        (θ .propQuo (bisim→EquivRel R)
          (θ .descends R .fst code₁₀ .quoᴸ)
          (θ .descends R .fst code₁₁ .quoᴸ)))
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

  isSNRSConstant : isSNRS {ℓ = ℓ} constant-setStructure constant-rel
  isSNRSConstant .propQuo R = isContr→isProp (isContrSingl _)
  isSNRSConstant .descends _ .fst _ .quoᴸ = (_ , refl)
  isSNRSConstant .descends _ .fst _ .quoᴿ = (_ , refl)
  isSNRSConstant .descends _ .fst r .path = r
  isSNRSConstant .descends _ .snd d = d .quoᴸ .snd ∙∙ d .path ∙∙ sym (d .quoᴿ .snd)

-- Variable structure

pointed-setStructure : SetStructure ℓ ℓ
pointed-setStructure .struct = pointed-structure
pointed-setStructure .set setX = setX

pointed-rel : StrRel pointed-structure ℓ
pointed-rel .rel _ _ R = R
pointed-rel .prop propR = propR

isSNRSPointed : isSNRS {ℓ = ℓ} pointed-setStructure pointed-rel
isSNRSPointed .propQuo _ = isContr→isProp (isContrSingl _)
isSNRSPointed .descends _ .fst _ .quoᴸ = (_ , refl)
isSNRSPointed .descends _ .fst _ .quoᴿ = (_ , refl)
isSNRSPointed .descends {A = _ , x} {_ , y} R .fst r .path =
  ua-gluePath (Bisim→Equiv.Thm R) (eq/ (S.fwd x) y (S.zigzag (S.bwdRel y) r (S.fwdRel x)))
  where
  module S = isBisimulation (R .snd)
isSNRSPointed .descends {A = _ , x} {_ , y} R .snd d =
  R .snd .zigzag
    (R .snd .fwdRel x)
    (isEquivRel→isEffective
      (λ _ _ → R .snd .prop _ _)
      (bisim→EquivRel (invBisim R) .snd)
      (R .snd .fwd x) y
      .equiv-proof
      (cong (E.Thm .fst) (d .quoᴸ .snd)
        ∙∙ ua-ungluePath E.Thm (d .path)
        ∙∙ sym (d .quoᴿ .snd))
      .fst .fst)
    (R .snd .bwdRel y)
  where
  module S = isBisimulation (R .snd)
  module E = Bisim→Equiv R

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

isSNRSJoin :
  (S₁ : SetStructure ℓ ℓ₁) {ρ₁ : StrRel (S₁ .struct) ℓ₁'}
  (S₂ : SetStructure ℓ ℓ₂) {ρ₂ : StrRel (S₂ .struct) ℓ₂'}
  → isSNRS S₁ ρ₁ → isSNRS S₂ ρ₂
  → isSNRS (join-setStructure S₁ S₂) (join-rel ρ₁ ρ₂)
isSNRSJoin _ {ρ₁} _ {ρ₂} θ₁ θ₂ .propQuo R (t , r) (t' , r') =
  equivFun ΣPath≃PathΣ
    ( equivFun ΣPath≃PathΣ
      ( cong fst (θ₁ .propQuo R (t .fst , r .fst) (t' .fst , r' .fst))
      , cong fst (θ₂ .propQuo R (t .snd , r .snd) (t' .snd , r' .snd))
      )
    , isProp→PathP (λ _ → join-rel ρ₁ ρ₂ .prop (λ _ _ → squash/ _ _) _ _) _ _
    )
isSNRSJoin _ _ θ₁ θ₂ .descends _ .fst (code₁ , code₂) .quoᴸ .fst =
  θ₁ .descends _ .fst code₁ .quoᴸ .fst , θ₂ .descends _ .fst code₂ .quoᴸ .fst
isSNRSJoin _ _ θ₁ θ₂ .descends _  .fst (code₁ , code₂) .quoᴸ .snd =
  θ₁ .descends _ .fst code₁ .quoᴸ .snd , θ₂ .descends _ .fst code₂ .quoᴸ .snd
isSNRSJoin _ _ θ₁ θ₂ .descends _ .fst (code₁ , code₂) .quoᴿ .fst =
  θ₁ .descends _ .fst code₁ .quoᴿ .fst , θ₂ .descends _ .fst code₂ .quoᴿ .fst
isSNRSJoin _ _ θ₁ θ₂ .descends _ .fst (code₁ , code₂) .quoᴿ .snd =
  θ₁ .descends _ .fst code₁ .quoᴿ .snd , θ₂ .descends _ .fst code₂ .quoᴿ .snd
isSNRSJoin _ _ θ₁ θ₂ .descends _ .fst (code₁ , code₂) .path =
  equivFun ΣPathP≃PathPΣ (θ₁ .descends _ .fst code₁ .path , θ₂ .descends _ .fst code₂ .path)
isSNRSJoin _ {ρ₁} _ {ρ₂} θ₁ θ₂ .descends {A = X , s} {B = Y , t} R .snd d =
  θ₁ .descends R .snd d₁ , θ₂ .descends R .snd d₂
  where
  d₁ : BisimDescends _ ρ₁ (X , s .fst) (Y , t .fst) R
  d₁ .quoᴸ = d .quoᴸ .fst .fst , d .quoᴸ .snd .fst
  d₁ .quoᴿ = d .quoᴿ .fst .fst , d .quoᴿ .snd .fst
  d₁ .path i = d .path i .fst

  d₂ : BisimDescends _ ρ₂ (X , s .snd) (Y , t .snd) R
  d₂ .quoᴸ = d .quoᴸ .fst .snd , d .quoᴸ .snd .snd
  d₂ .quoᴿ = d .quoᴿ .fst .snd , d .quoᴿ .snd .snd
  d₂ .path i = d .path i .snd

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
  isSNRSParameterized _ ρ θ .propQuo R f f' =
    equivFun ΣPath≃PathΣ
      ( funExt (λ a → cong fst (θ a .propQuo R (f .fst a , f .snd a) (f' .fst a , f' .snd a)))
      , isProp→PathP (λ _ → parameterized-rel ρ .prop (λ _ _ → squash/ _ _) _ _) _ _
      )
  isSNRSParameterized _ ρ θ .descends _ .fst code .quoᴸ .fst a =
    θ a .descends _ .fst (code a) .quoᴸ .fst
  isSNRSParameterized _ ρ θ .descends _ .fst code .quoᴸ .snd a =
    θ a .descends _ .fst (code a) .quoᴸ .snd
  isSNRSParameterized _ ρ θ .descends _ .fst code .quoᴿ .fst a =
    θ a .descends _ .fst (code a) .quoᴿ .fst
  isSNRSParameterized _ ρ θ .descends _ .fst code .quoᴿ .snd a =
    θ a .descends _ .fst (code a) .quoᴿ .snd
  isSNRSParameterized _ ρ θ .descends _ .fst code .path =
    funExt λ a → θ a .descends _ .fst (code a) .path
  isSNRSParameterized _ ρ θ .descends {A = X , f} {B = Y , g} R .snd d a =
    θ a .descends R .snd d'
    where
    d' : BisimDescends _ (ρ a) (X , f a) (Y , g a) R
    d' .quoᴸ = d .quoᴸ .fst a , d .quoᴸ .snd a
    d' .quoᴿ = d .quoᴿ .fst a , d .quoᴿ .snd a
    d' .path i = d .path i a

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

isSNRSUnaryFun : (S : SetStructure ℓ ℓ₁) (ρ : StrRel (S .struct) ℓ₁')
  → isSNRS S ρ
  → isSNRS (unaryFun-setStructure S) (unaryFun-rel ρ)
isSNRSUnaryFun S ρ θ .propQuo R (t , c) (t' , c') =
  equivFun ΣPath≃PathΣ
    ( funExt
      (elimProp
        (λ _ → S .set squash/ _ _)
        (λ x → cong fst (θ .propQuo R (t [ x ] , c refl) (t' [ x ] , c' refl))))
    , isProp→PathP (λ _ → unaryFun-rel ρ .prop (λ _ _ → squash/ _ _) _ _) _ _
    )
isSNRSUnaryFun S ρ θ .descends {X , f} {Y , g} (R , bis) .fst code .quoᴸ =
  f₀ , λ p → subst (λ y → ρ .rel _ _ _ _ (f₀ y)) p (θ .descends _ .fst _ .quoᴸ .snd)
  where
  f₀ : _
  f₀ [ x ] = θ .descends (R , bis) .fst (code (bis .fwdRel x)) .quoᴸ .fst
  f₀ (eq/ x₀ x₁ r i) =
    quoᴸ-coherence S ρ θ (R , bis)
      (code (bis .fwdRel x₀))
      (code (bis .fwdRel x₁))
      (code r)
      i
  f₀ (squash/ _ _ p q j i) =
    S .set squash/ _ _ (cong f₀ p) (cong f₀ q) j i
isSNRSUnaryFun S ρ θ .descends (R , bis) .fst code .quoᴿ =
  g₀ , λ p → subst (λ y → ρ .rel _ _ _ _ (g₀ y)) p (θ .descends _ .fst _ .quoᴿ .snd)
  where
  g₀ : _
  g₀ [ y ] = θ .descends (R , bis) .fst (code (bis .bwdRel y)) .quoᴿ .fst
  g₀ (eq/ y₀ y₁ r i) =
    quoᴿ-coherence S ρ θ (R , bis)
      (code (bis .bwdRel y₀))
      (code (bis .bwdRel y₁))
      (code r)
      i
  g₀ (squash/ _ _ p q j i) =
    S .set squash/ _ _ (cong g₀ p) (cong g₀ q) j i
isSNRSUnaryFun S ρ θ .descends (R , bis) .fst code .path =
  ua→
    (elimProp
      (λ _ → isOfHLevelPathP' 1
        (λ i → S .set (subst isSet (λ j → ua E.Thm (i ∧ j)) squash/))
        _ _)
      (λ x →
        θ .descends _ .fst (code (bis .fwdRel x)) .path
        ▷ quoᴿ-coherence S ρ θ (R , bis) _ _ (code (bis .bwdRel (bis .fwd x)))))
  where
  module E = Bisim→Equiv (R , bis)
isSNRSUnaryFun S ρ θ .descends {A = X , f} {B = Y , g} (R , bis) .snd d {x} {y} r =
  θ .descends (R , bis) .snd dxy
  where
  dxy : BisimDescends (S .struct) ρ (X , f x) (Y , g y) (R , bis)
  dxy .quoᴸ = d .quoᴸ .fst [ x ] , d .quoᴸ .snd refl
  dxy .quoᴿ = d .quoᴿ .fst [ y ] , d .quoᴿ .snd refl
  dxy .path =
    ua→⁻ (d .path) [ x ]
    ▷ cong (d .quoᴿ .fst) (eq/ _ _ (bis .zigzag (bis .bwdRel y) r (bis .fwdRel x)))
