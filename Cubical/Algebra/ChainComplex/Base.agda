{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.ChainComplex.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup

private
  variable
    ℓ ℓ' ℓ'' : Level

record ChainComplex (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    chain   : (i : ℕ) → AbGroup ℓ
    bdry    : (i : ℕ) → AbGroupHom (chain (suc i)) (chain i)
    bdry²=0 : (i : ℕ) → compGroupHom (bdry (suc i)) (bdry i) ≡ trivGroupHom

record ChainComplexMap {ℓ ℓ' : Level}
 (A : ChainComplex ℓ) (B : ChainComplex ℓ') : Type (ℓ-max ℓ ℓ') where
  open ChainComplex
  field
    chainmap : (i : ℕ) → AbGroupHom (chain A i) (chain B i)
    bdrycomm : (i : ℕ)
      → compGroupHom (chainmap (suc i)) (bdry B i) ≡ compGroupHom (bdry A i) (chainmap i)

record ChainHomotopy {ℓ : Level} {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
  (f g : ChainComplexMap A B) : Type (ℓ-max ℓ' ℓ) where
  open ChainComplex
  open ChainComplexMap
  field
    htpy : (i : ℕ) → AbGroupHom (chain A i) (chain B (suc i))
    bdryhtpy : (i : ℕ)
      → subtrGroupHom (chain A (suc i)) (chain B (suc i))
                       (chainmap f (suc i)) (chainmap g (suc i))
       ≡ addGroupHom (chain A (suc i)) (chain B (suc i))
           (compGroupHom (htpy (suc i)) (bdry B (suc i)))
           (compGroupHom (bdry A i) (htpy i))

record CoChainComplex (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    cochain   : (i : ℕ) → AbGroup ℓ
    cobdry    : (i : ℕ) → AbGroupHom (cochain i) (cochain (suc i))
    cobdry²=0 : (i : ℕ) → compGroupHom (cobdry i) (cobdry (suc i))
                             ≡ trivGroupHom

open ChainComplexMap
ChainComplexMap≡ : {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
  {f g : ChainComplexMap A B}
  → ((i : ℕ) → chainmap f i ≡ chainmap g i)
  → f ≡ g
chainmap (ChainComplexMap≡ p i) n = p n i
bdrycomm (ChainComplexMap≡ {A = A} {B = B} {f = f} {g = g} p i) n =
  isProp→PathP {B = λ i → compGroupHom (p (suc n) i) (ChainComplex.bdry B n)
                          ≡ compGroupHom (ChainComplex.bdry A n) (p n i)}
      (λ i → isSetGroupHom _ _)
      (bdrycomm f n) (bdrycomm g n) i

compChainMap : {A : ChainComplex ℓ} {B : ChainComplex ℓ'} {C : ChainComplex ℓ''}
  → (f : ChainComplexMap A B) (g : ChainComplexMap B C)
  → ChainComplexMap A C
compChainMap {A = A} {B} {C} ϕ' ψ' = main
  where
  ϕ = chainmap ϕ'
  commϕ = bdrycomm ϕ'
  ψ = chainmap ψ'
  commψ = bdrycomm ψ'

  main : ChainComplexMap A C
  chainmap main n = compGroupHom (ϕ n) (ψ n)
  bdrycomm main n =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
           (funExt λ x
           → (funExt⁻ (cong fst (commψ n)) (ϕ (suc n) .fst x))
            ∙ cong (fst (ψ n)) (funExt⁻ (cong fst (commϕ n)) x))

isChainEquiv : {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
  → ChainComplexMap A B  → Type (ℓ-max ℓ ℓ')
isChainEquiv f = ((n : ℕ) → isEquiv (chainmap f n .fst))

_≃Chain_ : (A : ChainComplex ℓ) (B : ChainComplex ℓ') → Type (ℓ-max ℓ ℓ')
A ≃Chain B = Σ[ f ∈ ChainComplexMap A B ] (isChainEquiv f)

idChainMap : (A : ChainComplex ℓ) → ChainComplexMap A A
chainmap (idChainMap A) _ = idGroupHom
bdrycomm (idChainMap A) _ =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _) refl

invChainMap : {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
  → (A ≃Chain B) → ChainComplexMap B A
chainmap (invChainMap (ϕ , eq)) n =
  GroupEquiv→GroupHom (invGroupEquiv ((chainmap ϕ n .fst , eq n) , snd (chainmap ϕ n)))
bdrycomm (invChainMap {B = B} (ϕ' , eq)) n =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt λ x
      → sym (retEq (_ , eq n ) _)
      ∙∙ cong (invEq (_ , eq n ))
              (sym (funExt⁻ (cong fst (ϕcomm n)) (invEq (_ , eq (suc n)) x)))
      ∙∙ cong (invEq (ϕ n  .fst , eq n ) ∘ fst (ChainComplex.bdry B n))
              (secEq (_ , eq (suc n)) x))
  where
  ϕ = chainmap ϕ'
  ϕcomm = bdrycomm ϕ'

invChainEquiv : {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
  → A ≃Chain B → B ≃Chain A
fst (invChainEquiv e) = invChainMap e
snd (invChainEquiv e) n = snd (invEquiv (chainmap (fst e) n .fst , snd e n))
