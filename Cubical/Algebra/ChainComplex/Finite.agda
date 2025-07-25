{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.ChainComplex.Finite where

{- When dealing with chain maps and chain homotopies constructively,
it is often the case the case that one only is able to obtain a finite
approximation rather than the full thing. This file contains
definitions of
(1) finite chain maps,
(2) finite chain homotopies
(3) finite chain equivalences
and proof their induced behaviour on homology
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Fin.Inductive.Base

open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ where
  record finChainComplexMap {ℓ ℓ' : Level} (m : ℕ)
   (A : ChainComplex ℓ) (B : ChainComplex ℓ') : Type (ℓ-max ℓ ℓ') where
    open ChainComplex
    field
      fchainmap : (i : Fin (suc m))
        → AbGroupHom (chain A (fst i)) (chain B (fst i))
      fbdrycomm : (i : Fin m)
        → compGroupHom (fchainmap (fsuc i)) (bdry B (fst i))
         ≡ compGroupHom (bdry A (fst i)) (fchainmap (injectSuc i))

  record finChainHomotopy {ℓ : Level} (m : ℕ)
    {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
    (f g : finChainComplexMap m A B) : Type (ℓ-max ℓ' ℓ) where
    open ChainComplex
    open finChainComplexMap
    field
      fhtpy : (i : Fin (suc m))
        → AbGroupHom (chain A (fst i)) (chain B (suc (fst i)))
      fbdryhtpy : (i : Fin m)
        → subtrGroupHom (chain A (suc (fst i))) (chain B (suc (fst i)))
                         (fchainmap f (fsuc i)) (fchainmap g (fsuc i))
         ≡ addGroupHom (chain A (suc (fst i))) (chain B (suc (fst i)))
             (compGroupHom (fhtpy (fsuc i)) (bdry B (suc (fst i))))
             (compGroupHom (bdry A (fst i)) (fhtpy (injectSuc i)))

  open finChainComplexMap
  finChainComplexMap≡ :
    {A : ChainComplex ℓ} {B : ChainComplex ℓ'} {m : ℕ}
    {f g : finChainComplexMap m A B}
    → ((i : Fin (suc m)) → fchainmap f i ≡ fchainmap g i)
    → f ≡ g
  fchainmap (finChainComplexMap≡ p i) n = p n i
  fbdrycomm (finChainComplexMap≡ {A = A} {B = B} {f = f} {g = g} p i) n =
    isProp→PathP {B = λ i
      → compGroupHom (p (fsuc n) i) (ChainComplex.bdry B (fst n))
       ≡ compGroupHom (ChainComplex.bdry A (fst n)) (p (injectSuc n) i)}
     (λ i → isSetGroupHom _ _)
     (fbdrycomm f n) (fbdrycomm g n) i

  compFinChainMap :
    {A : ChainComplex ℓ} {B : ChainComplex ℓ'} {C : ChainComplex ℓ''} {m : ℕ}
    → (f : finChainComplexMap m A B) (g : finChainComplexMap m B C)
    → finChainComplexMap m A C
  compFinChainMap {A = A} {B} {C} {m = m} ϕ' ψ' = main
    where
    ϕ = fchainmap ϕ'
    commϕ = fbdrycomm ϕ'
    ψ = fchainmap ψ'
    commψ = fbdrycomm ψ'

    main : finChainComplexMap m A C
    fchainmap main n = compGroupHom (ϕ n) (ψ n)
    fbdrycomm main n =
      Σ≡Prop (λ _ → isPropIsGroupHom _ _)
             (funExt λ x
             → (funExt⁻ (cong fst (commψ n)) (ϕ (fsuc n) .fst x))
              ∙ cong (fst (ψ (injectSuc n))) (funExt⁻ (cong fst (commϕ n)) x))

  isFinChainEquiv : {A : ChainComplex ℓ} {B : ChainComplex ℓ'} {m : ℕ}
    → finChainComplexMap m A B  → Type (ℓ-max ℓ ℓ')
  isFinChainEquiv {m = m} f = ((n : Fin (suc m)) → isEquiv (fchainmap f n .fst))

  _≃⟨_⟩Chain_ : (A : ChainComplex ℓ) (m : ℕ) (B : ChainComplex ℓ')
    → Type (ℓ-max ℓ ℓ')
  A ≃⟨ m ⟩Chain B = Σ[ f ∈ finChainComplexMap m A B ] (isFinChainEquiv f)

  idFinChainMap : (m : ℕ) (A : ChainComplex ℓ) → finChainComplexMap m A A
  fchainmap (idFinChainMap m A) _ = idGroupHom
  fbdrycomm (idFinChainMap m A) _ =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _) refl

  invFinChainMap : {A : ChainComplex ℓ} {B : ChainComplex ℓ'} {m : ℕ}
    → (A ≃⟨ m ⟩Chain B) → finChainComplexMap m B A
  fchainmap (invFinChainMap {m = m} (ϕ , eq)) n =
    GroupEquiv→GroupHom
      (invGroupEquiv ((fchainmap ϕ n .fst , eq n) , snd (fchainmap ϕ n)))
  fbdrycomm (invFinChainMap {B = B} {m = m} (ϕ' , eq)) n =
      Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt λ x
        → sym (retEq (_ , eq (injectSuc n) ) _)
        ∙∙ cong (invEq (_ , eq (injectSuc n) ))
                (sym (funExt⁻ (cong fst (ϕcomm n)) (invEq (_ , eq (fsuc n)) x)))
        ∙∙ cong (invEq (ϕ (injectSuc n)  .fst , eq (injectSuc n) )
                ∘ fst (ChainComplex.bdry B (fst n)))
                (secEq (_ , eq (fsuc n)) x))
    where
    ϕ = fchainmap ϕ'
    ϕcomm = fbdrycomm ϕ'

  invFinChainEquiv : {A : ChainComplex ℓ} {B : ChainComplex ℓ'} {m : ℕ}
    → A ≃⟨ m ⟩Chain B → B ≃⟨ m ⟩Chain A
  fst (invFinChainEquiv e) = invFinChainMap e
  snd (invFinChainEquiv e) n = snd (invEquiv (fchainmap (fst e) n .fst , snd e n))
