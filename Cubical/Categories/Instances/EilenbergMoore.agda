{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Instances.EilenbergMoore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Univalence

open import Cubical.Categories.Category
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Adjoint

private
  variable
    ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} (monadM : Monad C) where

  private
    M : Functor C C
    M = fst monadM

  --open Category
  private
    module C = Category C
  open Functor
  open NatTrans

  open IsMonad (snd monadM)

  record IsEMAlgebra (algA : Algebra M) : Type ℓC' where
    constructor proveEMAlgebra
    open Algebra algA
    field
      str-η : str C.∘ N-ob η carrier ≡ C.id
      str-μ : str C.∘ N-ob μ carrier ≡ str C.∘ F-hom M str

  open IsEMAlgebra

  isPropIsEMAlgebra : ∀ {algA} → isProp (IsEMAlgebra algA)
  isPropIsEMAlgebra {algA} isalg isalg' = cong₂ proveEMAlgebra
    (C.isSetHom _ _ (str-η isalg) (str-η isalg'))
    (C.isSetHom _ _ (str-μ isalg) (str-μ isalg'))

  EMAlgebra : Type (ℓ-max ℓC ℓC')
  EMAlgebra = Σ[ algA ∈ Algebra M ] IsEMAlgebra algA

  EMCategory : Category (ℓ-max (ℓ-max ℓC ℓC') ℓC') ℓC'
    -- cannot simplify level: --lossy-unification won't allow it.
  EMCategory = FullSubcategory (AlgebrasCategory M) IsEMAlgebra

  ForgetEM : Functor EMCategory (AlgebrasCategory M)
  ForgetEM = FullInclusion (AlgebrasCategory M) IsEMAlgebra

  ForgetEMAlgebra : Functor EMCategory C
  ForgetEMAlgebra = funcComp (ForgetAlgebra M) ForgetEM

  open Algebra
  freeEMAlgebra : C.ob → EMAlgebra
  carrier (fst (freeEMAlgebra x)) = F-ob M x
  str (fst (freeEMAlgebra x)) = N-ob μ x
  str-η (snd (freeEMAlgebra x)) = lemma
    where lemma : N-ob η (F-ob M x) C.⋆ N-ob μ x ≡ C.id
          lemma = funExt⁻ (congP (λ i → N-ob) idl-μ) x
  str-μ (snd (freeEMAlgebra x)) = lemma
    where lemma : N-ob μ (F-ob M x) C.⋆ N-ob μ x ≡ F-hom M (N-ob μ x) C.⋆ N-ob μ x
          lemma = funExt⁻ (congP (λ i → N-ob) (symP-fromGoal assoc-μ)) x

  open AlgebraHom
  FreeEMAlgebra : Functor C EMCategory
  F-ob FreeEMAlgebra x = freeEMAlgebra x
  carrierHom (F-hom FreeEMAlgebra {x} {y} φ) = F-hom M φ
  strHom (F-hom FreeEMAlgebra {x} {y} φ) = sym (N-hom μ φ)
  F-id FreeEMAlgebra = AlgebraHom≡ M (F-id M)
  F-seq FreeEMAlgebra {x} {y} {z} φ ψ = AlgebraHom≡ M (F-seq M φ ψ)

  ForgetFreeEMAlgebra : funcComp ForgetEMAlgebra FreeEMAlgebra ≡ M
  ForgetFreeEMAlgebra = Functor≡ (λ x → refl) (λ f → refl)

  emCounit : NatTrans (funcComp FreeEMAlgebra ForgetEMAlgebra) (funcId EMCategory)
  carrierHom (N-ob emCounit (algebra A α , isEMA)) = α
  strHom (N-ob emCounit (algebra A α , isEMA)) = str-μ isEMA
  N-hom emCounit {algebra A α , isEMA} {algebra B β , isEMB} (algebraHom f isalgF) =
    AlgebraHom≡ M (sym (isalgF))

  open NaturalBijection
  open _⊣_
  open _≅_

  emBijection : ∀ a emB →
    (EMCategory [ FreeEMAlgebra ⟅ a ⟆ , emB ]) ≅ (C [ a , ForgetEMAlgebra ⟅ emB ⟆ ])
  fun (emBijection a (algebra b β , isEMB)) (algebraHom f isalgF) = f C.∘ N-ob η a
  carrierHom (inv (emBijection a (algebra b β , isEMB)) f) = β C.∘ F-hom M f
  strHom (inv (emBijection a (algebra b β , isEMB)) f) =
    (N-ob μ a C.⋆ (F-hom M f C.⋆ β))
      ≡⟨ sym (C.⋆Assoc _ _ _) ⟩
    ((N-ob μ a C.⋆ F-hom M f) C.⋆ β)
      ≡⟨ cong (C._⋆ β) (sym (N-hom μ f)) ⟩
    ((F-hom M (F-hom M f) C.⋆ N-ob μ b) C.⋆ β)
      ≡⟨ C.⋆Assoc _ _ _ ⟩
    (F-hom M (F-hom M f) C.⋆ (N-ob μ b C.⋆ β))
      ≡⟨ cong (F-hom M (F-hom M f) C.⋆_) (str-μ isEMB) ⟩
    (F-hom M (F-hom M f) C.⋆ (F-hom M β C.⋆ β))
      ≡⟨ sym (C.⋆Assoc _ _ _) ⟩
    ((F-hom M (F-hom M f) C.⋆ F-hom M β) C.⋆ β)
      ≡⟨ cong (C._⋆ β) (sym (F-seq M _ _)) ⟩
    (F-hom M (F-hom M f C.⋆ β) C.⋆ β) ∎
  rightInv (emBijection a (algebra b β , isEMB)) f =
    (N-ob η a C.⋆ (F-hom M f C.⋆ β))
      ≡⟨ sym (C.⋆Assoc _ _ _) ⟩
    ((N-ob η a C.⋆ F-hom M f) C.⋆ β)
      ≡⟨ cong (C._⋆ β) (sym (N-hom η f)) ⟩
    ((f C.⋆ N-ob η b) C.⋆ β)
      ≡⟨ C.⋆Assoc _ _ _ ⟩
    (f C.⋆ (N-ob η b C.⋆ β))
      ≡⟨ cong (f C.⋆_) (str-η isEMB) ⟩
    (f C.⋆ C.id)
      ≡⟨ C.⋆IdR _ ⟩
    f ∎
  leftInv (emBijection a (algebra b β , isEMB)) (algebraHom f isalgF) = AlgebraHom≡ M (
    (F-hom M (N-ob η a C.⋆ f) C.⋆ β)
      ≡⟨ cong (C._⋆ β) (F-seq M _ _) ⟩
    ((F-hom M (N-ob η a) C.⋆ F-hom M f) C.⋆ β)
      ≡⟨ C.⋆Assoc _ _ _ ⟩
    (F-hom M (N-ob η a) C.⋆ (F-hom M f C.⋆ β))
      ≡⟨ cong (F-hom M (N-ob η a) C.⋆_) (sym isalgF) ⟩
    (F-hom M (N-ob η a) C.⋆ (N-ob μ a C.⋆ f))
      ≡⟨ sym (C.⋆Assoc _ _ _) ⟩
    ((F-hom M (N-ob η a) C.⋆ N-ob μ a) C.⋆ f)
      ≡⟨ cong (C._⋆ f) (funExt⁻ (congP (λ i → N-ob) idr-μ) a) ⟩
    (C.id C.⋆ f)
      ≡⟨ C.⋆IdL f ⟩
    f ∎
    )

  emAdjunction : FreeEMAlgebra ⊣ ForgetEMAlgebra
  adjIso emAdjunction {a} {algebra b β , isEMB} = emBijection a (algebra b β , isEMB)
  adjNatInD emAdjunction {a} {algebra b β , isEMB} {algebra c γ , isEMC}
    (algebraHom f isalgF) (algebraHom g isalgG) =
    sym (C.⋆Assoc _ _ _)
  adjNatInC emAdjunction {a} {b} {algebra c γ , isEMC} f g = AlgebraHom≡ M (
    (F-hom M (g C.⋆ f) C.⋆ γ)
      ≡⟨ cong (C._⋆ γ) (F-seq M _ _) ⟩
    ((F-hom M g C.⋆ F-hom M f) C.⋆ γ)
      ≡⟨ C.⋆Assoc _ _ _ ⟩
    (F-hom M g C.⋆ (F-hom M f C.⋆ γ)) ∎
    )

module _ {C : Category ℓC ℓC'} {monadM monadN : Monad C} (monadν : MonadHom monadM monadN) where

  open Category C
  open Functor
  open IsEMAlgebra
  open NatTrans

  private
    M N : Functor C C
    M = fst monadM
    N = fst monadN
    module M = IsMonad (snd monadM)
    module N = IsMonad (snd monadN)
    ν : NatTrans M N
    ν = fst monadν
    module ν = IsMonadHom (snd monadν)

  mapIsEMAlgebra : (algA : Algebra N) → IsEMAlgebra monadN algA → IsEMAlgebra monadM (F-ob (AlgebrasFunctor ν) algA)
  str-η (mapIsEMAlgebra (algebra a αN) isEMA) =
    N-ob M.η a ⋆ (N-ob ν a ⋆ αN)
      ≡⟨ sym (⋆Assoc _ _ _) ⟩
    (N-ob M.η a ⋆ N-ob ν a) ⋆ αN
      ≡⟨ cong (_⋆ αN) (cong (λ θ → N-ob θ a) ν.N-η) ⟩
    N-ob N.η a ⋆ αN
      ≡⟨ isEMA .str-η ⟩
    id ∎
  str-μ (mapIsEMAlgebra (algebra a αN) isEMA) =
    N-ob M.μ a ⋆ (N-ob ν a ⋆ αN)
      ≡⟨ sym (⋆Assoc _ _ _) ⟩
    (N-ob M.μ a ⋆ N-ob ν a) ⋆ αN
      ≡⟨ cong (_⋆ αN) (cong (λ θ → N-ob θ a) ν.N-μ) ⟩
    ((F-hom M (N-ob ν a) ⋆ N-ob ν (F-ob N a)) ⋆ N-ob N.μ a) ⋆ αN
      ≡⟨ ⋆Assoc _ _ _ ⟩
    (F-hom M (N-ob ν a) ⋆ N-ob ν (F-ob N a)) ⋆ (N-ob N.μ a ⋆ αN)
      ≡⟨ cong ((F-hom M (N-ob ν a) ⋆ N-ob ν (F-ob N a)) ⋆_) (isEMA .str-μ) ⟩
    (F-hom M (N-ob ν a) ⋆ N-ob ν (F-ob N a)) ⋆ (F-hom N αN ⋆ αN)
      ≡⟨ sym (⋆Assoc _ _ _) ⟩
    ((F-hom M (N-ob ν a) ⋆ N-ob ν (F-ob N a)) ⋆ F-hom N αN) ⋆ αN
      ≡⟨ cong (_⋆ αN) (⋆Assoc _ _ _) ⟩
    (F-hom M (N-ob ν a) ⋆ (N-ob ν (F-ob N a) ⋆ F-hom N αN)) ⋆ αN
      ≡⟨ cong (_⋆ αN) (cong (F-hom M (N-ob ν a) ⋆_) (sym (N-hom ν αN))) ⟩
    (F-hom M (N-ob ν a) ⋆ (F-hom M αN ⋆ N-ob ν a)) ⋆ αN
      ≡⟨ cong (_⋆ αN) (sym (⋆Assoc _ _ _)) ⟩
    ((F-hom M (N-ob ν a) ⋆ F-hom M αN) ⋆ N-ob ν a) ⋆ αN
      ≡⟨ cong (_⋆ αN) (cong (_⋆ N-ob ν a) (sym (F-seq M _ _))) ⟩
    (F-hom M (N-ob ν a ⋆ αN) ⋆ N-ob ν a) ⋆ αN
      ≡⟨ ⋆Assoc _ _ _ ⟩
    F-hom M (N-ob ν a ⋆ αN) ⋆ (N-ob ν a ⋆ αN) ∎

  EMFunctor : Functor (EMCategory monadN) (EMCategory monadM)
  EMFunctor = MapFullSubcategory
    (AlgebrasCategory N) (IsEMAlgebra monadN)
    (AlgebrasCategory M) (IsEMAlgebra monadM)
    (AlgebrasFunctor ν) mapIsEMAlgebra
