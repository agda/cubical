{-# OPTIONS --safe #-}
module Cubical.Categories.Monad.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} (M : Functor C C) where
  open Category C
  open Functor
  open NatTrans

  IsPointed : Type (ℓ-max ℓ ℓ')
  IsPointed = NatTrans (funcId C) M

  record IsMonad : Type (ℓ-max ℓ ℓ') where
    field
      η : IsPointed
      μ : NatTrans (funcComp M M) M
      idl-μ : PathP (λ i → NatTrans (F-rUnit {F = M} i) M) (compTrans μ (η ∘ˡ M)) (idTrans M)
      idr-μ : PathP (λ i → NatTrans (F-lUnit {F = M} i) M) (compTrans μ (M ∘ʳ η)) (idTrans M)
      assoc-μ : PathP (λ i → NatTrans (F-assoc {F = M} {G = M} {H = M} i) M)
        (compTrans μ (M ∘ʳ μ))
        (compTrans μ (μ ∘ˡ M))

    -- bind : Hom[-,M-] -> Hom[M-,M-]
    bind : NatTrans (funcComp (HomFunctor C) ((funcId C ^opF) ×F M)) (funcComp (HomFunctor C) ((M ^opF) ×F M))
    N-ob bind (x , y) f = N-ob μ y ∘ F-hom M f
    N-hom bind {x , y} {x' , y'} (f , h) = funExt λ g →
      (F-hom M ((f ⋆ g) ⋆ F-hom M h) ⋆ N-ob μ y')
        ≡⟨ cong (_⋆ N-ob μ y') (F-seq M (f ⋆ g) (F-hom M h)) ⟩
      ((F-hom M (f ⋆ g) ⋆ F-hom M (F-hom M h)) ⋆ N-ob μ y')
        ≡⟨ ⋆Assoc (F-hom M (f ⋆ g)) (F-hom M (F-hom M h)) (N-ob μ y') ⟩
      (F-hom M (f ⋆ g) ⋆ (F-hom M (F-hom M h) ⋆ N-ob μ y'))
        ≡⟨ cong (F-hom M (f ⋆ g) ⋆_) (N-hom μ h) ⟩
      (F-hom M (f ⋆ g) ⋆ (N-ob μ y ⋆ F-hom M h))
        ≡⟨ sym (⋆Assoc (F-hom M (f ⋆ g)) (N-ob μ y) (F-hom M h)) ⟩
      ((F-hom M (f ⋆ g) ⋆ N-ob μ y) ⋆ F-hom M h)
        ≡⟨ cong (_⋆ F-hom M h) (cong (_⋆ N-ob μ y) (F-seq M f g)) ⟩
      (((F-hom M f ⋆ F-hom M g) ⋆ N-ob μ y) ⋆ F-hom M h)
        ≡⟨ cong (_⋆ F-hom M h) (⋆Assoc (F-hom M f) (F-hom M g) (N-ob μ y)) ⟩
      ((M .F-hom f ⋆ (F-hom M g ⋆ N-ob μ y)) ⋆ F-hom M h) ∎

  -- Define comonads as monads on the opposite category?

module _ (C : Category ℓ ℓ') where
  Monad : Type (ℓ-max ℓ ℓ')
  Monad = Σ[ M ∈ Functor C C ] IsMonad M

module _ {C : Category ℓ ℓ'} (monadM monadN : Monad C) (ν : NatTrans (fst monadM) (fst monadN)) where

  private
    M N : Functor C C
    M = fst monadM
    N = fst monadN
    module M = IsMonad (snd monadM)
    module N = IsMonad (snd monadN)

  record IsMonadHom : Type (ℓ-max ℓ ℓ') where
    constructor proveMonadHom
    field
      N-η : compTrans ν M.η ≡ N.η
      N-μ : compTrans ν M.μ ≡ compTrans N.μ (whiskerTrans ν ν)
  open IsMonadHom

  isProp-IsMonadHom : isProp (IsMonadHom)
  N-η (isProp-IsMonadHom (proveMonadHom N-η1 N-μ1) (proveMonadHom N-η2 N-μ2) i) = isSetNatTrans _ _ N-η1 N-η2 i
  N-μ (isProp-IsMonadHom (proveMonadHom N-η1 N-μ1) (proveMonadHom N-η2 N-μ2) i) = isSetNatTrans _ _ N-μ1 N-μ2 i

module _ {C : Category ℓ ℓ'} (monadM monadN : Monad C) where
  MonadHom : Type (ℓ-max ℓ ℓ')
  MonadHom = Σ[ ν ∈ NatTrans (fst monadM) (fst monadN) ] IsMonadHom monadM monadN ν
