module Cubical.Algebra.CommAlgebraAlt.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Univalence
open import Cubical.Algebra.CommAlgebraAlt.Base

private
  variable
    ℓ ℓ' ℓ'' : Level


CommAlgebraPath :
  (R : CommRing ℓ)
  (A B : CommAlgebra R ℓ')
  → (Σ[ f ∈ CommRingEquiv (A .fst) (B .fst) ] (f .fst .fst , f .snd)  ∘cr A .snd ≡ B .snd)
  ≃ (A ≡ B)
CommAlgebraPath R A B =
  (Σ-cong-equiv
    (CommRingPath _ _)
    (λ e → compPathlEquiv (computeSubst e)))
  ∙ₑ ΣPathTransport≃PathΣ A B
  where computeSubst :
          (e : CommRingEquiv (fst A) (fst B))
          → subst (CommRingHom R) (uaCommRing e) (A .snd)
            ≡ (CommRingEquiv→CommRingHom e) ∘cr A .snd
        computeSubst e =
          CommRingHom≡ $
            (subst (CommRingHom R) (uaCommRing e) (A .snd)) .fst
              ≡⟨ sym (substCommSlice (CommRingHom R) (λ X → ⟨ R ⟩ → ⟨ X ⟩) (λ _ → fst) (uaCommRing e) (A .snd)) ⟩
            subst (λ X → ⟨ R ⟩ → ⟨ X ⟩) (uaCommRing e) (A .snd .fst)
              ≡⟨ fromPathP (funTypeTransp (λ _ → ⟨ R ⟩) ⟨_⟩ (uaCommRing e) (A .snd .fst)) ⟩
            subst ⟨_⟩ (uaCommRing e) ∘ A .snd .fst ∘ subst (λ _ → ⟨ R ⟩) (sym (uaCommRing e))
              ≡⟨ cong ((subst ⟨_⟩ (uaCommRing e) ∘ A .snd .fst) ∘_) (funExt (λ _ → transportRefl _)) ⟩
            (subst ⟨_⟩ (uaCommRing e) ∘ (A .snd .fst))
              ≡⟨ funExt (λ _ → uaβ (e .fst) _) ⟩
            (CommRingEquiv→CommRingHom e ∘cr A .snd) .fst  ∎

uaCommAlgebra : {R : CommRing ℓ} {A B : CommAlgebra R ℓ'} → CommAlgebraEquiv A B → A ≡ B
uaCommAlgebra {R = R} {A = A} {B = B} = equivFun (CommAlgebraPath R A B)

isGroupoidCommAlgebra : {R : CommRing ℓ} → isGroupoid (CommAlgebra R ℓ')
isGroupoidCommAlgebra A B = isOfHLevelRespectEquiv 2 (CommAlgebraPath _ _ _) (isSetCommAlgebraEquiv _ _)
