module Cubical.Algebra.CommAlgebra.Univalence where

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
open import Cubical.Algebra.CommAlgebra.Base

private
  variable
    ℓ ℓ' ℓ'' : Level


module _ {R : CommRing ℓ} where

  CommAlgebraPath' :
    (A B : CommAlgebra R ℓ')
    → (Σ[ f ∈ CommRingEquiv (A .fst) (B .fst) ] (f .fst .fst , f .snd)  ∘cr A .snd ≡ B .snd)
    ≃ (A ≡ B)
  CommAlgebraPath' A B =
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


  CommRingEquiv→CommAlgebraEquiv :
    {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''}
    → (e : CommRingEquiv (A .fst) (B .fst))
    → e .fst .fst ∘ A .snd .fst ≡ B .snd .fst
    → CommAlgebraEquiv A B
  CommRingEquiv→CommAlgebraEquiv {A = A} {B = B} e p = e .fst , isHom
    where
      opaque
        isHom : IsCommAlgebraHom A B (e .fst .fst)
        isHom = record { isCommRingHom = e .snd ; commutes = CommRingHom≡ p }

  CommAlgebraEquiv→CREquivΣ :
    {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''}
    → (CommAlgebraEquiv A B)
      ≃ (Σ[ f ∈ CommRingEquiv (A .fst) (B .fst) ] (f .fst .fst , f .snd)  ∘cr A .snd ≡ B .snd)
  CommAlgebraEquiv→CREquivΣ =
    isoToEquiv $
    iso to from
        (λ _ → Σ≡Prop (λ _ → isSetCommRingHom _ _ _ _) (Σ≡Prop (λ f → isPropIsCommRingHom _ (f .fst) _) refl))
        (λ _ → Σ≡Prop (isPropIsCommAlgebraHom _ _ ∘ fst) refl)
    where to : CommAlgebraEquiv _ _ → _
          to e = (e .fst , IsCommAlgebraHom.isCommRingHom (e .snd)) , IsCommAlgebraHom.commutes (e .snd)

          from : _ → CommAlgebraEquiv _ _
          from (e , commutes) = CommRingEquiv→CommAlgebraEquiv e (cong fst commutes)

  CommAlgebraPath :
    (A B : CommAlgebra R ℓ')
    → CommAlgebraEquiv A B
    ≃ (A ≡ B)
  CommAlgebraPath A B =
    CommAlgebraEquiv A B
       ≃⟨ CommAlgebraEquiv→CREquivΣ ⟩
    Σ[ f ∈ CommRingEquiv (A .fst) (B .fst) ] (f .fst .fst , f .snd)  ∘cr A .snd ≡ B .snd
       ≃⟨ CommAlgebraPath' A B ⟩
    A ≡ B  ■

  uaCommAlgebra : {A B : CommAlgebra R ℓ'} → CommAlgebraEquiv A B → A ≡ B
  uaCommAlgebra {A = A} {B = B} =
    equivFun $ CommAlgebraPath A B


  isGroupoidCommAlgebra : isGroupoid (CommAlgebra R ℓ')
  isGroupoidCommAlgebra A B =
    isOfHLevelRespectEquiv
      2
      (CommAlgebraPath' _ _)
      (isSetΣSndProp (isSetCommRingEquiv _ _) λ _ → isSetCommRingHom _ _ _ _)
