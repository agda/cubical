{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebraAlt.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

CommAlgebra : (R : CommRing ℓ) (ℓ' : Level) → Type _
CommAlgebra R ℓ' = Σ[ A ∈ CommRing ℓ' ] CommRingHom R A

module _ {R : CommRing ℓ} where
  open RingHoms

  CommAlgebra→CommRing : (A : CommAlgebra R ℓ') → CommRing ℓ'
  CommAlgebra→CommRing = fst

  CommAlgebraHom : (A : CommAlgebra R ℓ') (B : CommAlgebra R ℓ'') → Type _
  CommAlgebraHom A B = Σ[ f ∈ CommRingHom (fst A) (fst B) ]  f ∘r snd A ≡ snd B

  idCAlgHom : (A : CommAlgebra R ℓ) → CommAlgebraHom A A
  idCAlgHom A = (idCommRingHom (fst A)) , Σ≡Prop (λ _ → isPropIsCommRingHom (R .snd) _ (A .fst .snd)) refl

  compCommAlgebraHom : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} {C : CommAlgebra R ℓ'''}
                      → (g : CommAlgebraHom B C) → (f : CommAlgebraHom A B)
                      → CommAlgebraHom A C
  compCommAlgebraHom {A = A} {B = B} {C = C} g f =
    ((fst g) ∘r (fst f)) ,
    Σ≡Prop (λ _ → isPropIsCommRingHom (R .snd) _ (C .fst .snd))
           (
            (fst g ∘r (fst f ∘r snd A)) .fst ≡⟨ cong (λ h → (fst g ∘r h) .fst) (f .snd) ⟩
            (fst g ∘r snd B) .fst            ≡⟨ cong fst (g .snd) ⟩
            (C .snd .fst) ∎)

  ⟨_⟩ₐ : (A : CommAlgebra R ℓ') → Type ℓ'
  ⟨ A ⟩ₐ = A .fst .fst

  module CommAlgebraStr (A : CommAlgebra R ℓ') where
    open CommRingStr {{...}}
    instance
      _ = A
      _ : CommRingStr ⟨ A ⟩ₐ
      _ = (A .fst .snd)
      _ : CommRingStr (R .fst)
      _ = (R .snd)

    infixl 7 _⋆_
    _⋆_ : ⟨ R ⟩ → ⟨ A ⟩ₐ → ⟨ A ⟩ₐ
    _⋆_ r x = (A .snd .fst r) · x

    ⋆Assoc  : (r s : ⟨ R ⟩) (x : ⟨ A ⟩ₐ) → (r · s) ⋆ x ≡ r ⋆ (s ⋆ x)
    ⋆Assoc r s x = cong (_· x) (pres· r s) ∙ sym (·Assoc _ _ _)
      where open IsRingHom (A .snd .snd)

    ⋆DistR+ : (r : ⟨ R ⟩) (x y : ⟨ A ⟩ₐ) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y)
    ⋆DistR+ r x y = ·DistR+ _ _ _

    ⋆DistL+ : (r s : ⟨ R ⟩) (x : ⟨ A ⟩ₐ) → (r + s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x)
    ⋆DistL+ r s x = cong (_· x) (pres+ r s) ∙ ·DistL+ _ _ _
      where open IsRingHom (A .snd .snd)

    ⋆IdL    : (x : ⟨ A ⟩ₐ) → 1r ⋆ x ≡ x
    ⋆IdL x = cong (_· x) pres1 ∙ ·IdL x
      where open IsRingHom (A .snd .snd)

    ⋆AssocL : (r : ⟨ R ⟩) (x y : ⟨ A ⟩ₐ) → (r ⋆ x) · y ≡ r ⋆ (x · y)
    ⋆AssocL r x y = sym (·Assoc (A .snd .fst r) x y)
