{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebraAlt.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

CommAlgebra : (R : CommRing ℓ) (ℓ' : Level) → Type _
CommAlgebra R ℓ' = Σ[ A ∈ CommRing ℓ' ] CommRingHom R A

module _ {R : CommRing ℓ} where
  CommAlgebra→CommRing : (A : CommAlgebra R ℓ') → CommRing ℓ'
  CommAlgebra→CommRing = fst

  CommAlgebraHom : (A : CommAlgebra R ℓ') (B : CommAlgebra R ℓ'') → Type _
  CommAlgebraHom A B = Σ[ f ∈ CommRingHom (fst A) (fst B) ]  f ∘cr snd A ≡ snd B

  idCAlgHom : (A : CommAlgebra R ℓ) → CommAlgebraHom A A
  idCAlgHom A = (idCommRingHom (fst A)) , Σ≡Prop (λ _ → isPropIsCommRingHom (R .snd) _ (A .fst .snd)) refl

  compCommAlgebraHom : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} {C : CommAlgebra R ℓ'''}
                      → (g : CommAlgebraHom B C) → (f : CommAlgebraHom A B)
                      → CommAlgebraHom A C
  compCommAlgebraHom {A = A} {B = B} {C = C} g f =
    ((fst g) ∘cr (fst f)) , pasting
    where
      opaque
        pasting : ((fst g) ∘cr (fst f)) ∘cr snd A ≡ snd C
        pasting =
          Σ≡Prop (λ _ → isPropIsCommRingHom (R .snd) _ (C .fst .snd))
                 (
                  (fst g ∘cr (fst f ∘cr snd A)) .fst ≡⟨ cong (λ h → (fst g ∘cr h) .fst) (f .snd) ⟩
                  (fst g ∘cr snd B) .fst            ≡⟨ cong fst (g .snd) ⟩
                  (C .snd .fst) ∎)

  ⟨_⟩ₐ : (A : CommAlgebra R ℓ') → Type ℓ'
  ⟨ A ⟩ₐ = A .fst .fst

  ⟨_⟩ₐ→ : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} (f : CommAlgebraHom A B) → ⟨ A ⟩ₐ → ⟨ B ⟩ₐ
  ⟨ f ⟩ₐ→ = f .fst .fst

  _$ca_ : {A : CommAlgebra R ℓ} {B : CommAlgebra R ℓ'} → (φ : CommAlgebraHom A B) → (x : ⟨ A ⟩ₐ) → ⟨ B ⟩ₐ
  φ $ca x = φ .fst .fst x

  _∘ca_ : {A : CommAlgebra R ℓ} {B : CommAlgebra R ℓ'} {C : CommAlgebra R ℓ''}
        → CommAlgebraHom B C → CommAlgebraHom A B → CommAlgebraHom A C
  g ∘ca f = compCommAlgebraHom g f

  opaque
    CommAlgebraHom≡ :
      {A : CommAlgebra R ℓ} {B : CommAlgebra R ℓ'} {f g : CommAlgebraHom A B}
      → f .fst .fst ≡ g .fst .fst
      → f ≡ g
    CommAlgebraHom≡ {B = B} p =
      Σ≡Prop (λ _ → isSetΣSndProp (isSetΠ (λ _ → is-set))
                                  (λ _ → isPropIsCommRingHom _ _ _)
                                  _ _)
             (Σ≡Prop (λ _ → isPropIsCommRingHom _ _ _)
              p)
      where open CommRingStr (B .fst .snd) using (is-set)

    CommAlgebra≡ :
      {A B : CommAlgebra R ℓ'}
      → (p : (A .fst) ≡ (B .fst))
      → (pathToEquiv $ cong fst p) .fst ∘ (A .snd) .fst ≡ (B .snd) .fst
      → A ≡ B
    CommAlgebra≡ p q = {!!}

  CommAlgebraEquiv : (A : CommAlgebra R ℓ') (B : CommAlgebra R ℓ'') → Type _
  CommAlgebraEquiv A B = Σ[ f ∈ CommRingEquiv (A .fst) (B .fst) ] (f .fst .fst , f .snd)  ∘cr A .snd ≡ B .snd

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
      where open IsCommRingHom (A .snd .snd)

    ⋆DistR+ : (r : ⟨ R ⟩) (x y : ⟨ A ⟩ₐ) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y)
    ⋆DistR+ r x y = ·DistR+ _ _ _

    ⋆DistL+ : (r s : ⟨ R ⟩) (x : ⟨ A ⟩ₐ) → (r + s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x)
    ⋆DistL+ r s x = cong (_· x) (pres+ r s) ∙ ·DistL+ _ _ _
      where open IsCommRingHom (A .snd .snd)

    ⋆IdL    : (x : ⟨ A ⟩ₐ) → 1r ⋆ x ≡ x
    ⋆IdL x = cong (_· x) pres1 ∙ ·IdL x
      where open IsCommRingHom (A .snd .snd)

    ⋆AssocL : (r : ⟨ R ⟩) (x y : ⟨ A ⟩ₐ) → (r ⋆ x) · y ≡ r ⋆ (x · y)
    ⋆AssocL r x y = sym (·Assoc (A .snd .fst r) x y)

{- Convenience forgetful functions -}
module _ {R : CommRing ℓ} where
  CommAlgebra→Ring : (A : CommAlgebra R ℓ') → Ring ℓ'
  CommAlgebra→Ring A = CommRing→Ring (fst A)

  CommAlgebraHom→CommRingHom : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''}
                             → CommAlgebraHom A B
                             → CommRingHom (CommAlgebra→CommRing A) (CommAlgebra→CommRing B)
  CommAlgebraHom→CommRingHom = fst

  CommAlgebraHom→RingHom : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''}
                             → CommAlgebraHom A B
                             → RingHom (CommAlgebra→Ring A) (CommAlgebra→Ring B)
  CommAlgebraHom→RingHom = CommRingHom→RingHom ∘ CommAlgebraHom→CommRingHom
