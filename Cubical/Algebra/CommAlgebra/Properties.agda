module Cubical.Algebra.CommAlgebra.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure using (⟨_⟩; withOpaqueStr)

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Univalence
open import Cubical.Algebra.CommAlgebra.Notation

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module _ {R : CommRing ℓ} where

  opaque
    compIdCommAlgebraHom : {A B : CommAlgebra R ℓ'} (f : CommAlgebraHom A B)
                      →  (f ∘ca idCAlgHom A) ≡ f
    compIdCommAlgebraHom f = CommAlgebraHom≡ refl

    idCompCommAlgebraHom : {A B : CommAlgebra R ℓ'} (f : CommAlgebraHom A B)
                      → (idCommAlgebraHom B) ∘ca f ≡ f
    idCompCommAlgebraHom f = CommAlgebraHom≡ refl

    compAssocCommAlgebraHom : {A B C D : CommAlgebra R ℓ'}
                           (f : CommAlgebraHom A B) (g : CommAlgebraHom B C) (h : CommAlgebraHom C D)
                         →  h ∘ca (g ∘ca f) ≡ (h ∘ca g) ∘ca f
    compAssocCommAlgebraHom f g h = CommAlgebraHom≡ refl

  invCommAlgebraEquiv : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''}
                        → CommAlgebraEquiv A B
                        → CommAlgebraEquiv B A
  invCommAlgebraEquiv {A = A} {B = B} f = CommRingEquiv→CommAlgebraEquiv f⁻¹ commutes
    where f⁻¹ = invCommRingEquiv (CommAlgebra→CommRing A) (CommAlgebra→CommRing B) (CommAlgebraEquiv→CommRingEquiv f)
          f⁻¹∘f≡Id : f⁻¹ .fst .fst ∘ f .fst .fst ≡ idfun _
          f⁻¹∘f≡Id = funExt (secIsEq (equivIsEquiv (f⁻¹ .fst)))
          opaque
            commutes : (f⁻¹ .fst .fst) ∘ B .snd .fst ≡ A .snd .fst
            commutes =
                f⁻¹ .fst .fst ∘ B .snd .fst                ≡⟨ sym ( cong ((f⁻¹ .fst .fst) ∘_) (cong fst (IsCommAlgebraHom.commutes (f .snd)))) ⟩
                f⁻¹ .fst .fst ∘  f .fst .fst ∘ A .snd .fst ≡⟨ cong (_∘ A .snd .fst) f⁻¹∘f≡Id  ⟩
                A .snd .fst ∎

  compCommAlgebraEquiv : {A : CommAlgebra R ℓ'} {B : CommAlgebra R ℓ''} {C : CommAlgebra R ℓ'''}
                      → (f : CommAlgebraEquiv A B) → (g : CommAlgebraEquiv B C)
                      → CommAlgebraEquiv A C
  compCommAlgebraEquiv {A = A} {B = B} {C = C} (f , fIsHom) (g , gIsHom) =
    (compEquiv f g) , snd (compCommAlgebraHom ((fst f) , fIsHom) ((fst g) , gIsHom))


module _
  -- Variable generalization would fail below without the module parameters A and B.
  {R : CommRing ℓ}
  {A : CommAlgebra R ℓ'}
  {B : CommAlgebra R ℓ''}
  {f : ⟨ A ⟩ₐ → ⟨ B ⟩ₐ}
  where

  open InstancesForCAlg A
  open InstancesForCAlg B

  module _
    (p1 : f 1r ≡ 1r)
    (p+ : (x y : ⟨ A ⟩ₐ) → f (x + y) ≡ f x + f y)
    (p· : (x y : ⟨ A ⟩ₐ) → f (x · y) ≡ f x · f y)
    (p⋆ : (r : ⟨ R ⟩) (x : ⟨ A ⟩ₐ) → f (r ⋆ x) ≡ r ⋆ f x)
    where

    makeIsCommAlgebraHom : IsCommAlgebraHom A B f
    makeIsCommAlgebraHom .IsCommAlgebraHom.isCommRingHom = makeIsCommRingHom p1 p+ p·
    makeIsCommAlgebraHom .IsCommAlgebraHom.commutes =
      CommRingHom≡ $ funExt λ r → f (A .snd .fst r)        ≡⟨ cong f (sym (·IdR _)) ⟩
                                  f ((A .snd .fst r) · 1r) ≡⟨⟩
                                  f (r ⋆ 1r)               ≡⟨ p⋆ _ _ ⟩
                                  r ⋆ (f 1r)               ≡⟨⟩
                                  (B .snd .fst r) · f 1r   ≡⟨ cong ((B .snd .fst r) ·_) p1 ⟩
                                  (B .snd .fst r) · 1r     ≡⟨ ·IdR _ ⟩
                                  B .snd .fst r ∎
