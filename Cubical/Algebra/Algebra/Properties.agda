{-# OPTIONS --safe #-}
module Cubical.Algebra.Algebra.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Module
open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Algebra.Base

open Iso

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level




module AlgebraTheory (R : Ring ℓ) (A : Algebra R ℓ') where
  open RingStr (snd R) renaming (_+_ to _+r_ ; _·_ to _·r_)
  open AlgebraStr (A .snd)

  0-actsNullifying : (x : ⟨ A ⟩) → 0r ⋆ x ≡ 0a
  0-actsNullifying x =
    let idempotent-+ = 0r ⋆ x              ≡⟨ cong (λ u → u ⋆ x) (sym (RingTheory.0Idempotent R)) ⟩
                       (0r +r 0r) ⋆ x      ≡⟨ ⋆-ldist 0r 0r x ⟩
                       (0r ⋆ x) + (0r ⋆ x) ∎
    in RingTheory.+Idempotency→0 (Algebra→Ring A) (0r ⋆ x) idempotent-+

  ⋆Dist· : (x y : ⟨ R ⟩) (a b : ⟨ A ⟩) → (x ·r y) ⋆ (a · b) ≡ (x ⋆ a) · (y ⋆ b)
  ⋆Dist· x y a b = (x ·r y) ⋆ (a · b) ≡⟨ ⋆-rassoc _ _ _ ⟩
                   a · ((x ·r y) ⋆ b) ≡⟨ cong (a ·_) (⋆-assoc _ _ _) ⟩
                   a · (x ⋆ (y ⋆ b)) ≡⟨ sym (⋆-rassoc _ _ _) ⟩
                   x ⋆ (a · (y ⋆ b)) ≡⟨ sym (⋆-lassoc _ _ _) ⟩
                   (x ⋆ a) · (y ⋆ b) ∎


module AlgebraHoms {R : Ring ℓ} where
  open IsAlgebraHom

  idAlgebraHom : (A : Algebra R ℓ') → AlgebraHom A A
  fst (idAlgebraHom A) x = x
  pres0 (snd (idAlgebraHom A)) = refl
  pres1 (snd (idAlgebraHom A)) = refl
  pres+ (snd (idAlgebraHom A)) x y = refl
  pres· (snd (idAlgebraHom A)) x y = refl
  pres- (snd (idAlgebraHom A)) x = refl
  pres⋆ (snd (idAlgebraHom A)) r x = refl

  compIsAlgebraHom : {A : Algebra R ℓ'} {B : Algebra R ℓ''} {C : Algebra R ℓ'''}
    {g : ⟨ B ⟩ → ⟨ C ⟩} {f : ⟨ A ⟩ → ⟨ B ⟩}
    → IsAlgebraHom (B .snd) g (C .snd)
    → IsAlgebraHom (A .snd) f (B .snd)
    → IsAlgebraHom (A .snd) (g ∘ f) (C .snd)
  compIsAlgebraHom {g = g} {f} gh fh .pres0 = cong g (fh .pres0) ∙ gh .pres0
  compIsAlgebraHom {g = g} {f} gh fh .pres1 = cong g (fh .pres1) ∙ gh .pres1
  compIsAlgebraHom {g = g} {f} gh fh .pres+ x y = cong g (fh .pres+ x y) ∙ gh .pres+ (f x) (f y)
  compIsAlgebraHom {g = g} {f} gh fh .pres· x y = cong g (fh .pres· x y) ∙ gh .pres· (f x) (f y)
  compIsAlgebraHom {g = g} {f} gh fh .pres- x = cong g (fh .pres- x) ∙ gh .pres- (f x)
  compIsAlgebraHom {g = g} {f} gh fh .pres⋆ r x = cong g (fh .pres⋆ r x) ∙ gh .pres⋆ r (f x)

  compAlgebraHom : {A : Algebra R ℓ'} {B : Algebra R ℓ''} {C : Algebra R ℓ'''}
              → AlgebraHom A B → AlgebraHom B C → AlgebraHom A C
  compAlgebraHom f g .fst = g .fst ∘ f .fst
  compAlgebraHom f g .snd = compIsAlgebraHom (g .snd) (f .snd)

  syntax compAlgebraHom f g = g ∘a f

  compIdAlgebraHom : {A B : Algebra R ℓ'} (φ : AlgebraHom A B) → compAlgebraHom (idAlgebraHom A) φ ≡ φ
  compIdAlgebraHom φ = AlgebraHom≡ refl

  idCompAlgebraHom : {A B : Algebra R ℓ'} (φ : AlgebraHom A B) → compAlgebraHom φ (idAlgebraHom B) ≡ φ
  idCompAlgebraHom φ = AlgebraHom≡ refl

  compAssocAlgebraHom : {A B C D : Algebra R ℓ'}
                        (φ : AlgebraHom A B) (ψ : AlgebraHom B C) (χ : AlgebraHom C D)
                      → compAlgebraHom (compAlgebraHom φ ψ) χ ≡ compAlgebraHom φ (compAlgebraHom ψ χ)
  compAssocAlgebraHom _ _ _ = AlgebraHom≡ refl


module AlgebraEquivs {R : Ring ℓ} where
  open IsAlgebraHom
  open AlgebraHoms

  compIsAlgebraEquiv : {A : Algebra R ℓ'} {B : Algebra R ℓ''} {C : Algebra R ℓ'''}
    {g : ⟨ B ⟩ ≃ ⟨ C ⟩} {f : ⟨ A ⟩ ≃ ⟨ B ⟩}
    → IsAlgebraEquiv (B .snd) g (C .snd)
    → IsAlgebraEquiv (A .snd) f (B .snd)
    → IsAlgebraEquiv (A .snd) (compEquiv f g) (C .snd)
  compIsAlgebraEquiv {g = g} {f} gh fh = compIsAlgebraHom {g = g .fst} {f .fst} gh fh

  compAlgebraEquiv : {A : Algebra R ℓ'} {B : Algebra R ℓ''} {C : Algebra R ℓ'''}
                → AlgebraEquiv A B → AlgebraEquiv B C → AlgebraEquiv A C
  fst (compAlgebraEquiv f g) = compEquiv (f .fst) (g .fst)
  snd (compAlgebraEquiv f g) = compIsAlgebraEquiv {g = g .fst} {f = f .fst} (g .snd) (f .snd)



-- the Algebra version of uaCompEquiv
module AlgebraUAFunctoriality {R : Ring ℓ} where
 open AlgebraStr
 open AlgebraEquivs

 Algebra≡ : (A B : Algebra R ℓ') → (
   Σ[ p ∈ ⟨ A ⟩ ≡ ⟨ B ⟩ ]
   Σ[ q0 ∈ PathP (λ i → p i) (0a (snd A)) (0a (snd B)) ]
   Σ[ q1 ∈ PathP (λ i → p i) (1a (snd A)) (1a (snd B)) ]
   Σ[ r+ ∈ PathP (λ i → p i → p i → p i) (_+_ (snd A)) (_+_ (snd B)) ]
   Σ[ r· ∈ PathP (λ i → p i → p i → p i) (_·_ (snd A)) (_·_ (snd B)) ]
   Σ[ s- ∈ PathP (λ i → p i → p i) (-_ (snd A)) (-_ (snd B)) ]
   Σ[ s⋆ ∈ PathP (λ i → ⟨ R ⟩ → p i → p i) (_⋆_ (snd A)) (_⋆_ (snd B)) ]
   PathP (λ i → IsAlgebra R (q0 i) (q1 i) (r+ i) (r· i) (s- i) (s⋆ i)) (isAlgebra (snd A))
                                                                     (isAlgebra (snd B)))
   ≃ (A ≡ B)
 Algebra≡ A B = isoToEquiv theIso
   where
   open Iso
   theIso : Iso _ _
   fun theIso (p , q0 , q1 , r+ , r· , s- , s⋆ , t) i = p i
                 , algebrastr (q0 i) (q1 i) (r+ i) (r· i) (s- i) (s⋆ i) (t i)
   inv theIso x = cong ⟨_⟩ x , cong (0a ∘ snd) x , cong (1a ∘ snd) x
                , cong (_+_ ∘ snd) x , cong (_·_ ∘ snd) x , cong (-_ ∘ snd) x , cong (_⋆_ ∘ snd) x
                , cong (isAlgebra ∘ snd) x
   rightInv theIso _ = refl
   leftInv theIso _ = refl

 caracAlgebra≡ : {A B : Algebra R ℓ'} (p q : A ≡ B) → cong ⟨_⟩ p ≡ cong ⟨_⟩ q → p ≡ q
 caracAlgebra≡ {A = A} {B = B} p q P =
   sym (transportTransport⁻ (ua (Algebra≡ A B)) p)
                                    ∙∙ cong (transport (ua (Algebra≡ A B))) helper
                                    ∙∙ transportTransport⁻ (ua (Algebra≡ A B)) q
     where
     helper : transport (sym (ua (Algebra≡ A B))) p ≡ transport (sym (ua (Algebra≡ A B))) q
     helper = Σ≡Prop
                (λ _ → isPropΣ
                          (isOfHLevelPathP' 1 (is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ λ _ → is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set (snd B)) _ _)
                          λ _ → isOfHLevelPathP 1 (isPropIsAlgebra _ _ _ _ _ _ _) _ _)
               (transportRefl (cong ⟨_⟩ p) ∙ P ∙ sym (transportRefl (cong ⟨_⟩ q)))

 uaCompAlgebraEquiv : {A B C : Algebra R ℓ'} (f : AlgebraEquiv A B) (g : AlgebraEquiv B C)
                  → uaAlgebra (compAlgebraEquiv f g) ≡ uaAlgebra f ∙ uaAlgebra g
 uaCompAlgebraEquiv f g = caracAlgebra≡ _ _ (
   cong ⟨_⟩ (uaAlgebra (compAlgebraEquiv f g))
     ≡⟨ uaCompEquiv _ _ ⟩
   cong ⟨_⟩ (uaAlgebra f) ∙ cong ⟨_⟩ (uaAlgebra g)
     ≡⟨ sym (cong-∙ ⟨_⟩ (uaAlgebra f) (uaAlgebra g)) ⟩
   cong ⟨_⟩ (uaAlgebra f ∙ uaAlgebra g) ∎)
