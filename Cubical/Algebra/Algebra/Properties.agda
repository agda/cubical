{-# OPTIONS --safe #-}
module Cubical.Algebra.Algebra.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Module

open import Cubical.Algebra.Algebra.Base

open Iso

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    R : Ring ℓ
    A B C D : Algebra R ℓ

module AlgebraTheory (R : Ring ℓ) (A : Algebra R ℓ') where
  open RingStr (snd R) renaming (_+_ to _+r_ ; _·_ to _·r_)
  open AlgebraStr (A .snd)

  ⋆AnnihilL : (x : ⟨ A ⟩) → 0r ⋆ x ≡ 0a
  ⋆AnnihilL = ModuleTheory.⋆AnnihilL R (Algebra→Module A)

  ⋆AnnihilR : (r : ⟨ R ⟩) → r ⋆ 0a ≡ 0a
  ⋆AnnihilR = ModuleTheory.⋆AnnihilR R (Algebra→Module A)

  ⋆Dist· : (x y : ⟨ R ⟩) (a b : ⟨ A ⟩) → (x ·r y) ⋆ (a · b) ≡ (x ⋆ a) · (y ⋆ b)
  ⋆Dist· x y a b = (x ·r y) ⋆ (a · b) ≡⟨ ⋆AssocR _ _ _ ⟩
                   a · ((x ·r y) ⋆ b) ≡⟨ cong (a ·_) (⋆Assoc _ _ _) ⟩
                   a · (x ⋆ (y ⋆ b)) ≡⟨ sym (⋆AssocR _ _ _) ⟩
                   x ⋆ (a · (y ⋆ b)) ≡⟨ sym (⋆AssocL _ _ _) ⟩
                   (x ⋆ a) · (y ⋆ b) ∎


module AlgebraHoms where
  open IsAlgebraHom

  idAlgebraHom : (A : Algebra R ℓ') → AlgebraHom A A
  fst (idAlgebraHom A) x = x
  pres0 (snd (idAlgebraHom A)) = refl
  pres1 (snd (idAlgebraHom A)) = refl
  pres+ (snd (idAlgebraHom A)) x y = refl
  pres· (snd (idAlgebraHom A)) x y = refl
  pres- (snd (idAlgebraHom A)) x = refl
  pres⋆ (snd (idAlgebraHom A)) r x = refl

  compIsAlgebraHom :
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

  _∘≃a_ : AlgebraEquiv B C → AlgebraEquiv A B → AlgebraEquiv A C
  _∘≃a_  g f .fst = compEquiv (fst f) (fst g)
  _∘≃a_  g f .snd = compIsAlgebraHom (g .snd) (f .snd)

  compAlgebraHom : AlgebraHom A B → AlgebraHom B C → AlgebraHom A C
  compAlgebraHom f g .fst = g .fst ∘ f .fst
  compAlgebraHom f g .snd = compIsAlgebraHom (g .snd) (f .snd)

  _∘a_ : AlgebraHom B C → AlgebraHom A B → AlgebraHom A C
  _∘a_ = flip compAlgebraHom

  compIdAlgebraHom : (φ : AlgebraHom A B) → compAlgebraHom (idAlgebraHom A) φ ≡ φ
  compIdAlgebraHom φ = AlgebraHom≡ refl

  idCompAlgebraHom :(φ : AlgebraHom A B) → compAlgebraHom φ (idAlgebraHom B) ≡ φ
  idCompAlgebraHom φ = AlgebraHom≡ refl

  compAssocAlgebraHom : (φ : AlgebraHom A B) (ψ : AlgebraHom B C) (χ : AlgebraHom C D)
                      → compAlgebraHom (compAlgebraHom φ ψ) χ ≡ compAlgebraHom φ (compAlgebraHom ψ χ)
  compAssocAlgebraHom _ _ _ = AlgebraHom≡ refl


module AlgebraEquivs where
  open IsAlgebraHom
  open AlgebraHoms

  module _ where

    invAlgebraEquiv : AlgebraEquiv A B → AlgebraEquiv B A
    (invAlgebraEquiv f').fst = invEquiv (fst f')
    (invAlgebraEquiv {A = A} {B = B} f').snd = hom
      where
        open AlgebraStr {{...}}
        instance
          _ = snd A
          _ = snd B

        f⁻¹ = fst (invEquiv (fst f'))
        f = fst (fst f')
        f⁻¹∘f≡id : (x : _) → f⁻¹ (f x) ≡ x
        f⁻¹∘f≡id = snd (isEquiv→hasRetract (snd (fst f')))
        f∘f⁻¹≡id : (y : _) → f (f⁻¹ y) ≡ y
        f∘f⁻¹≡id = snd (isEquiv→hasSection (snd (fst f')))

        hom : IsAlgebraHom (B .snd) f⁻¹ (A .snd)
        pres0 hom =
          f⁻¹ 0a     ≡⟨ sym (cong f⁻¹ (snd f' .pres0)) ⟩
          f⁻¹ (f 0a) ≡⟨ f⁻¹∘f≡id 0a ⟩
          0a ∎
        pres1 hom =
          f⁻¹ 1a     ≡⟨ sym (cong f⁻¹ (snd f' .pres1)) ⟩
          f⁻¹ (f 1a) ≡⟨ f⁻¹∘f≡id 1a ⟩
          1a ∎
        pres+ hom x y =
          f⁻¹ (x + y)                  ≡[ i ]⟨ f⁻¹ ((f∘f⁻¹≡id x (~ i)) + (f∘f⁻¹≡id y (~ i))) ⟩
          f⁻¹ (f (f⁻¹ x) + f (f⁻¹ y))  ≡⟨ sym (cong f⁻¹ (snd f' .pres+ _ _)) ⟩
          f⁻¹ (f (f⁻¹ x + f⁻¹ y))      ≡⟨ f⁻¹∘f≡id _ ⟩
          f⁻¹ x + f⁻¹ y ∎
        pres· hom x y =
          f⁻¹ (x · y)                  ≡[ i ]⟨ f⁻¹ ((f∘f⁻¹≡id x (~ i)) · (f∘f⁻¹≡id y (~ i))) ⟩
          f⁻¹ (f (f⁻¹ x) · f (f⁻¹ y))  ≡⟨ sym (cong f⁻¹ (snd f' .pres· _ _)) ⟩
          f⁻¹ (f (f⁻¹ x · f⁻¹ y))      ≡⟨ f⁻¹∘f≡id _ ⟩
          f⁻¹ x · f⁻¹ y ∎
        pres- hom x =
          f⁻¹ (- x)            ≡⟨ sym (cong (λ u → f⁻¹ (- u)) (f∘f⁻¹≡id _)) ⟩
          f⁻¹ (- f (f⁻¹ x))    ≡⟨ sym (cong f⁻¹ (snd f' .pres- (f⁻¹ x)) ) ⟩
          f⁻¹ (f (- f⁻¹ x))    ≡⟨ f⁻¹∘f≡id _ ⟩
          (- f⁻¹ x) ∎
        pres⋆ hom r x =
          f⁻¹ (r ⋆ x)           ≡⟨ cong (λ u → f⁻¹ (r ⋆ u)) (sym (f∘f⁻¹≡id _)) ⟩
          f⁻¹ (r ⋆ f (f⁻¹ x))   ≡⟨ sym (cong f⁻¹ (snd f' .pres⋆ r (f⁻¹ x))) ⟩
          f⁻¹ (f (r ⋆ (f⁻¹ x))) ≡⟨ f⁻¹∘f≡id _ ⟩
          r ⋆ (f⁻¹ x) ∎

  compIsAlgebraEquiv :
    {g : ⟨ B ⟩ ≃ ⟨ C ⟩} {f : ⟨ A ⟩ ≃ ⟨ B ⟩}
    → IsAlgebraEquiv (B .snd) g (C .snd)
    → IsAlgebraEquiv (A .snd) f (B .snd)
    → IsAlgebraEquiv (A .snd) (compEquiv f g) (C .snd)
  compIsAlgebraEquiv {g = g} {f} gh fh = compIsAlgebraHom {g = g .fst} {f .fst} gh fh

  compAlgebraEquiv : AlgebraEquiv A B → AlgebraEquiv B C → AlgebraEquiv A C
  fst (compAlgebraEquiv f g) = compEquiv (f .fst) (g .fst)
  snd (compAlgebraEquiv f g) = compIsAlgebraEquiv {g = g .fst} {f = f .fst} (g .snd) (f .snd)

  preCompAlgEquiv :
    AlgebraEquiv A B → AlgebraHom B C ≃ AlgebraHom A C
  (preCompAlgEquiv f).fst g = g ∘a (AlgebraEquiv→AlgebraHom f)
  (preCompAlgEquiv {A = A} {B = B} {C = C} f).snd = snd (isoToEquiv isoOnHoms)
    where
      isoOnTypes : Iso (fst B → fst C) (fst A → fst C)
      isoOnTypes = equivToIso (_ , (snd (preCompEquiv (fst f))))

      f⁻¹ : AlgebraEquiv B A
      f⁻¹ = invAlgebraEquiv f

      isoOnHoms : Iso (AlgebraHom B C) (AlgebraHom A C)
      fun isoOnHoms g = g ∘a AlgebraEquiv→AlgebraHom f
      inv isoOnHoms h = h ∘a AlgebraEquiv→AlgebraHom f⁻¹
      rightInv isoOnHoms h =
        Σ≡Prop
          (λ h → isPropIsAlgebraHom _ (A .snd) h (C .snd))
          (isoOnTypes .rightInv (h .fst))
      leftInv isoOnHoms g =
        Σ≡Prop
          (λ g → isPropIsAlgebraHom _ (B .snd) g (C .snd))
          (isoOnTypes .leftInv (g .fst))

-- the Algebra version of uaCompEquiv
module AlgebraUAFunctoriality where
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

 caracAlgebra≡ : (p q : A ≡ B) → cong ⟨_⟩ p ≡ cong ⟨_⟩ q → p ≡ q
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

 uaCompAlgebraEquiv : (f : AlgebraEquiv A B) (g : AlgebraEquiv B C)
                  → uaAlgebra (compAlgebraEquiv f g) ≡ uaAlgebra f ∙ uaAlgebra g
 uaCompAlgebraEquiv f g = caracAlgebra≡ _ _ (
   cong ⟨_⟩ (uaAlgebra (compAlgebraEquiv f g))
     ≡⟨ uaCompEquiv _ _ ⟩
   cong ⟨_⟩ (uaAlgebra f) ∙ cong ⟨_⟩ (uaAlgebra g)
     ≡⟨ sym (cong-∙ ⟨_⟩ (uaAlgebra f) (uaAlgebra g)) ⟩
   cong ⟨_⟩ (uaAlgebra f ∙ uaAlgebra g) ∎)
