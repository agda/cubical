module Cubical.HITs.AbPath.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws as GLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed

open import Cubical.HITs.AbPath.Base

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Abelianization.Properties as Abi
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Group.Free

open import Cubical.Homotopy.Group.Base

open IsAbGroup
open IsGroup
open IsMonoid
open IsSemigroup
open AbGroupStr

elimProp≡ᵃᵇ : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} {B : x ≡ᵃᵇ y → Type ℓ'}
  → ((s : _) → isProp (B s))
  → ((p : x ≡ y) → B (paths p))
  → (x : _) → B x
elimProp≡ᵃᵇ pr path* (paths x) = path* x
elimProp≡ᵃᵇ {B = B} pr path* (com p q r i) = help i
  where
  help : PathP (λ i → B (com p q r i))
               (path* (p ∙ sym q ∙ r))
               (path* (r ∙ sym q ∙ p))
  help = isProp→PathP (λ _ → pr _) _ _

private
  pathsᵃᵇLemmaL : ∀ {ℓ} {A : Type ℓ} {x y : A} (z : _)
    (p : x ≡ z) (q : x ≡ y)(r : x ≡ y) (s : x ≡ y)
    → Path (z ≡ᵃᵇ y) (paths (sym p ∙ q ∙ sym r ∙ s))
                    (paths (sym p ∙ s ∙ sym r ∙ q))
  pathsᵃᵇLemmaL =
    J> λ q r s
      → cong paths (sym (lUnit _)) ∙ com q r s ∙ cong paths (lUnit _)

  pathsᵃᵇLemmaR : ∀ {ℓ} {A : Type ℓ} {x y : A} (z : _)
    (p : y ≡ z) (q : x ≡ y)(r : x ≡ y) (s : x ≡ y)
    → Path (x ≡ᵃᵇ z) (paths ((q ∙ sym r ∙ s) ∙ p))
                    (paths ((s ∙ sym r ∙ q) ∙ p))
  pathsᵃᵇLemmaR =
    J> λ q r s
      → cong paths (sym (rUnit _)) ∙ com q r s ∙ cong paths (rUnit _)

-- 'left action of Ω (A , x) on x ≡ᵃᵇ y'
act≡ᵃᵇ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ x) → x ≡ᵃᵇ y → x ≡ᵃᵇ y
act≡ᵃᵇ p (paths x₁) = paths (p ∙ x₁)
act≡ᵃᵇ {y = y} p (com q r s i) = pathsᵃᵇLemmaL _ (sym p) q r s i

actL·πᵃᵇ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) → y ≡ᵃᵇ z → x ≡ᵃᵇ z
actL·πᵃᵇ p (paths q) = paths (p ∙ q)
actL·πᵃᵇ p (com q r s i) = pathsᵃᵇLemmaL _ (sym p) q r s i

·πᵃᵇ : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → ∥ x ≡ᵃᵇ y ∥₂ → ∥ y ≡ᵃᵇ z ∥₂ → ∥ x ≡ᵃᵇ z ∥₂
·πᵃᵇ {x = x} {y} {z} = ST.rec2 squash₂ preMult
  where
  preMult : x ≡ᵃᵇ y → y ≡ᵃᵇ z → ∥ x ≡ᵃᵇ z ∥₂
  preMult (paths p) q = ∣ actL·πᵃᵇ p q ∣₂
  preMult (com p q r i) s = lem s i
    where
    lem : (s : y ≡ᵃᵇ z) → ∣ actL·πᵃᵇ (p ∙ sym q ∙ r) s ∣₂
                        ≡ ∣ actL·πᵃᵇ (r ∙ sym q ∙ p) s ∣₂
    lem = elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
      λ s i → ∣ pathsᵃᵇLemmaR _ s p q r i ∣₂

symᵃᵇ : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ᵃᵇ y → y ≡ᵃᵇ x
symᵃᵇ (paths x) = paths (sym x)
symᵃᵇ {A = A} {x} {y} (com p q r i) = lem i
  where
  lem : Path (y ≡ᵃᵇ x) (paths (sym (p ∙ sym q ∙ r)))
                      (paths (sym (r ∙ sym q ∙ p)))
  lem = cong paths (symDistr _ _ ∙ cong₂ _∙_ (symDistr _ _) refl
                  ∙ sym (GLaws.assoc _ _ _))
     ∙∙ com _ _ _
     ∙∙ sym (cong paths (symDistr _ _ ∙ cong₂ _∙_ (symDistr _ _) refl
                  ∙ sym (GLaws.assoc _ _ _)))

-πᵃᵇ : ∀ {ℓ} {A : Type ℓ} {x y : A} → ∥ x ≡ᵃᵇ y ∥₂ → ∥ y ≡ᵃᵇ x ∥₂
-πᵃᵇ = ST.map symᵃᵇ

reflᵃᵇ : ∀ {ℓ} {A : Type ℓ} {x : A} → x ≡ᵃᵇ x
reflᵃᵇ = paths refl

-- Group laws
·πᵃᵇrUnit : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : ∥ x ≡ᵃᵇ y ∥₂)
  → ·πᵃᵇ p ∣ reflᵃᵇ ∣₂ ≡ p
·πᵃᵇrUnit = ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
  λ p → cong ∣_∣₂ (cong paths (sym (rUnit _))))

·πᵃᵇlUnit : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : ∥ x ≡ᵃᵇ y ∥₂)
  → ·πᵃᵇ ∣ reflᵃᵇ ∣₂ p ≡ p
·πᵃᵇlUnit = ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
  λ p → cong ∣_∣₂ (cong paths (sym (lUnit _))))

·πᵃᵇrCancel : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : ∥ x ≡ᵃᵇ y ∥₂)
  → ·πᵃᵇ p (-πᵃᵇ p) ≡ ∣ reflᵃᵇ ∣₂
·πᵃᵇrCancel = ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
  λ p → cong ∣_∣₂ (cong paths (rCancel _)))

·πᵃᵇlCancel : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : ∥ x ≡ᵃᵇ y ∥₂)
  → ·πᵃᵇ (-πᵃᵇ p) p ≡ ∣ reflᵃᵇ ∣₂
·πᵃᵇlCancel = ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
  λ p → cong ∣_∣₂ (cong paths (lCancel _)))

·πᵃᵇassoc : ∀ {ℓ} {A : Type ℓ} {x : A} (p q r : ∥ x ≡ᵃᵇ x ∥₂)
  → ·πᵃᵇ p (·πᵃᵇ q r)  ≡ ·πᵃᵇ (·πᵃᵇ p q) r
·πᵃᵇassoc = ST.elim3 (λ _ _ _ → isSetPathImplicit)
  (elimProp≡ᵃᵇ (λ _ → isPropΠ2 λ _ _ → squash₂ _ _)
   λ p → elimProp≡ᵃᵇ (λ _ → isPropΠ λ _ → squash₂ _ _)
     λ q → elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
       λ r → cong ∣_∣₂ (cong paths (GLaws.assoc p q r)))

·πᵃᵇcomm : ∀ {ℓ} {A : Type ℓ} {x : A} (p q : ∥ x ≡ᵃᵇ x ∥₂) → ·πᵃᵇ p q ≡ ·πᵃᵇ q p
·πᵃᵇcomm = ST.elim2 (λ _ _ → isSetPathImplicit)
  (elimProp≡ᵃᵇ (λ _ → isPropΠ (λ _ → squash₂ _ _))
    λ p → elimProp≡ᵃᵇ (λ _ → squash₂ _ _) λ q
      → cong ∣_∣₂ (cong paths (cong₂ _∙_ refl (lUnit q))
                 ∙ com p refl q
                 ∙ cong paths (cong₂ _∙_ refl (sym (lUnit p)))))

π₁ᵃᵇAbGroup : ∀ {ℓ} (A : Pointed ℓ) → AbGroup ℓ
fst (π₁ᵃᵇAbGroup (A , a)) = ∥ a ≡ᵃᵇ a ∥₂
0g (snd (π₁ᵃᵇAbGroup A)) = ∣ reflᵃᵇ ∣₂
_+_ (snd (π₁ᵃᵇAbGroup A)) = ·πᵃᵇ
- snd (π₁ᵃᵇAbGroup A) = -πᵃᵇ
is-set (isSemigroup (isMonoid (isGroup (isAbGroup (snd (π₁ᵃᵇAbGroup A)))))) = squash₂
IsSemigroup.·Assoc (isSemigroup (isMonoid (isGroup (isAbGroup (snd (π₁ᵃᵇAbGroup A)))))) =
  ·πᵃᵇassoc
IsMonoid.·IdR (isMonoid (isGroup (isAbGroup (snd (π₁ᵃᵇAbGroup A))))) = ·πᵃᵇrUnit
IsMonoid.·IdL (isMonoid (isGroup (isAbGroup (snd (π₁ᵃᵇAbGroup A))))) = ·πᵃᵇlUnit
·InvR (isGroup (isAbGroup (snd (π₁ᵃᵇAbGroup A)))) = ·πᵃᵇrCancel
·InvL (isGroup (isAbGroup (snd (π₁ᵃᵇAbGroup A)))) = ·πᵃᵇlCancel
IsAbGroup.+Comm (isAbGroup (snd (π₁ᵃᵇAbGroup A))) = ·πᵃᵇcomm

-πᵃᵇinvDistr : ∀ {ℓ} {A : Pointed ℓ} (p q : ∥ Ωᵃᵇ A ∥₂)
  → -πᵃᵇ {x = pt A} (·πᵃᵇ p q) ≡ ·πᵃᵇ (-πᵃᵇ p) (-πᵃᵇ q)
-πᵃᵇinvDistr {A = A} p q =
  GroupTheory.invDistr (AbGroup→Group (π₁ᵃᵇAbGroup A)) p q
  ∙ ·πᵃᵇcomm (-πᵃᵇ q) (-πᵃᵇ p)

Ωᵃᵇ→Abelianizeπ₁ : ∀ {ℓ} {A : Pointed ℓ} →  Ωᵃᵇ A → Abelianization (πGr 0 A)
Ωᵃᵇ→Abelianizeπ₁ (paths x) = η ∣ x ∣₂
Ωᵃᵇ→Abelianizeπ₁ {A = A} (com p q r i) = help i
  where
  open AbelianizationGroupStructure (πGr 0 A)
  help : Path (Abelianization (πGr 0 A))
              (η (·π 0 ∣ p ∣₂ (·π 0 ∣ sym q ∣₂ ∣ r ∣₂)))
              (η (·π 0 ∣ r ∣₂ (·π 0 ∣ sym q ∣₂ ∣ p ∣₂)))
  help = commAb (η ∣ p ∣₂) (η (·π 0 ∣ sym q ∣₂ ∣ r ∣₂))
       ∙ cong (_·Ab η ∣ p ∣₂) (commAb (η ∣ sym q ∣₂) (η ∣ r ∣₂))
       ∙ sym (assocAb (η ∣ r ∣₂) (η ∣ sym q ∣₂) (η ∣ p ∣₂))

π₁ᵃᵇ→Abelianizeπ₁ : ∀ {ℓ} {A : Pointed ℓ}
  → ∥ Ωᵃᵇ A ∥₂ → Abelianization (πGr 0 A)
π₁ᵃᵇ→Abelianizeπ₁ = ST.rec isset Ωᵃᵇ→Abelianizeπ₁

π₁→π₁ᵃᵇHom : ∀ {ℓ} {A : Pointed ℓ}
  → GroupHom (πGr 0 A) (AbGroup→Group (π₁ᵃᵇAbGroup A))
fst π₁→π₁ᵃᵇHom = ST.map paths
snd π₁→π₁ᵃᵇHom =
  makeIsGroupHom (ST.elim2 (λ _ _ → isSetPathImplicit) λ p q → refl)

-- Below definition is verbose to speed up type checking
Abelianizeπ₁→π₁ᵃᵇ : ∀ {ℓ} {A : Pointed ℓ}
  → AbGroupHom (AbelianizationAbGroup (πGr 0 A)) (π₁ᵃᵇAbGroup A)
fst (Abelianizeπ₁→π₁ᵃᵇ {A = A}) =
  fst (fromAbelianization (π₁ᵃᵇAbGroup A) π₁→π₁ᵃᵇHom)
snd (Abelianizeπ₁→π₁ᵃᵇ {A = A}) =
  makeIsGroupHom (elimProp2 _ (λ _ _ → squash₂ _ _ )
    (ST.elim2 (λ _ _ → isSetPathImplicit)
      λ f g → refl))

Abelianizeπ₁≅π₁ᵃᵇ : ∀ {ℓ} (A : Pointed ℓ)
  → AbGroupIso (AbelianizationAbGroup (πGr 0 A)) (π₁ᵃᵇAbGroup A)
Iso.fun (fst (Abelianizeπ₁≅π₁ᵃᵇ A)) = fst Abelianizeπ₁→π₁ᵃᵇ
Iso.inv (fst (Abelianizeπ₁≅π₁ᵃᵇ A)) = π₁ᵃᵇ→Abelianizeπ₁
Iso.rightInv (fst (Abelianizeπ₁≅π₁ᵃᵇ A)) =
  ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _) λ p → refl)
Iso.leftInv (fst (Abelianizeπ₁≅π₁ᵃᵇ A)) = Abi.elimProp _ (λ _ → isset _ _)
  (ST.elim (λ _ → isOfHLevelPath 2 isset _ _) λ p → refl)
snd (Abelianizeπ₁≅π₁ᵃᵇ A) = Abelianizeπ₁→π₁ᵃᵇ {A = A} .snd
