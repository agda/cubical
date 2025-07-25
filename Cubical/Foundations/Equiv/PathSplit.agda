{-

Theory about path split equivalences.
They are convenient to construct localization HITs as in
(the "modalities paper")
https://arxiv.org/abs/1706.07526

- there are construction from and to equivalences ([pathSplitToEquiv] , [equivToPathSplit])
- the structure of a path split equivalence is actually a proposition ([isPropIsPathSplitEquiv])

The module starts with a couple of general facts about equivalences:

- if f is an equivalence then (cong f) is an equivalence ([equivCong])
- if f is an equivalence then pre- and postcomposition with f are equivalences ([preCompEquiv], [postCompEquiv])

(those are not in 'Equiv.agda' because they need Univalence.agda (which imports Equiv.agda))
-}
module Cubical.Foundations.Equiv.PathSplit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Foundations.Equiv.Properties

open import Cubical.Data.Sigma

record isPathSplitEquiv {ℓ ℓ'} {A : Type  ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    sec : hasSection f
    secCong : (x y : A) → hasSection (λ (p : x ≡ y) → cong f p)

PathSplitEquiv : ∀ {ℓ ℓ'} (A : Type  ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
PathSplitEquiv A B = Σ[ f ∈ (A → B) ] isPathSplitEquiv f

open isPathSplitEquiv

idIsPathSplitEquiv : ∀ {ℓ} {A : Type ℓ} → isPathSplitEquiv (λ (x : A) → x)
sec idIsPathSplitEquiv     = (λ x → x) , (λ _ → refl)
secCong idIsPathSplitEquiv = λ _ _ → (λ p → p) , λ p _ → p

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where

  open Iso

  toIso : (f : A → B) → isPathSplitEquiv f → Iso A B
  fun (toIso f _) = f
  inv (toIso _ p) = p .sec .fst
  rightInv (toIso _ p)  = p .sec .snd
  leftInv (toIso f p) x = p .secCong (p .sec .fst (f x)) x .fst (p .sec .snd (f x))

  toIsEquiv : (f : A → B) → isPathSplitEquiv f → isEquiv f
  toIsEquiv f p = isoToIsEquiv (toIso f p)

  sectionOfEquiv' : (f : A → B) → isEquiv f → B → A
  sectionOfEquiv' f isEqv x = isEqv .equiv-proof x .fst .fst

  isSec : (f : A → B) → (pf : isEquiv f) → section f (sectionOfEquiv' f pf)
  isSec f isEqv x = isEqv .equiv-proof x .fst .snd

  sectionOfEquiv : (f : A → B) → isEquiv f → hasSection f
  sectionOfEquiv f e = sectionOfEquiv' f e , isSec f e

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where

  fromIsEquiv : (f : A → B) → isEquiv f → isPathSplitEquiv f
  sec (fromIsEquiv f pf) = sectionOfEquiv' f pf , isSec f pf
  secCong (fromIsEquiv f pf) x y = sectionOfEquiv (cong f) (isEquivCong (f , pf))

  pathSplitToEquiv : PathSplitEquiv A B → A ≃ B
  fst (pathSplitToEquiv (f , _)) = f
  snd (pathSplitToEquiv (_ , e)) = toIsEquiv _ e

  equivToPathSplit : A ≃ B → PathSplitEquiv A B
  fst (equivToPathSplit (f , _)) = f
  snd (equivToPathSplit (_ , e)) = fromIsEquiv _ e

  equivHasUniqueSection : (f : A → B) → isEquiv f → ∃![ g ∈ (B → A) ] section f g
  equivHasUniqueSection f eq = helper'
    where
    helper : isContr (fiber (λ (φ : B → A) → f ∘ φ) (idfun B))
    helper = (equiv-proof (snd (postCompEquiv (f , eq)))) (idfun B)

    helper' : ∃![ φ ∈ (B → A) ] ((x : B) → f (φ x) ≡ x)
    fst helper' = (helper .fst .fst , λ x i → helper .fst .snd i x)
    snd helper' y i = (fst (η i) , λ b j → snd (η i) j b)
      where η = helper .snd (fst y , λ i b → snd y b i)

{-
  PathSplitEquiv is a proposition and the type
  of path split equivs is equivalent to the type of equivalences
-}
isPropIsPathSplitEquiv : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → isProp (isPathSplitEquiv f)
isPropIsPathSplitEquiv {A = A} {B = B} f
  record { sec = sec-φ ; secCong = secCong-φ }
  record { sec = sec-ψ ; secCong = secCong-ψ } i
  =
  record {
    sec = sectionsAreEqual i ;
    secCong = λ x y → congSectionsAreEqual x y (secCong-φ x y) (secCong-ψ x y) i
  }
  where
    φ' = record { sec = sec-φ ; secCong = secCong-φ }
    ψ' = record { sec = sec-ψ ; secCong = secCong-ψ }
    sectionsAreEqual : sec-φ ≡ sec-ψ
    sectionsAreEqual = (sym (contraction sec-φ)) ∙ (contraction  sec-ψ)
      where contraction = snd (equivHasUniqueSection f (toIsEquiv f φ'))
    congSectionsAreEqual : (x y : A) (l u : hasSection (λ (p : x ≡ y) → cong f p)) → l ≡ u
    congSectionsAreEqual x y l u = (sym (contraction l)) ∙ (contraction u)
      where contraction = snd (equivHasUniqueSection
                                 (λ (p : x ≡ y) → cong f p)
                                 (isEquivCong (pathSplitToEquiv (f , φ'))))

module _ {ℓ} {A B : Type ℓ} where
  isEquivIsPathSplitToIsEquiv : (f : A → B) → isEquiv (fromIsEquiv f)
  isEquivIsPathSplitToIsEquiv f =
    isoToIsEquiv
      (iso (fromIsEquiv f) (toIsEquiv f) (λ b → isPropIsPathSplitEquiv f _ _) (λ a → isPropIsEquiv f _ _ ))

  isEquivPathSplitToEquiv : isEquiv (pathSplitToEquiv {A = A} {B = B})
  isEquivPathSplitToEquiv =
    isoToIsEquiv
      (iso pathSplitToEquiv equivToPathSplit
        (λ {(f , e) i → (f , isPropIsEquiv f (toIsEquiv f (fromIsEquiv f e)) e i)})
        (λ {(f , e) i → (f , isPropIsPathSplitEquiv f (fromIsEquiv f (toIsEquiv f e)) e i)}))

  equivPathSplitToEquiv : (PathSplitEquiv A B) ≃ (A ≃ B)
  equivPathSplitToEquiv = (pathSplitToEquiv , isEquivPathSplitToEquiv)


secCongDep : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
             → (f : ∀ a → B a → C a) {a a' : A} (q : a ≡ a')
             → (∀ a (x y : B a) → hasSection (λ (p : x ≡ y) → cong (f a) p))
             → (∀ (x : B a) (y : B a') → hasSection (λ (p : PathP (λ i → B (q i)) x y) → cong₂ f q p))
secCongDep {B = B} f {a} p secCong
  = J (λ a' q → (x : B a) (y : B a') → hasSection (λ (p : PathP (λ i → B (q i)) x y) → cong₂ f q p))
      (secCong a) p
