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
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.PathSplitEquiv where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

isEquivCong : ∀ {ℓ} {A B : Type ℓ} {x y : A} (e : A ≃ B) → isEquiv (λ (p : x ≡ y) → (cong (fst e) p))
isEquivCong e = EquivJ (λ (B' A' : Type _) (e' : A' ≃ B') →
                         (x' y' : A') → isEquiv (λ (p : x' ≡ y') → cong (fst e') p))
                       (λ _ x' y' → idIsEquiv (x' ≡ y')) _ _ e _ _

congEquiv : ∀ {ℓ} {A B : Type ℓ} {x y : A} (e : A ≃ B) → (x ≡ y) ≃ (e .fst x ≡ e .fst y)
congEquiv e = ((λ (p : _ ≡ _) → cong (fst e) p) , isEquivCong e)

isEquivPreComp : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : Type ℓ′} (e : A ≃ B)
  → isEquiv (λ (φ : B → C) → φ ∘ e .fst)
isEquivPreComp {A = A} {C = C} e = EquivJ
                  (λ (B A : Type _) (e' : A ≃ B) → isEquiv (λ (φ : B → C) → φ ∘ e' .fst))
                  (λ A → idIsEquiv (A → C)) _ _ e

isEquivPostComp : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : Type ℓ′} (e : A ≃ B)
  → isEquiv (λ (φ : C → A) → e .fst ∘ φ)
isEquivPostComp {A = A} {C = C} e = EquivJ
                  (λ (B A : Type _) (e' : A ≃ B) →  isEquiv (λ (φ : C → A) → e' .fst ∘ φ))
                  (λ A → idIsEquiv (C → A)) _ _ e

preCompEquiv : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : Type ℓ′} (e : A ≃ B)
             → (B → C) ≃ (A → C)
preCompEquiv e = (λ φ x → φ (fst e x)) , isEquivPreComp e

postCompEquiv : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : Type ℓ′} (e : A ≃ B)
             → (C → A) ≃ (C → B)
postCompEquiv e = (λ φ x → fst e (φ x)) , isEquivPostComp e



record isPathSplitEquiv {ℓ ℓ'} {A : Type  ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    s : B → A
    sec : section f s
    secCong : (x y : A) → Σ[ s' ∈ (f(x) ≡ f(y) → x ≡ y) ] section (cong f) s'

PathSplitEquiv : ∀ {ℓ ℓ'} (A : Type  ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
PathSplitEquiv A B = Σ[ f ∈ (A → B) ] isPathSplitEquiv f

open isPathSplitEquiv

idIsPathSplitEquiv : ∀ {ℓ} {A : Type ℓ} → isPathSplitEquiv (λ (x : A) → x)
s idIsPathSplitEquiv x = x
sec idIsPathSplitEquiv x = refl
secCong idIsPathSplitEquiv = λ x y → (λ p → p) , λ p _ → p

module _ {ℓ} {A B : Type ℓ} where
  toIsEquiv : (f : A → B) → isPathSplitEquiv f → isEquiv f
  toIsEquiv f record { s = s ; sec = sec ; secCong = secCong } =
    (isoToEquiv (iso f s sec (λ x → (secCong (s (f x)) x).fst (sec (f x))))) .snd

  sectionOfEquiv' : (f : A → B) → isEquiv f → B → A
  sectionOfEquiv' f record { equiv-proof = all-fibers-contractible } x =
    all-fibers-contractible x .fst .fst

  isSec : (f : A → B) → (pf : isEquiv f) → section f (sectionOfEquiv' f pf)
  isSec f record { equiv-proof = all-fibers-contractible } x =
    all-fibers-contractible x .fst .snd

  sectionOfEquiv : (f : A → B) → isEquiv f → Σ (B → A) (section f)
  sectionOfEquiv f e = sectionOfEquiv' f e , isSec f e

module _ {ℓ} {A B : Type ℓ} where
  abstract
    fromIsEquiv : (f : A → B) → isEquiv f → isPathSplitEquiv f
    s (fromIsEquiv f pf) = sectionOfEquiv' f pf
    sec (fromIsEquiv f pf) = isSec f pf
    secCong (fromIsEquiv f pf) x y = sectionOfEquiv cong-f eq-cong
            where
            cong-f : x ≡ y → f x ≡ f y
            cong-f = λ (p : x ≡ y) → cong f p
            eq-cong : isEquiv cong-f
            eq-cong = isEquivCong (f , pf)

  pathSplitToEquiv : PathSplitEquiv A B → A ≃ B
  fst (pathSplitToEquiv (f , _)) = f
  snd (pathSplitToEquiv (_ , e)) = toIsEquiv _ e

  equivToPathSplit : A ≃ B → PathSplitEquiv A B
  fst (equivToPathSplit (f , _)) = f
  snd (equivToPathSplit (_ , e)) = fromIsEquiv _ e

  equivHasUniqueSection : (f : A → B)
    → isEquiv f → isContr (Σ (B → A) (section f))
  equivHasUniqueSection f eq = helper'
    where
      idB = λ (x : B) → x
      abstract
        helper : isContr (fiber (λ (φ : B → A) → f ∘ φ) idB)
        helper = (equiv-proof (snd (postCompEquiv (f , eq)))) idB
      helper' : isContr (Σ[ φ ∈ (B → A) ] ((x : B) → f (φ x) ≡ x))
      fst helper' = (φ , λ x i → η i x)
        where φ = fst (fst helper)
              η : f ∘ φ ≡ idB
              η = snd (fst helper)
      (snd helper') y i = (fst (η i) , λ b j → snd (η i) j b)
        where η = (snd helper) (fst y , λ i b → snd y b i)

{-
  PathSplitEquiv is a proposition and the type
  of path split equivs is equivalent to the type of equivalences
-}
isPropIsPathSplitEquiv : ∀ {ℓ} {A B : Type ℓ} (f : A → B)
     → isProp (isPathSplitEquiv f)
isPropIsPathSplitEquiv {_} {A} {B} f
  record { s = φ ; sec = sec-φ ; secCong = secCong-φ }
  record { s = ψ ; sec = sec-ψ ; secCong = secCong-ψ } i
  =
  record {
    s = fst (sectionsAreEqual i) ;
    sec = snd (sectionsAreEqual i) ;
    secCong = λ x y → congSectionsAreEqual x y (secCong-φ x y) (secCong-ψ x y) i
  }
  where
    φ' = record { s = φ ; sec = sec-φ ; secCong = secCong-φ }
    ψ' = record { s = ψ ; sec = sec-ψ ; secCong = secCong-ψ }
    sectionsAreEqual : (φ , sec-φ) ≡ (ψ , sec-ψ)
    sectionsAreEqual = (sym (contraction (φ , sec-φ))) ∙ (contraction  (ψ , sec-ψ))
      where contraction = snd (equivHasUniqueSection f (toIsEquiv f φ'))
    congSectionsAreEqual : (x y : A) (l u : Σ (f(x) ≡ f(y) → x ≡ y) (section (cong f))) → l ≡ u
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
