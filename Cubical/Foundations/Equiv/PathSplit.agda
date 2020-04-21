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
module Cubical.Foundations.Equiv.PathSplit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Foundations.Equiv.Properties

record isPathSplitEquiv {ℓ ℓ'} {A : Type  ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    sec : hasSection f
    secCong : (x y : A) → hasSection (λ (p : x ≡ y) → cong f p)

PathSplitEquiv : ∀ {ℓ ℓ'} (A : Type  ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
PathSplitEquiv A B = Σ[ f ∈ (A → B) ] isPathSplitEquiv f

open isPathSplitEquiv

idIsPathSplitEquiv : ∀ {ℓ} {A : Type ℓ} → isPathSplitEquiv (λ (x : A) → x)
sec idIsPathSplitEquiv = (λ x → x) , (λ x → refl)
secCong idIsPathSplitEquiv = λ x y → (λ p → p) , λ p _ → p

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  toIsEquiv : (f : A → B) → isPathSplitEquiv f → isEquiv f
  toIsEquiv f record { sec = sec ; secCong = secCong } =
    (isoToEquiv (iso f (fst sec) (snd sec) (λ x → (secCong (fst sec (f x)) x).fst (snd sec (f x))))) .snd

  sectionOfEquiv' : (f : A → B) → isEquiv f → B → A
  sectionOfEquiv' f isEqv x =
    let all-fibers-contractible = isEqv .equiv-proof
    in  all-fibers-contractible x .fst .fst

  isSec : (f : A → B) → (pf : isEquiv f) → section f (sectionOfEquiv' f pf)
  isSec f isEqv x =
    let all-fibers-contractible = isEqv .equiv-proof
    in  all-fibers-contractible x .fst .snd

  sectionOfEquiv : (f : A → B) → isEquiv f → hasSection f
  sectionOfEquiv f e = sectionOfEquiv' f e , isSec f e

module _ {ℓ} {A B : Type ℓ} where
  abstract
    fromIsEquiv : (f : A → B) → isEquiv f → isPathSplitEquiv f
    sec (fromIsEquiv f pf) = sectionOfEquiv' f pf , isSec f pf
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
