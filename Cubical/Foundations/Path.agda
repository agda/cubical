{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Reflection.StrictEquiv

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

-- Less polymorphic version of `cong`, to avoid some unresolved metas
cong′ : ∀ {B : Type ℓ'} (f : A → B) {x y : A} (p : x ≡ y)
      → Path B (f x) (f y)
cong′ f = cong f
{-# INLINE cong′ #-}

PathP≡Path : ∀ (P : I → Type ℓ) (p : P i0) (q : P i1) →
             PathP P p q ≡ Path (P i1) (transport (λ i → P i) p) q
PathP≡Path P p q i = PathP (λ j → P (i ∨ j)) (transport-filler (λ j → P j) p i) q

PathP≡Path⁻ : ∀ (P : I → Type ℓ) (p : P i0) (q : P i1) →
             PathP P p q ≡ Path (P i0) p (transport⁻ (λ i → P i) q)
PathP≡Path⁻ P p q i = PathP (λ j → P (~ i ∧ j)) p (transport⁻-filler (λ j → P j) q i)

PathP≃Path : ∀ (P : I → Type ℓ) (p : P i0) (q : P i1) →
             PathP P p q ≃ Path (P i1) (transport (λ i → P i) p) q
PathP≃Path P p q = transportEquiv (PathP≡Path P p q)

-- Alternative more unfolded proof
toPathP-isEquiv : ∀ (A : I → Type ℓ) {x y} → isEquiv (toPathP {A = A} {x} {y})
toPathP-isEquiv A {x} {y} = isoToIsEquiv (iso toPathP fromPathP to-from from-to)
 where
   to-from : ∀ (p : PathP A x y) → toPathP (fromPathP p) ≡ p
   to-from p h i = outS (hcomp-unique (λ { j (i = i0) → x ; j (i = i1) → fromPathP p j })
                                  (inS (transp (λ j → A (i ∧ j)) (~ i) x))
                                  \ h → inS (sq1 h i))
                        h
      where
        sq1 : (\ h → A [ x ≡ transp (\ j → A (h ∨ j)) h (p h) ]) [ (\ i → transp (λ j → A (i ∧ j)) (~ i) x) ≡ p ]
        sq1 = \ h i → comp (\ z → (hcomp (\ w →
                                                    \ { (z = i1) → A (i ∧ (w ∨ h))
                                                      ; (z = i0) → A (i ∧ h)
                                                      ; (i = i0) → A i0
                                                      ; (i = i1) → A (h ∨ (w ∧ z))
                                                      ; (h = i0) → A (i ∧ (w ∧ z))
                                                      ; (h = i1) → A i})
                                                   ((A (i ∧ h)))))
                                          (\ z → \ { (i = i0) → x
                                                   ; (i = i1) → transp (\ j → A (h ∨ (z ∧ j))) (h ∨ ~ z) (p h)
                                                   ; (h = i0) → transp (λ j → A ((i ∧ z) ∧ j)) (~ (i ∧ z)) x
                                                   ; (h = i1) → p i })
                                (p (i ∧ h))
   from-to : ∀ (q : transp (\ i → A i) i0 x ≡ y) → fromPathP (toPathP {A = A} q) ≡ q
   from-to q = (\ h i → outS (transp-hcomp i {A' = A i1} (\ j → inS (A (i ∨ j)))
                                           ((λ { j (i = i0) → x ; j (i = i1) → q j }))
                                           (inS ((transp (λ j → A (i ∧ j)) (~ i) x))))
                             h)
             ∙ (\ h i → outS (hcomp-unique {A = A i1} ((λ { j (i = i0) → transp (\ i → A i) i0 x ; j (i = i1) → q j }))
                                      (inS ((transp (λ j → A (i ∨ j)) i (transp (λ j → A (i ∧ j)) (~ i) x))))
                                      \ h → inS (sq2 h i))
                             h)
             ∙ sym (lUnit q)
     where
       sq2 : (\ h → transp (\ i → A i) i0 x ≡ q h) [ (\ i → transp (\ j → A (i ∨ j)) i (transp (\ j → A (i ∧ j)) (~ i) x)) ≡ refl ∙ q ]
       sq2 = \ h i → comp (\ z → hcomp (\ w → \ { (i = i1) → A i1
                                              ; (i = i0) → A (h ∨ (w ∧ z))
                                              ; (h = i0) → A (i ∨ (w ∧ z))
                                              ; (h = i1) → A i1
                                              ; (z = i0) → A (i ∨ h)
                                              ; (z = i1) → A ((i ∨ h) ∨ w) })
                                             (A (i ∨ h)))
                 (\ z → \ { (i = i0) → transp (λ j → A ((z ∨ h) ∧ j)) (~ z ∧ ~ h) x
                          ; (i = i1) → q (z ∧ h)
                          ; (h = i1) → compPath-filler refl q z i
                          ; (h = i0) → transp (\ j → A (i ∨ (z ∧ j))) (i ∨ ~ z) (transp (\ j → A (i ∧ j)) (~ i) x)
                          })
                          (transp (\ j → A ((i ∨ h) ∧ j)) (~ (i ∨ h)) x)

PathP≡compPath : ∀ {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
                 → (PathP (λ i → x ≡ q i) p r) ≡ (p ∙ q ≡ r)
PathP≡compPath p q r k = PathP (λ i → p i0 ≡ q (i ∨ k)) (λ j → compPath-filler p q k j) r

PathP≡doubleCompPathˡ : ∀ {A : Type ℓ} {w x y z : A} (p : w ≡ y) (q : w ≡ x) (r : y ≡ z) (s : x ≡ z)
                        → (PathP (λ i → p i ≡ s i) q r) ≡ (p ⁻¹ ∙∙ q ∙∙ s ≡ r)
PathP≡doubleCompPathˡ p q r s k = PathP (λ i → p (i ∨ k) ≡ s (i ∨ k))
                                        (λ j → doubleCompPath-filler (p ⁻¹) q s k j) r

PathP≡doubleCompPathʳ : ∀ {A : Type ℓ} {w x y z : A} (p : w ≡ y) (q : w ≡ x) (r : y ≡ z) (s : x ≡ z)
                        → (PathP (λ i → p i ≡ s i) q r) ≡ (q ≡ p ∙∙ r ∙∙ s ⁻¹)
PathP≡doubleCompPathʳ p q r s k  = PathP (λ i → p (i ∧ (~ k)) ≡ s (i ∧ (~ k)))
                                         q (λ j → doubleCompPath-filler p r (s ⁻¹) k j)

compPathl-cancel : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → p ∙ (sym p ∙ q) ≡ q
compPathl-cancel p q = p ∙ (sym p ∙ q) ≡⟨ assoc p (sym p) q ⟩
                       (p ∙ sym p) ∙ q ≡⟨ cong (_∙ q) (rCancel p) ⟩
                              refl ∙ q ≡⟨ sym (lUnit q) ⟩
                                     q ∎

compPathr-cancel : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : z ≡ y) (q : x ≡ y) → (q ∙ sym p) ∙ p ≡ q
compPathr-cancel {x = x} p q i j =
  hcomp-equivFiller (doubleComp-faces (λ _ → x) (sym p) j) (inS (q j)) (~ i)

compPathl-isEquiv : {x y z : A} (p : x ≡ y) → isEquiv (λ (q : y ≡ z) → p ∙ q)
compPathl-isEquiv p = isoToIsEquiv (iso (p ∙_) (sym p ∙_) (compPathl-cancel p) (compPathl-cancel (sym p)))

compPathlEquiv : {x y z : A} (p : x ≡ y) → (y ≡ z) ≃ (x ≡ z)
compPathlEquiv p = (p ∙_) , compPathl-isEquiv p

compPathr-isEquiv : {x y z : A} (p : y ≡ z) → isEquiv (λ (q : x ≡ y) → q ∙ p)
compPathr-isEquiv p = isoToIsEquiv (iso (_∙ p) (_∙ sym p) (compPathr-cancel p) (compPathr-cancel (sym p)))

compPathrEquiv : {x y z : A} (p : y ≡ z) → (x ≡ y) ≃ (x ≡ z)
compPathrEquiv p = (_∙ p) , compPathr-isEquiv p

-- Variations of isProp→isSet for PathP
isProp→SquareP : ∀ {B : I → I → Type ℓ} → ((i j : I) → isProp (B i j))
             → {a : B i0 i0} {b : B i0 i1} {c : B i1 i0} {d : B i1 i1}
             → (r : PathP (λ j → B j i0) a c) (s : PathP (λ j → B j i1) b d)
             → (t : PathP (λ j → B i0 j) a b) (u : PathP (λ j → B i1 j) c d)
             → SquareP B t u r s
isProp→SquareP {B = B} isPropB {a = a} r s t u i j =
  hcomp (λ { k (i = i0) → isPropB i0 j (base i0 j) (t j) k
           ; k (i = i1) → isPropB i1 j (base i1 j) (u j) k
           ; k (j = i0) → isPropB i i0 (base i i0) (r i) k
           ; k (j = i1) → isPropB i i1 (base i i1) (s i) k
        }) (base i j) where
    base : (i j : I) → B i j
    base i j = transport (λ k → B (i ∧ k) (j ∧ k)) a

isProp→isPropPathP : ∀ {ℓ} {B : I → Type ℓ} → ((i : I) → isProp (B i))
                   → (b0 : B i0) (b1 : B i1)
                   → isProp (PathP (λ i → B i) b0 b1)
isProp→isPropPathP {B = B} hB b0 b1 = isProp→SquareP (λ _ → hB) refl refl

isProp→isContrPathP : {A : I → Type ℓ} → (∀ i → isProp (A i))
                    → (x : A i0) (y : A i1)
                    → isContr (PathP A x y)
isProp→isContrPathP h x y = isProp→PathP h x y , isProp→isPropPathP h x y _

-- Flipping a square along its diagonal

flipSquare : {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  → Square a₀₋ a₁₋ a₋₀ a₋₁ → Square a₋₀ a₋₁ a₀₋ a₁₋
flipSquare sq i j = sq j i

module _ {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁} {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  where

  flipSquareEquiv : Square a₀₋ a₁₋ a₋₀ a₋₁ ≃ Square a₋₀ a₋₁ a₀₋ a₁₋
  unquoteDef flipSquareEquiv = defStrictEquiv flipSquareEquiv flipSquare flipSquare

  flipSquarePath : Square a₀₋ a₁₋ a₋₀ a₋₁ ≡ Square a₋₀ a₋₁ a₀₋ a₁₋
  flipSquarePath = ua flipSquareEquiv

module _ {a₀₀ a₁₁ : A} {a₋ : a₀₀ ≡ a₁₁}
  {a₁₀ : A} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₀ : a₀₀ ≡ a₁₀} where

  slideSquareFaces : (i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A
  slideSquareFaces i j k (i = i0) = a₋ (j ∧ ~ k)
  slideSquareFaces i j k (i = i1) = a₁₋ j
  slideSquareFaces i j k (j = i0) = a₋₀ i
  slideSquareFaces i j k (j = i1) = a₋ (i ∨ ~ k)

  slideSquare : Square a₋ a₁₋ a₋₀ refl → Square refl a₁₋ a₋₀ a₋
  slideSquare sq i j = hcomp (slideSquareFaces i j) (sq i j)

  slideSquareEquiv : (Square a₋ a₁₋ a₋₀ refl) ≃ (Square refl a₁₋ a₋₀ a₋)
  slideSquareEquiv = isoToEquiv (iso slideSquare slideSquareInv fillerTo fillerFrom) where
    slideSquareInv : Square refl a₁₋ a₋₀ a₋ → Square a₋ a₁₋ a₋₀ refl
    slideSquareInv sq i j = hcomp (λ k → slideSquareFaces i j (~ k)) (sq i j)
    fillerTo : ∀ p → slideSquare (slideSquareInv p) ≡ p
    fillerTo p k i j = hcomp-equivFiller (λ k → slideSquareFaces i j (~ k)) (inS (p i j)) (~ k)
    fillerFrom : ∀ p → slideSquareInv (slideSquare p) ≡ p
    fillerFrom p k i j = hcomp-equivFiller (slideSquareFaces i j) (inS (p i j)) (~ k)

-- The type of fillers of a square is equivalent to the double composition identites
Square≃doubleComp : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
                    (a₀₋ : a₀₀ ≡ a₀₁) (a₁₋ : a₁₀ ≡ a₁₁)
                    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
                    → Square a₀₋ a₁₋ a₋₀ a₋₁ ≃ (a₋₀ ⁻¹ ∙∙ a₀₋ ∙∙ a₋₁ ≡ a₁₋)
Square≃doubleComp a₀₋ a₁₋ a₋₀ a₋₁ = transportEquiv (PathP≡doubleCompPathˡ a₋₀ a₀₋ a₁₋ a₋₁)

-- sym induces an equivalence on identity types of paths
symIso : {a b : A} (p q : a ≡ b) → Iso (p ≡ q) (q ≡ p)
symIso p q = iso sym sym (λ _ → refl) λ _ → refl

private
  mx : Type ℓ → Type ℓ' → Level
  mx {ℓ} {ℓ'} _ _ = ℓ-max ℓ ℓ'

record Reveal_·_is_ (f : A → B) (x : A) (y : B) : Type (mx A B) where
  constructor [_]ᵢ
  field path : f x ≡ y

inspect : (f : A → B) (x : A) → Reveal f · x is f x
inspect f x .Reveal_·_is_.path = refl
