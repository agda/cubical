{-

Half adjoint equivalences ([HAEquiv])

- Iso to HAEquiv ([iso→HAEquiv])
- Equiv to HAEquiv ([equiv→HAEquiv])
- Cong is an equivalence ([congEquiv])

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Equiv.HalfAdjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

record isHAEquiv {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    g : B → A
    linv : ∀ a → g (f a) ≡ a
    rinv : ∀ b → f (g b) ≡ b
    com : ∀ a → cong f (linv a) ≡ rinv (f a)

  -- from redtt's ha-equiv/symm
  com-op : ∀ b → cong g (rinv b) ≡ linv (g b)
  com-op b j i = hcomp (λ k → λ { (i = i0) → linv (g b) (j ∧ (~ k))
                                ; (j = i0) → g (rinv b i)
                                ; (j = i1) → linv (g b) (i ∨ (~ k))
                                ; (i = i1) → g b })
                       (cap1 j i)

    where cap0 : Square {- (j = i0) -} (λ i → f (g (rinv b i)))
                        {- (j = i1) -} (λ i → rinv b i)
                        {- (i = i0) -} (λ j → f (linv (g b) j))
                        {- (i = i1) -} (λ j → rinv b j)

          cap0 j i = hcomp (λ k → λ { (i = i0) → com (g b) (~ k) j
                                    ; (j = i0) → f (g (rinv b i))
                                    ; (j = i1) → rinv b i
                                    ; (i = i1) → rinv b j })
                           (rinv (rinv b i) j)

          filler : I → I → A
          filler j i = hfill (λ k → λ { (i = i0) → g (rinv b k)
                                      ; (i = i1) → g b })
                             (inS (linv (g b) i)) j

          cap1 : Square {- (j = i0) -} (λ i → g (rinv b i))
                        {- (j = i1) -} (λ i → g b)
                        {- (i = i0) -} (λ j → linv (g b) j)
                        {- (i = i1) -} (λ j → g b)

          cap1 j i = hcomp (λ k → λ { (i = i0) → linv (linv (g b) j) k
                                    ; (j = i0) → linv (g (rinv b i)) k
                                    ; (j = i1) → filler i k
                                    ; (i = i1) → filler j k })
                           (g (cap0 j i))

  isHAEquiv→Iso : Iso A B
  Iso.fun isHAEquiv→Iso = f
  Iso.inv isHAEquiv→Iso = g
  Iso.rightInv isHAEquiv→Iso = rinv
  Iso.leftInv isHAEquiv→Iso = linv

  isHAEquiv→isEquiv : isEquiv f
  isHAEquiv→isEquiv .equiv-proof y = (g y , rinv y) , isCenter where
    isCenter : ∀ xp → (g y , rinv y) ≡ xp
    isCenter (x , p) i = gy≡x i , ry≡p i where
      gy≡x : g y ≡ x
      gy≡x = sym (cong g p) ∙∙ refl ∙∙ linv x

      lem0 : Square (cong f (linv x)) p (cong f (linv x)) p
      lem0 i j = invSides-filler p (sym (cong f (linv x))) (~ i) j

      ry≡p : Square (rinv y) p (cong f gy≡x) refl
      ry≡p i j = hcomp (λ k → λ { (i = i0) → cong rinv p k j
                                ; (i = i1) → lem0 k j
                                ; (j = i0) → f (doubleCompPath-filler (sym (cong g p)) refl (linv x) k i)
                                ; (j = i1) → p k })
                       (com x (~ i) j)

open isHAEquiv using (isHAEquiv→Iso; isHAEquiv→isEquiv) public

HAEquiv : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
HAEquiv A B = Σ[ f ∈ (A → B) ] isHAEquiv f

-- vogt's lemma (https://ncatlab.org/nlab/show/homotopy+equivalence#vogts_lemma)
iso→HAEquiv : Iso A B → HAEquiv A B
iso→HAEquiv e = f , isHAEquivf
  where
    f = Iso.fun e
    g = Iso.inv e
    ε = Iso.rightInv e
    η = Iso.leftInv e

    Hfa≡fHa : (f : A → A) → (H : ∀ a → f a ≡ a) → ∀ a → H (f a) ≡ cong f (H a)
    Hfa≡fHa f H = J (λ f p → ∀ a → funExt⁻ (sym p) (f a) ≡ cong f (funExt⁻ (sym p) a))
                    (λ a → refl)
                    (sym (funExt H))

    isHAEquivf : isHAEquiv f
    isHAEquiv.g isHAEquivf         = g
    isHAEquiv.linv isHAEquivf       = η
    isHAEquiv.rinv isHAEquivf b i   =
      hcomp (λ j → λ { (i = i0) → ε (f (g b)) j
                     ; (i = i1) → ε b j })
            (f (η (g b) i))
    isHAEquiv.com isHAEquivf a i j =
      hcomp (λ k → λ { (i = i0) → ε (f (η a j)) k
                     ; (j = i0) → ε (f (g (f a))) k
                     ; (j = i1) → ε (f a) k})
            (f (Hfa≡fHa (λ x → g (f x)) η a (~ i) j))

equiv→HAEquiv : A ≃ B → HAEquiv A B
equiv→HAEquiv e = e .fst , λ where
  .isHAEquiv.g → invIsEq (snd e)
  .isHAEquiv.linv → retIsEq (snd e)
  .isHAEquiv.rinv → secIsEq (snd e)
  .isHAEquiv.com a → flipSquare (slideSquare (commSqIsEq (snd e) a))

congIso : {x y : A} (e : Iso A B) → Iso (x ≡ y) (Iso.fun e x ≡ Iso.fun e y)
congIso {x = x} {y} e = goal
  where
  open isHAEquiv (iso→HAEquiv e .snd)
  open Iso

  goal : Iso (x ≡ y) (Iso.fun e x ≡ Iso.fun e y)
  fun goal   = cong (iso→HAEquiv e .fst)
  inv goal p = sym (linv x) ∙∙ cong g p ∙∙ linv y
  rightInv goal p i j =
    hcomp (λ k → λ { (i = i0) → iso→HAEquiv e .fst
                                  (doubleCompPath-filler (sym (linv x)) (cong g p) (linv y) k j)
                   ; (i = i1) → rinv (p j) k
                   ; (j = i0) → com x i k
                   ; (j = i1) → com y i k })
          (iso→HAEquiv e .fst (g (p j)))
  leftInv goal p i j =
    hcomp (λ k → λ { (i = i1) → p j
                   ; (j = i0) → Iso.leftInv e x (i ∨ k)
                   ; (j = i1) → Iso.leftInv e y (i ∨ k) })
          (Iso.leftInv e (p j) i)

invCongFunct : {x : A} (e : Iso A B) (p : Iso.fun e x ≡ Iso.fun e x) (q : Iso.fun e x ≡ Iso.fun e x)
             → Iso.inv (congIso e) (p ∙ q) ≡ Iso.inv (congIso e) p ∙ Iso.inv (congIso e) q
invCongFunct {x = x} e p q = helper (Iso.inv e) _ _ _
  where
  helper : {x : A} {y : B} (f : A → B) (r : f x ≡ y) (p q : x ≡ x)
         → (sym r ∙∙ cong f (p ∙ q) ∙∙ r) ≡ (sym r ∙∙ cong f p ∙∙ r) ∙ (sym r ∙∙ cong f q ∙∙ r)
  helper {x = x} f =
    J (λ y r → (p q : x ≡ x)
    → (sym r ∙∙ cong f (p ∙ q) ∙∙ r) ≡ (sym r ∙∙ cong f p ∙∙ r) ∙ (sym r ∙∙ cong f q ∙∙ r))
      λ p q → (λ i → rUnit (congFunct f p q i) (~ i))
             ∙ λ i → rUnit (cong f p) i ∙ rUnit (cong f q) i
