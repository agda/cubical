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
    sec : ∀ a → g (f a) ≡ a
    ret : ∀ b → f (g b) ≡ b
    com : ∀ a → cong f (sec a) ≡ ret (f a)

  -- from redtt's ha-equiv/symm
  com-op : ∀ b → cong g (ret b) ≡ sec (g b)
  com-op b j i = hcomp (λ k → λ { (i = i0) → sec (g b) (j ∧ (~ k))
                                ; (j = i0) → g (ret b i)
                                ; (j = i1) → sec (g b) (i ∨ (~ k))
                                ; (i = i1) → g b })
                       (cap1 j i)

    where cap0 : Square {- (j = i0) -} (λ i → f (g (ret b i)))
                        {- (j = i1) -} (λ i → ret b i)
                        {- (i = i0) -} (λ j → f (sec (g b) j))
                        {- (i = i1) -} (λ j → ret b j)

          cap0 j i = hcomp (λ k → λ { (i = i0) → com (g b) (~ k) j
                                    ; (j = i0) → f (g (ret b i))
                                    ; (j = i1) → ret b i
                                    ; (i = i1) → ret b j })
                           (ret (ret b i) j)

          filler : I → I → A
          filler j i = hfill (λ k → λ { (i = i0) → g (ret b k)
                                      ; (i = i1) → g b })
                             (inS (sec (g b) i)) j

          cap1 : Square {- (j = i0) -} (λ i → g (ret b i))
                        {- (j = i1) -} (λ i → g b)
                        {- (i = i0) -} (λ j → sec (g b) j)
                        {- (i = i1) -} (λ j → g b)

          cap1 j i = hcomp (λ k → λ { (i = i0) → sec (sec (g b) j) k
                                    ; (j = i0) → sec (g (ret b i)) k
                                    ; (j = i1) → filler i k
                                    ; (i = i1) → filler j k })
                           (g (cap0 j i))

  isHAEquiv→Iso : Iso A B
  Iso.fun isHAEquiv→Iso = f
  Iso.inv isHAEquiv→Iso = g
  Iso.rightInv isHAEquiv→Iso = ret
  Iso.leftInv isHAEquiv→Iso = sec

  isHAEquiv→isEquiv : isEquiv f
  isHAEquiv→isEquiv .equiv-proof y = (g y , ret y) , isCenter where
    isCenter : ∀ xp → (g y , ret y) ≡ xp
    isCenter (x , p) i = gy≡x i , ry≡p i where
      gy≡x : g y ≡ x
      gy≡x = sym (cong g p) ∙∙ refl ∙∙ sec x

      lem0 : Square (cong f (sec x)) p (cong f (sec x)) p
      lem0 i j = invSides-filler p (sym (cong f (sec x))) (~ i) j

      ry≡p : Square (ret y) p (cong f gy≡x) refl
      ry≡p i j = hcomp (λ k → λ { (i = i0) → cong ret p k j
                                ; (i = i1) → lem0 k j
                                ; (j = i0) → f (doubleCompPath-filler (sym (cong g p)) refl (sec x) k i)
                                ; (j = i1) → p k })
                       (com x (~ i) j)

open isHAEquiv using (isHAEquiv→Iso; isHAEquiv→isEquiv) public

HAEquiv : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
HAEquiv A B = Σ[ f ∈ (A → B) ] isHAEquiv f

-- vogt's lemma (https://ncatlab.org/nlab/show/homotopy+equivalence#vogts_lemma)
iso→HAEquiv : Iso A B → HAEquiv A B
iso→HAEquiv (iso f g ε η) = f , isHAEquivf
  where
    Hfa≡fHa : (f : A → A) → (H : ∀ a → f a ≡ a) → ∀ a → H (f a) ≡ cong f (H a)
    Hfa≡fHa f H = J (λ f p → ∀ a → funExt⁻ (sym p) (f a) ≡ cong f (funExt⁻ (sym p) a))
                    (λ a → refl)
                    (sym (funExt H))

    isHAEquivf : isHAEquiv f
    isHAEquiv.g isHAEquivf         = g
    isHAEquiv.sec isHAEquivf       = η
    isHAEquiv.ret isHAEquivf b i   =
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
  .isHAEquiv.sec → retIsEq (snd e)
  .isHAEquiv.ret → secIsEq (snd e)
  .isHAEquiv.com a → flipSquare (slideSquare (commSqIsEq (snd e) a))

congIso : {x y : A} (e : Iso A B) → Iso (x ≡ y) (Iso.fun e x ≡ Iso.fun e y)
congIso {x = x} {y} e = goal
  where
  open isHAEquiv (iso→HAEquiv e .snd)
  open Iso

  goal : Iso (x ≡ y) (Iso.fun e x ≡ Iso.fun e y)
  fun goal   = cong (iso→HAEquiv e .fst)
  inv goal p = sym (sec x) ∙∙ cong g p ∙∙ sec y
  rightInv goal p i j =
    hcomp (λ k → λ { (i = i0) → iso→HAEquiv e .fst
                                  (doubleCompPath-filler (sym (sec x)) (cong g p) (sec y) k j)
                   ; (i = i1) → ret (p j) k
                   ; (j = i0) → com x i k
                   ; (j = i1) → com y i k })
          (iso→HAEquiv e .fst (g (p j)))
  leftInv goal p i j =
    hcomp (λ k → λ { (i = i1) → p j
                   ; (j = i0) → Iso.leftInv e x (i ∨ k)
                   ; (j = i1) → Iso.leftInv e y (i ∨ k) })
          (Iso.leftInv e (p j) i)
