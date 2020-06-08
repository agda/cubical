{-

Theory about isomorphisms

- Definitions of [section] and [retract]
- Definition of isomorphisms ([Iso])
- Any isomorphism is an equivalence ([isoToEquiv])

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Isomorphism where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Base

open import Cubical.Foundations.Function

private
  variable
    ℓ : Level

-- Section and retract
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  section : (f : A → B) → (g : B → A) → Type ℓ'
  section f g = ∀ b → f (g b) ≡ b

  -- NB: `g` is the retraction!
  retract : (f : A → B) → (g : B → A) → Type ℓ
  retract f g = ∀ a → g (f a) ≡ a

record Iso {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor iso
  field
    fun : A → B
    inv : B → A
    rightInv : section fun inv
    leftInv  : retract fun inv

isIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type _
isIso {A = A} {B = B} f = Σ[ g ∈ (B → A) ] Σ[ _ ∈ section f g ] retract f g

-- Any iso is an equivalence
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (i : Iso A B) where
  open Iso i renaming ( fun to f
                      ; inv to g
                      ; rightInv to s
                      ; leftInv to t)

  private
    module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
      fill0 : I → I → A
      fill0 i = hfill (λ k → λ { (i = i1) → t x0 k
                               ; (i = i0) → g y })
                      (inS (g (p0 (~ i))))

      fill1 : I → I → A
      fill1 i = hfill (λ k → λ { (i = i1) → t x1 k
                               ; (i = i0) → g y })
                      (inS (g (p1 (~ i))))

      fill2 : I → I → A
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
                               ; (i = i0) → fill0 k i1 })
                      (inS (g y))

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → A
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → t (fill2 i i1) (~ k)
                              ; (j = i0) → g y })
                     (fill2 i j)

      sq1 : I → I → B
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 (~ j)) k
                               ; (i = i0) → s (p0 (~ j)) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k })
                      (f (sq i j))

      lemIso : (x0 , p0) ≡ (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = λ j → sq1 i (~ j)

  isoToIsEquiv : isEquiv f
  isoToIsEquiv .equiv-proof y .fst .fst = g y
  isoToIsEquiv .equiv-proof y .fst .snd = s y
  isoToIsEquiv .equiv-proof y .snd z = lemIso y (g y) (fst z) (s y) (snd z)


isoToEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Iso A B → A ≃ B
isoToEquiv i .fst = _
isoToEquiv i .snd = isoToIsEquiv i

isoToPath : ∀ {ℓ} {A B : Type ℓ} → Iso A B → A ≡ B
isoToPath {A = A} {B = B} f i =
  Glue B (λ { (i = i0) → (A , isoToEquiv f)
            ; (i = i1) → (B , idEquiv B) })

open Iso

invIso : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} → Iso X Y → Iso Y X
fun (invIso f) = inv f
inv (invIso f) = fun f
rightInv (invIso f) = leftInv f
leftInv (invIso f)  = rightInv f

compIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
          → Iso A B → Iso B C → Iso A C
fun (compIso (iso f _ _ _) (iso g _ _ _))       = g ∘ f
inv (compIso (iso _ finv _ _) (iso _ ginv _ _)) = finv ∘ ginv
rightInv (compIso (iso _ _ rightInv _) (iso g ginv rightInv' _)) b =
  cong g (rightInv (ginv b)) ∙ rightInv' b
leftInv (compIso (iso f finv _ leftInv) (iso _ _ _ leftInv')) a =
  cong finv (leftInv' (f a)) ∙ leftInv a

composesToId→Iso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}  (G : Iso A B) (g : B → A)
                 → G .fun ∘ g ≡ idfun B → Iso B A
fun (composesToId→Iso _ g _)             = g
inv (composesToId→Iso (iso f _ _ _) _ _) = f
rightInv (composesToId→Iso (iso f finv _ leftInv) g path) b =
  sym (leftInv (g (f b))) ∙∙ cong (λ g → finv (g (f b))) path ∙∙ leftInv b
leftInv (composesToId→Iso _ _ path) b i = path i b

idIso : ∀ {ℓ} {X : Type ℓ} → Iso X X
fun idIso = idfun _
inv idIso = idfun _
rightInv idIso _ = refl
leftInv idIso _  = refl

-- Helpful notation
_Iso⟨_⟩_ : ∀ {ℓ ℓ' ℓ''} {B : Type ℓ'} {C : Type ℓ''} (X : Type ℓ) → Iso X B → Iso B C → Iso X C
_ Iso⟨ f ⟩ g = compIso f g

_∎Iso : ∀ {ℓ} (X : Type ℓ) → Iso X X
X ∎Iso = idIso {X = X}

infixr  0 _Iso⟨_⟩_
infix   1 _∎Iso

