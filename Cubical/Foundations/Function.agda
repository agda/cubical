{-
  Definitions for functions
-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Function where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : A → Type ℓ
    C : (a : A) → B a → Type ℓ
    D : (a : A) (b : B a) → C a b → Type ℓ
    E : (x : A) → (y : B x) → (z : C x y) → (w : D x y z) → Type ℓ
    F : (x : A) → (y : B x) → (z : C x y) → (w : D x y z) → (u : E x y z w) → Type ℓ

-- The identity function
idfun : (A : Type ℓ) → A → A
idfun _ x = x

infixr -1 _$_

_$_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → ((a : A) → B a) → (a : A) → B a
f $ a = f a
{-# INLINE _$_ #-}

infixr 9 _∘_

_∘_ : (g : {a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)
{-# INLINE _∘_ #-}

∘-assoc : (h : {a : A} {b : B a} → (c : C a b) → D a b c)
          (g : {a : A} → (b : B a) → C a b)
          (f : (a : A) → B a)
        → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-assoc h g f i x = h (g (f x))

∘-idˡ : (f : (a : A) → B a) → f ∘ idfun A ≡ f
∘-idˡ f i x = f x

∘-idʳ : (f : (a : A) → B a) → (λ {a} → idfun (B a)) ∘ f ≡ f
∘-idʳ f i x = f x

flip : {B : Type ℓ'} {C : A → B → Type ℓ''} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f y x = f x y
{-# INLINE flip #-}

const : {B : Type ℓ} → A → B → A
const x = λ _ → x
{-# INLINE const #-}

case_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → (x : A) → (∀ x → B x) → B x
case x of f = f x
{-# INLINE case_of_ #-}

case_return_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} (x : A) (B : A → Type ℓ') → (∀ x → B x) → B x
case x return P of f = f x
{-# INLINE case_return_of_ #-}

uncurry : ((x : A) → (y : B x) → C x y) → (p : Σ A B) → C (fst p) (snd p)
uncurry f (x , y) = f x y

uncurry2 : ((x : A) → (y : B x) → (z : C x y) → D x y z)
         → (p : Σ A (λ x → Σ (B x) (C x))) → D (p .fst) (p .snd .fst) (p .snd .snd)
uncurry2 f (x , y , z) = f x y z

uncurry3 : ((x : A) → (y : B x) → (z : C x y) → (w : D x y z) → E x y z w)
         → (p : Σ A (λ x → Σ (B x) (λ y → Σ (C x y) (D x y))))
         → E (p .fst) (p .snd .fst) (p .snd .snd .fst) (p .snd .snd .snd)
uncurry3 f (x , y , z , w) = f x y z w

uncurry4 : ((x : A) → (y : B x) → (z : C x y) → (w : D x y z) → (u : E x y z w) → F x y z w u)
         → (p : Σ A (λ x → Σ (B x) (λ y → Σ (C x y) (λ z → Σ (D x y z) (E x y z)))))
         → F (p .fst) (p .snd .fst) (p .snd .snd .fst) (p .snd .snd .snd .fst) (p .snd .snd .snd .snd)
uncurry4 f (x , y , z , w , u) = f x y z w u


curry : ((p : Σ A B) → C (fst p) (snd p)) → (x : A) → (y : B x) → C x y
curry f x y = f (x , y)

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  -- Notions of 'coherently constant' functions for low dimensions.
  -- These are the properties of functions necessary to e.g. eliminate
  -- from the propositional truncation.

  -- 2-Constant functions are coherently constant if B is a set.
  2-Constant : (A → B) → Type _
  2-Constant f = ∀ x y → f x ≡ f y

  2-Constant-isProp : isSet B → (f : A → B) → isProp (2-Constant f)
  2-Constant-isProp Bset f link1 link2 i x y j
    = Bset (f x) (f y) (link1 x y) (link2 x y) i j

  -- 3-Constant functions are coherently constant if B is a groupoid.
  record 3-Constant (f : A → B) : Type (ℓ-max ℓ ℓ') where
    field
      link : 2-Constant f
      coh₁ : ∀ x y z → Square (link x y) (link x z) refl (link y z)

    coh₂ : ∀ x y z → Square (link x z) (link y z) (link x y) refl
    coh₂ x y z i j
      = hcomp (λ k → λ
              { (j = i0) → link x y i
              ; (i = i0) → link x z (j ∧ k)
              ; (j = i1) → link x z (i ∨ k)
              ; (i = i1) → link y z j
              })
          (coh₁ x y z j i)

    link≡refl : ∀ x → refl ≡ link x x
    link≡refl x i j
      = hcomp (λ k → λ
              { (i = i0) → link x x (j ∧ ~ k)
              ; (i = i1) → link x x j
              ; (j = i0) → f x
              ; (j = i1) → link x x (~ i ∧ ~ k)
              })
          (coh₁ x x x (~ i) j)

    downleft : ∀ x y → Square (link x y) refl refl (link y x)
    downleft x y i j
      = hcomp (λ k → λ
              { (i = i0) → link x y j
              ; (i = i1) → link≡refl x (~ k) j
              ; (j = i0) → f x
              ; (j = i1) → link y x i
              })
          (coh₁ x y x i j)

    link≡symlink : ∀ x y → link x y ≡ sym (link y x)
    link≡symlink x y i j
      = hcomp (λ k → λ
              { (i = i0) → link x y j
              ; (i = i1) → link y x (~ j ∨ ~ k)
              ; (j = i0) → f x
              ; (j = i1) → link y x (i ∧ ~ k)
              })
          (downleft x y i j)

homotopyNatural : {B : Type ℓ'} {f g : A → B} (H : ∀ a → f a ≡ g a) {x y : A} (p : x ≡ y) →
                  H x ∙ cong g p ≡ cong f p ∙ H y
homotopyNatural {f = f} {g = g} H {x} {y} p i j =
    hcomp (λ k → λ { (i = i0) → compPath-filler (H x) (cong g p) k j
                   ; (i = i1) → compPath-filler' (cong f p) (H y) k j
                   ; (j = i0) → cong f p (i ∧ ~ k)
                   ; (j = i1) → cong g p (i ∨ k) })
          (H (p i) j)

homotopySymInv : {f : A → A} (H : ∀ a → f a ≡ a) (a : A)
               → Path (f a ≡ f a) (λ i → H (H a (~ i)) i) refl
homotopySymInv {f = f} H a j i =
  hcomp (λ k → λ { (i = i0) → f a
                 ; (i = i1) → H a (j ∧ ~ k)
                 ; (j = i0) → H (H a (~ i)) i
                 ; (j = i1) → H a (i ∧ ~ k)})
        (H (H a (~ i ∨ j)) i)
