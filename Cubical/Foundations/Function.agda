{-
  Definitions for functions
-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Function where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.CartesianKanOps

-- The identity function
idfun : ∀ {ℓ} → (A : Type ℓ) → A → A
idfun _ x = x

infixr 9 _∘_

_∘_ : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {B : A → Type ℓ′} {C : (a : A) → B a → Type ℓ″}
        (g : {a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)
{-# INLINE _∘_ #-}

∘-assoc : ∀ {ℓ ℓ′ ℓ″ ℓ‴} {A : Type ℓ} {B : A → Type ℓ′} {C : (a : A) → B a → Type ℓ″} {D : (a : A) (b : B a) → C a b → Type ℓ‴}
            (h : {a : A} {b : B a} → (c : C a b) → D a b c) (g : {a : A} → (b : B a) → C a b) (f : (a : A) → B a)
          → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-assoc h g f i x = h (g (f x))

∘-idˡ : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} (f : (a : A) → B a) → f ∘ idfun A ≡ f
∘-idˡ f i x = f x

∘-idʳ : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} (f : (a : A) → B a) → (λ {a} → idfun (B a)) ∘ f ≡ f
∘-idʳ f i x = f x


const : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → A → B → A
const x = λ _ → x
{-# INLINE const #-}

case_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → (x : A) → (∀ x → B x) → B x
case x of f = f x
{-# INLINE case_of_ #-}

case_return_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} (x : A) (B : A → Type ℓ') → (∀ x → B x) → B x
case x return P of f = f x
{-# INLINE case_return_of_ #-}

uncurry
  : ∀{ℓ ℓ′ ℓ″} {A : Type ℓ} {B : A → Type ℓ′} {C : (a : A) → B a → Type ℓ″}
  → ((x : A) → (y : B x) → C x y)
  → (p : Σ A B) → C (fst p) (snd p)
uncurry f (x , y) = f x y

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

homotopySymInv : ∀ {ℓ} {A : Type ℓ} {f : A → A} (p : ∀ a → f a ≡ a)
  (a : A) → Path (f a ≡ f a) (λ i → p (p a (~ i)) i) refl
homotopySymInv {f = f} p a j i =
  hcomp
    (λ k → λ {
      (i = i0) → f a;
      (i = i1) → p a (j ∧ ~ k);
      (j = i0) → p (p a (~ i)) i;
      (j = i1) → p a (i ∧ ~ k)})
    (p (p a (~ i ∨ j)) i)

module _ {ℓ} {A : Type ℓ} where
  Fixpoint : (A → A) → Type ℓ
  Fixpoint f = Σ A λ x → f x ≡ x

  fixpoint : {f : A → A} → Fixpoint f → A
  fixpoint = fst

  fixpointPath : {f : A → A} → (p : Fixpoint f) → f (fixpoint p) ≡ fixpoint p
  fixpointPath = snd

  2-Constant→isPropFixpoint : (f : A → A) → 2-Constant f → isProp (Fixpoint f)
  2-Constant→isPropFixpoint f connection (x , p) (y , q) i = s i , t i where
    infixl 25 _[0→_] _[_→0]
    -- some helpful notation to aid readability
    _[0→_] : {x y : A} (p : x ≡ y) → (i : I) → x ≡ p i
    p [0→ i ] = λ k → p (i ∧ k)
    _[_→0] : {x y : A} (p : x ≡ y) → (i : I) → p i ≡ x
    p [ i →0] = λ k → p (i ∧ ~ k)
    noose : ∀ x y → f x ≡ f y
    noose x y = sym (connection x x) ∙ connection x y
    -- the main idea is that for any path p, cong f p does not depend p
    -- but only on its endpoints and the structure of 2-Constant f
    KrausLemma : ∀ {x y} → (p : x ≡ y) → cong f p ≡ noose x y
    KrausLemma {x} = J (λ y p → cong f p ≡ noose x y) (sym (lCancel (connection x x)))
    -- suppose we have a path s : x ≡ y, then we need to proof transport s p ≡ q
    -- a short calculation with the lemma reveals that we require:
    -- sym (noose x y) ∙ p ∙ s ≡ q
    -- reordering motivates the required definition:
    s : x ≡ y
    s = sym p ∙∙ noose x y ∙∙ q
    t' : sym (cong f s) ∙∙ p ∙∙ s ≡ q
    t' =
      sym (cong f s) ∙∙ p ∙∙ s
        ≡[ i ]⟨ sym (KrausLemma s i) ∙∙ p ∙∙ (sym p ∙∙ noose x y ∙∙ q) ⟩
      (sym (noose x y) ∙∙ p ∙∙ (sym p ∙∙ noose x y ∙∙ q))
        ≡[ i ]⟨ sym (noose x y) ∙∙ p [0→ ~ i ] ∙∙ (p [ ~ i →0] ∙∙ noose x y ∙∙ q) ⟩
      (sym (noose x y) ∙∙ refl ∙∙ (noose x y ∙ q))
        ≡⟨ J (λ _ p → p ∙∙ refl ∙∙ (sym p ∙ q) ≡ q) (λ i → lUnit (lUnit q (~ i)) (~ i)) (sym (noose x y)) ⟩
      q ∎
    t : PathP (λ i → cong f s i ≡ s i) p q
    t = coe1→0 (λ k → PathP (λ i → cong f s (i ∨ k) ≡ s (i ∨ k)) (doubleCompPath-filler (sym (cong f s)) p s k) q) t'
