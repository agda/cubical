{-
  General lemmas about morphisms (defined as loosely as possible)
-}
module Cubical.Functions.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open Iso
module ax {ℓ : Level} (A : Type ℓ) (_+A_ : A → A → A) (a₀ : A) where
  rUnit = (a : A) → a +A a₀ ≡ a
  lUnit = (a : A) → a₀ +A a ≡ a

  rCancel : (-A_ : A → A) → Type ℓ
  rCancel -A_ = (a : A) → a +A (-A a) ≡ a₀

  lCancel : (-A_ : A → A) → Type ℓ
  lCancel -A_ = (a : A) → (-A a) +A a ≡ a₀

  assoc = (x y z : A) → x +A (y +A z) ≡ ((x +A y) +A z)

  comm = (x y : A) → x +A y ≡ y +A x

module morphLemmas {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'}
         (_+A_ : A → A → A) (_+B_ : B → B → B)
         (f : A → B) (f-hom : (x y : A) → f (x +A y) ≡ f x +B f y)
         where

  0↦0 : (a₀ : A) (b₀ : B) (-A_ : A → A) (-B_ : B → B)
      → ax.rUnit A _+A_ a₀
      → ax.rUnit B _+B_ b₀
      → ax.rCancel B _+B_ b₀ -B_
      → ax.assoc B _+B_ b₀
      → f a₀ ≡ b₀
  0↦0 a₀ b₀ -A_ -B_ rUnitA rUnitB rCancelB assocB =
       sym (rUnitB (f a₀))
    ∙∙ cong (f a₀ +B_) (sym (rCancelB (f a₀)))
    ∙∙ assocB (f a₀) (f a₀) (-B f a₀)
    ∙∙ sym (cong (_+B (-B f a₀)) (cong f (sym (rUnitA a₀)) ∙ f-hom a₀ a₀))
    ∙∙ rCancelB (f a₀)

  distrMinus : (a₀ : A) (b₀ : B) (-A_ : A → A) (-B_ : B → B)
            → ax.lUnit B _+B_ b₀
            → ax.rUnit B _+B_ b₀
            → ax.lCancel A _+A_ a₀ -A_
            → ax.rCancel B _+B_ b₀ -B_
            → ax.assoc B _+B_ b₀
            → (0↦0 : f a₀ ≡ b₀)
            → (x : A) → f (-A x) ≡ -B (f x)
  distrMinus a₀ b₀ -A_ -B_ lUnitB rUnitB lCancelA rCancelB assocB 0↦0 x =
       sym (rUnitB _)
    ∙∙ cong (f (-A x) +B_) (sym (rCancelB (f x)))
    ∙∙ assocB _ _ _
    ∙∙ cong (_+B (-B (f x))) (sym (f-hom (-A x) x) ∙∙ cong f (lCancelA x) ∙∙ 0↦0)
    ∙∙ lUnitB _

  distrMinus' : (a₀ : A) (b₀ : B) (-A_ : A → A) (-B_ : B → B)
             → ax.lUnit B _+B_ b₀
             → ax.rUnit B _+B_ b₀
             → ax.rUnit A _+A_ a₀
             → ax.lCancel A _+A_ a₀ -A_
             → ax.rCancel B _+B_ b₀ -B_
             → ax.assoc A _+A_ a₀
             → ax.assoc B _+B_ b₀
             → f a₀ ≡ b₀ -- not really needed, but it can be useful to specify the proof yourself
             → (x y : A)
             → f (x +A (-A y)) ≡ (f x +B (-B (f y)))
  distrMinus' a₀ b₀ -A_ -B_ lUnitB rUnitB rUnitA lCancelA rCancelB assocA assocB 0↦0 x y =
       sym (rUnitB _)
    ∙∙ cong (f (x +A (-A y)) +B_) (sym (rCancelB (f y))) ∙ assocB _ _ _
    ∙∙ cong (_+B (-B f y)) (sym (f-hom (x +A (-A y)) y)
                          ∙ cong f (sym (assocA x (-A y) y)
                                 ∙∙ cong (x +A_) (lCancelA y)
                                 ∙∙ rUnitA x))

  isMorphInv :  (g : B → A) → section f g → retract f g
             → (x y : B)
             → (g (x +B y) ≡ (g x +A g y))
  isMorphInv g sect retr x y =
       cong g (cong₂ _+B_ (sym (sect x)) (sym (sect y)))
    ∙∙ cong g (sym (f-hom (g x) (g y)))
    ∙∙ retr (g x +A g y)
