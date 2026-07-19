module Cubical.Algebra.Group.Instances.NProd where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.Group

private variable
  ℓ : Level

open GroupStr

NProd-Group : (G : (n : ℕ) → Type ℓ) → (Gstr : (n : ℕ) → GroupStr (G n)) → Group ℓ
fst (NProd-Group G Gstr) = (n : ℕ) → G n
1g (snd (NProd-Group G Gstr)) = λ n → 1g (Gstr n)
GroupStr._·_ (snd (NProd-Group G Gstr)) = λ f g n → Gstr n ._·_ (f n) (g n)
inv (snd (NProd-Group G Gstr)) = λ f n → (Gstr n).inv (f n)
isGroup (snd (NProd-Group G Gstr)) = makeIsGroup (isSetΠ (λ _ → is-set (Gstr _)))
                                                 (λ f g h → funExt λ n → ·Assoc (Gstr n) _ _ _)
                                                 (λ f → funExt λ n → ·IdR (Gstr n) _)
                                                 (λ f → funExt λ n → ·IdL (Gstr n) _)
                                                 (λ f → funExt λ n → ·InvR (Gstr n) _)
                                                  λ f → funExt λ n → ·InvL (Gstr n) _
