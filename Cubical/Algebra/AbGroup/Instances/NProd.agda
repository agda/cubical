module Cubical.Algebra.AbGroup.Instances.NProd where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Instances.NProd
open import Cubical.Algebra.AbGroup

private variable
  ℓ : Level

open AbGroupStr

NProd-AbGroup : (G : (n : ℕ) → Type ℓ) → (Gstr : (n : ℕ) → AbGroupStr (G n)) → AbGroup ℓ
NProd-AbGroup G Gstr = Group→AbGroup (NProd-Group G (λ n → AbGroupStr→GroupStr (Gstr n)))
                                      λ f g → funExt λ n → +Comm (Gstr n) _ _
