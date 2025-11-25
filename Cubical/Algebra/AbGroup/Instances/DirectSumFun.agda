module Cubical.Algebra.AbGroup.Instances.DirectSumFun where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.DirectSum.DirectSumFun.Base
open import Cubical.Algebra.DirectSum.DirectSumFun.Properties

private variable
  ℓ : Level

module _ (G : (n : ℕ) → Type ℓ) (Gstr : (n : ℕ) → AbGroupStr (G n)) where

  open AbGroupStr
  open DSF-properties G Gstr

  ⊕Fun-AbGr : AbGroup ℓ
  fst ⊕Fun-AbGr = ⊕Fun G Gstr
  0g (snd ⊕Fun-AbGr) = 0⊕Fun
  AbGroupStr._+_ (snd ⊕Fun-AbGr) = _+⊕Fun_
  - snd ⊕Fun-AbGr = Inv⊕Fun
  isAbGroup (snd ⊕Fun-AbGr) = makeIsAbGroup isSet⊕Fun +⊕FunAssoc +⊕FunRid +⊕FunInvR +⊕FunComm
