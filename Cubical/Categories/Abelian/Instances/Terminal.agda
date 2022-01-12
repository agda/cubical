{-# OPTIONS --safe #-}
module Cubical.Categories.Abelian.Instances.Terminal where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Abelian.Base
open import Cubical.Categories.Additive.Instances.Terminal renaming (terminal to terminalAdd)

open import Cubical.Data.Unit

private
  variable
    ℓ : Level

private
  open PreabCategory
  open PreabCategoryStr

  terminalPreAb : PreabCategory ℓ ℓ
  PreabCategory.additcat terminalPreAb = terminalAdd
  hasKernels (preab terminalPreAb) f =
    kernel tt* refl (isKernel refl (λ _ _ _ → (refl , refl) , λ _ → refl))
  hasCokernels (preab terminalPreAb) f =
    cokernel tt* refl (isCokernel refl (λ _ _ _ → (refl , refl) , λ _ → refl))

open AbelianCategory
open AbelianCategoryStr

terminal : AbelianCategory ℓ ℓ
preabcat terminal = terminalPreAb
monNormal (abeli terminal) m _ = tt* , (m , (isKernel refl λ _ _ _ → (refl , refl) , (λ _ → refl)))
epiNormal (abeli terminal) e _ = tt* , (e , (isCokernel refl (λ _ _ _ → (refl , refl) , (λ _ → refl))))
