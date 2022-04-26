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
  open PreAbCategory
  open PreAbCategoryStr

  terminalPreAb : PreAbCategory ℓ ℓ
  PreAbCategory.additive terminalPreAb = terminalAdd

  Kernel.k (hasKernels (preAbStr terminalPreAb) f) = tt*
  Kernel.ker (hasKernels (preAbStr terminalPreAb) f) = refl
  IsKernel.ker⋆f (Kernel.isKer (hasKernels (preAbStr terminalPreAb) f)) = refl
  IsKernel.univ (Kernel.isKer (hasKernels (preAbStr terminalPreAb) f)) = λ _ _ _ → (refl , refl) , λ _ → refl

  Cokernel.c (hasCokernels (preAbStr terminalPreAb) f) = tt*
  Cokernel.coker (hasCokernels (preAbStr terminalPreAb) f) = refl
  IsCokernel.f⋆coker (Cokernel.isCoker (hasCokernels (preAbStr terminalPreAb) f)) = refl
  IsCokernel.univ (Cokernel.isCoker (hasCokernels (preAbStr terminalPreAb) f)) = λ _ _ _ → (refl , refl) , λ _ → refl

open AbelianCategory
open AbelianCategoryStr

terminal : AbelianCategory ℓ ℓ
preAb terminal = terminalPreAb

fst (monNormal (abelianStr terminal) m _) = tt*
fst (snd (monNormal (abelianStr terminal) m _)) = m
IsKernel.ker⋆f (snd (snd (monNormal (abelianStr terminal) m _))) = refl
IsKernel.univ (snd (snd (monNormal (abelianStr terminal) m _))) = λ _ _ _ → (refl , refl) , (λ _ → refl)

fst (epiNormal (abelianStr terminal) e _) = tt*
fst (snd (epiNormal (abelianStr terminal) e _)) = e
IsCokernel.f⋆coker (snd (snd (epiNormal (abelianStr terminal) e _))) = refl
IsCokernel.univ (snd (snd (epiNormal (abelianStr terminal) e _))) = λ _ _ _ → (refl , refl) , (λ _ → refl)
