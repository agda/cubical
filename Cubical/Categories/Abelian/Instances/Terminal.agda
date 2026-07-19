module Cubical.Categories.Abelian.Instances.Terminal where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Abelian.Base
open import Cubical.Categories.Additive.Instances.Terminal

open import Cubical.Data.Unit

private
  variable
    ℓ : Level

private
  open PreAbCategory
  open PreAbCategoryStr

  terminalPreAbCategory : PreAbCategory ℓ ℓ
  PreAbCategory.additive terminalPreAbCategory = terminalAdditiveCategory

  Kernel.k (hasKernels (preAbStr terminalPreAbCategory) f) = tt*
  Kernel.ker (hasKernels (preAbStr terminalPreAbCategory) f) = refl
  IsKernel.ker⋆f (Kernel.isKer (hasKernels (preAbStr terminalPreAbCategory) f)) = refl
  IsKernel.univ (Kernel.isKer (hasKernels (preAbStr terminalPreAbCategory) f)) = λ _ _ _ → (refl , refl) , λ _ → refl

  Cokernel.c (hasCokernels (preAbStr terminalPreAbCategory) f) = tt*
  Cokernel.coker (hasCokernels (preAbStr terminalPreAbCategory) f) = refl
  IsCokernel.f⋆coker (Cokernel.isCoker (hasCokernels (preAbStr terminalPreAbCategory) f)) = refl
  IsCokernel.univ (Cokernel.isCoker (hasCokernels (preAbStr terminalPreAbCategory) f)) = λ _ _ _ → (refl , refl) , λ _ → refl

open AbelianCategory
open AbelianCategoryStr

terminalAbelianCategory : AbelianCategory ℓ ℓ
preAb terminalAbelianCategory = terminalPreAbCategory

fst (monNormal (abelianStr terminalAbelianCategory) m _) = tt*
fst (snd (monNormal (abelianStr terminalAbelianCategory) m _)) = m
IsKernel.ker⋆f (snd (snd (monNormal (abelianStr terminalAbelianCategory) m _))) = refl
IsKernel.univ (snd (snd (monNormal (abelianStr terminalAbelianCategory) m _))) = λ _ _ _ → (refl , refl) , (λ _ → refl)

fst (epiNormal (abelianStr terminalAbelianCategory) e _) = tt*
fst (snd (epiNormal (abelianStr terminalAbelianCategory) e _)) = e
IsCokernel.f⋆coker (snd (snd (epiNormal (abelianStr terminalAbelianCategory) e _))) = refl
IsCokernel.univ (snd (snd (epiNormal (abelianStr terminalAbelianCategory) e _))) = λ _ _ _ → (refl , refl) , (λ _ → refl)
