-- (Pre)abelian categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Abelian.Base where

open import Cubical.Categories.Additive.Base
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Morphism
open import Cubical.Data.Sigma.Base
open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level


-- (Co)kernels
module _ (C : PreaddCategory ℓ ℓ') where
  open PreaddCategory C

  module _ {x y : ob} (f : Hom[ x , y ]) where

    -- Kernels
    record IsKernel {k : ob} (ker : Hom[ k , x ]) : Type (ℓ-max ℓ ℓ') where
      field
        ker⋆f : ker ⋆ f ≡ 0h
        univ : ∀ (w : ob) (t : Hom[ w , x ])
          → (t ⋆ f ≡ 0h) → ∃![ u ∈ Hom[ w , k ] ] (u ⋆ ker ≡ t)

    record Kernel : Type (ℓ-max ℓ ℓ') where
      constructor kernel
      field
        k : ob
        ker : Hom[ k , x ]
        isKer : IsKernel ker

      open IsKernel isKer public


    -- Cokernels
    record IsCokernel {c : ob} (coker : Hom[ y , c ]) : Type (ℓ-max ℓ ℓ') where
      field
        f⋆coker : f ⋆ coker ≡ 0h
        univ : ∀ (w : ob) (t : Hom[ y , w ])
          → (f ⋆ t ≡ 0h) → ∃![ u ∈ Hom[ c , w ] ] (coker ⋆ u ≡ t)

    record Cokernel : Type (ℓ-max ℓ ℓ') where
      field
        c : ob
        coker : Hom[ y , c ]
        isCoker : IsCokernel coker

      open IsCokernel isCoker public


-- Preabelian categories
record PreabCategoryStr (C : AdditiveCategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  open AdditiveCategory C
  field
    hasKernels : {x y : ob} → (f : Hom[ x , y ]) → Kernel preaddcat f
    hasCokernels : {x y : ob} → (f : Hom[ x , y ]) → Cokernel preaddcat f

  -- Convenient ker/coker functions
  ker = λ {x y} (f : Hom[ x , y ]) → hasKernels f .Kernel.ker
  coker = λ {x y} (f : Hom[ x , y ]) → hasCokernels f .Cokernel.coker


record PreAbCategory (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    additive : AdditiveCategory ℓ ℓ'
    preAbStr : PreabCategoryStr additive

  open AdditiveCategory additive public
  open PreabCategoryStr preAbStr public


-- Abelian categories
record AbelianCategoryStr (C : PreAbCategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  open PreAbCategory C

  private
    _=ker_ : ∀ {k x y} → Hom[ k , x ] → Hom[ x , y ] → Type (ℓ-max ℓ ℓ')
    m =ker f = IsKernel preaddcat f m

    _=coker_ : ∀ {c x y} → Hom[ y , c ] → Hom[ x , y ] → Type (ℓ-max ℓ ℓ')
    e =coker f = IsCokernel preaddcat f e

  field
    monNormal : {x y : ob} → (m : Hom[ x , y ]) → isMonic cat m
      → Σ[ z ∈ ob ] Σ[ f ∈ Hom[ y , z ] ] (m =ker f)

    epiNormal : {x y : ob} → (e : Hom[ x , y ]) → isEpic cat e
      → Σ[ w ∈ ob ] Σ[ f ∈ Hom[ w , x ] ] (e =coker f)


record AbelianCategory (ℓ ℓ' : Level): Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    preAb : PreAbCategory ℓ ℓ'
    abelianStr : AbelianCategoryStr preAb

  open PreAbCategory preAb public
  open AbelianCategoryStr abelianStr public
