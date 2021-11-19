-- Defines abelian categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Abelian.Base where

open import Cubical.Algebra.AbGroup.Base using (AbGroupStr)
open import Cubical.Categories.Category.Base using (Precategory; _^op)
open import Cubical.Categories.Colimits.Coproduct using (isCoproduct)
open import Cubical.Categories.Limits.Product using (isProduct)
open import Cubical.Categories.Limits.Terminal using (isInitial; isFinal)
open import Cubical.Categories.Morphism using (isMonic; isEpic)
open import Cubical.Data.Sigma.Base using (∃!-syntax; Σ-syntax)
open import Cubical.Foundations.Prelude using (Level; Type; ℓ-suc; ℓ-max; _≡_)

private
  variable
    ℓ ℓ' : Level

module _ {C : Precategory ℓ ℓ'} where
  open Precategory C


  -- MORPHISM / OBJECT DEFINITIONS

  -- Zero morphism
  record isZero {x y : ob} (f : Hom[ x , y ]) : Type (ℓ-max ℓ ℓ') where
    field
      const : {w : ob} → (g h : Hom[ w , x ]) →
        f ∘ g ≡ f ∘ h
      coconst : {z : ob} → (g h : Hom[ y , z ]) →
        g ∘ f ≡ h ∘ f


  -- Binary biproducts
  record Biproduct (x y : ob) : Type (ℓ-max ℓ ℓ') where
    field
      b : ob
      px : Hom[ b , x ]
      py : Hom[ b , y ]
      ix : Hom[ x , b ]
      iy : Hom[ y , b ]

      pxix : px ∘ ix ≡ id x
      pxiy : isZero (px ∘ iy)
      pyix : isZero (py ∘ ix)
      pyiy : py ∘ iy ≡ id y

      bProd : isProduct {C = C} px py
      bCopr : isCoproduct {C = C} ix iy


  -- Kernels and cokernels
  module _ {x y : ob} where
    module _ (f : Hom[ x , y ]) where

      record PreZeroer : Type (ℓ-max ℓ ℓ') where
        constructor prezeroer
        field
          w : ob
          k : Hom[ w , x ]
          H : isZero (f ∘ k)

      record isKernel (Z : PreZeroer) : Type (ℓ-max ℓ ℓ') where
        open PreZeroer Z
        field
          univProp : (Y : PreZeroer) →
            let open PreZeroer Y renaming (w to w'; k to k') in
            ∃![ u ∈ Hom[ w' , w ] ]  k ∘ u ≡ k'


      record PostZeroer : Type (ℓ-max ℓ ℓ') where
        constructor postzeroer
        field
          z : ob
          c : Hom[ y , z ]
          H : isZero (c ∘ f)

      record isCokernel (Z : PostZeroer) : Type (ℓ-max ℓ ℓ') where
        open PostZeroer Z
        field
          univProp : (Y : PostZeroer) →
            let open PostZeroer Y renaming (z to z'; c to c') in
            ∃![ u ∈ Hom[ z , z' ] ]  u ∘ c ≡ c'


    record _=ker_ {w : ob} (kerf : Hom[ w , x ]) (f : Hom[ x , y ]) : Type (ℓ-max ℓ ℓ') where
      field
        isEq : Σ[ H ∈ isZero (f ∘ kerf) ] isKernel f (prezeroer w kerf H)

    record Kernel (f : Hom[ x , y ]) : Type (ℓ-max ℓ ℓ') where
      field
        w : ob
        ker : Hom[ w , x ]
        isKer : ker =ker f


    record _=coker_ {z : ob} (cokerf : Hom[ y , z ]) (f : Hom[ x , y ]) : Type (ℓ-max ℓ ℓ') where
      field
        isCoeq : Σ[ H ∈ isZero (cokerf ∘ f) ] isCokernel f (postzeroer z cokerf H)
    
    record Cokernel (f : Hom[ x , y ]) : Type (ℓ-max ℓ ℓ') where
      field
        z : ob
        coker : Hom[ y , z ]
        isCoker : coker =coker f



  -- ABELIAN HIERARCHY OF CATEGORIES

  -- Preadditive categories
  record isPreadditive : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    field
      AbEnriched : (x y : ob) → AbGroupStr (Hom[ x , y ])
      
      distl : (x y z : ob) → (f : Hom[ y , z ]) → (g h : Hom[ x , y ]) →
        let open AbGroupStr (AbEnriched x y) in
        let open AbGroupStr (AbEnriched x z) renaming (_+_ to _+'_) in
          f ∘ (g + h) ≡ (f ∘ g) +' (f ∘ h)

      distr : (x y z : ob) → (f g : Hom[ y , z ]) → (h : Hom[ x , y ]) →
        let open AbGroupStr (AbEnriched y z) in
        let open AbGroupStr (AbEnriched x z) renaming (_+_ to _+'_) in
          (f + g) ∘ h ≡ (f ∘ h) +' (g ∘ h)


  -- Additive categories
  record isAdditive : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    field
      C-Preadd : isPreadditive

      -- Zero object
      z : ob
      zInit : isInitial C z
      zFinal : isFinal C z

      -- Binary biproducts
      bp : (x y : ob) → Biproduct x y
  

  -- Preabelian categories
  record isPreabelian : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    field
      C-Addit : isAdditive
      hasKernels : {x y : ob} → (f : Hom[ x , y ]) → Kernel f
      hasCokernels : {x y : ob} → (f : Hom[ x , y ]) → Cokernel f
  

  -- Abelian categories
  record isAbelian : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    field
      C-Preab : isPreabelian
      
      monNormal : {x y : ob} → (m : Hom[ x , y ]) → isMonic {C = C} m
        → Σ[ z ∈ ob ] Σ[ f ∈ Hom[ y , z ] ] (m =ker f)

      epiNormal : {x y : ob} → (e : Hom[ x , y ]) → isEpic {C = C} e
        → Σ[ w ∈ ob ] Σ[ f ∈ Hom[ w , x ] ] (e =coker f) 
