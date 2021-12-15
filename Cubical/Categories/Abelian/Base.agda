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

module _ (C : Category ℓ ℓ') (habstr : HomAbStr C) where
  open Category C
  open HomAbStr habstr using (0h)

  -- Zero morphisms
  record isZero {x y : ob} (f : Hom[ x , y ]) : Type (ℓ-max ℓ ℓ') where
    field
      const : ∀ {w} (g h : Hom[ w , x ]) → g ⋆ f ≡ h ⋆ f
      coconst : ∀ {z} (g h : Hom[ y , z ]) → f ⋆ g ≡ f ⋆ h


  module _ {x y : ob} (f : Hom[ x , y ]) where

    -- Kernels
    record IsKernel {k : ob} (ker : Hom[ k , x ]) : Type (ℓ-max ℓ ℓ') where
      field
        ker⋆f : isZero (ker ⋆ f)
        univ : ∀ (w : ob) (t : Hom[ w , x ])
          → isZero (t ⋆ f) → ∃![ u ∈ Hom[ w , k ] ] (u ⋆ ker ≡ t)

    makeIsKernel : {k : ob} (ker : Hom[ k , x ]) →
      (ker ⋆ f) ≡ 0h
      → (u : ∀ (w : ob) (t : Hom[ w , x ]) → (t ⋆ f ≡ 0h)  →  Hom[ w , k ])
      → (    ∀ (w : ob) (t : Hom[ w , x ]) → (H : t ⋆ f ≡ 0h)  →  (u w t H) ⋆ ker ≡ t)
      → (    ∀ (w : ob) (t : Hom[ w , x ]) → (H : t ⋆ f ≡ 0h)  →  ∀ v → (v ⋆ ker ≡ t) → (v ≡ (u w t H)))
      → IsKernel ker

    makeIsKernel = ?

    record Kernel : Type (ℓ-max ℓ ℓ') where
      constructor kernel
      field
        k : ob
        ker : Hom[ k , x ]
        isKer : IsKernel ker

      open IsKernel isKer


    -- Cokernels
    record IsCokernel {c : ob} (coker : Hom[ y , c ]) : Type (ℓ-max ℓ ℓ') where
      field
        f⋆coker : isZero (f ⋆ coker)
        univ : ∀ (w : ob) (t : Hom[ y , w ])
          → isZero (f ⋆ t) → ∃![ u ∈ Hom[ c , w ] ] (coker ⋆ u ≡ t)

    record Cokernel : Type (ℓ-max ℓ ℓ') where
      field
        c : ob
        coker : Hom[ y , c ]
        isCoker : IsCokernel coker

      open IsCokernel isCoker


  -- Preabelian categories
  record PreabCategoryStr : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    field
      addit : AdditiveCategoryStr C
      hasKernels : {x y : ob} → (f : Hom[ x , y ]) → Kernel f
      hasCokernels : {x y : ob} → (f : Hom[ x , y ]) → Cokernel f

    open AdditiveCategoryStr addit public


  -- Abelian categories
  record AbelianCategoryStr : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    field
      preab : PreabCategoryStr

    private
      _=ker_ : ∀ {k x y} → Hom[ k , x ] → Hom[ x , y ] → Type (ℓ-max ℓ ℓ')
      m =ker f = IsKernel f m

      _=coker_ : ∀ {c x y} → Hom[ y , c ] → Hom[ x , y ] → Type (ℓ-max ℓ ℓ')
      e =coker f = IsCokernel f e

    field
      monNormal : {x y : ob} → (m : Hom[ x , y ]) → isMonic C m
        → Σ[ z ∈ ob ] Σ[ f ∈ Hom[ y , z ] ] (m =ker f)

      epiNormal : {x y : ob} → (e : Hom[ x , y ]) → isEpic C e
        → Σ[ w ∈ ob ] Σ[ f ∈ Hom[ w , x ] ] (e =coker f)

    open PreabCategoryStr preab public


record PreabCategory (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cat : Category ℓ ℓ'
    preab : PreabCategoryStr cat

  open Category cat public
  open PreabCategoryStr preab public


record AbelianCategory (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cat : Category ℓ ℓ'
    abcatstr : AbelianCategoryStr cat

  open Category cat public
  open AbelianCategoryStr abcatstr public


module _ (A : AdditiveCategory ℓ ℓ') where
  open AdditiveCategory A

  AddCat→AbelCat :
    (hasKernels : {x y : ob} → (f : Hom[ x , y ]) → Kernel cat f)
    (hasCokernels : {x y : ob} → (f : Hom[ x , y ]) → Cokernel cat f)
    (monNormal : {x y : ob} → (m : Hom[ x , y ]) → isMonic cat m
        → Σ[ z ∈ ob ] Σ[ f ∈ Hom[ y , z ] ] (IsKernel cat f m))
    (epiNormal : {x y : ob} → (e : Hom[ x , y ]) → isEpic cat e
        → Σ[ w ∈ ob ] Σ[ f ∈ Hom[ w , x ] ] (IsCokernel cat f e))
    → AbelianCategory ℓ ℓ'

  AddCat→AbelCat hk hc mn en = record {
      cat = cat;
      abcatstr = record {
        preab = record {
          addit = addit;
          hasKernels = hk ;
          hasCokernels = hc } ;
        monNormal = mn ;
        epiNormal = en } }




-- Test making kernel
-- open import Cubical.Algebra.AbGroup.Base
-- open import Cubical.Algebra.Group.Base --hiding (Subgroup)
-- open import Cubical.Algebra.Group.Subgroup hiding (Subgroup)
-- open import Cubical.Categories.Instances.AbGroups renaming (AbGroupCategory to Ab)

-- module _ {A B : AbGroup ℓ} (f : AbGroupHom A B) where

--   kerf-SubgroupA : Subgroup A
--   kerf-SubgroupA = kerSubgroup f

--   kerf-Group : Group ℓ
--   kerf-Group = Subgroup→Group (AbGroup→Group A) kerf-SubgroupA

--   kerf : AbGroup ℓ
--   kerf = Group→AbGroup kerf-Group
--          λ (a , Ha) (a' , Ha') → {! ΣPathP !}
--   --Subgroup→Group (kerSubgroup f)
--   --(λ a → Σ[ b ∈ B .fst ] (f a ≡ b), {!   !}) , {!   !}



open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties renaming (compGroupHom to _⋆_)
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Categories.Instances.Groups renaming (GroupCategory to Grp)
open import Cubical.Data.Sigma.Properties


module _ {G H : Group ℓ} (f : GroupHom G H) where
  open GroupStr (snd H) using () renaming (1g to 1H; rid to idrH)
  open GroupTheory H using () renaming (inv1g to inv1H)

  kerf : Group ℓ
  kerf = Subgroup→Group G (kerSubgroup f)

  kerf-incl : GroupHom kerf G
  kerf-incl = SubgIncl G (kerSubgroup f)

  zero : ∀ {J : Group ℓ} → GroupHom J H
  zero = (λ _ → 1H) , record {
      pres· = λ _ _ → sym (idrH _) ;
      pres1 = refl ;
      presinv = λ _ → sym inv1H }

  zsub : ∀ {G} (x : GroupHom G H) → x ≡ zero → isZero Grp x
  zsub = {!   !}

  zsub⁻¹ : ∀ {G} (x : GroupHom G H) → isZero Grp x → x ≡ zero
  zsub⁻¹ = {!   !}

  kerf⋆f : kerf-incl ⋆ f ≡ zero
  kerf⋆f = GroupHom≡ (funExt (λ (_ , P) → P))


  -- ∀ (w : ob) (t : Hom[ w , x ])
  --        → isZero (t ⋆ f) → ∃![ u ∈ Hom[ w , k ] ] (u ⋆ ker ≡ t)

  module _ (J : Group ℓ) (t : GroupHom J G)
           (t⋆f : t ⋆ f ≡ zero)
           where

    u : GroupHom J kerf
    u = (λ j → t .fst j ,
          funExt⁻ (fst (PathPΣ t⋆f)) j
        ) , record {
          pres· = λ j j' → ΣPathP ({!   !} , {!   !}) ;
          pres1 = {! refl ? !} ;
          presinv = {!   !} }

    u⋆kerf : u ⋆ kerf-incl ≡ t
    u⋆kerf = {!   !}

    u-unq : ∀ v → (v ⋆ kerf-incl ≡ t) → (v ≡ u)
    u-unq v v⋆k = GroupHom≡ (funExt (λ j → {!   !}))


  c = {! u  !}


  gpKernel : Kernel Grp f
  gpKernel = record {
    k = kerf ;
    ker = kerf-incl ;
    isKer = record {
      ker⋆f = zsub {!   !} kerf⋆f ;
      univ = λ J t t⋆f →
        ((u J t (zsub⁻¹ (t ⋆ f) t⋆f)) ,
        (u⋆kerf J t (zsub⁻¹ (t ⋆ f) t⋆f))) ,
        λ (v , Hv) → {! \  !} } }
