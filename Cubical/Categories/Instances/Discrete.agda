-- Discrete category over a type A
-- A must be an h-groupoid for the homs to be sets
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Discrete where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport

private
  variable
    ℓ ℓC ℓC' : Level

open Category

-- Discrete category
DiscreteCategory : hGroupoid ℓ → Category ℓ ℓ
DiscreteCategory A .ob = A .fst
DiscreteCategory A .Hom[_,_] a a' = a ≡ a'
DiscreteCategory A .id = refl
DiscreteCategory A ._⋆_ = _∙_
DiscreteCategory A .⋆IdL f = sym (lUnit f)
DiscreteCategory A .⋆IdR f = sym (rUnit f)
DiscreteCategory A .⋆Assoc f g h = sym (assoc f g h)
DiscreteCategory A .isSetHom {x} {y} = A .snd x y


module _ {A : hGroupoid ℓ}
         {C : Category ℓC ℓC'} where
  open Functor

  -- Functions f: A → ob C give functors F: DiscreteCategory A → C
  DiscFunc : (fst A → ob C) → Functor (DiscreteCategory A) C
  DiscFunc f .F-ob = f
  DiscFunc f .F-hom {x} p = subst (λ z → C [ f x , f z ]) p (id C)
  DiscFunc f .F-id {x} = substRefl {B = λ z → C [ f x , f z ]} (id C)

  -- Preserves composition
  DiscFunc f .F-seq {x} {y} p q =
      let open Category C using () renaming (_⋆_ to _●_) in

      let Hom[fx,f—] = (λ (w : A .fst) → C [ f x , f w ]) in
      let Hom[fy,f—] = (λ (w : A .fst) → C [ f y , f w ]) in
      let id-fx = id C {f x} in
      let id-fy = id C {f y} in
      let Fp = (subst Hom[fx,f—] (p) id-fx) in

      subst Hom[fx,f—] (p ∙ q) id-fx            ≡⟨ substComposite Hom[fx,f—] _ _ _ ⟩
      subst Hom[fx,f—] (q) (Fp)                 ≡⟨ cong (subst _ q) (sym (⋆IdR C _)) ⟩
      subst Hom[fx,f—] (q) (Fp ● id-fy)         ≡⟨ substCommSlice _ _ (λ _ → Fp ●_) q _ ⟩
      Fp ● (subst Hom[fy,f—] (q) id-fy)         ∎
