-- Product of two categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.BinProduct where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level


open Category

_×C_ : (C : Category ℓC ℓC') → (D : Category ℓD ℓD')
    → Category (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')

(C ×C D) .ob = (ob C) × (ob D)
(C ×C D) .Hom[_,_] (c , d) (c' , d') = (C [ c , c' ]) × (D [ d , d' ])
(C ×C D) .id = (id C , id D)
(C ×C D) ._⋆_ _ _ = (_ ⋆⟨ C ⟩ _ , _ ⋆⟨ D ⟩ _)
(C ×C D) .⋆IdL _ = ≡-× (⋆IdL C _) (⋆IdL D _)
(C ×C D) .⋆IdR _ = ≡-× (⋆IdR C _) (⋆IdR D _)
(C ×C D) .⋆Assoc _ _ _ = ≡-× (⋆Assoc C _ _ _) (⋆Assoc D _ _ _)
(C ×C D) .isSetHom = isSet× (isSetHom C) (isSetHom D)

infixr 5 _×C_

open Functor

Fst : (C : Category ℓC ℓC') → (D : Category ℓD ℓD') → Functor (C ×C D) C
F-ob (Fst C D) = fst
F-hom (Fst C D) = fst
F-id (Fst C D) = refl
F-seq (Fst C D) _ _ = refl

Snd : (C : Category ℓC ℓC') → (D : Category ℓD ℓD') → Functor (C ×C D) D
F-ob (Snd C D) = snd
F-hom (Snd C D) = snd
F-id (Snd C D) = refl
F-seq (Snd C D) _ _ = refl

module _ where
  private
    variable
      A : Category ℓA ℓA'
      B : Category ℓB ℓB'
      C : Category ℓC ℓC'
      D : Category ℓD ℓD'
      E : Category ℓE ℓE'

  open Functor

  _,F_ : Functor C D → Functor C E → Functor C (D ×C E)
  (G ,F H) .F-ob a = (G ⟅ a ⟆ , H ⟅ a ⟆)
  (G ,F H) .F-hom g = (G ⟪ g ⟫ , H ⟪ g ⟫)
  (G ,F H) .F-id = ≡-× (G .F-id) (H .F-id)
  (G ,F H) .F-seq _ _ = ≡-× (G .F-seq _ _) (H .F-seq _ _)

  _×F_ : Functor A C → Functor B D → Functor (A ×C B) (C ×C D)
  _×F_ {A = A} {B = B} G H = G ∘F Fst A B ,F H ∘F Snd A B

-- Some useful functors
module _ (C : Category ℓC ℓC')
         (D : Category ℓD ℓD') where
  open Functor

  module _ (E : Category ℓE ℓE') where
    -- Associativity of product
    ×C-assoc : Functor (C ×C (D ×C E)) ((C ×C D) ×C E)
    ×C-assoc .F-ob (c , (d , e)) = ((c , d), e)
    ×C-assoc .F-hom (f , (g , h)) = ((f , g), h)
    ×C-assoc .F-id = refl
    ×C-assoc .F-seq _ _ = refl

  -- Left/right injections into product
  linj : (d : ob D) → Functor C (C ×C D)
  linj d = Id ,F Constant C D d

  rinj : (c : ob C) → Functor D (C ×C D)
  rinj c = Constant D C c ,F Id

{-
  TODO:
    - define inverse to `assoc`, prove isomorphism
    - prove product is commutative up to isomorphism
-}


  -- The isomorphisms in product category

  open isIso

  CatIso× : {x y : C .ob}{z w : D .ob} → CatIso C x y → CatIso D z w → CatIso (C ×C D) (x , z) (y , w)
  CatIso× f g .fst = f .fst , g .fst
  CatIso× f g .snd .inv = f .snd .inv , g .snd .inv
  CatIso× f g .snd .sec i = f .snd .sec i , g .snd .sec i
  CatIso× f g .snd .ret i = f .snd .ret i , g .snd .ret i
