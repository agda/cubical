{-# OPTIONS --safe #-}

module Cubical.Categories.Monoidal.Cartesian where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') (binProd : BinProducts C) (term : Terminal C) where
  open Functor
  open BinProduct
  open Category C

  private
    _×_ : ob -> ob -> ob
    _×_ x y = binProdOb (binProd x y)

    variable
      x y z w : ob
      f g h k : Hom[ z , x ]

    pr1 : Hom[ x × y , x ]
    pr1 = binProdPr₁ (binProd _ _)

    pr2 : Hom[ x × y , y ]
    pr2 = binProdPr₂ (binProd _ _)

    ⟨_,_⟩ : Hom[ z , x ] -> Hom[ z , y ] -> Hom[ z , x × y ]
    ⟨_,_⟩ f g = fst (fst (univProp (binProd _ _) f g))

    _×ₕ_ : Hom[ x , y ] -> Hom[ z , w ] -> Hom[ x × z , y × w ]
    _×ₕ_ f g = ⟨ pr1 ⋆ f , pr2 ⋆ g ⟩

    ⟨─,─⟩-isUnique : h ⋆ pr1 ≡ f -> h ⋆ pr2 ≡ g -> ⟨ f , g ⟩ ≡ h
    ⟨─,─⟩-isUnique {h = h} {f = f} {g = g} pr1-path pr2-path i = fst (snd (univProp (binProd _ _) f g) (h , pr1-path , pr2-path) i)

    ⟨─,─⟩-pr1 : ⟨ f , g ⟩ ⋆ pr1 ≡ f
    ⟨─,─⟩-pr1 {f = f} {g = g} = univProp (binProd _ _) f g .fst .snd .fst

    ⟨─,─⟩-pr2 : ⟨ f , g ⟩ ⋆ pr2 ≡ g
    ⟨─,─⟩-pr2 {f = f} {g = g} = univProp (binProd _ _) f g .fst .snd .snd

    ⟨─,─⟩-compLeft : h ⋆ ⟨ f , g ⟩ ≡ ⟨ h ⋆ f , h ⋆ g ⟩
    ⟨─,─⟩-compLeft {h = h} {f = f} {g = g} = sym (⟨─,─⟩-isUnique
      (⋆Assoc _ _ _ ∙ cong (h ⋆_) ⟨─,─⟩-pr1)
      (⋆Assoc _ _ _ ∙ cong (h ⋆_) ⟨─,─⟩-pr2))


    ⟨─,─⟩-compRight : ⟨ f , g ⟩ ⋆ (h ×ₕ k) ≡ ⟨ f ⋆ h , g ⋆ k ⟩
    ⟨─,─⟩-compRight = sym (⟨─,─⟩-isUnique
      ( ⋆Assoc _ _ _
      ∙ cong (_ ⋆_) ⟨─,─⟩-pr1
      ∙ sym (⋆Assoc _ _ _)
      ∙ cong (_⋆ _) ⟨─,─⟩-pr1 )

      ( ⋆Assoc _ _ _
      ∙ cong (_ ⋆_) ⟨─,─⟩-pr2
      ∙ sym (⋆Assoc _ _ _)
      ∙ cong (_⋆ _) ⟨─,─⟩-pr2 ) )

  cartesianTensorStr : TensorStr C
  TensorStr.─⊗─ cartesianTensorStr .F-ob (x , y) = x × y
  TensorStr.─⊗─ cartesianTensorStr .F-hom (f , g) = f ×ₕ g
  TensorStr.─⊗─ cartesianTensorStr .F-id = ⟨─,─⟩-isUnique (⋆IdL _ ∙ sym (⋆IdR _)) (⋆IdL _ ∙ sym (⋆IdR _))
  TensorStr.─⊗─ cartesianTensorStr .F-seq (f , f') (g , g') = ⟨─,─⟩-isUnique lem1 lem2
    where
      lem1 : ((f ×ₕ f') ⋆ (g ×ₕ g')) ⋆ pr1 ≡ pr1 ⋆ f ⋆ g
      lem1 = ⋆Assoc _ _ _
           ∙ ⟨ refl ⟩⋆⟨ ⟨─,─⟩-pr1 ⟩
           ∙ sym (⋆Assoc _ _ _)
           ∙ ⟨ ⟨─,─⟩-pr1 ⟩⋆⟨ refl ⟩
           ∙ ⋆Assoc _ _ _

      lem2 : ((f ×ₕ f') ⋆ (g ×ₕ g')) ⋆ pr2 ≡ pr2 ⋆ f' ⋆ g'
      lem2 = ⋆Assoc _ _ _
           ∙ ⟨ refl ⟩⋆⟨ ⟨─,─⟩-pr2 ⟩
           ∙ sym (⋆Assoc _ _ _)
           ∙ ⟨ ⟨─,─⟩-pr2 ⟩⋆⟨ refl ⟩
           ∙ ⋆Assoc _ _ _

  TensorStr.unit cartesianTensorStr = fst term

  open TensorStr cartesianTensorStr

  private
    terminalMap : Hom[ x , unit ]
    terminalMap = fst (snd term _)

    terminalMapUnique : {f g : Hom[ x , unit ]} -> f ≡ g
    terminalMapUnique = sym (snd (snd term _) _) ∙ snd (snd term _) _

    1×─ : Functor C C
    1×─ = ─⊗─ ∘F rinj _ _ unit

    ─×1 : Functor C C
    ─×1 = ─⊗─ ∘F linj _ _ unit

    prodAssocRight : Functor (C ×C C ×C C) C
    prodAssocRight = ─⊗─ ∘F (Id ×F ─⊗─)

    prodAssocLeft : Functor (C ×C C ×C C) C
    prodAssocLeft = ─⊗─ ∘F (─⊗─ ×F Id) ∘F (×C-assoc C C C)

    open NatIso
    open NatTrans
    open isIso

    leftUnitor : NatIso 1×─ Id
    leftUnitor .trans .N-ob _ = pr2
    leftUnitor .trans .N-hom _ = ⟨─,─⟩-pr2
    leftUnitor .nIso x .inv = ⟨ terminalMap , id ⟩
    leftUnitor .nIso x .sec = ⟨─,─⟩-pr2
    leftUnitor .nIso x .ret = ⟨─,─⟩-compLeft ∙ ⟨─,─⟩-isUnique terminalMapUnique ((⋆IdL _) ∙ sym (⋆IdR _))

    rightUnitor : NatIso ─×1 Id
    rightUnitor .trans .N-ob _ = pr1
    rightUnitor .trans .N-hom _ = ⟨─,─⟩-pr1
    rightUnitor .nIso x .inv = ⟨ id , terminalMap ⟩
    rightUnitor .nIso x .sec = ⟨─,─⟩-pr1
    rightUnitor .nIso x .ret = ⟨─,─⟩-compLeft ∙ ⟨─,─⟩-isUnique (⋆IdL _ ∙ sym (⋆IdR _)) terminalMapUnique

    associator : NatIso prodAssocRight prodAssocLeft

    associator .trans .N-ob _ = ⟨ ⟨ pr1 , pr2 ⋆ pr1 ⟩ , pr2 ⋆ pr2 ⟩

    associator .trans .N-hom (f , g , h) = ⟨─,─⟩-compLeft
                                         ∙ cong₂ ⟨_,_⟩ prodAssocRight-pr12 prodAssocRight-pr3
                                         ∙ sym ⟨─,─⟩-compRight
      where
        prodAssocRight-pr1 : prodAssocRight .F-hom (f , g , h) ⋆ pr1 ≡ pr1 ⋆ f
        prodAssocRight-pr1 = ⟨─,─⟩-pr1

        prodAssocRight-pr2 : prodAssocRight .F-hom (f , g , h) ⋆ pr2 ⋆ pr1 ≡ (pr2 ⋆ pr1) ⋆ g
        prodAssocRight-pr2 = sym (⋆Assoc _ _ _)
                           ∙ ⟨ ⟨─,─⟩-pr2 ⟩⋆⟨ refl ⟩
                           ∙ ⋆Assoc _ _ _
                           ∙ ⟨ refl ⟩⋆⟨ ⟨─,─⟩-pr1 ⟩
                           ∙ sym (⋆Assoc _ _ _)

        prodAssocRight-pr12 : prodAssocRight .F-hom (f , g , h) ⋆ ⟨ pr1 , pr2 ⋆ pr1 ⟩ ≡ ⟨ pr1 , pr2 ⋆ pr1 ⟩ ⋆ (f ×ₕ g)
        prodAssocRight-pr12 = ⟨─,─⟩-compLeft
                            ∙ cong₂ ⟨_,_⟩ prodAssocRight-pr1 prodAssocRight-pr2
                            ∙ sym ⟨─,─⟩-compRight

        prodAssocRight-pr3 : prodAssocRight .F-hom (f , g , h) ⋆ pr2 ⋆ pr2 ≡ (pr2 ⋆ pr2) ⋆ h
        prodAssocRight-pr3 = sym (⋆Assoc _ _ _)
                           ∙ cong (_⋆ pr2) ⟨─,─⟩-pr2
                           ∙ ⋆Assoc _ _ _
                           ∙ cong (pr2 ⋆_) ⟨─,─⟩-pr2
                           ∙ sym (⋆Assoc _ _ _)

    associator .nIso x .inv = ⟨ pr1 ⋆ pr1 , ⟨ pr1 ⋆ pr2 , pr2 ⟩ ⟩
    associator .nIso x .sec = ⟨─,─⟩-compLeft
                            ∙ cong₂ ⟨_,_⟩
                                ( ⟨─,─⟩-compLeft
                                ∙ cong₂ ⟨_,_⟩
                                    ⟨─,─⟩-pr1
                                    (sym (⋆Assoc _ _ _) ∙ ⟨ ⟨─,─⟩-pr2 ⟩⋆⟨ refl ⟩ ∙ ⟨─,─⟩-pr1 ) )

                                ( sym (⋆Assoc _ _ _)
                                ∙ ⟨ ⟨─,─⟩-pr2 ⟩⋆⟨ refl ⟩
                                ∙ ⟨─,─⟩-pr2 )

                            ∙ ⟨─,─⟩-isUnique (sym (⟨─,─⟩-isUnique ⟨ ⋆IdL _ ⟩⋆⟨ refl ⟩ ⟨ ⋆IdL _ ⟩⋆⟨ refl ⟩)) (⋆IdL _)

    associator .nIso x .ret = ⟨─,─⟩-compLeft
                            ∙ ⟨─,─⟩-isUnique
                                ( ⋆IdL _
                                ∙ sym ⟨─,─⟩-pr1
                                ∙ ⟨ sym ⟨─,─⟩-pr1 ⟩⋆⟨ refl ⟩
                                ∙ ⋆Assoc _ _ _ )

                                ( ⋆IdL _
                                ∙ sym (⟨─,─⟩-isUnique refl refl)
                                ∙ cong₂ ⟨_,_⟩
                                    ( sym ⟨─,─⟩-pr2
                                    ∙ ⟨ sym ⟨─,─⟩-pr1 ⟩⋆⟨ refl ⟩
                                    ∙ ⋆Assoc _ _ _ )
                                    ( sym ⟨─,─⟩-pr2 )
                                ∙ sym ⟨─,─⟩-compLeft )


  cartesianMonoidalStr : MonoidalStr C
  MonoidalStr.tenstr cartesianMonoidalStr = cartesianTensorStr
  MonoidalStr.α cartesianMonoidalStr = associator
  MonoidalStr.η cartesianMonoidalStr = leftUnitor
  MonoidalStr.ρ cartesianMonoidalStr = rightUnitor
  MonoidalStr.pentagon cartesianMonoidalStr x y z w = ⟨ refl ⟩⋆⟨ ⟨─,─⟩-compRight ⟩
                                           ∙ ⟨─,─⟩-compLeft
                                           ∙ ⟨─,─⟩-isUnique lem1 lem2
                                           ∙ sym ⟨─,─⟩-compLeft
    where
      lem1 : ⟨ ⟨ ⟨ pr1 , pr2 ⋆ pr1 ⟩ ,  pr2 ⋆ pr2 ⟩ ⋆ ⟨ pr1 , pr2 ⋆ pr1 ⟩
             , ⟨ ⟨ pr1 , pr2 ⋆ pr1 ⟩ , pr2 ⋆ pr2 ⟩ ⋆ pr2 ⋆ pr2
             ⟩ ⋆ pr1
           ≡ (id ×ₕ ⟨ ⟨ pr1 , pr2 ⋆ pr1 ⟩ , pr2 ⋆ pr2 ⟩) ⋆ ⟨ pr1 , pr2 ⋆ pr1 ⟩ ⋆ ⟨ ⟨ pr1 , pr2 ⋆ pr1 ⟩ , pr2 ⋆ pr2 ⟩
      lem1 = ⟨─,─⟩-pr1
           ∙ ⟨─,─⟩-compLeft

           ∙ (cong₂ ⟨_,_⟩
                ( ⟨─,─⟩-pr1
                ∙ cong₂ ⟨_,_⟩
                    (sym ⟨─,─⟩-pr1)
                    ( sym ⟨─,─⟩-pr1
                    ∙ ⟨ sym ⟨─,─⟩-pr2 ⟩⋆⟨ refl ⟩
                    ∙ ⋆Assoc _ _ _ )
                ∙ sym ⟨─,─⟩-compLeft )

                ( sym (⋆Assoc _ _ _)
                ∙ ⟨ ⟨─,─⟩-pr2 ⟩⋆⟨ refl ⟩
                ∙ ⋆Assoc _ _ _
                ∙ sym ⟨─,─⟩-pr2
                ∙ ⟨ sym ⟨─,─⟩-pr2 ⟩⋆⟨ refl ⟩
                ∙ ⋆Assoc _ _ _ ))

           ∙ sym ⟨─,─⟩-compLeft
           ∙ ⟨ cong₂ ⟨_,_⟩
                 (sym (⋆IdR _) ∙ sym ⟨─,─⟩-pr1)
                 ( sym ⟨─,─⟩-pr1
                 ∙ ⟨ cong₂ ⟨_,_⟩ (sym ⟨─,─⟩-compLeft) refl
                   ∙ sym ⟨─,─⟩-compLeft
                   ∙ sym ⟨─,─⟩-pr2
                   ⟩⋆⟨ refl ⟩
                 ∙ ⋆Assoc _ _ _ )
             ∙ sym ⟨─,─⟩-compLeft
             ⟩⋆⟨ refl ⟩
           ∙ ⋆Assoc _ _ _

      lem2 : ⟨ ⟨ ⟨ pr1 , pr2 ⋆ pr1 ⟩ , pr2 ⋆ pr2 ⟩ ⋆ ⟨ pr1 , pr2 ⋆ pr1 ⟩
             , ⟨ ⟨ pr1 , pr2 ⋆ pr1 ⟩ , pr2 ⋆ pr2 ⟩ ⋆ pr2 ⋆ pr2
             ⟩ ⋆ pr2
          ≡ (id ×ₕ ⟨ ⟨ pr1 , pr2 ⋆ pr1 ⟩ , pr2 ⋆ pr2 ⟩) ⋆ (pr2 ⋆ pr2) ⋆ id
      lem2 = ⟨─,─⟩-pr2
           ∙ sym (⋆Assoc _ _ _)
           ∙ ⟨ ⟨─,─⟩-pr2 ⟩⋆⟨ refl ⟩
           ∙ ⋆Assoc _ _ _
           ∙ ⟨ refl ⟩⋆⟨ sym ⟨─,─⟩-pr2 ⟩
           ∙ sym (⋆Assoc _ _ _)
           ∙ ⟨ sym ⟨─,─⟩-pr2 ⟩⋆⟨ refl ⟩
           ∙ ⋆Assoc _ _ _
           ∙ sym (⋆IdR _)
           ∙ ⋆Assoc _ _ _

  MonoidalStr.triangle cartesianMonoidalStr x y
    = ⟨─,─⟩-compRight
    ∙ ⟨─,─⟩-isUnique
        (⟨─,─⟩-pr1 ∙ ⋆IdR _ ∙ sym ⟨─,─⟩-pr1)
        (⟨─,─⟩-pr2 ∙ sym (⋆IdR _))
