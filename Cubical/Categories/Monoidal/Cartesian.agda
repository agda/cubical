
module Cubical.Categories.Monoidal.Cartesian where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.Terminal as Terminal using (Terminal)
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.NaturalTransformation

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') (binProd : BinProducts C) (term : Terminal C) where
  open Functor
  open Category C

  open BinProducts C binProd
    using ()
    renaming ( binProdOb to _×_
             ; binProdPr₁ to pr₁
             ; binProdPr₂ to pr₂
             ; binProdArrow to ⟨_,_⟩
             ; binProdMap to _×ₕ_
             ; binProdArrowUnique to ⟨,⟩unique
             ; binProdArrowPr₁ to ⟨,⟩pr₁
             ; binProdArrowPr₂ to ⟨,⟩pr₂
             ; binProdArrowCompLeft to ⟨,⟩compLeft
             ; binProdArrowCompRight to ⟨,⟩compRight)

  cartesianTensorStr : TensorStr C
  TensorStr.─⊗─ cartesianTensorStr .F-ob (x , y) = x × y
  TensorStr.─⊗─ cartesianTensorStr .F-hom (f , g) = f ×ₕ g
  TensorStr.─⊗─ cartesianTensorStr .F-id = ⟨,⟩unique (⋆IdL _ ∙ sym (⋆IdR _)) (⋆IdL _ ∙ sym (⋆IdR _))
  TensorStr.─⊗─ cartesianTensorStr .F-seq (f , f') (g , g') = ⟨,⟩unique lem1 lem2
    where
      lem1 : ((f ×ₕ f') ⋆ (g ×ₕ g')) ⋆ pr₁ ≡ pr₁ ⋆ f ⋆ g
      lem1 = ⋆Assoc _ _ _
           ∙ ⟨ refl ⟩⋆⟨ ⟨,⟩pr₁ ⟩
           ∙ sym (⋆Assoc _ _ _)
           ∙ ⟨ ⟨,⟩pr₁ ⟩⋆⟨ refl ⟩
           ∙ ⋆Assoc _ _ _

      lem2 : ((f ×ₕ f') ⋆ (g ×ₕ g')) ⋆ pr₂ ≡ pr₂ ⋆ f' ⋆ g'
      lem2 = ⋆Assoc _ _ _
           ∙ ⟨ refl ⟩⋆⟨ ⟨,⟩pr₂ ⟩
           ∙ sym (⋆Assoc _ _ _)
           ∙ ⟨ ⟨,⟩pr₂ ⟩⋆⟨ refl ⟩
           ∙ ⋆Assoc _ _ _

  TensorStr.unit cartesianTensorStr = fst term

  open TensorStr cartesianTensorStr

  private
    terminalArrow : ∀ {x} -> Hom[ x , unit ]
    terminalArrow {x} = Terminal.terminalArrow C term x

    terminalArrowUnique : ∀ {x} {f g : Hom[ x , unit ]} -> f ≡ g
    terminalArrowUnique {f = f} {g = g} = sym (Terminal.terminalArrowUnique C {term} f) ∙ Terminal.terminalArrowUnique C {term} g

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
    leftUnitor .trans .N-ob _ = pr₂
    leftUnitor .trans .N-hom _ = ⟨,⟩pr₂
    leftUnitor .nIso x .inv = ⟨ terminalArrow , id ⟩
    leftUnitor .nIso x .sec = ⟨,⟩pr₂
    leftUnitor .nIso x .ret = ⟨,⟩compLeft ∙ ⟨,⟩unique terminalArrowUnique ((⋆IdL _) ∙ sym (⋆IdR _))

    rightUnitor : NatIso ─×1 Id
    rightUnitor .trans .N-ob _ = pr₁
    rightUnitor .trans .N-hom _ = ⟨,⟩pr₁
    rightUnitor .nIso x .inv = ⟨ id , terminalArrow ⟩
    rightUnitor .nIso x .sec = ⟨,⟩pr₁
    rightUnitor .nIso x .ret = ⟨,⟩compLeft ∙ ⟨,⟩unique (⋆IdL _ ∙ sym (⋆IdR _)) terminalArrowUnique

    associator : NatIso prodAssocRight prodAssocLeft

    associator .trans .N-ob _ = ⟨ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩ , pr₂ ⋆ pr₂ ⟩

    associator .trans .N-hom (f , g , h) = ⟨,⟩compLeft
                                         ∙ cong₂ ⟨_,_⟩ prodAssocRight-pr₁2 prodAssocRight-pr3
                                         ∙ sym ⟨,⟩compRight
      where
        prodAssocRight-pr₁ : prodAssocRight .F-hom (f , g , h) ⋆ pr₁ ≡ pr₁ ⋆ f
        prodAssocRight-pr₁ = ⟨,⟩pr₁

        prodAssocRight-pr₂ : prodAssocRight .F-hom (f , g , h) ⋆ pr₂ ⋆ pr₁ ≡ (pr₂ ⋆ pr₁) ⋆ g
        prodAssocRight-pr₂ = sym (⋆Assoc _ _ _)
                           ∙ ⟨ ⟨,⟩pr₂ ⟩⋆⟨ refl ⟩
                           ∙ ⋆Assoc _ _ _
                           ∙ ⟨ refl ⟩⋆⟨ ⟨,⟩pr₁ ⟩
                           ∙ sym (⋆Assoc _ _ _)

        prodAssocRight-pr₁2 : prodAssocRight .F-hom (f , g , h) ⋆ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩ ≡ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩ ⋆ (f ×ₕ g)
        prodAssocRight-pr₁2 = ⟨,⟩compLeft
                            ∙ cong₂ ⟨_,_⟩ prodAssocRight-pr₁ prodAssocRight-pr₂
                            ∙ sym ⟨,⟩compRight

        prodAssocRight-pr3 : prodAssocRight .F-hom (f , g , h) ⋆ pr₂ ⋆ pr₂ ≡ (pr₂ ⋆ pr₂) ⋆ h
        prodAssocRight-pr3 = sym (⋆Assoc _ _ _)
                           ∙ cong (_⋆ pr₂) ⟨,⟩pr₂
                           ∙ ⋆Assoc _ _ _
                           ∙ cong (pr₂ ⋆_) ⟨,⟩pr₂
                           ∙ sym (⋆Assoc _ _ _)

    associator .nIso x .inv = ⟨ pr₁ ⋆ pr₁ , ⟨ pr₁ ⋆ pr₂ , pr₂ ⟩ ⟩
    associator .nIso x .sec = ⟨,⟩compLeft
                            ∙ cong₂ ⟨_,_⟩
                                ( ⟨,⟩compLeft
                                ∙ cong₂ ⟨_,_⟩
                                    ⟨,⟩pr₁
                                    (sym (⋆Assoc _ _ _) ∙ ⟨ ⟨,⟩pr₂ ⟩⋆⟨ refl ⟩ ∙ ⟨,⟩pr₁ ) )

                                ( sym (⋆Assoc _ _ _)
                                ∙ ⟨ ⟨,⟩pr₂ ⟩⋆⟨ refl ⟩
                                ∙ ⟨,⟩pr₂ )

                            ∙ ⟨,⟩unique (sym (⟨,⟩unique ⟨ ⋆IdL _ ⟩⋆⟨ refl ⟩ ⟨ ⋆IdL _ ⟩⋆⟨ refl ⟩)) (⋆IdL _)

    associator .nIso x .ret = ⟨,⟩compLeft
                            ∙ ⟨,⟩unique
                                ( ⋆IdL _
                                ∙ sym ⟨,⟩pr₁
                                ∙ ⟨ sym ⟨,⟩pr₁ ⟩⋆⟨ refl ⟩
                                ∙ ⋆Assoc _ _ _ )

                                ( ⋆IdL _
                                ∙ sym (⟨,⟩unique refl refl)
                                ∙ cong₂ ⟨_,_⟩
                                    ( sym ⟨,⟩pr₂
                                    ∙ ⟨ sym ⟨,⟩pr₁ ⟩⋆⟨ refl ⟩
                                    ∙ ⋆Assoc _ _ _ )
                                    ( sym ⟨,⟩pr₂ )
                                ∙ sym ⟨,⟩compLeft )


  cartesianMonoidalStr : MonoidalStr C
  MonoidalStr.tenstr cartesianMonoidalStr = cartesianTensorStr
  MonoidalStr.α cartesianMonoidalStr = associator
  MonoidalStr.η cartesianMonoidalStr = leftUnitor
  MonoidalStr.ρ cartesianMonoidalStr = rightUnitor
  MonoidalStr.pentagon cartesianMonoidalStr x y z w = ⟨ refl ⟩⋆⟨ ⟨,⟩compRight ⟩
                                           ∙ ⟨,⟩compLeft
                                           ∙ ⟨,⟩unique lem1 lem2
                                           ∙ sym ⟨,⟩compLeft
    where
      lem1 : ⟨ ⟨ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩ ,  pr₂ ⋆ pr₂ ⟩ ⋆ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩
             , ⟨ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩ , pr₂ ⋆ pr₂ ⟩ ⋆ pr₂ ⋆ pr₂
             ⟩ ⋆ pr₁
           ≡ (id ×ₕ ⟨ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩ , pr₂ ⋆ pr₂ ⟩) ⋆ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩ ⋆ ⟨ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩ , pr₂ ⋆ pr₂ ⟩
      lem1 = ⟨,⟩pr₁
           ∙ ⟨,⟩compLeft

           ∙ (cong₂ ⟨_,_⟩
                ( ⟨,⟩pr₁
                ∙ cong₂ ⟨_,_⟩
                    (sym ⟨,⟩pr₁)
                    ( sym ⟨,⟩pr₁
                    ∙ ⟨ sym ⟨,⟩pr₂ ⟩⋆⟨ refl ⟩
                    ∙ ⋆Assoc _ _ _ )
                ∙ sym ⟨,⟩compLeft )

                ( sym (⋆Assoc _ _ _)
                ∙ ⟨ ⟨,⟩pr₂ ⟩⋆⟨ refl ⟩
                ∙ ⋆Assoc _ _ _
                ∙ sym ⟨,⟩pr₂
                ∙ ⟨ sym ⟨,⟩pr₂ ⟩⋆⟨ refl ⟩
                ∙ ⋆Assoc _ _ _ ))

           ∙ sym ⟨,⟩compLeft
           ∙ ⟨ cong₂ ⟨_,_⟩
                 (sym (⋆IdR _) ∙ sym ⟨,⟩pr₁)
                 ( sym ⟨,⟩pr₁
                 ∙ ⟨ cong₂ ⟨_,_⟩ (sym ⟨,⟩compLeft) refl
                   ∙ sym ⟨,⟩compLeft
                   ∙ sym ⟨,⟩pr₂
                   ⟩⋆⟨ refl ⟩
                 ∙ ⋆Assoc _ _ _ )
             ∙ sym ⟨,⟩compLeft
             ⟩⋆⟨ refl ⟩
           ∙ ⋆Assoc _ _ _

      lem2 : ⟨ ⟨ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩ , pr₂ ⋆ pr₂ ⟩ ⋆ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩
             , ⟨ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩ , pr₂ ⋆ pr₂ ⟩ ⋆ pr₂ ⋆ pr₂
             ⟩ ⋆ pr₂
          ≡ (id ×ₕ ⟨ ⟨ pr₁ , pr₂ ⋆ pr₁ ⟩ , pr₂ ⋆ pr₂ ⟩) ⋆ (pr₂ ⋆ pr₂) ⋆ id
      lem2 = ⟨,⟩pr₂
           ∙ sym (⋆Assoc _ _ _)
           ∙ ⟨ ⟨,⟩pr₂ ⟩⋆⟨ refl ⟩
           ∙ ⋆Assoc _ _ _
           ∙ ⟨ refl ⟩⋆⟨ sym ⟨,⟩pr₂ ⟩
           ∙ sym (⋆Assoc _ _ _)
           ∙ ⟨ sym ⟨,⟩pr₂ ⟩⋆⟨ refl ⟩
           ∙ ⋆Assoc _ _ _
           ∙ sym (⋆IdR _)
           ∙ ⋆Assoc _ _ _

  MonoidalStr.triangle cartesianMonoidalStr x y
    = ⟨,⟩compRight
    ∙ ⟨,⟩unique
        (⟨,⟩pr₁ ∙ ⋆IdR _ ∙ sym ⟨,⟩pr₁)
        (⟨,⟩pr₂ ∙ sym (⋆IdR _))
