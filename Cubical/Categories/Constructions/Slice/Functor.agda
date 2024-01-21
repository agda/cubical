{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Slice.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import Cubical.Categories.Category
open import Cubical.Categories.Category.Properties
open import Cubical.Categories.Constructions.Slice.Base
open import Cubical.Categories.Constructions.Slice.Properties

open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint

open Category hiding (_∘_)
open _≃ᶜ_
open Functor
open NatTrans

private
  variable
    ℓ ℓ' : Level
    C D : Category ℓ ℓ'
    c d : C .ob

infix 39 _F/_
infix 40 _﹗

_F/_ : ∀ (F : Functor C D) c → Functor (SliceCat C c) (SliceCat D (F ⟅ c ⟆))
F-ob (F F/ c) = sliceob ∘ F-hom F ∘ S-arr
F-hom (F F/ c) h = slicehom _
  $ sym ( F-seq F _ _) ∙ cong (F-hom F) (S-comm h)
F-id (F F/ c) = SliceHom-≡-intro' _ _  $ F-id F
F-seq (F F/ c) _ _ = SliceHom-≡-intro' _ _  $ F-seq F _ _

_﹗ : ∀ {c d} f → Functor  (SliceCat C c) (SliceCat C d)
F-ob (_﹗ {C = C} f) (sliceob x) = sliceob (_⋆_ C x f)
F-hom (_﹗ {C = C} f) (slicehom h p) = slicehom _ $
  sym (C .⋆Assoc _ _ _) ∙ cong (λ x → (_⋆_ C x f)) p
F-id (f ﹗) = SliceHom-≡-intro' _ _ refl
F-seq (f ﹗) _ _ = SliceHom-≡-intro' _ _ refl

module Pullbacks (Pbs : Pullbacks C) where

 open Pullback

 _⋆ᶜ_ = C ._⋆_

 module BaseChange {c d} (𝑓 : C [ c , d ]) where

  module _ {x : SliceCat C d .ob} where
   pb = Pbs (cospan c d _ 𝑓 (x .S-arr))

   module _ {y : SliceCat C d .ob} (h : (SliceCat C d) [ y , x ]) where

    pbU : _
    pbU = let pbx = Pbs (cospan c d _ 𝑓 (y .S-arr))
     in univProp pb
           (pbPr₁ pbx) (h .S-hom ∘⟨ C ⟩ pbPr₂ pbx) 
            (pbCommutes pbx ∙∙ 
                cong (C ⋆ pbPr₂ (Pbs (cospan c d (S-ob y) _ (y .S-arr))))
                  (sym (h .S-comm)) ∙∙ sym (C .⋆Assoc _ _ _)) 
  infix 40 _＊

  _＊ : Functor (SliceCat C d) (SliceCat C c)
  F-ob _＊ x = sliceob (pbPr₁ pb)
  F-hom _＊ f =
    let ((f' , (u , _)) , _) = pbU f
    in slicehom f' (sym u)
  F-id _＊ = SliceHom-≡-intro' _ _ $
     univProp' pb (sym (C .⋆IdL _)) (C .⋆IdR _ ∙ sym (C .⋆IdL _))

  F-seq _＊ _ _ =
   let (u₁ , v₁) = pbU _ .fst .snd
       (u₂ , v₂) = pbU _ .fst .snd
   in SliceHom-≡-intro' _ _ $ univProp' pb
       (u₂ ∙∙ cong (C ⋆ _) u₁ ∙∙ sym (C .⋆Assoc _ _ _))
       (sym (C .⋆Assoc _ _ _) ∙∙ cong (λ x → (C ⋆ x) _) v₂ ∙∙
                     AssocCong₂⋆R C v₁)

 open BaseChange using (_＊)
 open NaturalBijection renaming (_⊣_ to _⊣₂_) 
 open Iso
 open _⊣₂_


 module _ (𝑓 : C [ c , d ]) where

  open BaseChange 𝑓 using (pb ; pbU)
 
  𝑓﹗⊣𝑓＊ : 𝑓 ﹗ ⊣₂ 𝑓 ＊
  fun (adjIso 𝑓﹗⊣𝑓＊) (slicehom h o) =
   let ((_ , (p , _)) , _) = univProp pb _ _ (sym o)
   in slicehom _ (sym p)
  inv (adjIso 𝑓﹗⊣𝑓＊) (slicehom h o) = slicehom _ $
    AssocCong₂⋆R C (sym (pbCommutes pb)) ∙ cong (_⋆ᶜ 𝑓) o
  rightInv (adjIso 𝑓﹗⊣𝑓＊) (slicehom h o) =
    SliceHom-≡-intro' _ _ (univProp' pb (sym o) refl)
  leftInv (adjIso 𝑓﹗⊣𝑓＊) (slicehom h o) =
   let ((_ , (_ , q)) , _) = univProp pb _ _ _
   in SliceHom-≡-intro' _ _ (sym q)
  adjNatInD 𝑓﹗⊣𝑓＊ f k = SliceHom-≡-intro' _ _ $
    let ((h' , (v' , u')) , _) = univProp pb _ _ _
        ((_ , (v'' , u'')) , _) = univProp pb _ _ _
    in univProp' pb (v' ∙∙ cong (h' ⋆ᶜ_) v'' ∙∙ sym (C .⋆Assoc _ _ _))
                    (cong (_⋆ᶜ _) u' ∙ AssocCong₂⋆R C u'')

  adjNatInC 𝑓﹗⊣𝑓＊ g h = SliceHom-≡-intro' _ _ $ C .⋆Assoc _ _ _ 


 open UnitCounit


 module SlicedAdjoint {L : Functor C D} {R} (L⊣R : L ⊣ R) where 

  module 𝑪 = Category C
  module 𝑫 = Category D


  open _⊣_ L⊣R

  module _ {c} {d} where
   module aI = Iso (adjIso (adj→adj' _ _ L⊣R) {c} {d}) 

  module Left (b : D .ob) where

   ⊣F/ : Functor (SliceCat C (R ⟅ b ⟆)) (SliceCat D b) 
   ⊣F/ =  N-ob ε b ﹗ ∘F L F/ (R ⟅ b ⟆)

   L/b⊣R/b : ⊣F/ ⊣₂ (R F/ b)  
   fun (adjIso L/b⊣R/b) (slicehom _ p) =
     slicehom _ $ 𝑪.⋆Assoc _ _ _
      ∙∙ cong (_ 𝑪.⋆_) (sym (F-seq R _ _) ∙∙ cong (F-hom R) p ∙∙ F-seq R _ _)
      ∙∙ (AssocCong₂⋆L C (sym (N-hom η _))
      ∙∙ cong (_ 𝑪.⋆_) (Δ₂ _) ∙∙ C .⋆IdR _)

   inv (adjIso L/b⊣R/b) (slicehom _ p) =
     slicehom _ $ AssocCong₂⋆R D (sym (N-hom ε _))
         ∙ cong (𝑫._⋆ _) (sym (F-seq L _ _) ∙ cong (F-hom L) p)         
   rightInv (adjIso L/b⊣R/b) _ = SliceHom-≡-intro' _ _ $ aI.rightInv _
   leftInv (adjIso L/b⊣R/b) _ = SliceHom-≡-intro' _ _ $ aI.leftInv _
   adjNatInD L/b⊣R/b _ _ = SliceHom-≡-intro' _ _ $
     cong (_ 𝑪.⋆_) (F-seq R _ _) ∙ sym (C .⋆Assoc _ _ _)
   adjNatInC L/b⊣R/b _ _ = SliceHom-≡-intro' _ _ $
     cong (𝑫._⋆ _) (F-seq L _ _) ∙ (D .⋆Assoc _ _ _)


  module Right (b : C .ob) where

   F/⊣ : Functor (SliceCat D (L ⟅ b ⟆)) (SliceCat C b)
   F/⊣ = (N-ob η b) ＊ ∘F R F/ (L ⟅ b ⟆)



   module _ {d} {p : 𝑫.Hom[ d , L ⟅ b ⟆ ]} where
    module PB = Pullback (Pbs (cospan _ _ _ (N-ob η b) (F-hom R p)))

   L/b⊣R/b : L F/ b ⊣₂ F/⊣
   fun (adjIso L/b⊣R/b) (slicehom f s) = slicehom _ (sym (fst (snd (fst pbu'))))
     where

    pbu' = PB.univProp _ _
           (N-hom η _ ∙∙
               cong (_ 𝑪.⋆_) (cong (F-hom R) (sym s) ∙ F-seq R _ _)
             ∙∙ sym (𝑪.⋆Assoc _ _ _))
   inv (adjIso L/b⊣R/b) (slicehom f s) = slicehom _
         (𝑫.⋆Assoc _ _ _
            ∙∙ congS (𝑫._⋆ (N-ob ε _ 𝑫.⋆ _)) (F-seq L _ _)
            ∙∙ 𝑫.⋆Assoc _ _ _ ∙ cong (F-hom L f 𝑫.⋆_)
                  (cong ((F-hom L (PB.pbPr₂)) 𝑫.⋆_) (sym (N-hom ε _))
                   ∙∙ sym (𝑫.⋆Assoc _ _ _)
                   ∙∙ cong (𝑫._⋆ N-ob ε (F-ob L b))
                      (sym (F-seq L _ _)
                     ∙∙ cong (F-hom L) (sym (PB.pbCommutes))
                     ∙∙ F-seq L _ _)
                   ∙∙ 𝑫.⋆Assoc _ _ _
                   ∙∙ cong (F-hom L (PB.pbPr₁) 𝑫.⋆_) (Δ₁ b)
                   ∙ 𝑫.⋆IdR _)
            ∙∙ sym (F-seq L _ _)
            ∙∙ cong (F-hom L) s)

   rightInv (adjIso L/b⊣R/b) h = SliceHom-≡-intro' _ _ $ 
    let p₂ : ∀ {x} → N-ob η _ 𝑪.⋆ F-hom R (F-hom L x 𝑫.⋆ N-ob ε _) ≡ x
        p₂ = cong (_ 𝑪.⋆_) (F-seq R _ _) ∙
                   AssocCong₂⋆L C (sym (N-hom η _))
                    ∙∙ cong (_ 𝑪.⋆_) (Δ₂ _) ∙∙ 𝑪.⋆IdR _
        

    in PB.univProp' (sym (S-comm h)) p₂
         
   leftInv (adjIso L/b⊣R/b) _ = SliceHom-≡-intro' _ _ $
       cong ((𝑫._⋆ _) ∘ F-hom L)
            (sym (snd (snd (fst (PB.univProp _ _ _)))))
            ∙ aI.leftInv _
   adjNatInD L/b⊣R/b _ _ = SliceHom-≡-intro' _ _ $
    let ee = _
        ((_ , (u , v)) , _) = PB.univProp _ _ _
        ((_ , (u' , v')) , _) = PB.univProp _  _ _

    in PB.univProp'
         (u ∙∙ cong (ee 𝑪.⋆_) u' ∙∙ sym (𝑪.⋆Assoc ee _ _))
         (cong (N-ob η _ 𝑪.⋆_) (F-seq R _ _)
               ∙∙ sym (𝑪.⋆Assoc _ _ _) ∙∙
               (cong (𝑪._⋆ _) v ∙ AssocCong₂⋆R C v'))

   adjNatInC L/b⊣R/b _ _ = let w = _ in SliceHom-≡-intro' _ _ $
       cong (𝑫._⋆ _) (F-seq L _ w ∙∙ cong (𝑫._⋆ (F-hom L w)) (F-seq L _ _) ∙∙
          (𝑫.⋆Assoc _ _ _)) ∙∙ (𝑫.⋆Assoc _ _ _)
       ∙∙ cong (_ 𝑫.⋆_) (cong (𝑫._⋆ _) (sym (F-seq L _ _)))
              

