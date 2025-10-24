
module Cubical.Categories.Constructions.Slice.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category
open import Cubical.Categories.Category.Properties

open import Cubical.Categories.Constructions.Slice.Base

open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint

open import Cubical.Tactics.FunctorSolver.Reflection


open Category hiding (_∘_)
open Functor
open NatTrans

private
  variable
    ℓ ℓ' : Level
    C D : Category ℓ ℓ'

infix 39 _F/_
infix 40 ∑_

_F/_ : ∀ (F : Functor C D) c → Functor (SliceCat C c) (SliceCat D (F ⟅ c ⟆))
F-ob (F F/ c) = sliceob ∘ F ⟪_⟫ ∘ S-arr
F-hom (F F/ c) h = slicehom _
  $ sym ( F-seq F _ _) ∙ cong (F ⟪_⟫) (S-comm h)
F-id (F F/ c) = SliceHom-≡-intro' _ _  $ F-id F
F-seq (F F/ c) _ _ = SliceHom-≡-intro' _ _  $ F-seq F _ _


∑_ : ∀ {c d} f → Functor  (SliceCat C c) (SliceCat C d)
F-ob (∑_ {C = C} f) (sliceob x) = sliceob (x ⋆⟨ C ⟩ f)
F-hom (∑_ {C = C} f) (slicehom h p) = slicehom _ $
  sym (C .⋆Assoc _ _ _) ∙ cong (comp' C f) p
F-id (∑ f) = SliceHom-≡-intro' _ _ refl
F-seq (∑ f) _ _ = SliceHom-≡-intro' _ _ refl

module _ (Pbs : Pullbacks C) where

 open Category C using () renaming (_⋆_ to _⋆ᶜ_)

 module BaseChange {c d} (𝑓 : C [ c , d ]) where
  infix 40 _＊

  module _ {x@(sliceob arr) : SliceOb C d} where
   open Pullback (Pbs (cospan _ _ _ 𝑓 arr)) public

  module _ {x} {y} ((slicehom h h-comm) : SliceCat C d [ y , x ]) where

   pbU = univProp (pbPr₁ {x = y}) (pbPr₂ ⋆ᶜ h)
          (pbCommutes {x = y} ∙∙ cong (pbPr₂ ⋆ᶜ_) (sym (h-comm)) ∙∙ sym (C .⋆Assoc _ _ _))
           .fst .snd

  _＊ : Functor (SliceCat C d) (SliceCat C c)
  F-ob _＊ x = sliceob (pbPr₁ {x = x})
  F-hom _＊ f = slicehom _ (sym (fst (pbU f)))
  F-id _＊ = SliceHom-≡-intro' _ _ $ pullbackArrowUnique (sym (C .⋆IdL _)) (C .⋆IdR _ ∙ sym (C .⋆IdL _))

  F-seq _＊ _ _ =
   let (u₁ , v₁) = pbU _ ; (u₂ , v₂) = pbU _
   in SliceHom-≡-intro' _ _ $ pullbackArrowUnique
       (u₂ ∙∙ cong (C ⋆ _) u₁ ∙∙ sym (C .⋆Assoc _ _ _))
       (sym (C .⋆Assoc _ _ _) ∙∙ cong (comp' C _) v₂ ∙∙ AssocCong₂⋆R C v₁)

 open BaseChange using (_＊)
 open NaturalBijection renaming (_⊣_ to _⊣₂_)
 open Iso
 open _⊣₂_


 module _ {c d}(𝑓 : C [ c , d ]) where

  open BaseChange 𝑓 hiding (_＊)

  ∑𝑓⊣𝑓＊ : ∑ 𝑓 ⊣₂ 𝑓 ＊
  fun (adjIso ∑𝑓⊣𝑓＊) (slicehom h o) =
   let ((_ , (p , _)) , _) = univProp _ _ (sym o)
   in slicehom _ (sym p)
  inv (adjIso ∑𝑓⊣𝑓＊) (slicehom h o) = slicehom _ $
    AssocCong₂⋆R C (sym (pbCommutes)) ∙ cong (_⋆ᶜ 𝑓) o
  rightInv (adjIso ∑𝑓⊣𝑓＊) (slicehom h o) =
    SliceHom-≡-intro' _ _ (pullbackArrowUnique (sym o) refl)
  leftInv (adjIso ∑𝑓⊣𝑓＊) (slicehom h o) =
   let ((_ , (_ , q)) , _) = univProp _ _ _
   in SliceHom-≡-intro' _ _ (sym q)
  adjNatInD ∑𝑓⊣𝑓＊ f k = SliceHom-≡-intro' _ _ $
    let ((h' , (v' , u')) , _) = univProp _ _ _
        ((_ , (v'' , u'')) , _) = univProp _ _ _
    in pullbackArrowUnique (v' ∙∙ cong (h' ⋆ᶜ_) v'' ∙∙ sym (C .⋆Assoc _ _ _))
                    (cong (_⋆ᶜ _) u' ∙ AssocCong₂⋆R C u'')

  adjNatInC ∑𝑓⊣𝑓＊ g h = SliceHom-≡-intro' _ _ $ C .⋆Assoc _ _ _


 open UnitCounit

 module SlicedAdjoint {L : Functor C D} {R} (L⊣R : L ⊣ R) where

  open Category D using () renaming (_⋆_ to _⋆ᵈ_)

  open _⊣_ L⊣R

  module _ {c} {d} where
   module aI = Iso (adjIso (adj→adj' _ _ L⊣R) {c} {d})

  module Left (b : D .ob) where

   ⊣F/ : Functor (SliceCat C (R ⟅ b ⟆)) (SliceCat D b)
   ⊣F/ =  ∑ (ε ⟦ b ⟧) ∘F L F/ (R ⟅ b ⟆)

   L/b⊣R/b : ⊣F/ ⊣₂ (R F/ b)
   fun (adjIso L/b⊣R/b) (slicehom _ p) = slicehom _ $
           C .⋆Assoc _ _ _
        ∙∙ cong (_ ⋆ᶜ_) (sym (F-seq R _ _) ∙∙ cong (R ⟪_⟫) p ∙∙ F-seq R _ _)
        ∙∙ AssocCong₂⋆L C (sym (N-hom η _))
        ∙∙ cong (_ ⋆ᶜ_) (Δ₂ _)
        ∙∙ C .⋆IdR _

   inv (adjIso L/b⊣R/b) (slicehom _ p) =
     slicehom _ $ AssocCong₂⋆R D (sym (N-hom ε _))
         ∙ cong (_⋆ᵈ _) (sym (F-seq L _ _) ∙ cong (L ⟪_⟫) p)
   rightInv (adjIso L/b⊣R/b) _ = SliceHom-≡-intro' _ _ $ aI.rightInv _
   leftInv (adjIso L/b⊣R/b) _ = SliceHom-≡-intro' _ _ $ aI.leftInv _
   adjNatInD L/b⊣R/b _ _ = SliceHom-≡-intro' _ _ $
     cong (_ ⋆ᶜ_) (F-seq R _ _) ∙ sym (C .⋆Assoc _ _ _)
   adjNatInC L/b⊣R/b _ _ = SliceHom-≡-intro' _ _ $
     cong (_⋆ᵈ _) (F-seq L _ _) ∙ (D .⋆Assoc _ _ _)


  module Right (b : C .ob) where

   F/⊣ : Functor (SliceCat D (L ⟅ b ⟆)) (SliceCat C b)
   F/⊣ = (η ⟦ b ⟧) ＊ ∘F R F/ (L ⟅ b ⟆)

   open BaseChange (η ⟦ b ⟧) hiding (_＊)

   L/b⊣R/b : L F/ b ⊣₂ F/⊣
   fun (adjIso L/b⊣R/b) (slicehom f s) = slicehom _ $
     sym $ univProp _ _ (N-hom η _ ∙∙
               cong (_ ⋆ᶜ_) (cong (R ⟪_⟫) (sym s) ∙ F-seq R _ _)
             ∙∙ sym (C .⋆Assoc _ _ _)) .fst .snd .fst
   inv (adjIso L/b⊣R/b) (slicehom f s) = slicehom _
         (D .⋆Assoc _ _ _
            ∙∙ congS (_⋆ᵈ (ε ⟦ _ ⟧ ⋆⟨ D ⟩ _)) (F-seq L _ _)
            ∙∙ D .⋆Assoc _ _ _ ∙ cong (L ⟪ f ⟫ ⋆ᵈ_)
                  (cong (L ⟪ pbPr₂ ⟫ ⋆ᵈ_) (sym (N-hom ε _))
                   ∙∙ sym (D .⋆Assoc _ _ _)
                   ∙∙ cong (_⋆ᵈ ε ⟦ F-ob L b ⟧)
                      (preserveCommF L $ sym pbCommutes)
                   ∙∙ D .⋆Assoc _ _ _
                   ∙∙ cong (L ⟪ pbPr₁ ⟫ ⋆ᵈ_) (Δ₁ b)
                   ∙ D .⋆IdR _)
            ∙∙ sym (F-seq L _ _)
            ∙∙ cong (L ⟪_⟫) s)

   rightInv (adjIso L/b⊣R/b) h = SliceHom-≡-intro' _ _ $
    let p₂ : ∀ {x} → η ⟦ _ ⟧ ⋆ᶜ R ⟪ L ⟪ x ⟫ ⋆⟨ D ⟩ ε ⟦ _ ⟧ ⟫ ≡ x
        p₂ = cong (_ ⋆ᶜ_) (F-seq R _ _) ∙
                   AssocCong₂⋆L C (sym (N-hom η _))
                    ∙∙ cong (_ ⋆ᶜ_) (Δ₂ _) ∙∙ C .⋆IdR _


    in pullbackArrowUnique (sym (S-comm h)) p₂

   leftInv (adjIso L/b⊣R/b) _ = SliceHom-≡-intro' _ _ $
       cong ((_⋆ᵈ _) ∘ L ⟪_⟫) (sym (snd (snd (fst (univProp _ _ _)))))
       ∙ aI.leftInv _
   adjNatInD L/b⊣R/b _ _ = SliceHom-≡-intro' _ _ $
    let (h , (u , v)) = univProp _ _ _ .fst
        (u' , v') = pbU _

    in pullbackArrowUnique
         (u ∙∙ cong (h ⋆ᶜ_) u' ∙∙ sym (C .⋆Assoc h _ _))
         (cong (_ ⋆ᶜ_) (F-seq R _ _)
               ∙∙ sym (C .⋆Assoc _ _ _) ∙∙
               (cong (_⋆ᶜ _) v ∙ AssocCong₂⋆R C v'))

   adjNatInC L/b⊣R/b g h = let w = _ in SliceHom-≡-intro' _ _ $
     cong (_⋆ᵈ _) (cong (L ⟪_⟫) (C .⋆Assoc _ _ w) ∙ F-seq L _ (_ ⋆ᶜ w))
      ∙ D .⋆Assoc _ _ _

