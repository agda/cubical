{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Slice.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
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

F/ : ∀ c (F : Functor C D) → Functor (SliceCat C c) (SliceCat D (F ⟅ c ⟆))     
F-ob (F/ c F) = sliceob ∘ F-hom F ∘ S-arr
F-hom (F/ c F) h = slicehom _
 (sym ( F-seq F _ _) ∙ cong (F-hom F) (S-comm h))
F-id (F/ c F) = SliceHom-≡-intro' _ _  (F-id F)
F-seq (F/ c F) _ _ = SliceHom-≡-intro' _ _  (F-seq F _ _)


module _ (Pbs : Pullbacks C) (c : C .ob) where

 open Pullback

 module _ {Y} (f : C [ c , Y ]) where

  private module _ (x : SliceCat C Y .ob) where
   pb = Pbs (cospan c Y _ f (x .S-arr))

   module _ {y : SliceCat C Y .ob} (h : (SliceCat C Y) [ y , x ]) where

    pbU : _
    pbU = let pbx = Pbs (cospan c Y _ f (y .S-arr))
     in univProp pb
           (pbPr₁ pbx) (h .S-hom ∘⟨ C ⟩ pbPr₂ pbx) 
            (pbCommutes pbx ∙∙ 
                cong (C ⋆ pbPr₂ (Pbs (cospan c Y (S-ob y) _ (y .S-arr))))
                  (sym (h .S-comm)) ∙∙ sym (C .⋆Assoc _ _ _)) 

  PbFunctor : Functor (SliceCat C Y) (SliceCat C c)
  F-ob PbFunctor x = sliceob (pbPr₁ (pb x))
  F-hom PbFunctor {x} {y} f =
    let ((f' , (u , _)) , _) = pbU y f
    in slicehom f' (sym u)

  F-id PbFunctor =
      SliceHom-≡-intro' _ _ (cong fst (pbU _ _ .snd
          (_ , sym (C .⋆IdL _) , C .⋆IdR _ ∙ sym (C .⋆IdL _))))
  F-seq PbFunctor _ _ =
   let (u₁ , v₁) = pbU _ _ .fst .snd
       (u₂ , v₂) = pbU _ _ .fst .snd
   in SliceHom-≡-intro' _ _ (cong fst (pbU _ _ .snd
          (_ , u₂ ∙∙ cong (C ⋆ _) u₁ ∙∙ sym (C .⋆Assoc _ _ _)
        , (sym (C .⋆Assoc _ _ _) ∙∙ cong (λ x → (C ⋆ x) _) v₂ ∙∙
                     AssocCong₂⋆R {C = C} _ v₁))))


 open UnitCounit
 
 module SlicedAdjoint {L : Functor C D} {R} (L⊣R : L ⊣ R) where 

-- --  L/b : Functor (SliceCat C c) (SliceCat D (L ⟅ c ⟆))
-- --  F-ob L/b (sliceob S-arr) = sliceob (F-hom L S-arr)
-- --  F-hom L/b (slicehom S-hom S-comm) =
-- --    slicehom _ (sym ( F-seq L _ _) ∙ cong (F-hom L) S-comm)
-- --  F-id L/b = SliceHom-≡-intro' _ _  (F-id L)
-- --  F-seq L/b _ _ = SliceHom-≡-intro' _ _ (F-seq L _ _)

  -- R' : Functor (SliceCat D (L ⟅ c ⟆)) (SliceCat C (funcComp R L .F-ob c))
  -- F-ob R' (sliceob S-arr) = sliceob (F-hom R S-arr)
  -- F-hom R' (slicehom S-hom S-comm) = slicehom _ (sym ( F-seq R _ _) ∙ cong (F-hom R) S-comm)
  -- F-id R' = SliceHom-≡-intro' _ _  (F-id R)
  -- F-seq R' _ _ = SliceHom-≡-intro' _ _ (F-seq R _ _)

-- --  -- R/b : Functor (SliceCat D (L ⟅ c ⟆)) (SliceCat C c)
-- --  -- R/b = BaseChangeFunctor.BaseChangeFunctor Pbs (N-ob (_⊣_.η L⊣R) c)
-- --  --          ∘F R'
  module 𝑪 = Category C
  module 𝑫 = Category D

  open _⊣_ L⊣R

  F/⊣ : Functor (SliceCat D (L ⟅ c ⟆)) (SliceCat C c)
  F/⊣ = PbFunctor (N-ob η c)  ∘F F/ (L ⟅ c ⟆)  R

  L/b⊣R/b : F/ c L ⊣ F/⊣
  N-ob (_⊣_.η L/b⊣R/b) x = 
   slicehom {!(N-ob η $ S-ob x)!} {!!}
  N-hom (_⊣_.η L/b⊣R/b) = {!!}
  N-ob (_⊣_.ε L/b⊣R/b) x =
   slicehom ({!F-hom L ?!} 𝑫.⋆ (N-ob ε $ S-ob x)) {!!}
  N-hom (_⊣_.ε L/b⊣R/b) = {!!}
  _⊣_.triangleIdentities L/b⊣R/b = {!!}
  -- N-ob (_⊣_.η L/b⊣R/b) x =
  --   slicehom ({!N-ob η $ S-ob x!}) {!!}
  -- N-hom (_⊣_.η L/b⊣R/b) = {!!}
  -- N-ob (_⊣_.ε L/b⊣R/b) x =
  --   slicehom (F-hom L ((pbPr₁ ((Pbs
  --      (cospan c (F-ob R (F-ob L c)) (F-ob R (S-ob x)) (N-ob η c)
  --       (F-hom R (S-arr x))))))) 𝑫.⋆
  --        {!S-arr x !}) {!!}
  -- N-hom (_⊣_.ε L/b⊣R/b) = {!!}
  -- _⊣_.triangleIdentities L/b⊣R/b = {!!}
  -- -- N-ob (_⊣_.η L/b⊣R/b) = {!!}
  -- -- N-hom (_⊣_.η L/b⊣R/b) = {!!}
  -- -- _⊣_.ε L/b⊣R/b = {!!}
  -- -- _⊣_.triangleIdentities L/b⊣R/b = {!!}
