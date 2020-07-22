{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Properties
open import Cubical.DStructures.Product
open import Cubical.DStructures.Combine
open import Cubical.DStructures.Type

private
  variable
    ℓ ℓ' : Level

module Groups (ℓ : Level) where
  -- groups with group isomorphisms structure
  𝒮-group : URGStr (Group {ℓ}) ℓ
  𝒮-group = urgstr GroupEquiv
                       idGroupEquiv
                       (isUnivalent'→isUnivalent GroupEquiv
                                                 idGroupEquiv
                                                 λ G H → invEquiv (GroupPath G H))

module Morphisms (ℓ ℓ' : Level) where
  open Groups

  -- notation
  -- G - group
  -- G² - pair of groups
  -- F - morphism forth
  -- B - morphism back
  -- SecRet - two morphisms that are a section retraction pair

  G² = Group {ℓ} × Group {ℓ'}
  G²F = Σ[ (G , H) ∈ G² ] GroupHom G H
  G²B = Σ[ (G , H) ∈ G² ] GroupHom H G
  G²FB = Σ[ (G , H) ∈ G² ] GroupHom G H × GroupHom H G

  -- type of Split epimorphisms
  G²SecRet = Σ[ ((G , H) , f , b) ∈ G²FB ] isGroupHomRet f b

  G²SecRetB = Σ[ (((G , H) , f , b) , isRet) ∈ G²SecRet ] GroupHom H G

  -- type of internal reflexive graphs in the category of groups
  G²SecRet² = Σ[ ((((G , H) , f , b) , isRet) , b') ∈ G²SecRetB ] isGroupHomRet f b'

  module GroupDisplayHelper {G : Group {ℓ}} {H : Group {ℓ'}} where
    BContr : (f : GroupHom H G) → isContr (Σ[ f' ∈ GroupHom H G ] (GroupHom.fun f ∼ GroupHom.fun f'))
    BContr f =  isOfHLevelRespectEquiv 0 (Σ-cong-equiv-snd (λ f' → isoToEquiv (invIso (GroupMorphismExtIso f f')))) (isContrSingl f)

    module Coherence {G' : Group {ℓ}} {H' : Group {ℓ'}}
                     (eG : GroupEquiv G G') (eH : GroupEquiv H H') where
           tr-eG = GroupEquiv.eq eG .fst
           tr-eH = GroupEquiv.eq eH .fst
           _* = GroupHom.fun

           FCondition : (f : GroupHom G H) (f' : GroupHom G' H')
                          → Type (ℓ-max ℓ ℓ')
           FCondition f f' = (g : ⟨ G ⟩) → tr-eH ((f *) g) ≡ (f' *) (tr-eG g)

           BCondition : (f : GroupHom H G) (f' : GroupHom H' G')
                         → Type (ℓ-max ℓ ℓ')
           BCondition f f' = (h : ⟨ H ⟩) → tr-eG ((f *) h) ≡ (f' *) (tr-eH h)

  open GroupDisplayHelper
--𝒮\

  -- Group morphisms displayed over pairs of groups
  𝒮ᴰ-G²\F : URGStrᴰ (𝒮-group ℓ ×𝒮 𝒮-group ℓ')
                            (λ (G , H) → GroupHom G H)
                            (ℓ-max ℓ ℓ')
  𝒮ᴰ-G²\F =
    make-𝒮ᴰ (λ {(G , _)} f (eG , eH) f'
                   → Coherence.FCondition eG eH f f')
                (λ _ _ → refl)
                λ (G , H) f → isOfHLevelRespectEquiv 0
                                                     -- Σ[ f' ∈ GroupHom G H ] (f ≡ f')
                                                     --  ≃ Σ[ (grouphom f' _) ∈ GroupHom G H ] ((g : ⟨ G ⟩) → GroupHom.fun f g ≡ f' g)
                                                     (Σ-cong-equiv-snd (λ f' → isoToEquiv (invIso (GroupMorphismExtIso f f'))))
                                                     (isContrSingl f)


  -- Type of two groups with a group morphism
  𝒮-G²F : URGStr G²F (ℓ-max ℓ ℓ')
  𝒮-G²F = ∫⟨ 𝒮-group ℓ ×𝒮 𝒮-group ℓ' ⟩ 𝒮ᴰ-G²\F




  -- Same as 𝒮-G²F but with the morphism going the other way
  𝒮ᴰ-G²\B : URGStrᴰ (𝒮-group ℓ ×𝒮 𝒮-group ℓ')
                             (λ (G , H) → GroupHom H G)
                             (ℓ-max ℓ ℓ')
  𝒮ᴰ-G²\B =
    make-𝒮ᴰ (λ {(_ , H)} f (eG , eH) f'
                  -- → (h : ⟨ H ⟩) → GroupEquiv.eq eG .fst (GroupHom.fun f h) ≡ GroupHom.fun f' (GroupEquiv.eq eH .fst h))
                  → Coherence.BCondition eG eH f f')
                (λ _ _ → refl)
                λ _ f → BContr f
                {- λ (G , H) f → isOfHLevelRespectEquiv 0
                                                     (Σ-cong-equiv-snd (λ f' → isoToEquiv (invIso (GroupMorphismExtIso f f'))))
                                                     (isContrSingl f) -}

  -- Type of two groups with a group morphism going back
  𝒮-G²B : URGStr G²B (ℓ-max ℓ ℓ')
  𝒮-G²B = ∫⟨ 𝒮-group ℓ ×𝒮 𝒮-group ℓ' ⟩ 𝒮ᴰ-G²\B


  -- Morphisms going forth and back displayed over pairs of groups
  𝒮ᴰ-G²\FB : URGStrᴰ (𝒮-group ℓ ×𝒮 𝒮-group ℓ')
                   (λ (G , H) → GroupHom G H × GroupHom H G)
                   (ℓ-max ℓ ℓ')
  𝒮ᴰ-G²\FB = combine-𝒮ᴰ 𝒮ᴰ-G²\F 𝒮ᴰ-G²\B

  -- Type of pairs of groups with morphisms going forth and back
  𝒮-G²FB : URGStr G²FB (ℓ-max ℓ ℓ')
  𝒮-G²FB = ∫⟨ 𝒮-group ℓ ×𝒮 𝒮-group ℓ' ⟩ 𝒮ᴰ-G²\FB


  -- section retraction pair displayed over pairs of groups
  𝒮ᴰ-G²FB\Split : URGStrᴰ 𝒮-G²FB
                          (λ ((G , H) , (f , g)) → isGroupHomRet f g)
                          ℓ-zero
  𝒮ᴰ-G²FB\Split =
    Subtype→Sub-𝒮ᴰ (λ ((G , H) , (f , g)) → isGroupHomRet f g , isPropIsGroupHomRet f g)
                       𝒮-G²FB

  -- type of group section retraction pairs
  𝒮-G²FBSplit : URGStr G²SecRet (ℓ-max ℓ ℓ')
  𝒮-G²FBSplit = ∫⟨ 𝒮-G²FB ⟩ 𝒮ᴰ-G²FB\Split


  -- section retraction pair + morphism back displayed over SG²Secre
  𝒮ᴰ-G²FBSplit\B : URGStrᴰ 𝒮-G²FBSplit
                        (λ (((G , H) , _) , _) → GroupHom H G)
                        (ℓ-max ℓ ℓ')
  𝒮ᴰ-G²FBSplit\B
    = make-𝒮ᴰ (λ {(((G , H) , _) , _)} f (((eG , eH) , _) , _) f'
                     → Coherence.BCondition eG eH f f')
                  (λ _ _ → refl)
                  λ (((G , H) , x) , isRet) f → BContr f

  𝒮-G²FBSplitB : URGStr G²SecRetB (ℓ-max ℓ ℓ')
  𝒮-G²FBSplitB = ∫⟨ 𝒮-G²FBSplit ⟩ 𝒮ᴰ-G²FBSplit\B


  𝒮ᴰ-G²FBSplitB\Split : URGStrᴰ 𝒮-G²FBSplitB
                        (λ ((((G , H) , f , b) , isRet) , b')
                          → isGroupHomRet f b')
                        ℓ-zero
  𝒮ᴰ-G²FBSplitB\Split = Subtype→Sub-𝒮ᴰ (λ ((((G , H) , f , b) , isRet) , b')
                                   → isGroupHomRet f b' , isPropIsGroupHomRet f b')
                                𝒮-G²FBSplitB

  𝒮-G²FBSplitBSplit : URGStr G²SecRet² (ℓ-max ℓ ℓ')
  𝒮-G²FBSplitBSplit = ∫⟨ 𝒮-G²FBSplitB ⟩ 𝒮ᴰ-G²FBSplitB\Split
