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
  URGStrGroup : URGStr (Group {ℓ}) ℓ
  URGStrGroup = urgstr GroupEquiv
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
 
  -- type of split epimorphisms
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


  -- Group morphisms displayed over pairs of groups
  SᴰG²F : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
                            (λ (G , H) → GroupHom G H)
                            (ℓ-max ℓ ℓ')
  SᴰG²F =
    makeURGStrᴰ (λ {(G , _)} f (eG , eH) f'
                   → Coherence.FCondition eG eH f f')
                (λ _ _ → refl)
                λ (G , H) f → isOfHLevelRespectEquiv 0
                                                     -- Σ[ f' ∈ GroupHom G H ] (f ≡ f')
                                                     --  ≃ Σ[ (grouphom f' _) ∈ GroupHom G H ] ((g : ⟨ G ⟩) → GroupHom.fun f g ≡ f' g)
                                                     (Σ-cong-equiv-snd (λ f' → isoToEquiv (invIso (GroupMorphismExtIso f f'))))
                                                     (isContrSingl f)


  -- Type of two groups with a group morphism
  SG²F : URGStr G²F (ℓ-max ℓ ℓ')
  SG²F = ∫⟨ URGStrGroup ℓ ×URG URGStrGroup ℓ' ⟩ SᴰG²F




  -- Same as SG²F but with the morphism going the other way
  SᴰG²B : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
                             (λ (G , H) → GroupHom H G)
                             (ℓ-max ℓ ℓ')
  SᴰG²B =
    makeURGStrᴰ (λ {(_ , H)} f (eG , eH) f'
                  -- → (h : ⟨ H ⟩) → GroupEquiv.eq eG .fst (GroupHom.fun f h) ≡ GroupHom.fun f' (GroupEquiv.eq eH .fst h))
                  → Coherence.BCondition eG eH f f')
                (λ _ _ → refl)
                λ _ f → BContr f
                {- λ (G , H) f → isOfHLevelRespectEquiv 0
                                                     (Σ-cong-equiv-snd (λ f' → isoToEquiv (invIso (GroupMorphismExtIso f f'))))
                                                     (isContrSingl f) -}

  -- Type of two groups with a group morphism going back
  SG²B : URGStr G²B (ℓ-max ℓ ℓ')
  SG²B = ∫⟨ URGStrGroup ℓ ×URG URGStrGroup ℓ' ⟩ SᴰG²B


  -- Morphisms going forth and back displayed over pairs of groups
  SᴰG²FB : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
                   (λ (G , H) → GroupHom G H × GroupHom H G)
                   (ℓ-max ℓ ℓ')
  SᴰG²FB = combineURGStrᴰ SᴰG²F SᴰG²B

  -- Type of pairs of groups with morphisms going forth and back
  SG²FB : URGStr G²FB (ℓ-max ℓ ℓ')
  SG²FB = ∫⟨ URGStrGroup ℓ ×URG URGStrGroup ℓ' ⟩ SᴰG²FB


  -- section retraction pair displayed over pairs of groups
  SᴰG²SecRet : URGStrᴰ SG²FB
                          (λ ((G , H) , (f , g)) → isGroupHomRet f g)
                          ℓ-zero
  SᴰG²SecRet =
    Subtype→SubURGᴰ (λ ((G , H) , (f , g)) → isGroupHomRet f g , isPropIsGroupHomRet f g)
                       SG²FB

  -- type of group section retraction pairs
  SG²SecRet : URGStr G²SecRet (ℓ-max ℓ ℓ')
  SG²SecRet = ∫⟨ SG²FB ⟩ SᴰG²SecRet


  -- section retraction pair + morphism back displayed over SG²Secre
  SᴰG²SecRetB : URGStrᴰ SG²SecRet
                        (λ (((G , H) , _) , _) → GroupHom H G)
                        (ℓ-max ℓ ℓ')
  SᴰG²SecRetB
    = makeURGStrᴰ (λ {(((G , H) , _) , _)} f (((eG , eH) , _) , _) f'
                     → Coherence.BCondition eG eH f f')
                  (λ _ _ → refl)
                  λ (((G , H) , x) , isRet) f → BContr f

  SG²SecRetB : URGStr G²SecRetB (ℓ-max ℓ ℓ')
  SG²SecRetB = ∫⟨ SG²SecRet ⟩ SᴰG²SecRetB


  SᴰG²SecRet² : URGStrᴰ SG²SecRetB
                        (λ ((((G , H) , f , b) , isRet) , b')
                          → isGroupHomRet f b')
                        ℓ-zero
  SᴰG²SecRet² = Subtype→SubURGᴰ (λ ((((G , H) , f , b) , isRet) , b')
                                   → isGroupHomRet f b' , isPropIsGroupHomRet f b')
                                SG²SecRetB

  SG²SecRet² : URGStr G²SecRet² (ℓ-max ℓ ℓ')
  SG²SecRet² = ∫⟨ SG²SecRetB ⟩ SᴰG²SecRet²
