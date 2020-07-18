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

  G² = Group {ℓ} × Group {ℓ'}
  G²F = Σ[ (G , H) ∈ G² ] GroupHom G H
  G²B = Σ[ (G , H) ∈ G² ] GroupHom H G
  G²FB = Σ[ (G , H) ∈ G² ] GroupHom G H × GroupHom H G
  G²FB² = Σ[ (G , H) ∈ G² ] (GroupHom G H × GroupHom H G) × GroupHom H G
  G²SecRet = Σ[ (_ , f , b) ∈ G²FB ] isGroupHomRet f b
  G²SecRetB = Σ[ (_ , (f , b) , _) ∈ G²FB² ] isGroupHomRet f b
  G²SecRet² = Σ[ ((_ , (f , _) , b') , _) ∈ G²SecRetB ] isGroupHomRet f b'


  -- Group morphisms displayed over pairs of groups
  GroupsMorphismᴰ : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
                            (λ (G , H) → GroupHom G H)
                            (ℓ-max ℓ ℓ')
  GroupsMorphismᴰ =
    makeURGStrᴰ (λ (G , H) → GroupHom G H)
                (ℓ-max ℓ ℓ')
                (λ {(G , _)} f (eG , eH) f'
                   → (g : ⟨ G ⟩) → GroupEquiv.eq eH .fst (GroupHom.fun f g) ≡ GroupHom.fun f' (GroupEquiv.eq eG  .fst g))
                (λ _ _ → refl)
                λ (G , H) f → isOfHLevelRespectEquiv 0
                                                     -- Σ[ f' ∈ GroupHom G H ] (f ≡ f')
                                                     --  ≃ Σ[ (grouphom f' _) ∈ GroupHom G H ] ((g : ⟨ G ⟩) → GroupHom.fun f g ≡ f' g)
                                                     (Σ-cong-equiv-snd (λ f' → isoToEquiv (invIso (GroupMorphismExtIso f f'))))
                                                     (isContrSingl f)
  -- Type of two groups with a group morphism
  GroupsMorphism : URGStr G²F (ℓ-max ℓ ℓ')
  GroupsMorphism = ∫⟨ URGStrGroup ℓ ×URG URGStrGroup ℓ' ⟩ GroupsMorphismᴰ

  -- Same as GroupsMorphism but with the morphism going the other way
  GroupsMorphismBᴰ : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
                             (λ (G , H) → GroupHom H G)
                             (ℓ-max ℓ ℓ')
  GroupsMorphismBᴰ =
    makeURGStrᴰ (λ (G , H) → GroupHom H G)
                (ℓ-max ℓ ℓ')
                (λ {(_ , H)} f (eG , eH) f'
                  → (h : ⟨ H ⟩) → GroupEquiv.eq eG .fst (GroupHom.fun f h) ≡ GroupHom.fun f' (GroupEquiv.eq eH .fst h))
                (λ _ _ → refl)
                λ (G , H) f → isOfHLevelRespectEquiv 0
                                                     (Σ-cong-equiv-snd (λ f' → isoToEquiv (invIso (GroupMorphismExtIso f f'))))
                                                     (isContrSingl f)

  -- Type of two groups with a group morphism going back
  GroupsMorphismB : URGStr G²B (ℓ-max ℓ ℓ')
  GroupsMorphismB = ∫⟨ URGStrGroup ℓ ×URG URGStrGroup ℓ' ⟩ GroupsMorphismBᴰ

  -- Morphisms going forth and back displayed over pairs of groups
  GroupsMorphismFBᴰ : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
                              (λ (G , H) → GroupHom G H × GroupHom H G)
                              (ℓ-max ℓ ℓ')
  GroupsMorphismFBᴰ = combineURGStrᴰ GroupsMorphismᴰ GroupsMorphismBᴰ

  -- Type of pairs of groups with morphisms going forth and back
  GroupsMorphismFB : URGStr G²FB (ℓ-max ℓ ℓ')
  GroupsMorphismFB = ∫⟨ URGStrGroup ℓ ×URG URGStrGroup ℓ' ⟩ GroupsMorphismFBᴰ

  -- displayed over pairs of groups, one morphism going forth and two going back
  GroupsMorphismFBBᴰ : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
                               (λ (G , H) → (GroupHom G H × GroupHom H G) × GroupHom H G)
                               (ℓ-max ℓ ℓ')
  GroupsMorphismFBBᴰ = combineURGStrᴰ GroupsMorphismFBᴰ GroupsMorphismBᴰ

  -- type of pairs of groups with one morphism going forth and two going back
  GroupsMorphismFBB : URGStr G²FB² (ℓ-max ℓ ℓ')
  GroupsMorphismFBB = ∫⟨ URGStrGroup ℓ ×URG URGStrGroup ℓ' ⟩ GroupsMorphismFBBᴰ

  -- section retraction pair displayed over pairs of groups
  GroupsSecRetᴰ : URGStrᴰ GroupsMorphismFB
                          (λ ((G , H) , (f , g)) → isGroupHomRet f g)
                          ℓ-zero
  GroupsSecRetᴰ =
    Subtype→SubURGᴰ (λ ((G , H) , (f , g)) → isGroupHomRet f g , isPropIsGroupHomRet f g)
                       GroupsMorphismFB

  -- type of group section retraction pairs
  GroupsSecRet : URGStr G²SecRet
                        (ℓ-max ℓ ℓ')
  GroupsSecRet = ∫⟨ GroupsMorphismFB ⟩ GroupsSecRetᴰ

  -- two groups, morphisms forth bback, sec/ret witness, morphism back
  GroupsMorphismSecRetBᴰ : URGStrᴰ GroupsMorphismFBB
                                    (λ ((G , H) , (f , b) , b') → isGroupHomRet f b)
                                    ℓ-zero
  GroupsMorphismSecRetBᴰ =
    Subtype→SubURGᴰ (λ ((G , H) , (f , b) , b') → isGroupHomRet f b , isPropIsGroupHomRet f b)
                    GroupsMorphismFBB

  {-
  This would be nice, but I stopped trying to load it after 5 minutes

  GroupsMorphismSecRetBᴰ : URGStrᴰ GroupsMorphismFBB (λ ((G , H) , (f , b) , b') → isGroupHomRet f b) (ℓ-max ℓ ℓ')
  GroupsMorphismSecRetBᴰ = HorizontalLiftᴰ GroupsMorphismFBᴰ GroupsMorphismBᴰ GroupsSecRetᴰ
  -}

  GroupsMorphismSecRetB : URGStr G²SecRetB
                                 (ℓ-max ℓ ℓ')
  GroupsMorphismSecRetB = ∫⟨ GroupsMorphismFBB ⟩ GroupsMorphismSecRetBᴰ

  GroupsMorphismSec2Retᴰ : URGStrᴰ GroupsMorphismSecRetB {!!} {!!}
  GroupsMorphismSec2Retᴰ = {!!}


{-
  GroupsFBBSecRetᴰ : URGStrᴰ {!!} (λ (a , _) → {!!}) {!!}
  GroupsFBBSecRetᴰ = Liftᴰ GroupsSecRetᴰ {!GroupsMorphismFBBᴰ!}

  -- displayed over two groups with FBB morphisms, both B morphisms being retractions of F
  GroupsSecRetRetᴰ : URGStrᴰ GroupsMorphismFBB
                             (λ ((G , H) , (f , g) , g') → isGroupHomRet f g × isGroupHomRet f g')
                             ℓ-zero
  GroupsSecRetRetᴰ = combineURGStrᴰ {!Liftᴰ GroupsMorphismFBᴰ GroupsSecRet!} {!!}
  -}

{-
module _ (ℓ ℓ' : Level) where
  URGStr×rev = URGStr-transport Σ-swap-≃ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
  GroupsMorphismBᴰ : URGStrᴰ URGStr×rev (λ (G , H) → GroupHom H G) (ℓ-max ℓ ℓ')
  GroupsMorphismBᴰ =  ×URG-swap (GroupsMorphismᴰ ℓ ℓ')

  -- Type of two groups with a group morphism
  GroupsMorphismB : URGStr (Σ[ (G , H) ∈ (Group × Group) ] GroupHom H G) (ℓ-max ℓ ℓ')
  GroupsMorphismB = ∫⟨ URGStr×rev ⟩ ?

  -- Groups with back and forth morphisms
  GroupsMorphismsBFᴰ : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ') {!!} (ℓ-max ℓ ℓ')
  GroupsMorphismsBFᴰ = combineURGStrᴰ {!!} {!!}
-}


{-
private
  -- abbreviations
  module _ {ℓ : Level} {G G' : Group {ℓ = ℓ}} (e : GroupEquiv G G') where
    groupTransp : ⟨ G ⟩ → ⟨ G' ⟩
    groupTransp = GroupEquiv.eq e .fst
module _ (ℓ ℓ' : Level) where
  -- group actions displayed over pairs of groups
  URGStrActionᴰ : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
                         (λ (G , H) → Σ[ _α_ ∈ LeftActionStructure ⟨ G ⟩ ⟨ H ⟩ ] (IsGroupAction G H _α_))
                         (ℓ-max ℓ ℓ')
  URGStrActionᴰ =
    -- the type is over (G , H) is the actions of G on H
    makeURGStrᴰ (λ GH → ActGH {GH})
                (ℓ-max ℓ ℓ')
                -- actions are related when they respect the relation of G, G' and H, H'
                (λ {(G , H)} {(G' , H')} (_α_ , isAct) (pG , pH) (_α'_ , isAct')
                  → ((g : ⟨ G ⟩) → (h : ⟨ H ⟩)
                    → groupTransp pH (g α h) ≡ (groupTransp pG g α' groupTransp pH h)))
                -- reflexivity over idGroupEquiv is easy
                (λ _ _ _ → refl)
                -- contractibility of the total space
                -- uses isPropIsGroupAction
                λ (G , H) (_α_ , isAct) → {!!}
                where
                  module _ {(G , H) : Group {ℓ = ℓ} × Group {ℓ = ℓ'}} where
                    -- the actions of G on H
                    ActGH = Σ[ _α_ ∈ LeftActionStructure ⟨ G ⟩ ⟨ H ⟩ ]
                               (IsGroupAction G H _α_)

module _ (ℓ ℓ' : Level) where
  -- sections and retractions over a pair of groups
  URGStrSecRetᴰ : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
                         (λ (G , H) → Σ[ f ∈ (GroupHom G H) ]
                                      Σ[ g ∈ (GroupHom H G) ]
                                         section (GroupHom.fun f) (GroupHom.fun g))
                         (ℓ-max ℓ ℓ')
  URGStrSecRetᴰ =
    makeURGStrᴰ (λ GH → fgsec {GH})
                (ℓ-max ℓ ℓ')
                (λ {(G , H)} {(G' , H')}
                   ((grouphom f _) , (grouphom g _) , sec)
                   (pG , pH)
                   ((grouphom f' _) , (grouphom g' _) , sec')
                  → ((x : ⟨ G ⟩) → f' (groupTransp pG x) ≡ groupTransp pH (f x))
                    × ((y : ⟨ H ⟩) → g' (groupTransp pH y) ≡ groupTransp pG (g y)))
                (λ (_ , _ , _) → (λ _ → refl) , λ _ → refl)
                λ (G , H) (f , g , sec) → isOfHLevelRespectEquiv 0 (sequence {(G , H)} (f , g , sec)) {!!}
                where
                  module _ {(G , H) : Group {ℓ = ℓ} × Group {ℓ = ℓ'}} where
                    -- in the context of a pair of groups define the type of section triples
                    fgsec = Σ[ f ∈ GroupHom G H ]
                            Σ[ g ∈ GroupHom H G ]
                            section (GroupHom.fun f) (GroupHom.fun g)
                    module _ ((f , g , sec) : fgsec) where
                      -- over one section triple deform the total space
                      sequence = Σ[ f' ∈ GroupHom G H ] (GroupHom.fun f' ≡ f*)
                                    ≃⟨ Σ-cong-equiv-snd (λ f' → invEquiv (Σ-contractSnd {!!})) ⟩
                                 Σ[ f' ∈ GroupHom G H ] Σ[ _ ∈ GroupHom.fun f' ≡ f* ] Σ[ g' ∈ GroupHom H G ] (GroupHom.fun g' ≡ g*)
                                    ≃⟨ Σ-cong-equiv-snd (λ f' → compEquiv (compEquiv (invEquiv Σ-assoc-≃) (Σ-cong-equiv-fst Σ-swap-≃)) Σ-assoc-≃) ⟩
                                 Σ[ f' ∈ GroupHom G H ] Σ[ g' ∈ GroupHom H G ] Σ[ _ ∈ GroupHom.fun f' ≡ f* ] (GroupHom.fun g' ≡ g*)
                                    ≃⟨ Σ-cong-equiv-snd (λ f' → Σ-cong-equiv-snd (λ g' → Σ-cong-equiv-snd (λ _ → invEquiv (Σ-contractSnd {!!})))) ⟩
                                 Σ[ f' ∈ GroupHom G H ] Σ[ g' ∈ GroupHom H G ] (ghf f' ≡ f*) × (ghf g' ≡ g*) × section (ghf f') (ghf g')
                                    ≃⟨ Σ-cong-equiv-snd (λ f' → Σ-cong-equiv-snd (λ g' → compEquiv (invEquiv Σ-assoc-≃) Σ-swap-≃)) ⟩
                                 Σ[ f' ∈ GroupHom G H ] Σ[ g' ∈ GroupHom H G ] section (ghf f') (ghf g') × (ghf f' ≡ f*) × (ghf g' ≡ g*)
                                    ≃⟨ Σ-cong-equiv-snd (λ f' → invEquiv Σ-assoc-≃) ⟩
                                 Σ[ f' ∈ GroupHom G H ] Σ[ (g' , sec') ∈ Σ[ g' ∈ GroupHom H G ] (section (ghf f') (ghf g')) ] (GroupHom.fun f' ≡ f*) × (GroupHom.fun g' ≡ g*)
                                    ≃⟨ invEquiv Σ-assoc-≃ ⟩
                                 Σ[ (f' , g' , sec') ∈ fgsec ] (GroupHom.fun f' ≡ f*) × (GroupHom.fun g' ≡ g*)
                                    ≃⟨ Σ-cong-equiv-snd (λ (f' , g' , sec) → Σ-cong-equiv (invEquiv funExtEquiv) λ _ → invEquiv funExtEquiv) ⟩
                                 Σ[ (f' , g' , sec') ∈ fgsec ] ((x : ⟨ G ⟩) → (GroupHom.fun f' x) ≡ (f* x)) × ((y : ⟨ H ⟩) → (GroupHom.fun g' y) ≡ (g* y)) ■
                                   where
                                     ghf = GroupHom.fun
                                     f* = ghf f
                                     g* = ghf g

module DoubleSec (ℓ ℓ' : Level) where
  -- two groups with two sections/retractions
  -- not what we need tho
  open Combine
  GroupsDoubleSec : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
              (λ (G , H) → (Σ[ f ∈ (GroupHom G H) ] Σ[ g ∈ (GroupHom H G) ] section (GroupHom.fun f) (GroupHom.fun g))
                          × (Σ[ f ∈ (GroupHom G H) ] Σ[ g ∈ (GroupHom H G) ] section (GroupHom.fun f) (GroupHom.fun g)))
              (ℓ-max ℓ ℓ')
  GroupsDoubleSec = combineURGStrᴰ (URGStrSecRetᴰ ℓ ℓ') (URGStrSecRetᴰ ℓ ℓ')
-}
