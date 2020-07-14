{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma

open import Cubical.DStructures.DispSIP
open import Cubical.DStructures.Product
open import Cubical.Relation.Binary
open BinaryRelation
open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction


module _ (ℓ : Level) where
  URGStrGroup : URGStr (Group {ℓ = ℓ}) ℓ
  URGStrGroup = urgstr GroupEquiv
                       idGroupEquiv
                       (isUnivalent'→isUnivalent GroupEquiv
                                                 idGroupEquiv
                                                 λ G H → invEquiv (GroupPath G H))
private
  module _ {ℓ : Level} {G G' : Group {ℓ = ℓ}} (e : GroupEquiv G G') where
    groupTransp : ⟨ G ⟩ → ⟨ G' ⟩
    groupTransp = GroupEquiv.eq e .fst

module _ (ℓ ℓ' : Level) where
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
    makeURGStrᴰ (λ (G , H) → Σ[ f ∈ (GroupHom G H) ]
                                Σ[ g ∈ (GroupHom H G) ]
                                  section (GroupHom.fun f) (GroupHom.fun g))
                (ℓ-max ℓ ℓ')
                (λ {(G , H)} {(G' , H')}
                   ((grouphom f _) , (grouphom g _) , sec)
                   (pG , pH)
                   ((grouphom f' _) , (grouphom g' _) , sec')
                  → ((x : ⟨ G ⟩) → f' (groupTransp pG x) ≡ groupTransp pH (f x))
                    × ((y : ⟨ H ⟩) → g' (groupTransp pH y) ≡ groupTransp pG (g y)))
                (λ (_ , _ , _) → (λ _ → refl) , λ _ → refl)
                λ (G , H) (f , g , sec) → {!!}
