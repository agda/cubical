{-

  Explicit "redundant" definition of a bifunctor F : C , D → E.
  Includes all 3 of
  1. A "parallel action" f × g
  2. Two "separate actions" f × d and c × g
  Plus axioms that say
  1. The actions are functorial
  2. and that they agree

  The full definition includes some redundant *axioms* to make it
  convenient to use, so we include two alternative formulations to
  make it easier to prove.

-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Bifunctor.Redundant where

open import Cubical.Foundations.Prelude hiding (Path)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct hiding (Fst; Snd)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
import Cubical.Categories.Bifunctor as Separate

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓc ℓc' ℓd ℓd' ℓe ℓe' : Level

open Category
open Functor
open NatTrans

-- This definition is the most convenient to use
-- But its axioms are redundant as well as its
record Bifunctor (C : Category ℓc ℓc')
                 (D : Category ℓd ℓd')
                 (E : Category ℓe ℓe')
       : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓd (ℓ-max ℓd' (ℓ-max ℓe ℓe'))))) where
  field
    Bif-ob : C .ob → D .ob → E .ob
    Bif-homL : ∀ {c c'} → (f : C [ c , c' ]) → ∀ d
             → E [ Bif-ob c d , Bif-ob c' d ]
    Bif-homR : ∀ {d d'} c → (g : D [ d , d' ]) → E [ Bif-ob c d , Bif-ob c d' ]
    Bif-hom× : ∀ {c c' d d'} (f : C [ c , c' ])(g : D [ d , d' ])
             → E [ Bif-ob c d , Bif-ob c' d' ]
    Bif-L-id : ∀ {c d} → Bif-homL (C .id {c}) d ≡ E .id
    Bif-L-seq : ∀ {c c' c'' d} (f : C [ c , c' ])(f' : C [ c' , c'' ])
             → Bif-homL (f ⋆⟨ C ⟩ f') d ≡ Bif-homL f d ⋆⟨ E ⟩ Bif-homL f' d
    Bif-R-id : ∀ {c d} → Bif-homR c (D .id {d}) ≡ E .id
    Bif-R-seq : ∀ {c d d' d''} (g : D [ d , d' ])(g' : D [ d' , d'' ])
             → Bif-homR c (g ⋆⟨ D ⟩ g') ≡ Bif-homR c g ⋆⟨ E ⟩ Bif-homR c g'
    Bif-×-id : ∀ {c d} → Bif-hom× (C .id {c}) (D .id {d}) ≡ E .id
    Bif-×-seq : ∀ {c c' c'' d d' d''}
               (f : C [ c , c' ])(f' : C [ c' , c'' ])
               (g : D [ d , d' ])(g' : D [ d' , d'' ])
             → Bif-hom× (f ⋆⟨ C ⟩ f') (g ⋆⟨ D ⟩ g')
             ≡ Bif-hom× f g ⋆⟨ E ⟩ Bif-hom× f' g'
    Bif-L×-agree : ∀ {c c' d} → (f : C [ c , c' ])
                 → Bif-homL f d ≡ Bif-hom× f (D .id)
    Bif-R×-agree : ∀ {c d d'} → (g : D [ d , d' ])
                 → Bif-homR c g ≡ Bif-hom× (C .id) g
    Bif-LR-fuse : ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
               → Bif-homL f d ⋆⟨ E ⟩ Bif-homR c' g
               ≡ Bif-hom× f g

    Bif-RL-fuse : ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
               → Bif-homR c g ⋆⟨ E ⟩ Bif-homL f d'
               ≡ Bif-hom× f g

record BifunctorParAx (C : Category ℓc ℓc')
                  (D : Category ℓd ℓd')
                  (E : Category ℓe ℓe')
       : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓd (ℓ-max ℓd' (ℓ-max ℓe ℓe'))))) where
  field
    Bif-ob : C .ob → D .ob → E .ob
    Bif-homL : ∀ {c c'} → (f : C [ c , c' ]) → ∀ d
             → E [ Bif-ob c d , Bif-ob c' d ]
    Bif-homR : ∀ {d d'} c → (g : D [ d , d' ]) → E [ Bif-ob c d , Bif-ob c d' ]
    Bif-hom× : ∀ {c c' d d'} (f : C [ c , c' ])(g : D [ d , d' ])
             → E [ Bif-ob c d , Bif-ob c' d' ]
    Bif-×-id : ∀ {c d} → Bif-hom× (C .id {c}) (D .id {d}) ≡ E .id
    Bif-×-seq : ∀ {c c' c'' d d' d''}
               (f : C [ c , c' ])(f' : C [ c' , c'' ])
               (g : D [ d , d' ])(g' : D [ d' , d'' ])
             → Bif-hom× (f ⋆⟨ C ⟩ f') (g ⋆⟨ D ⟩ g')
             ≡ Bif-hom× f g ⋆⟨ E ⟩ Bif-hom× f' g'
    Bif-L×-agree : ∀ {c c' d} → (f : C [ c , c' ])
                 → Bif-homL f d ≡ Bif-hom× f (D .id)
    Bif-R×-agree : ∀ {c d d'} → (g : D [ d , d' ])
                 → Bif-homR c g ≡ Bif-hom× (C .id) g

record BifunctorSepAx (C : Category ℓc ℓc')
                  (D : Category ℓd ℓd')
                  (E : Category ℓe ℓe')
       : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓd (ℓ-max ℓd' (ℓ-max ℓe ℓe'))))) where
  field
    Bif-ob : C .ob → D .ob → E .ob

    Bif-homL : ∀ {c c'} → (f : C [ c , c' ]) → ∀ d
             → E [ Bif-ob c d , Bif-ob c' d ]
    Bif-L-id : ∀ {c d} → Bif-homL (C .id {c}) d ≡ E .id
    Bif-L-seq : ∀ {c c' c'' d} (f : C [ c , c' ])(f' : C [ c' , c'' ])
             → Bif-homL (f ⋆⟨ C ⟩ f') d ≡ Bif-homL f d ⋆⟨ E ⟩ Bif-homL f' d

    Bif-homR : ∀ {d d'} c → (g : D [ d , d' ]) → E [ Bif-ob c d , Bif-ob c d' ]
    Bif-R-id : ∀ {c d} → Bif-homR c (D .id {d}) ≡ E .id
    Bif-R-seq : ∀ {c d d' d''} (g : D [ d , d' ])(g' : D [ d' , d'' ])
             → Bif-homR c (g ⋆⟨ D ⟩ g') ≡ Bif-homR c g ⋆⟨ E ⟩ Bif-homR c g'

    Bif-hom× : ∀ {c c' d d'} (f : C [ c , c' ])(g : D [ d , d' ])
             → E [ Bif-ob c d , Bif-ob c' d' ]
    Bif-LR-fuse : ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
               → Bif-homL f d ⋆⟨ E ⟩ Bif-homR c' g
               ≡ Bif-hom× f g
    Bif-RL-fuse : ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
               → Bif-homR c g ⋆⟨ E ⟩ Bif-homL f d'
               ≡ Bif-hom× f g

-- A version of bifunctor that only requires the separate actions and
-- constructs the joint action from them arbitrarily.
record BifunctorSep (C : Category ℓc ℓc')
                  (D : Category ℓd ℓd')
                  (E : Category ℓe ℓe')
       : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓd (ℓ-max ℓd' (ℓ-max ℓe ℓe'))))) where
  field
    Bif-ob : C .ob → D .ob → E .ob

    Bif-homL : ∀ {c c'} → (f : C [ c , c' ]) → ∀ d
             → E [ Bif-ob c d , Bif-ob c' d ]
    Bif-L-id : ∀ {c d} → Bif-homL (C .id {c}) d ≡ E .id
    Bif-L-seq : ∀ {c c' c'' d} (f : C [ c , c' ])(f' : C [ c' , c'' ])
             → Bif-homL (f ⋆⟨ C ⟩ f') d ≡ Bif-homL f d ⋆⟨ E ⟩ Bif-homL f' d

    Bif-homR : ∀ {d d'} c → (g : D [ d , d' ]) → E [ Bif-ob c d , Bif-ob c d' ]
    Bif-R-id : ∀ {c d} → Bif-homR c (D .id {d}) ≡ E .id
    Bif-R-seq : ∀ {c d d' d''} (g : D [ d , d' ])(g' : D [ d' , d'' ])
             → Bif-homR c (g ⋆⟨ D ⟩ g') ≡ Bif-homR c g ⋆⟨ E ⟩ Bif-homR c g'

    SepBif-RL-commute : ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
               → Bif-homR c g ⋆⟨ E ⟩ Bif-homL f d'
               ≡ Bif-homL f d ⋆⟨ E ⟩ Bif-homR c' g

-- A version of bifunctor that only requires the parallel action and
-- constructs the joint acions using id. This is definitionally
-- isomorphic to a functor out of the ordinary cartesian product of C
-- and D.
record BifunctorPar (C : Category ℓc ℓc')
                  (D : Category ℓd ℓd')
                  (E : Category ℓe ℓe')
       : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓd (ℓ-max ℓd' (ℓ-max ℓe ℓe'))))) where
  field
    Bif-ob : C .ob → D .ob → E .ob
    Bif-hom× : ∀ {c c' d d'} (f : C [ c , c' ])(g : D [ d , d' ])
             → E [ Bif-ob c d , Bif-ob c' d' ]
    Bif-×-id : ∀ {c d} → Bif-hom× (C .id {c}) (D .id {d}) ≡ E .id
    Bif-×-seq : ∀ {c c' c'' d d' d''}
               (f : C [ c , c' ])(f' : C [ c' , c'' ])
               (g : D [ d , d' ])(g' : D [ d' , d'' ])
             → Bif-hom× (f ⋆⟨ C ⟩ f') (g ⋆⟨ D ⟩ g')
             ≡ Bif-hom× f g ⋆⟨ E ⟩ Bif-hom× f' g'

private
  variable
    C D E : Category ℓ ℓ'

open Bifunctor
open BifunctorParAx
open BifunctorSepAx
open BifunctorSep

mkBifunctorSepAx : BifunctorSepAx C D E → Bifunctor C D E
mkBifunctorSepAx {C = C}{D = D}{E = E} F = G where
  G : Bifunctor C D E
  G .Bif-ob = F .Bif-ob
  G .Bif-homL = F .Bif-homL
  G .Bif-homR = F .Bif-homR
  G .Bif-hom× = F .Bif-hom×
  G .Bif-L-id = F .Bif-L-id
  G .Bif-L-seq = F .Bif-L-seq
  G .Bif-R-id = F .Bif-R-id
  G .Bif-R-seq = F .Bif-R-seq
  G .Bif-LR-fuse = F .Bif-LR-fuse
  G .Bif-RL-fuse = F .Bif-RL-fuse
  G .Bif-×-id = sym (F .Bif-LR-fuse _ _)
    ∙ cong₂ (seq' E) (F .Bif-L-id) (F .Bif-R-id)
    ∙ E .⋆IdR _
  G .Bif-×-seq f f' g g' =
    sym (F .Bif-LR-fuse _ _)
    ∙ cong₂ (seq' E) (F .Bif-L-seq _ _) (F .Bif-R-seq _ _)
    ∙ E .⋆Assoc _ _ _
    ∙ cong₂ (seq' E) refl
          (sym (E .⋆Assoc _ _ _)
          ∙ cong₂ (comp' E) refl (F .Bif-LR-fuse _ _ ∙ sym (F .Bif-RL-fuse _ _))
          ∙ E .⋆Assoc _ _ _
          ∙ cong₂ (seq' E) refl (F .Bif-LR-fuse _ _))
          -- ∙ {!!})
    ∙ sym (E .⋆Assoc _ _ _)
    ∙ cong₂ (comp' E) refl (F .Bif-LR-fuse _ _)

  G .Bif-L×-agree f =
    sym (E .⋆IdR _)
    ∙ cong₂ (seq' E) refl (sym (F .Bif-R-id))
    ∙ F .Bif-LR-fuse _ _
  G .Bif-R×-agree g =
    sym (E .⋆IdL _)
    ∙ cong₂ (comp' E) refl (sym (F .Bif-L-id))
    ∙ F .Bif-LR-fuse _ _

mkBifunctorSep : BifunctorSep C D E → Bifunctor C D E
mkBifunctorSep {C = C}{D = D}{E = E} F = mkBifunctorSepAx G where
  G : BifunctorSepAx C D E
  G .Bif-ob = F .Bif-ob
  G .Bif-homL = F .Bif-homL
  G .Bif-L-id = F .Bif-L-id
  G .Bif-L-seq = F .Bif-L-seq
  G .Bif-homR = F .Bif-homR
  G .Bif-R-id = F .Bif-R-id
  G .Bif-R-seq = F .Bif-R-seq
  G .Bif-hom× f g = seq' E (F .Bif-homL f _) (F .Bif-homR _ g)
  G .Bif-LR-fuse f g = refl
  G .Bif-RL-fuse f g = F .SepBif-RL-commute f g

mkBifunctorParAx : BifunctorParAx C D E → Bifunctor C D E
mkBifunctorParAx {C = C}{D = D}{E = E} F = G where
  open BifunctorParAx F
  open Bifunctor
  G : Bifunctor C D E
  G .Bif-ob = F .Bif-ob
  G .Bif-homL = F .Bif-homL
  G .Bif-homR = F .Bif-homR
  G .Bif-hom× = F .Bif-hom×
  G .Bif-×-id = F .Bif-×-id
  G .Bif-×-seq = F .Bif-×-seq
  G .Bif-L×-agree = F .Bif-L×-agree
  G .Bif-R×-agree = F .Bif-R×-agree

  G .Bif-L-id = F .Bif-L×-agree _ ∙ F .Bif-×-id
  G .Bif-L-seq f f' = F .Bif-L×-agree _
    ∙ cong₂ (F .Bif-hom×) refl (sym (D .⋆IdR (D .id)))
    ∙ F .Bif-×-seq f f' (D .id) (D .id)
    ∙ cong₂ (seq' E) (sym (F .Bif-L×-agree _)) (sym (F .Bif-L×-agree _))
  G .Bif-R-id = F .Bif-R×-agree _ ∙ F .Bif-×-id
  G .Bif-R-seq g g' = G .Bif-R×-agree _
    ∙ cong₂ (F .Bif-hom×) (sym (C .⋆IdR (C .id))) refl
    ∙ F .Bif-×-seq _ _ _ _
    ∙ cong₂ (seq' E) (sym (F .Bif-R×-agree _)) (sym (F .Bif-R×-agree _))

  G .Bif-LR-fuse f g =
    cong₂ (seq' E) (F .Bif-L×-agree _) (F .Bif-R×-agree _)
    ∙ sym (F .Bif-×-seq _ _ _ _)
    ∙ cong₂ (F .Bif-hom×) (C .⋆IdR _) (D .⋆IdL _)
  G .Bif-RL-fuse f g =
    cong₂ (seq' E) (F .Bif-R×-agree _) (F .Bif-L×-agree _)
    ∙ sym (F .Bif-×-seq _ _ _ _)
    ∙ cong₂ (F .Bif-hom×) (C .⋆IdL _) (D .⋆IdR _)

mkBifunctorPar : BifunctorPar C D E → Bifunctor C D E
mkBifunctorPar {C = C}{D = D}{E = E} F = mkBifunctorParAx G where
  module F = BifunctorPar F
  G : BifunctorParAx C D E
  G .Bif-ob = F.Bif-ob
  G .Bif-hom× = F.Bif-hom×
  G .Bif-×-id = F.Bif-×-id
  G .Bif-×-seq = F.Bif-×-seq
  G .Bif-homL f d = F.Bif-hom× f (D .id)
  G .Bif-homR c g = F.Bif-hom× (C .id) g
  G .Bif-L×-agree f = refl
  G .Bif-R×-agree g = refl

open Bifunctor
open BifunctorParAx
open BifunctorPar
open BifunctorSepAx
open BifunctorSep
-- action on objects
infix 30 _⟅_⟆b
_⟅_⟆b : (F : Bifunctor C D E)
     → C .ob × D .ob
     → E .ob
F ⟅ c , d ⟆b = Bif-ob F c d

-- actions on morphisms
infix 30 _⟪_⟫l
-- same infix level as on objects since these will
-- never be used in the same context
infix 30 _⟪_⟫r

-- same infix level as on objects since these will
-- never be used in the same context
infix 30 _⟪_⟫×

_⟪_⟫l : (F : Bifunctor C D E)
     → ∀ {c c' d}
     → C [ c , c' ]
     → E [(F ⟅ c , d ⟆b) , (F ⟅ c' , d ⟆b)]
F ⟪ f ⟫l = Bif-homL F f _

_⟪_⟫r : (F : Bifunctor C D E)
     → ∀ {c d d'}
     → D [ d , d' ]
     → E [(F ⟅ c , d ⟆b) , (F ⟅ c , d' ⟆b)]
F ⟪ f ⟫r = Bif-homR F _ f

_⟪_⟫× : (F : Bifunctor C D E)
      → ∀ {c c' d d'}
      → C [ c , c' ] × D [ d , d' ]
      → E [ F ⟅ c , d ⟆b , F ⟅ c' , d' ⟆b ]
F ⟪ f , g ⟫× = F .Bif-hom× f g

Bif-RL-commute
  : {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
  → (F : Bifunctor C D E)
  → ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
  → F ⟪ g ⟫r ⋆⟨ E ⟩ F ⟪ f ⟫l ≡ F ⟪ f ⟫l ⋆⟨ E ⟩ F ⟪ g ⟫r
Bif-RL-commute F f g =
  F .Bif-RL-fuse f g ∙ sym (F .Bif-LR-fuse f g)

-- Bif ×L commute that × commutes with homL
-- Bif L×  that × commutes with hom× ⋆ homL ≡ hom×

Bif-×L-fuse
  : {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
  → (F : Bifunctor C D E)
  → ∀ {c c' c''}{d d'}(f : C [ c , c' ])(f' : C [ c' , c'' ])
    (g : D [ d , d' ])
  → F ⟪ f , g ⟫× ⋆⟨ E ⟩ F ⟪ f' ⟫l ≡ F ⟪ (f ⋆⟨ C ⟩ f') , g ⟫×
Bif-×L-fuse {D = D}{E = E} F f f' g =
  cong₂ (seq' E) refl (F .Bif-L×-agree f')
  ∙ sym (F .Bif-×-seq f f' g _)
  ∙ cong₂ (F .Bif-hom×) refl (D .⋆IdR g)

Bif-L×-fuse
  : {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
  → (F : Bifunctor C D E)
  → ∀ {c c' c''}{d d'}(f : C [ c , c' ])(f' : C [ c' , c'' ])
    (g : D [ d , d' ])
  → F ⟪ f ⟫l ⋆⟨ E ⟩ F ⟪ f' , g ⟫× ≡ F ⟪ (f ⋆⟨ C ⟩ f') , g ⟫×
Bif-L×-fuse {D = D}{E = E} F f f' g =
  cong₂ (seq' E) (F .Bif-L×-agree f) refl
  ∙ sym (F .Bif-×-seq f f' (D .id) g)
  ∙ cong₂ (F .Bif-hom×) refl (D .⋆IdL g)

Bif-R×-fuse
  : {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
  → (F : Bifunctor C D E)
  → ∀ {c c' d d' d''} (f : C [ c , c' ])
    (g : D [ d , d' ]) (g' : D [ d' , d'' ])
  → F ⟪ g ⟫r ⋆⟨ E ⟩ F ⟪ f , g' ⟫×
    ≡ F ⟪ f , (g ⋆⟨ D ⟩ g')⟫×
Bif-R×-fuse {C = C}{E = E} F f g g' =
  cong₂ (comp' E) refl (F .Bif-R×-agree g)
  ∙ sym (F .Bif-×-seq _ f g g')
  ∙ cong₂ (F .Bif-hom×) (C .⋆IdL f) refl

Bif-×R-fuse
  : {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
  → (F : Bifunctor C D E)
  → ∀ {c c' d d' d''} (f : C [ c , c' ])
    (g : D [ d , d' ]) (g' : D [ d' , d'' ])
  → F ⟪ f , g ⟫× ⋆⟨ E ⟩ F ⟪ g' ⟫r
    ≡ F ⟪ f , (g ⋆⟨ D ⟩ g')⟫×
Bif-×R-fuse {C = C}{E = E} F f g g' =
  cong₂ (seq' E) refl (F .Bif-R×-agree g')
  ∙ sym (F .Bif-×-seq f _ g g')
  ∙ cong₂ (F .Bif-hom×) (C .⋆IdR _) refl

Fst : {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
    → Bifunctor C D C
Fst {C = C}{D = D} = mkBifunctorSepAx Fst' where
  Fst' : BifunctorSepAx C D C
  Fst' .Bif-ob c d = c
  Fst' .Bif-homL f d = f
  Fst' .Bif-L-id = refl
  Fst' .Bif-L-seq f f' = refl
  Fst' .Bif-homR c g = C .id
  Fst' .Bif-R-id = refl
  Fst' .Bif-R-seq g g' = sym (C .⋆IdL _)
  Fst' .Bif-hom× f g = f
  Fst' .Bif-LR-fuse f g = C .⋆IdR f
  Fst' .Bif-RL-fuse f g = C .⋆IdL f


Snd : {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
    → Bifunctor C D D
Snd {C = C}{D = D} = mkBifunctorSepAx Snd' where
  Snd' : BifunctorSepAx C D D
  Snd' .Bif-ob c d = d
  Snd' .Bif-homL f d = D .id
  Snd' .Bif-L-id = refl
  Snd' .Bif-L-seq f f' = sym (D .⋆IdL _)
  Snd' .Bif-homR c g = g
  Snd' .Bif-R-id = refl
  Snd' .Bif-R-seq g g' = refl
  Snd' .Bif-hom× f g = g
  Snd' .Bif-LR-fuse f g = D .⋆IdL g
  Snd' .Bif-RL-fuse f g = D .⋆IdR g

Sym : {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
    → Bifunctor C D E → Bifunctor D C E
Sym {C = C}{D = D}{E = E} F = mkBifunctorParAx Sym' where
  Sym' : BifunctorParAx D C E
  Sym' .Bif-ob d c = F ⟅ c , d ⟆b
  Sym' .Bif-homL g c = F ⟪ g ⟫r
  Sym' .Bif-homR d f = F ⟪ f ⟫l
  Sym' .Bif-hom× g f = F ⟪ f , g ⟫×
  Sym' .Bif-×-id = F .Bif-×-id
  Sym' .Bif-×-seq f f' g g' = F .Bif-×-seq g g' f f'
  Sym' .Bif-L×-agree = F .Bif-R×-agree
  Sym' .Bif-R×-agree = F .Bif-L×-agree

private
  variable
    C' D' E' : Category ℓ ℓ'

appL : (F : Bifunctor C D E) (c : C .ob) → Functor D E
appL F c .F-ob d = F ⟅ c , d ⟆b
appL F c .F-hom g = F ⟪ g ⟫r
appL F c .F-id = F .Bif-R-id
appL F c .F-seq g g' = F .Bif-R-seq g g'

appR : (F : Bifunctor C D E) (d : D .ob) → Functor C E
appR F d .F-ob c = F ⟅ c , d ⟆b
appR F d .F-hom f = F ⟪ f ⟫l
appR F d .F-id = F .Bif-L-id
appR F d .F-seq f f' = F .Bif-L-seq f f'

compL : (F : Bifunctor C' D E) (G : Functor C C') → Bifunctor C D E
compL {D = D}{E = E}{C = C} F G = mkBifunctorSepAx B where
  B : BifunctorSepAx C D E
  B .Bif-ob c d = F ⟅ G ⟅ c ⟆  , d ⟆b
  B .Bif-homL f d = F ⟪ G ⟪ f ⟫ ⟫l
  B .Bif-L-id {d = d} = ((appR F d) ∘F G) .F-id
  B .Bif-L-seq {d = d} f f' = ((appR F d) ∘F G) .F-seq f f'
  B .Bif-homR c g = F ⟪ g ⟫r
  B .Bif-R-id = F .Bif-R-id
  B .Bif-R-seq = F .Bif-R-seq
  B .Bif-hom× f g = F ⟪ G ⟪ f ⟫ , g ⟫×
  B .Bif-LR-fuse f = F .Bif-LR-fuse (G ⟪ f ⟫)
  B .Bif-RL-fuse f = F .Bif-RL-fuse (G ⟪ f ⟫)

compR : (F : Bifunctor C D' E) (G : Functor D D') → Bifunctor C D E
compR {C = C}{E = E}{D = D} F G = mkBifunctorSepAx B where
  B : BifunctorSepAx C D E
  B .Bif-ob c d = F ⟅ c , G ⟅ d ⟆ ⟆b
  B .Bif-homL f d = F ⟪ f ⟫l
  B .Bif-L-id = F .Bif-L-id
  B .Bif-L-seq = F .Bif-L-seq
  B .Bif-homR c g = F ⟪ G ⟪ g ⟫ ⟫r
  B .Bif-R-id {c = c} = ((appL F c) ∘F G) .F-id
  B .Bif-R-seq {c = c} = ((appL F c) ∘F G) .F-seq
  B .Bif-hom× f g = F ⟪ f , G ⟪ g ⟫ ⟫×
  B .Bif-LR-fuse f g = F .Bif-LR-fuse f (G ⟪ g ⟫)
  B .Bif-RL-fuse f g = F .Bif-RL-fuse f (G ⟪ g ⟫)

compF : (F : Functor E E') (G : Bifunctor C D E) → Bifunctor C D E'
compF {E = E}{E' = E'}{C = C}{D = D} F  G = mkBifunctorParAx B where
  B : BifunctorParAx C D E'
  B .Bif-ob c d = F ⟅ G ⟅ c , d ⟆b ⟆
  B .Bif-homL f d = F ⟪ G ⟪ f ⟫l ⟫
  B .Bif-homR c g = F ⟪ G ⟪ g ⟫r ⟫
  B .Bif-hom× f g = F ⟪ G ⟪ f , g ⟫× ⟫
  B .Bif-×-id = cong (F ⟪_⟫) (G .Bif-×-id) ∙ F .F-id
  B .Bif-×-seq f f' g g' = cong (F ⟪_⟫) (G .Bif-×-seq f f' g g')
    ∙ F .F-seq _ _
  B .Bif-L×-agree f = cong (F ⟪_⟫) (G .Bif-L×-agree f)
  B .Bif-R×-agree g = cong (F ⟪_⟫) (G .Bif-R×-agree g)

infixl 30 compL
infixl 30 compR
infixr 30 compF
infixl 30 compLR'

syntax compL F G = F ∘Fl G
syntax compR F G = F ∘Fr G
syntax compF F G = F ∘Fb G

-- | This includes an arbitrary choice, the action on objects should
-- | be definitionally equal to the other order, but the proofs are
-- | affected.
compLR : (F : Bifunctor C' D' E) (G : Functor C C')(H : Functor D D')
       → Bifunctor C D E
compLR F G H = F ∘Fl G ∘Fr H

compLR' : (F : Bifunctor C' D' E) (GH : Functor C C' × Functor D D')
        → Bifunctor C D E
compLR' F GH = compLR F (GH .fst) (GH .snd)

syntax compLR' F GH = F ∘Flr GH

-- For Hom we use the Seperate actions formulation because there is no
-- "nice" way to do triple composition (at least with this definition
-- of category).
HomBif : (C : Category ℓ ℓ') → Bifunctor (C ^op) C (SET ℓ')
HomBif C = mkBifunctorSep Hom where
  Hom : BifunctorSep (C ^op) C (SET _)
  Hom .Bif-ob c c' = (C [ c , c' ]) , C .isSetHom
  Hom .Bif-homL f c' f' = f ⋆⟨ C ⟩ f'
  Hom .Bif-L-id = funExt (C .⋆IdL)
  Hom .Bif-L-seq f' f = funExt (λ f'' → C .⋆Assoc f f' f'')
  Hom .Bif-homR c f' f = f ⋆⟨ C ⟩ f'
  Hom .Bif-R-id = funExt (C .⋆IdR)
  Hom .Bif-R-seq f' f'' = funExt λ f → sym (C .⋆Assoc f f' f'')
  Hom .SepBif-RL-commute f g = funExt (λ h → sym (C .⋆Assoc f h g))

BifunctorToParFunctor : Bifunctor C D E → Functor (C ×C D) E
BifunctorToParFunctor F .F-ob (c , d) = F .Bif-ob c d
BifunctorToParFunctor F .F-hom (f , g) = F .Bif-hom× f g
BifunctorToParFunctor F .F-id = F .Bif-×-id
BifunctorToParFunctor F .F-seq f g = F .Bif-×-seq _ _ _ _

CurriedToBifunctor : Functor C (FUNCTOR D E) → Bifunctor C D E
CurriedToBifunctor F = mkBifunctorSep G where
  G : BifunctorSep _ _ _
  G .Bif-ob c d = F ⟅ c ⟆ ⟅ d ⟆
  G .Bif-homL f d = F ⟪ f ⟫ ⟦ d ⟧
  G .Bif-homR c g = F ⟅ c ⟆ ⟪ g ⟫
  G .Bif-L-id {d = d} = (cong (_⟦ d ⟧) (F .F-id))
  G .Bif-L-seq f f' = (cong (_⟦ _ ⟧) (F .F-seq f f'))
  G .Bif-R-id = (F ⟅ _ ⟆) .F-id
  G .Bif-R-seq g g' = (F ⟅ _ ⟆) .F-seq g g'
  G .SepBif-RL-commute f g = (F ⟪ f ⟫) .N-hom g

CurryBifunctor : Bifunctor C D E → Functor C (FUNCTOR D E)
CurryBifunctor F .F-ob c = appL F c
CurryBifunctor F .F-hom f .N-ob d = appR F d .F-hom f
CurryBifunctor F .F-hom f .N-hom g = Bif-RL-commute F f g
CurryBifunctor F .F-id = makeNatTransPath (funExt λ d → F .Bif-L-id)
CurryBifunctor F .F-seq _ _ = makeNatTransPath (funExt λ d → F .Bif-L-seq _ _)

open Separate.Bifunctor
ForgetPar : Bifunctor C D E → Separate.Bifunctor C D E
ForgetPar F .Bif-ob = F .Bif-ob
ForgetPar F .Bif-homL = F .Bif-homL
ForgetPar F .Bif-homR = F .Bif-homR
ForgetPar F .Bif-idL = F .Bif-L-id
ForgetPar F .Bif-idR = F .Bif-R-id
ForgetPar F .Bif-seqL = F .Bif-L-seq
ForgetPar F .Bif-seqR = F .Bif-R-seq
ForgetPar F .Bif-assoc f g = sym (Bif-RL-commute F f g)

_^opBif : Bifunctor C D E
        → Bifunctor (C ^op) (D ^op) (E ^op)
_^opBif {C = C}{D = D}{E = E} F = mkBifunctorParAx G where
  module F = Bifunctor F
  G : BifunctorParAx (C ^op) (D ^op) (E ^op)
  G .Bif-ob = F.Bif-ob
  G .Bif-homL = F.Bif-homL
  G .Bif-homR = F.Bif-homR
  G .Bif-hom× = F.Bif-hom×
  G .Bif-×-id = F.Bif-×-id
  G .Bif-×-seq f f' g g' = F.Bif-×-seq f' f g' g
  G .Bif-L×-agree = F.Bif-L×-agree
  G .Bif-R×-agree = F.Bif-R×-agree
