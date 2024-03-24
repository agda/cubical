{-

  Explicit definition of a bifunctor as a "separately functorial"
  action satisfying a commutativity condition. This is equivalent to
  defining a bifunctor as a functor out of a product, but has better
  definitional behavior in some cases.

-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Bifunctor.Base where

open import Cubical.Foundations.Prelude hiding (Path)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct hiding (Fst; Snd)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors

open import Cubical.Data.Sigma
open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓc ℓc' ℓd ℓd' ℓe ℓe' : Level

open Category
open Functor
open NatTrans

record Bifunctor (C : Category ℓc ℓc')
                 (D : Category ℓd ℓd')
                 (E : Category ℓe ℓe')
       : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓd (ℓ-max ℓd' (ℓ-max ℓe ℓe'))))) where
  field
    Bif-ob : C .ob → D .ob → E .ob
    Bif-homL : ∀ {c c'} → (f : C [ c , c' ]) → ∀ d
             → E [ Bif-ob c d , Bif-ob c' d ]
    Bif-homR : ∀ {d d'} c → (g : D [ d , d' ]) → E [ Bif-ob c d , Bif-ob c d' ]
    Bif-idL : ∀ {c d} → Bif-homL (C .id {c}) d ≡ E .id
    Bif-idR : ∀ {c d} → Bif-homR c (D .id {d}) ≡ E .id
    Bif-seqL : ∀ {c c' c'' d} (f : C [ c , c' ])(f' : C [ c' , c'' ])
             → Bif-homL (f ⋆⟨ C ⟩ f') d ≡ Bif-homL f d ⋆⟨ E ⟩ Bif-homL f' d
    Bif-seqR : ∀ {c d d' d''} (g : D [ d , d' ])(g' : D [ d' , d'' ])
             → Bif-homR c (g ⋆⟨ D ⟩ g') ≡ Bif-homR c g ⋆⟨ E ⟩ Bif-homR c g'

    -- Note: if we drop the following condition we get a sensible
    -- notion of "separately functorial operation"
    Bif-assoc : ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
              → Bif-homL f d ⋆⟨ E ⟩ Bif-homR c' g
              ≡ Bif-homR c g ⋆⟨ E ⟩ Bif-homL f d'

open Bifunctor

private
  variable
     C : Category ℓc ℓc'
     C' : Category ℓc ℓc'
     D : Category ℓd ℓd'
     D' : Category ℓd ℓd'
     E : Category ℓe ℓe'
     E' : Category ℓe ℓe'

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

Fst : Bifunctor C D C
Fst .Bif-ob = λ z _ → z
Fst .Bif-homL = λ z d → z
Fst {C = C} .Bif-homR = λ c _ → C .id
Fst .Bif-idL = refl
Fst .Bif-idR = refl
Fst .Bif-seqL = λ f f' → refl
Fst {C = C} .Bif-seqR g g' = sym (C .⋆IdL _)
Fst {C = C} .Bif-assoc f g = C .⋆IdR _ ∙ sym (C .⋆IdL _)

Snd : Bifunctor C D D
Snd .Bif-ob c d = d
Snd {D = D} .Bif-homL f d = D .id
Snd .Bif-homR c g = g
Snd .Bif-idL = refl
Snd .Bif-idR = refl
Snd {D = D} .Bif-seqL f f' = sym (D .⋆IdL _)
Snd .Bif-seqR g g' = refl
Snd {D = D} .Bif-assoc f g = D .⋆IdL _ ∙ sym (D .⋆IdR _)

Sym : Bifunctor C D E → Bifunctor D C E
Sym F .Bif-ob d c = F ⟅ c , d ⟆b
Sym F .Bif-homL g c = F ⟪ g ⟫r
Sym F .Bif-homR d f = F ⟪ f ⟫l
Sym F .Bif-idL = F .Bif-idR
Sym F .Bif-idR = F .Bif-idL
Sym F .Bif-seqL = F .Bif-seqR
Sym F .Bif-seqR = F .Bif-seqL
Sym F .Bif-assoc f g = sym (F .Bif-assoc g f)

pAppL : (F : Bifunctor C D E) → C .ob → Functor D E
pAppL F c .F-ob d = F ⟅ c , d ⟆b
pAppL F c .F-hom g = F ⟪ g ⟫r
pAppL F c .F-id = F .Bif-idR
pAppL F c .F-seq f g = F .Bif-seqR _ _

pAppR : (F : Bifunctor C D E) → D .ob → Functor C E
pAppR F d .F-ob c = F ⟅ c , d ⟆b
pAppR F d .F-hom f = F ⟪ f ⟫l
pAppR F d .F-id = F .Bif-idL
pAppR F d .F-seq f g = F .Bif-seqL _ _

bifCompL : (F : Bifunctor C D E) (G : Functor C' C) → Bifunctor C' D E
bifCompL F G .Bif-ob c' d = F ⟅ G ⟅ c' ⟆ ,  d ⟆b
bifCompL F G .Bif-homL f d = F ⟪ G ⟪ f ⟫ ⟫l
bifCompL F G .Bif-homR c g = F ⟪ g ⟫r
bifCompL F G .Bif-idL = cong (F ⟪_⟫l) (G .F-id) ∙ F .Bif-idL
bifCompL F G .Bif-idR = F .Bif-idR
bifCompL F G .Bif-seqL f f' = cong (F ⟪_⟫l) (G .F-seq f f') ∙ F .Bif-seqL _ _
bifCompL F G .Bif-seqR g g' = F .Bif-seqR g g'
bifCompL F G .Bif-assoc f g = F .Bif-assoc _ _

bifCompR : (F : Bifunctor C D E) (G : Functor D' D) → Bifunctor C D' E
bifCompR F G .Bif-ob c d' = F ⟅ c , G ⟅ d' ⟆ ⟆b
bifCompR F G .Bif-homL f d = F ⟪ f ⟫l
bifCompR F G .Bif-homR c g = F ⟪ G ⟪ g ⟫ ⟫r
bifCompR F G .Bif-idL = F .Bif-idL
bifCompR F G .Bif-idR = cong (F ⟪_⟫r) (G .F-id) ∙ F .Bif-idR
bifCompR F G .Bif-seqL f f' = F .Bif-seqL _ _
bifCompR F G .Bif-seqR g g' = cong (F ⟪_⟫r) (G .F-seq _ _) ∙ F .Bif-seqR _ _
bifCompR F G .Bif-assoc f g = F .Bif-assoc _ _

bifCompF : (F : Functor E E') (G : Bifunctor C D E) → Bifunctor C D E'
bifCompF F G .Bif-ob c d = F ⟅ G ⟅ c , d ⟆b ⟆
bifCompF F G .Bif-homL f d = F ⟪ G ⟪ f ⟫l ⟫
bifCompF F G .Bif-homR c g = F ⟪ G ⟪ g ⟫r ⟫
bifCompF F G .Bif-idL = cong (F ⟪_⟫) (G .Bif-idL) ∙ F .F-id
bifCompF F G .Bif-idR = cong (F ⟪_⟫) (G .Bif-idR) ∙ F .F-id
bifCompF F G .Bif-seqL f f' = cong (F ⟪_⟫) (G .Bif-seqL _ _) ∙ F .F-seq _ _
bifCompF F G .Bif-seqR g g' = cong (F ⟪_⟫) (G .Bif-seqR _ _) ∙ F .F-seq _ _
bifCompF F G .Bif-assoc f g =
  sym (F .F-seq _ _) ∙ cong (F ⟪_⟫) (G .Bif-assoc _ _) ∙ F .F-seq _ _

infixr 30 bifCompL
infixr 30 bifCompR
infixr 30 bifCompF

syntax bifCompL F G = F ∘Fl G
syntax bifCompR F G = F ∘Fr G
syntax bifCompF F G = F ∘Fb G

HomBif : (C : Category ℓc ℓc') → Bifunctor (C ^op) C (SET ℓc')
HomBif C .Bif-ob c c' = (C [ c , c' ]) , (C .isSetHom)
HomBif C .Bif-homL f d f' = f ⋆⟨ C ⟩ f'
HomBif C .Bif-homR c f' f = f ⋆⟨ C ⟩ f'
HomBif C .Bif-idL = funExt (C .⋆IdL)
HomBif C .Bif-idR = funExt (C .⋆IdR)
HomBif C .Bif-seqL f' f = funExt (λ f'' → C .⋆Assoc _ _ _)
HomBif C .Bif-seqR g g' = funExt (λ g'' → sym (C .⋆Assoc _ _ _))
HomBif C .Bif-assoc f g = funExt (λ g' → C .⋆Assoc _ _ _)

UniversalBifunctor : Bifunctor C D (C ×C D)
UniversalBifunctor .Bif-ob c d = c , d
UniversalBifunctor {D = D} .Bif-homL f d = f , D .id
UniversalBifunctor {C = C} .Bif-homR c g = C .id , g
UniversalBifunctor .Bif-idL = refl
UniversalBifunctor .Bif-idR = refl
-- Weirdly cong₂ goes yellow here so let's just do it explicitly
UniversalBifunctor {C = C} {D = D} .Bif-seqL f f' i =
  seq' C f f' , D .⋆IdR (D .id) (~ i)
UniversalBifunctor {C = C}{D = D} .Bif-seqR g g' i =
  (C .⋆IdR (C .id) (~ i)) , seq' D g g'
UniversalBifunctor {C = C} {D = D} .Bif-assoc f g i =
  (idTrans (Id {C = C}) .N-hom f i) , idTrans (Id {C = D}) .N-hom g (~ i)

Bifunctor→Functor : Bifunctor C D E → Functor (C ×C D) E
Bifunctor→Functor F .F-ob p = F ⟅ p ⟆b
Bifunctor→Functor {E = E} F .F-hom (f , g) = F ⟪ f ⟫l ⋆⟨ E ⟩ F ⟪ g ⟫r
Bifunctor→Functor {E = E} F .F-id =
  cong₂ (seq' E) (F .Bif-idL) (F .Bif-idR) ∙ E .⋆IdL _
Bifunctor→Functor {E = E} F .F-seq (f , g) (f' , g') =
  cong₂ (E ._⋆_) (F .Bif-seqL _ _) (F .Bif-seqR _ _)
  ∙ E .⋆Assoc _ _ _
  ∙ cong₂ (E ._⋆_)
    refl
    (sym (E .⋆Assoc _ _ _) ∙ cong₂ (E ._⋆_) (F .Bif-assoc _ _) refl)
  ∙ lem where
  lem : E ._⋆_ (F .Bif-homL f _)
      (E ._⋆_ ((E ⋆ F .Bif-homR _ g) (F .Bif-homL f' _))
       (F .Bif-homR _ g'))
      ≡
      (E ⋆ (E ⋆ Bif-homL F f _) (Bif-homR F _ g))
      ((E ⋆ Bif-homL F f' _) (Bif-homR F _ g'))
  lem = solveCat! E

Functor→Bifunctor : Functor (C ×C D) E → Bifunctor C D E
Functor→Bifunctor {C = C}{D = D} F = F ∘Fb UniversalBifunctor {C = C}{D = D}
-- -- TODO: above is an Iso

λFR : Bifunctor C D E → Functor C (FUNCTOR D E)
λFR F .F-ob x .F-ob y = F ⟅ x , y ⟆b
λFR F .F-ob x .F-hom g = F ⟪ g ⟫r
λFR F .F-ob x .F-id = Bif-idR F
λFR F .F-ob x .F-seq = Bif-seqR F
λFR F .F-hom f .N-ob y = F ⟪ f ⟫l
λFR F .F-hom f .N-hom g = sym (Bif-assoc F f g)
λFR F .F-id = makeNatTransPath (funExt (λ x → Bif-idL F))
λFR F .F-seq f f' = makeNatTransPath (funExt (λ x → Bif-seqL F f f'))

appR : Bifunctor (FUNCTOR D E) D E
appR .Bif-ob F x = F ⟅ x ⟆
appR .Bif-homL α d = α ⟦ d ⟧
appR .Bif-idL = refl
appR .Bif-seqL f f' = refl
appR .Bif-homR F g = F ⟪ g ⟫
appR .Bif-idR {c = F} = F .F-id
appR .Bif-seqR {c = F} g g' = F .F-seq g g'
appR .Bif-assoc α g = sym (α .N-hom g)
