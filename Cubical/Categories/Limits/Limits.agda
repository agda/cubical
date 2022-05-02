-- Limits.
-- Heavily inspired by https://github.com/UniMath/UniMath/blob/master/UniMath/CategoryTheory/limits/graphs/limits.v
-- (except we're using categories instead of graphs to index limits)

{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.HITs.PropositionalTruncation.Base

module _ {ℓJ ℓJ' ℓC ℓC' : Level} {J : Category ℓJ ℓJ'} {C : Category ℓC ℓC'} where
  open Category
  open Functor

  private
    ℓ = ℓ-max (ℓ-max (ℓ-max ℓJ ℓJ') ℓC) ℓC'

  record Cone (D : Functor J C) (c : ob C) : Type (ℓ-max (ℓ-max ℓJ ℓJ') ℓC') where
    constructor cone

    field
      coneOut : (v : ob J) → C [ c , F-ob D v ]
      coneOutCommutes : {u v : ob J} (e : J [ u , v ]) →
                        coneOut u ⋆⟨ C ⟩ D .F-hom e ≡ coneOut v

  open Cone

  cone≡ : {D : Functor J C} {c : ob C} → {c1 c2 : Cone D c}
        → ((v : ob J) → coneOut c1 v ≡ coneOut c2 v) → c1 ≡ c2
  coneOut (cone≡ h i) v = h v i
  coneOutCommutes (cone≡ {D} {_} {c1} {c2} h i) {u} {v} e =
    isProp→PathP (λ j → isSetHom C (h u j ⋆⟨ C ⟩ D .F-hom e) (h v j))
                 (coneOutCommutes c1 e) (coneOutCommutes c2 e) i

  -- TODO: can we automate this a bit?
  isSetCone : (D : Functor J C) (c : ob C) → isSet (Cone D c)
  isSetCone D c = isSetRetract toConeΣ fromConeΣ (λ _ → refl)
                               (isSetΣSndProp (isSetΠ (λ _ → isSetHom C))
                                              (λ _ → isPropImplicitΠ2 (λ _ _ → isPropΠ (λ _ → isSetHom C _ _))))
    where
    ConeΣ = Σ[ f ∈ ((v : ob J) → C [ c , F-ob D v ]) ]
               ({u v : ob J} (e : J [ u , v ]) → f u ⋆⟨ C ⟩ D .F-hom e ≡ f v)

    toConeΣ : Cone D c → ConeΣ
    fst (toConeΣ x) = coneOut x
    snd (toConeΣ x) = coneOutCommutes x

    fromConeΣ : ConeΣ → Cone D c
    coneOut (fromConeΣ x) = fst x
    coneOutCommutes (fromConeΣ x) = snd x

  isConeMor : {c1 c2 : ob C} {D : Functor J C}
              (cc1 : Cone D c1) (cc2 : Cone D c2)
            → C [ c1 , c2 ] → Type (ℓ-max ℓJ ℓC')
  isConeMor cc1 cc2 f = (v : ob J) → f ⋆⟨ C ⟩ coneOut cc2 v ≡ coneOut cc1 v

  isPropIsConeMor : {c1 c2 : ob C} {D : Functor J C}
                    (cc1 : Cone D c1) (cc2 : Cone D c2) (f : C [ c1 , c2 ])
                  → isProp (isConeMor cc1 cc2 f)
  isPropIsConeMor cc1 cc2 f = isPropΠ (λ _ → isSetHom C _ _)

  isLimCone : (D : Functor J C) (c0 : ob C) → Cone D c0 → Type ℓ
  isLimCone D c0 cc0 = (c : ob C) → (cc : Cone D c)
                     → ∃![ f ∈ C [ c , c0 ] ] isConeMor cc cc0 f

  isPropIsLimCone : (D : Functor J C) (c0 : ob C) (cc0 : Cone D c0)
                  → isProp (isLimCone D c0 cc0)
  isPropIsLimCone D c0 cc0 = isPropΠ2 λ _ _ → isProp∃!

  record LimCone (D : Functor J C) : Type ℓ where
    constructor climCone

    field
      lim : ob C
      limCone : Cone D lim
      univProp : isLimCone D lim limCone

    limOut : (v : ob J) → C [ lim , D .F-ob v ]
    limOut = coneOut limCone

    limOutCommutes : {u v : ob J} (e : J [ u , v ])
                   → limOut u ⋆⟨ C ⟩ D .F-hom e ≡ limOut v
    limOutCommutes = coneOutCommutes limCone

    limArrow : (c : ob C) → (cc : Cone D c) → C [ c , lim ]
    limArrow c cc = univProp c cc .fst .fst

    limArrowCommutes : (c : ob C) → (cc : Cone D c) (u : ob J)
                     → limArrow c cc ⋆⟨ C ⟩ limOut u ≡ coneOut cc u
    limArrowCommutes c cc = univProp c cc .fst .snd

    limArrowUnique : (c : ob C) → (cc : Cone D c) (k : C [ c , lim ])
                   → isConeMor cc limCone k → limArrow c cc ≡ k
    limArrowUnique c cc k hk = cong fst (univProp c cc .snd (k , hk))

  open LimCone
  limOfArrows : (D₁ D₂ : Functor J C)
                (CC₁ : LimCone D₁) (CC₂ : LimCone D₂)
                (f : (u : ob J) → C [ D₁ .F-ob u , D₂ .F-ob u ])
                (fNat : {u v : ob J} (e : J [ u , v ])
                      →  f u ⋆⟨ C ⟩ D₂ .F-hom e ≡ D₁ .F-hom e ⋆⟨ C ⟩ f v)
              → C [ CC₁ .lim , CC₂ .lim ]
  limOfArrows D₁ D₂ CC₁ CC₂ f fNat = limArrow CC₂ (CC₁ .lim) coneD₂Lim₁
   where
   coneD₂Lim₁ : Cone D₂ (CC₁ .lim)
   coneOut coneD₂Lim₁ v = limOut CC₁ v ⋆⟨ C ⟩ f v
   coneOutCommutes coneD₂Lim₁ {u = u} {v = v} e =
     limOut CC₁ u ⋆⟨ C ⟩ f u ⋆⟨ C ⟩ D₂ .F-hom e   ≡⟨ ⋆Assoc C _ _ _ ⟩
     limOut CC₁ u ⋆⟨ C ⟩ (f u ⋆⟨ C ⟩ D₂ .F-hom e) ≡⟨ cong (λ x → seq' C (limOut CC₁ u) x) (fNat e) ⟩
     limOut CC₁ u ⋆⟨ C ⟩ (D₁ .F-hom e ⋆⟨ C ⟩ f v) ≡⟨ sym (⋆Assoc C _ _ _) ⟩
     limOut CC₁ u ⋆⟨ C ⟩ D₁ .F-hom e ⋆⟨ C ⟩ f v   ≡⟨ cong (λ x → x ⋆⟨ C ⟩ f v) (limOutCommutes CC₁ e) ⟩
     limOut CC₁ v ⋆⟨ C ⟩ f v ∎

-- A category is complete if it has all limits
Limits : {ℓJ ℓJ' ℓC ℓC' : Level} → Category ℓC ℓC' → Type _
Limits {ℓJ} {ℓJ'} C = (J : Category ℓJ ℓJ') → (D : Functor J C) → LimCone D

hasLimits : {ℓJ ℓJ' ℓC ℓC' : Level} → Category ℓC ℓC' → Type _
hasLimits {ℓJ} {ℓJ'} C = (J : Category ℓJ ℓJ') → (D : Functor J C) → ∥ LimCone D ∥

-- Limits of a specific shape J in a category C
LimitsOfShape : {ℓJ ℓJ' ℓC ℓC' : Level} → Category ℓJ ℓJ' → Category ℓC ℓC' → Type _
LimitsOfShape J C = (D : Functor J C) → LimCone D


-- Preservation of limits

module _ {ℓJ ℓJ' ℓC1 ℓC1' ℓC2 ℓC2' : Level}
         {C1 : Category ℓC1 ℓC1'} {C2 : Category ℓC2 ℓC2'}
         (F : Functor C1 C2) where
  open Category
  open Functor
  open Cone

  private
    ℓ = ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓJ ℓJ') ℓC1) ℓC1') ℓC2) ℓC2'

  mapCone : {J : Category ℓJ ℓJ'} (D : Functor J C1) {x : ob C1} (ccx : Cone D x) → Cone (funcComp F D) (F .F-ob x)
  coneOut (mapCone D ccx) v = F .F-hom (coneOut ccx v)
  coneOutCommutes (mapCone D ccx) e =
    sym (F-seq F (coneOut ccx _) (D ⟪ e ⟫)) ∙ cong (F .F-hom) (coneOutCommutes ccx e)

  preservesLimit : {J : Category ℓJ ℓJ'} (D : Functor J C1)
                 → (L : ob C1) → Cone D L → Type ℓ
  preservesLimit D L ccL =
    isLimCone D L ccL → isLimCone (funcComp F D) (F .F-ob L) (mapCone D ccL)

  -- TODO: prove that right adjoints preserve limits
