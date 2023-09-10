-- Limits.
-- Heavily inspired by https://github.com/UniMath/UniMath/blob/master/UniMath/CategoryTheory/limits/graphs/limits.v
-- (except we're using categories instead of graphs to index limits)

{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Limits.Initial

open import Cubical.HITs.PropositionalTruncation.Base

module _ {ℓJ ℓJ' ℓC ℓC' : Level} {J : Category ℓJ ℓJ'} {C : Category ℓC ℓC'} where
  open Category
  open Functor
  open NatTrans

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

  -- dependent versions
  conePathP : {D₁ D₂ : Functor J C} {c₁ c₂ : ob C} {cc₁ : Cone D₁ c₁} {cc₂ : Cone D₂ c₂}
              {p : D₁ ≡ D₂} {q : c₁ ≡ c₂}
            → (∀ v → PathP (λ i → C [ q i , p i .F-ob v ]) (cc₁ .coneOut v) (cc₂ .coneOut v))
            → PathP (λ i → Cone (p i) (q i)) cc₁ cc₂
  coneOut (conePathP coneOutPathP i) v = coneOutPathP v i
  coneOutCommutes (conePathP {cc₁ = cc₁} {cc₂ = cc₂} {p = p} coneOutPathP i) {u} {v} e =
    isProp→PathP (λ j → isSetHom C (coneOutPathP u j ⋆⟨ C ⟩ p j .F-hom e)
                                   (coneOutPathP v j))
                 (coneOutCommutes cc₁ e) (coneOutCommutes cc₂ e) i

  conePathPOb : {D : Functor J C} {c c' : ob C} {c1 : Cone D c} {c2 : Cone D c'} {p : c ≡ c'}
            → (∀ (v : ob J) → PathP (λ i → C [ p i , F-ob D v ]) (coneOut c1 v) (coneOut c2 v))
            → PathP (λ i → Cone D (p i)) c1 c2
  conePathPOb coneOutPathP = conePathP {p = refl} coneOutPathP

  conePathPDiag : {D₁ D₂ : Functor J C} {c : ob C} {cc₁ : Cone D₁ c} {cc₂ : Cone D₂ c} {p : D₁ ≡ D₂}
                → (∀ v → PathP (λ i → C [ c , p i .F-ob v ]) (cc₁ .coneOut v) (cc₂ .coneOut v))
                → PathP (λ i → Cone (p i) c) cc₁ cc₂
  conePathPDiag coneOutPathP = conePathP {q = refl} coneOutPathP


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

  preCompCone : {c1 c2 : ob C} (f : C [ c1 , c2 ]) {D : Functor J C}
              → Cone D c2 → Cone D c1
  coneOut (preCompCone f cc) v = f ⋆⟨ C ⟩ coneOut cc v
  coneOutCommutes (preCompCone f cc) e = ⋆Assoc C _ _ _
                                       ∙ cong (λ x → f ⋆⟨ C ⟩ x) (coneOutCommutes cc e)

  _★_ : {c1 c2 : ob C} (f : C [ c1 , c2 ]) {D : Functor J C} → Cone D c2 → Cone D c1
  _★_ = preCompCone

  natTransPostCompCone : {c : ob C} {D₁ D₂ : Functor J C} (α : NatTrans D₁ D₂)
                       → Cone D₁ c → Cone D₂ c
  coneOut (natTransPostCompCone α cc) u = cc .coneOut u ⋆⟨ C ⟩ α .N-ob u
  coneOutCommutes (natTransPostCompCone {D₁ = D₁} {D₂ = D₂} α cc) {u = u} {v = v}  e =
      cc .coneOut u ⋆⟨ C ⟩ α .N-ob u ⋆⟨ C ⟩ D₂ .F-hom e
    ≡⟨ ⋆Assoc C _ _ _ ⟩
      cc .coneOut u ⋆⟨ C ⟩ (α .N-ob u ⋆⟨ C ⟩ D₂ .F-hom e)
    ≡⟨ cong (λ x → cc .coneOut u ⋆⟨ C ⟩ x) (sym (α .N-hom e)) ⟩
      cc .coneOut u ⋆⟨ C ⟩ (D₁ .F-hom e ⋆⟨ C ⟩ α .N-ob v)
    ≡⟨ sym (⋆Assoc C _ _ _) ⟩
      cc .coneOut u ⋆⟨ C ⟩ D₁ .F-hom e ⋆⟨ C ⟩ α .N-ob v
    ≡⟨ cong (λ x → x ⋆⟨ C ⟩ α .N-ob v) (cc .coneOutCommutes e) ⟩
      cc .coneOut v ⋆⟨ C ⟩ α .N-ob v ∎

  _★ₙₜ_ : {c : ob C} {D₁ D₂ : Functor J C} → Cone D₁ c → NatTrans D₁ D₂ → Cone D₂ c
  _★ₙₜ_ = flip natTransPostCompCone

  isConeMor : {c1 c2 : ob C} {D : Functor J C}
              (cc1 : Cone D c1) (cc2 : Cone D c2)
            → C [ c1 , c2 ] → Type (ℓ-max ℓJ ℓC')
  isConeMor cc1 cc2 f = (v : ob J) → f ⋆⟨ C ⟩ coneOut cc2 v ≡ coneOut cc1 v

  isPropIsConeMor : {c1 c2 : ob C} {D : Functor J C}
                    (cc1 : Cone D c1) (cc2 : Cone D c2) (f : C [ c1 , c2 ])
                  → isProp (isConeMor cc1 cc2 f)
  isPropIsConeMor cc1 cc2 f = isPropΠ (λ _ → isSetHom C _ _)

  isConeMorId : {c : ob C} {D : Functor J C} (cc : Cone D c)
              → isConeMor cc cc (id C)
  isConeMorId _ _ = ⋆IdL C _

  isConeMorSeq : {c1 c2 c3 : ob C} {D : Functor J C}
                 (cc1 : Cone D c1) (cc2 : Cone D c2) (cc3  : Cone D c3)
                 {f : C [ c1 , c2 ]} {g : C [ c2 , c3 ]}
               → isConeMor cc1 cc2 f → isConeMor cc2 cc3 g → isConeMor cc1 cc3 (f ⋆⟨ C ⟩ g)
  isConeMorSeq cc1 cc2 cc3 {f} {g} isConeMorF isConeMorG v =
    ⋆Assoc C _ _ _ ∙∙ cong (λ x → f ⋆⟨ C ⟩ x) (isConeMorG v) ∙∙ isConeMorF v

  preCompConeMor : {c1 c2 : ob C} (f : C [ c1 , c2 ]) {D : Functor J C} (cc : Cone D c2)
                 → isConeMor (f ★ cc) cc f
  preCompConeMor f cc v = refl

  isLimCone : (D : Functor J C) (c0 : ob C) → Cone D c0 → Type ℓ
  isLimCone D c0 cc0 = (c : ob C) → (cc : Cone D c)
                     → ∃![ f ∈ C [ c , c0 ] ] isConeMor cc cc0 f

  isPropIsLimCone : (D : Functor J C) (c0 : ob C) (cc0 : Cone D c0)
                  → isProp (isLimCone D c0 cc0)
  isPropIsLimCone D c0 cc0 = isPropΠ2 λ _ _ → isProp∃!

  preCompUnique : {c1 c2 : ob C} (f : C [ c1 , c2 ]) {D : Functor J C} (cc : Cone D c2)
                → isLimCone D c2 cc
                → ∀ (g : C [ c1 , c2 ]) → isConeMor (f ★ cc) cc g → g ≡ f
  preCompUnique f cc ccIsLimCone g gIsConeMor =
     cong fst (isContr→isProp (ccIsLimCone _ (f ★ cc)) (g , gIsConeMor) (f , preCompConeMor f cc))

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
  limOfArrowsCone : {D₁ D₂ : Functor J C}
                    (CC₁ : LimCone D₁)
                  → NatTrans D₁ D₂
                  → Cone D₂ (CC₁ .lim)
  coneOut (limOfArrowsCone {D₁} {D₂} CC₁ α) v = limOut CC₁ v ⋆⟨ C ⟩ α .N-ob v
  coneOutCommutes (limOfArrowsCone {D₁} {D₂} CC₁ α) {u = u} {v = v} e =
     limOut CC₁ u ⋆⟨ C ⟩ α .N-ob u ⋆⟨ C ⟩ D₂ .F-hom e   ≡⟨ ⋆Assoc C _ _ _ ⟩
     limOut CC₁ u ⋆⟨ C ⟩ (α .N-ob u ⋆⟨ C ⟩ D₂ .F-hom e) ≡⟨ cong (λ x → seq' C (limOut CC₁ u) x) (sym (α .N-hom e)) ⟩
     limOut CC₁ u ⋆⟨ C ⟩ (D₁ .F-hom e ⋆⟨ C ⟩ α .N-ob v) ≡⟨ sym (⋆Assoc C _ _ _) ⟩
     limOut CC₁ u ⋆⟨ C ⟩ D₁ .F-hom e ⋆⟨ C ⟩ α .N-ob v   ≡⟨ cong (λ x → x ⋆⟨ C ⟩ α .N-ob v) (limOutCommutes CC₁ e) ⟩
     limOut CC₁ v ⋆⟨ C ⟩ α .N-ob v ∎

  limOfArrows : {D₁ D₂ : Functor J C}
                (CC₁ : LimCone D₁) (CC₂ : LimCone D₂)
              → NatTrans D₁ D₂
              → C [ CC₁ .lim , CC₂ .lim ]
  limOfArrows {D₁} {D₂} CC₁ CC₂ α = limArrow CC₂ (CC₁ .lim) (limOfArrowsCone CC₁ α)

  limOfArrowsOut : {D₁ D₂ : Functor J C}
                   (CC₁ : LimCone D₁) (CC₂ : LimCone D₂)
                   (α : NatTrans D₁ D₂) (u : ob J)
                 → limOfArrows CC₁ CC₂ α ⋆⟨ C ⟩ limOut CC₂ u ≡ limOut CC₁ u ⋆⟨ C ⟩ α .N-ob u
  limOfArrowsOut _ CC₂ _ _ = limArrowCommutes CC₂ _ _ _

  limOfArrowsId : {D : Functor J C} (CC : LimCone D)
                → limOfArrows CC CC (idTrans D) ≡ id C
  limOfArrowsId CC = limArrowUnique CC _ _ _ λ v → ⋆IdL C _ ∙ sym (⋆IdR C _)

  limOfArrowsSeq : {D₁ D₂ D₃ : Functor J C}
                   (CC₁ : LimCone D₁) (CC₂ : LimCone D₂) (CC₃ : LimCone D₃)
                   (α : NatTrans D₁ D₂) (β : NatTrans D₂ D₃)
                 → limOfArrows CC₁ CC₃ (α ●ᵛ β)
                 ≡ limOfArrows CC₁ CC₂ α ⋆⟨ C ⟩ limOfArrows CC₂ CC₃ β
  limOfArrowsSeq CC₁ CC₂ CC₃ α β = limArrowUnique CC₃ _ _ _ path
    where
    path : ∀ u
         → (limOfArrows CC₁ CC₂ α ⋆⟨ C ⟩ limOfArrows CC₂ CC₃ β) ⋆⟨ C ⟩ limOut CC₃ u
         ≡ limOut CC₁ u ⋆⟨ C ⟩ (α .N-ob u ⋆⟨ C ⟩ β .N-ob u)
    path u = (limOfArrows CC₁ CC₂ α ⋆⟨ C ⟩ limOfArrows CC₂ CC₃ β) ⋆⟨ C ⟩ limOut CC₃ u
           ≡⟨ ⋆Assoc C _ _ _ ⟩
             limOfArrows CC₁ CC₂ α ⋆⟨ C ⟩ (limOfArrows CC₂ CC₃ β ⋆⟨ C ⟩ limOut CC₃ u)
           ≡⟨ cong (λ x → limOfArrows CC₁ CC₂ α ⋆⟨ C ⟩ x) (limOfArrowsOut CC₂ CC₃ β u) ⟩
             limOfArrows CC₁ CC₂ α ⋆⟨ C ⟩ (limOut CC₂ u ⋆⟨ C ⟩ β .N-ob u)
           ≡⟨ sym (⋆Assoc C _ _ _) ⟩
             (limOfArrows CC₁ CC₂ α ⋆⟨ C ⟩ limOut CC₂ u) ⋆⟨ C ⟩ β .N-ob u
           ≡⟨ cong (λ x → x ⋆⟨ C ⟩ β .N-ob u) (limOfArrowsOut CC₁ CC₂ α u) ⟩
             (limOut CC₁ u ⋆⟨ C ⟩ α .N-ob u) ⋆⟨ C ⟩ β .N-ob u
           ≡⟨ ⋆Assoc C _ _ _ ⟩
             limOut CC₁ u ⋆⟨ C ⟩ (α .N-ob u ⋆⟨ C ⟩ β .N-ob u) ∎

  limArrowCompLimOfArrows : {D₁ D₂ : Functor J C}
                            (CC₁ : LimCone D₁) (CC₂ : LimCone D₂)
                            (α : NatTrans D₁ D₂)
                            (c : ob C) (cc : Cone D₁ c)
    → limArrow CC₂ _ (cc ★ₙₜ α) ≡ limArrow CC₁ _ cc ⋆⟨ C ⟩ limOfArrows CC₁ CC₂ α
  limArrowCompLimOfArrows CC₁ CC₂ α c cc = limArrowUnique CC₂ _ _ _ isConeMorComp
    where
    isConeMorComp : ∀ (u : ob J)
                  → limArrow CC₁ _ cc ⋆⟨ C ⟩ limOfArrows CC₁ CC₂ α ⋆⟨ C ⟩ limOut CC₂ u
                  ≡ cc .coneOut u ⋆⟨ C ⟩ α .N-ob u
    isConeMorComp u =
        limArrow CC₁ _ cc ⋆⟨ C ⟩ limOfArrows CC₁ CC₂ α ⋆⟨ C ⟩ limOut CC₂ u
      ≡⟨ ⋆Assoc C _ _ _ ⟩
        limArrow CC₁ _ cc ⋆⟨ C ⟩ (limOfArrows CC₁ CC₂ α ⋆⟨ C ⟩ limOut CC₂ u)
      ≡⟨ cong (λ x → limArrow CC₁ _ cc ⋆⟨ C ⟩ x) (limOfArrowsOut CC₁ CC₂ α u) ⟩
        limArrow CC₁ _ cc ⋆⟨ C ⟩ (limOut CC₁ u ⋆⟨ C ⟩ α .N-ob u)
      ≡⟨ sym (⋆Assoc C _ _ _) ⟩
        limArrow CC₁ _ cc ⋆⟨ C ⟩ limOut CC₁ u ⋆⟨ C ⟩ α .N-ob u
      ≡⟨ cong (λ x → x ⋆⟨ C ⟩ α .N-ob u) (limArrowCommutes CC₁ _ cc u) ⟩
        cc .coneOut u ⋆⟨ C ⟩ α .N-ob u ∎

  -- any two limits are isomorphic up to a unique cone isomorphism
  open isIso
  LimIso : (D : Functor J C) (L₁ L₂ : LimCone D)
         → ∃![ e ∈ CatIso C (lim L₁) (lim L₂) ] isConeMor (limCone L₁) (limCone L₂) (fst e)
  fst (fst (fst (LimIso D L₁ L₂))) = limArrow L₂ _ (limCone L₁)
  inv (snd (fst (fst (LimIso D L₁ L₂)))) = limArrow L₁ _ (limCone L₂)
  sec (snd (fst (fst (LimIso D L₁ L₂)))) = cong fst (isContr→isProp (univProp L₂ _ (limCone L₂))
                                            (_ , isConeMorComp) (id C , isConeMorId (limCone L₂)))
    where
    isConeMorComp : isConeMor (limCone L₂) (limCone L₂)
                      (limArrow L₁ (lim L₂) (limCone L₂) ⋆⟨ C ⟩ limArrow L₂ (lim L₁) (limCone L₁))
    isConeMorComp v =
        (limArrow L₁ (lim L₂) (limCone L₂) ⋆⟨ C ⟩ limArrow L₂ (lim L₁) (limCone L₁))
                                          ⋆⟨ C ⟩ coneOut (limCone L₂) v
      ≡⟨ ⋆Assoc C _ _ _ ⟩
        limArrow L₁ (lim L₂) (limCone L₂)
          ⋆⟨ C ⟩ (limArrow L₂ (lim L₁) (limCone L₁) ⋆⟨ C ⟩ coneOut (limCone L₂) v)
      ≡⟨ cong (λ x → limArrow L₁ (lim L₂) (limCone L₂) ⋆⟨ C ⟩ x)
              (limArrowCommutes L₂ _ (limCone L₁) v) ⟩
        limArrow L₁ (lim L₂) (limCone L₂)
          ⋆⟨ C ⟩ (coneOut (limCone L₁) v)
      ≡⟨ limArrowCommutes L₁ _ (limCone L₂) v ⟩
        coneOut (limCone L₂) v ∎
  ret (snd (fst (fst (LimIso D L₁ L₂)))) = cong fst (isContr→isProp (univProp L₁ _ (limCone L₁))
                                            (_ , isConeMorComp) (id C , isConeMorId (limCone L₁)))
    where
    isConeMorComp : isConeMor (limCone L₁) (limCone L₁)
                      (limArrow L₂ (lim L₁) (limCone L₁) ⋆⟨ C ⟩ limArrow L₁ (lim L₂) (limCone L₂))
    isConeMorComp v =
        (limArrow L₂ (lim L₁) (limCone L₁) ⋆⟨ C ⟩ limArrow L₁ (lim L₂) (limCone L₂))
                                          ⋆⟨ C ⟩ coneOut (limCone L₁) v
      ≡⟨ ⋆Assoc C _ _ _ ⟩
        limArrow L₂ (lim L₁) (limCone L₁)
          ⋆⟨ C ⟩ (limArrow L₁ (lim L₂) (limCone L₂) ⋆⟨ C ⟩ coneOut (limCone L₁) v)
      ≡⟨ cong (λ x → limArrow L₂ (lim L₁) (limCone L₁) ⋆⟨ C ⟩ x)
              (limArrowCommutes L₁ _ (limCone L₂) v) ⟩
        limArrow L₂ (lim L₁) (limCone L₁)
          ⋆⟨ C ⟩ (coneOut (limCone L₂) v)
      ≡⟨ limArrowCommutes L₂ _ (limCone L₁) v ⟩
        coneOut (limCone L₁) v ∎

  snd (fst (LimIso D L₁ L₂)) = limArrowCommutes L₂ _ _
  snd (LimIso D L₁ L₂) (e , isConeMorE) = Σ≡Prop
      (λ _ → isPropIsConeMor (limCone L₁) (limCone L₂) _)
      (CatIso≡ _ _ (limArrowUnique L₂ _ _ (fst e) isConeMorE))

  -- if the index category of the diagram has an initial object,
  -- we get a canonical limiting cone
  Initial→LimCone : (D : Functor J C) → Initial J → LimCone D
  lim (Initial→LimCone D (j , isInitJ)) = D .F-ob j
  coneOut (limCone (Initial→LimCone D (j , isInitJ))) k = D .F-hom (isInitJ k .fst)
  coneOutCommutes (limCone (Initial→LimCone D (j , isInitJ))) f =
                      sym (D .F-seq _ _) ∙ cong (D .F-hom) (sym (isInitJ _ .snd _))
  fst (fst (univProp (Initial→LimCone D (j , isInitJ)) c cc)) = cc .coneOut j
                                                                -- canonical arrow c → D(j)
  snd (fst (univProp (Initial→LimCone D (j , isInitJ)) c cc)) k =
                                                         cc .coneOutCommutes (isInitJ k .fst)
                                                         -- is a cone morphism
  snd (univProp (Initial→LimCone D (j , isInitJ)) c cc) (f , isConeMorF) = -- and indeed unique
    Σ≡Prop
      (λ _ → isPropIsConeMor cc (limCone (Initial→LimCone D (j , isInitJ))) _)
        (sym (isConeMorF j) ∙∙ cong (λ x → f ⋆⟨ C ⟩ x) (subst (λ x → D .F-hom x ≡ id C)
                                                              (sym (isInitJ j .snd _)) (D .F-id))
                            ∙∙ ⋆IdR C f)

  -- cones that respect isomorphisms are limiting cones
  Iso→LimCone : {D : Functor J C} {c₁ c₂ : ob C} (cc₁ : Cone D c₁) (e : CatIso C c₁ c₂)
              → isLimCone _ _ cc₁
              → (cc₂ : Cone D c₂)
              → isConeMor cc₁ cc₂ (e .fst)
              → isLimCone _ _ cc₂
  fst (fst (Iso→LimCone cc₁ e isLimConeCC₁ cc₂ isConeMorE d cd)) =
    isLimConeCC₁ d cd .fst .fst ⋆⟨ C ⟩ e .fst
  snd (fst (Iso→LimCone cc₁ e isLimConeCC₁ cc₂ isConeMorE d cd)) =
    isConeMorSeq cd cc₁ cc₂ (isLimConeCC₁ d cd .fst .snd) isConeMorE
  snd (Iso→LimCone cc₁ e isLimConeCC₁ cc₂ isConeMorE d cd) (f , isConeMorF) =
    Σ≡Prop (isPropIsConeMor cd cc₂) path
    where
    isConeMorE⁻¹ : isConeMor cc₂ cc₁ (e .snd .inv)
    isConeMorE⁻¹ v =
      e .snd .inv ⋆⟨ C ⟩ coneOut cc₁ v ≡⟨ cong (λ x → e .snd .inv ⋆⟨ C ⟩ x) (sym (isConeMorE v)) ⟩
      e .snd .inv ⋆⟨ C ⟩ (e .fst ⋆⟨ C ⟩ coneOut cc₂ v) ≡⟨ sym (⋆Assoc C _ _ _) ⟩
      (e .snd .inv ⋆⟨ C ⟩ e .fst) ⋆⟨ C ⟩ coneOut cc₂ v ≡⟨ cong (λ x → x ⋆⟨ C ⟩ coneOut cc₂ v)
                                                              (e .snd .sec) ⟩
      id C ⋆⟨ C ⟩ coneOut cc₂ v ≡⟨ ⋆IdL C _ ⟩
      coneOut cc₂ v ∎

    p : isLimConeCC₁ d cd .fst .fst ≡ f ⋆⟨ C ⟩ e .snd .inv
    p = cong fst (isLimConeCC₁ d cd .snd ( f ⋆⟨ C ⟩ e .snd .inv
                                         , isConeMorSeq cd cc₂ cc₁ isConeMorF isConeMorE⁻¹))

    path : isLimConeCC₁ d cd .fst .fst ⋆⟨ C ⟩ e .fst ≡ f
    path = isLimConeCC₁ d cd .fst .fst ⋆⟨ C ⟩ e .fst ≡⟨ cong (λ x → x ⋆⟨ C ⟩ e .fst) p ⟩
           (f ⋆⟨ C ⟩ e .snd .inv) ⋆⟨ C ⟩ e .fst ≡⟨ ⋆Assoc C _ _ _ ⟩
           f ⋆⟨ C ⟩ (e .snd .inv ⋆⟨ C ⟩ e .fst) ≡⟨ cong (λ x → f ⋆⟨ C ⟩ x) (e .snd .sec) ⟩
           f ⋆⟨ C ⟩ id C ≡⟨ ⋆IdR C _ ⟩
           f ∎

-- A category is complete if it has all limits
Limits : {ℓJ ℓJ' ℓC ℓC' : Level} → Category ℓC ℓC' → Type _
Limits {ℓJ} {ℓJ'} C = (J : Category ℓJ ℓJ') → (D : Functor J C) → LimCone D

hasLimits : {ℓJ ℓJ' ℓC ℓC' : Level} → Category ℓC ℓC' → Type _
hasLimits {ℓJ} {ℓJ'} C = (J : Category ℓJ ℓJ') → (D : Functor J C) → ∥ LimCone D ∥₁

-- Limits of a specific shape J in a category C
LimitsOfShape : {ℓJ ℓJ' ℓC ℓC' : Level} → Category ℓJ ℓJ' → Category ℓC ℓC' → Type _
LimitsOfShape J C = (D : Functor J C) → LimCone D


-- precomposition with a functor and preservation of limits
module _ {ℓJ ℓJ' ℓC1 ℓC1' ℓC2 ℓC2' : Level}
         {C1 : Category ℓC1 ℓC1'} {C2 : Category ℓC2 ℓC2'}
         (F : Functor C1 C2) where
  open Category
  open Functor
  open Cone

  -- same as F-cone!!!
  F-cone : {J : Category ℓJ ℓJ'} {D : Functor J C1} {x : ob C1}
          → Cone D x → Cone (funcComp F D) (F .F-ob x)
  coneOut (F-cone ccx) v = F .F-hom (coneOut ccx v)
  coneOutCommutes (F-cone ccx) e =
    sym (F-seq F (coneOut ccx _) _) ∙ cong (F .F-hom) (coneOutCommutes ccx e)

  preservesLimits : Type _
  preservesLimits = ∀ {J : Category ℓJ ℓJ'} {D : Functor J C1} {L : ob C1}
                      (ccL : Cone D L)
                  → isLimCone _ _ ccL → isLimCone (funcComp F D) (F .F-ob L) (F-cone ccL)

  -- characterizing limit preserving functors
  open LimCone

  preservesLimitsChar : (L₁ : Limits {ℓJ} {ℓJ'} C1) (L₂ : Limits {ℓJ} {ℓJ'} C2)
     → (e : ∀ J D → CatIso C2 (L₂ J (F ∘F D) .lim) (F .F-ob (L₁ J D .lim)))
     → (∀ J D → isConeMor (L₂ J (F ∘F D) .limCone) (F-cone (L₁ J D .limCone)) (e J D .fst))
     → preservesLimits
  preservesLimitsChar L₁ L₂ e isConeMorE {J = J} {D = D} {L = c} cc isLimConeCC =
    Iso→LimCone (L₂ J (F ∘F D) .limCone) f (L₂ J (F ∘F D) .univProp) (F-cone cc) isConeMorF
    where
    theCLimCone : LimCone D
    lim theCLimCone = c
    limCone theCLimCone = cc
    univProp theCLimCone = isLimConeCC

    f : CatIso C2 (lim (L₂ J (funcComp F D))) (F .F-ob c)
    f = ⋆Iso (e J D) (F-Iso {F = F} (LimIso D (L₁ J D) theCLimCone .fst .fst))

    isConeMorF : isConeMor (L₂ J (funcComp F D) .limCone) (F-cone cc) (f .fst)
    isConeMorF = isConeMorSeq (L₂ J (funcComp F D) .limCone)
                              (F-cone (L₁ J D .limCone))
                              (F-cone cc)
                  (isConeMorE J D)
                  (λ v → F-triangle F (limArrowCommutes theCLimCone _ _ _))

  -- TODO: prove that right adjoints preserve limits
