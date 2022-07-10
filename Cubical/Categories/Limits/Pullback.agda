{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Pullback where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Cospan
open import Cubical.Categories.Limits.Limits

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where

  open Category C
  open Functor

  record Cospan : Type (ℓ-max ℓ ℓ') where
    constructor cospan
    field
      l m r : ob
      s₁ : C [ l , m ]
      s₂ : C [ r , m ]

  open Cospan

  isPullback : (cspn : Cospan) →
    {c : ob} (p₁ : C [ c , cspn .l ]) (p₂ : C [ c , cspn .r ])
    (H : p₁ ⋆ cspn .s₁ ≡ p₂ ⋆ cspn .s₂) → Type (ℓ-max ℓ ℓ')
  isPullback cspn {c} p₁ p₂ H =
    ∀ {d} (h : C [ d , cspn .l ]) (k : C [ d , cspn .r ])
          (H' : h ⋆ cspn .s₁ ≡ k ⋆ cspn .s₂)
    → ∃![ hk ∈ C [ d , c ] ] (h ≡ hk ⋆ p₁) × (k ≡ hk ⋆ p₂)

  isPropIsPullback : (cspn : Cospan) →
    {c : ob} (p₁ : C [ c , cspn .l ]) (p₂ : C [ c , cspn .r ])
    (H : p₁ ⋆ cspn .s₁ ≡ p₂ ⋆ cspn .s₂) → isProp (isPullback cspn p₁ p₂ H)
  isPropIsPullback cspn p₁ p₂ H =
    isPropImplicitΠ (λ x → isPropΠ3 λ h k H' → isPropIsContr)

  record Pullback (cspn : Cospan) : Type (ℓ-max ℓ ℓ') where
    field
      pbOb  : ob
      pbPr₁ : C [ pbOb , cspn .l ]
      pbPr₂ : C [ pbOb , cspn .r ]
      pbCommutes : pbPr₁ ⋆ cspn .s₁ ≡ pbPr₂ ⋆ cspn .s₂
      univProp : isPullback cspn pbPr₁ pbPr₂ pbCommutes

  open Pullback

  pullbackArrow :
    {cspn : Cospan} (pb : Pullback cspn)
    {c : ob} (p₁ : C [ c , cspn .l ]) (p₂ : C [ c , cspn .r ])
    (H : p₁ ⋆ cspn .s₁ ≡ p₂ ⋆ cspn .s₂) → C [ c , pb . pbOb ]
  pullbackArrow pb p₁ p₂ H = pb .univProp p₁ p₂ H .fst .fst

  pullbackArrowPr₁ :
    {cspn : Cospan} (pb : Pullback cspn)
    {c : ob} (p₁ : C [ c , cspn .l ]) (p₂ : C [ c , cspn .r ])
    (H : p₁ ⋆ cspn .s₁ ≡ p₂ ⋆ cspn .s₂) →
    p₁ ≡ pullbackArrow pb p₁ p₂ H ⋆ pbPr₁ pb
  pullbackArrowPr₁ pb p₁ p₂ H = pb .univProp p₁ p₂ H .fst .snd .fst

  pullbackArrowPr₂ :
    {cspn : Cospan} (pb : Pullback cspn)
    {c : ob} (p₁ : C [ c , cspn .l ]) (p₂ : C [ c , cspn .r ])
    (H : p₁ ⋆ cspn .s₁ ≡ p₂ ⋆ cspn .s₂) →
    p₂ ≡ pullbackArrow pb p₁ p₂ H ⋆ pbPr₂ pb
  pullbackArrowPr₂ pb p₁ p₂ H = pb .univProp p₁ p₂ H .fst .snd .snd

  pullbackArrowUnique :
    {cspn : Cospan} (pb : Pullback cspn)
    {c : ob} (p₁ : C [ c , cspn .l ]) (p₂ : C [ c , cspn .r ])
    (H : p₁ ⋆ cspn .s₁ ≡ p₂ ⋆ cspn .s₂)
    (pbArrow' : C [ c , pb .pbOb ])
    (H₁ : p₁ ≡ pbArrow' ⋆ pbPr₁ pb) (H₂ : p₂ ≡ pbArrow' ⋆ pbPr₂ pb)
    → pullbackArrow pb p₁ p₂ H ≡ pbArrow'
  pullbackArrowUnique pb p₁ p₂ H pbArrow' H₁ H₂ =
    cong fst (pb .univProp p₁ p₂ H .snd (pbArrow' , (H₁ , H₂)))

  Pullbacks : Type (ℓ-max ℓ ℓ')
  Pullbacks = (cspn : Cospan) → Pullback cspn

  hasPullbacks : Type (ℓ-max ℓ ℓ')
  hasPullbacks = ∥ Pullbacks ∥₁


-- Pullbacks from limits
module _ {C : Category ℓ ℓ'} where
  open Category C
  open Functor
  open Pullback
  open LimCone
  open Cone
  open Cospan

  Cospan→Func : Cospan C → Functor CospanCat C
  Cospan→Func (cospan l m r f g) .F-ob ⓪ = l
  Cospan→Func (cospan l m r f g) .F-ob ① = m
  Cospan→Func (cospan l m r f g) .F-ob ② = r
  Cospan→Func (cospan l m r f g) .F-hom {⓪} {①} k = f
  Cospan→Func (cospan l m r f g) .F-hom {②} {①} k = g
  Cospan→Func (cospan l m r f g) .F-hom {⓪} {⓪} k = id
  Cospan→Func (cospan l m r f g) .F-hom {①} {①} k = id
  Cospan→Func (cospan l m r f g) .F-hom {②} {②} k = id
  Cospan→Func (cospan l m r f g) .F-id {⓪} = refl
  Cospan→Func (cospan l m r f g) .F-id {①} = refl
  Cospan→Func (cospan l m r f g) .F-id {②} = refl
  Cospan→Func (cospan l m r f g) .F-seq {⓪} {⓪} {⓪} φ ψ = sym (⋆IdL _)
  Cospan→Func (cospan l m r f g) .F-seq {⓪} {⓪} {①} φ ψ = sym (⋆IdL _)
  Cospan→Func (cospan l m r f g) .F-seq {⓪} {①} {①} φ ψ = sym (⋆IdR _)
  Cospan→Func (cospan l m r f g) .F-seq {①} {①} {①} φ ψ = sym (⋆IdL _)
  Cospan→Func (cospan l m r f g) .F-seq {②} {②} {②} φ ψ = sym (⋆IdL _)
  Cospan→Func (cospan l m r f g) .F-seq {②} {②} {①} φ ψ = sym (⋆IdL _)
  Cospan→Func (cospan l m r f g) .F-seq {②} {①} {①} φ ψ = sym (⋆IdR _)

  LimitsOfShapeCospanCat→Pullbacks : LimitsOfShape CospanCat C → Pullbacks C
  pbOb (LimitsOfShapeCospanCat→Pullbacks H cspn) = lim (H (Cospan→Func cspn))
  pbPr₁ (LimitsOfShapeCospanCat→Pullbacks H cspn) = limOut (H (Cospan→Func cspn)) ⓪
  pbPr₂ (LimitsOfShapeCospanCat→Pullbacks H cspn) = limOut (H (Cospan→Func cspn)) ②
  pbCommutes (LimitsOfShapeCospanCat→Pullbacks H cspn) = limOutCommutes (H (Cospan→Func cspn)) {v = ①} tt
                          ∙ sym (limOutCommutes (H (Cospan→Func cspn)) tt)
  univProp (LimitsOfShapeCospanCat→Pullbacks H cspn) {d = d} h k H' =
    uniqueExists (limArrow (H (Cospan→Func cspn)) d cc)
                 ( sym (limArrowCommutes (H (Cospan→Func cspn)) d cc ⓪)
                 , sym (limArrowCommutes (H (Cospan→Func cspn)) d cc ②))
                 (λ _ → isProp× (isSetHom _ _) (isSetHom _ _))
                 λ a' ha' → limArrowUnique (H (Cospan→Func cspn)) d cc a'
                               (λ { ⓪ → sym (ha' .fst)
                                  ; ① → cong (a' ⋆_) (sym (limOutCommutes (H (Cospan→Func cspn)) {⓪} {①} tt))
                                      ∙∙ sym (⋆Assoc _ _ _)
                                      ∙∙ cong (_⋆ cspn .s₁) (sym (ha' .fst))
                                  ; ② → sym (ha' .snd) })
    where
    cc : Cone (Cospan→Func cspn) d
    coneOut cc ⓪ = h
    coneOut cc ① = h ⋆ cspn .s₁
    coneOut cc ② = k
    coneOutCommutes cc {⓪} {⓪} e = ⋆IdR h
    coneOutCommutes cc {⓪} {①} e = refl
    coneOutCommutes cc {①} {①} e = ⋆IdR _
    coneOutCommutes cc {②} {①} e = sym H'
    coneOutCommutes cc {②} {②} e = ⋆IdR k

  Limits→Pullbacks : Limits C → Pullbacks C
  Limits→Pullbacks H = LimitsOfShapeCospanCat→Pullbacks (H CospanCat)
