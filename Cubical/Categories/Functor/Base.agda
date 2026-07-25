module Cubical.Categories.Functor.Base where

open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

record Functor (C : Category ℓC ℓC') (D : Category ℓD ℓD') :
         Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  no-eta-equality

  open Category

  field
    F-ob  : C .ob → D .ob
    F-hom : {x y : C .ob} → C [ x , y ] → D [ F-ob x , F-ob y ]
    F-id  : {x : C .ob} → F-hom (C .id) ≡ D .id {x = F-ob x}
    F-seq : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
          → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) ⋆⟨ D ⟩ (F-hom g)

  isFull = (x y : _) (F[f] : D [ F-ob x , F-ob y ]) → ∃[ f ∈ C [ x , y ] ] F-hom f ≡ F[f]
  isFaithful = (x y : _) (f g : C [ x , y ]) → F-hom f ≡ F-hom g → f ≡ g
  isFullyFaithful = (x y : _) → isEquiv (F-hom {x = x} {y = y})
  isEssentiallySurj = (d : D .ob) → ∃[ c ∈ C .ob ] CatIso D (F-ob c) d

  -- preservation of commuting squares and triangles
  F-square : {x y u v : C .ob}
             {f : C [ x , y ]} {g : C [ x , u ]}
             {h : C [ u , v ]} {k : C [ y , v ]}
           → f ⋆⟨ C ⟩ k ≡ g ⋆⟨ C ⟩ h
           → (F-hom f) ⋆⟨ D ⟩ (F-hom k) ≡ (F-hom g) ⋆⟨ D ⟩ (F-hom h)
  F-square Csquare = sym (F-seq _ _) ∙∙ cong F-hom Csquare ∙∙ F-seq _ _

  F-triangle : {x y z : C .ob}
               {f : C [ x , y ]} {g : C [ y , z ]} {h : C [ x , z ]}
             → f ⋆⟨ C ⟩ g ≡ h
             → (F-hom f) ⋆⟨ D ⟩ (F-hom g) ≡ (F-hom h)
  F-triangle Ctriangle = sym (F-seq _ _) ∙ cong F-hom Ctriangle

private
  variable
    ℓ ℓ' : Level
    B C D E : Category ℓ ℓ'

open Category
open Functor

Functor≡ : {F G : Functor C D}
         → (h : ∀ (c : ob C) → F-ob F c ≡ F-ob G c)
         → (∀ {c c' : ob C} (f : C [ c , c' ]) → PathP (λ i → D [ h c i , h c' i ]) (F-hom F f) (F-hom G f))
         → F ≡ G
F-ob (Functor≡ hOb hHom i) c = hOb c i
F-hom (Functor≡ hOb hHom i) f = hHom f i
F-id (Functor≡ {C = C} {D = D} {F = F} {G = G} hOb hHom i) =
  isProp→PathP (λ j → isSetHom D (hHom (C .id) j) (D .id)) (F-id F) (F-id G) i
F-seq (Functor≡ {C = C} {D = D} {F = F} {G = G} hOb hHom i) f g =
  isProp→PathP (λ j → isSetHom D (hHom (f ⋆⟨ C ⟩ g) j) ((hHom f j) ⋆⟨ D ⟩ (hHom g j))) (F-seq F f g) (F-seq G f g) i

FunctorSquare :
  {F₀₀ F₀₁ F₁₀ F₁₁ : Functor C D}
  (F₀₋ : F₀₀ ≡ F₀₁) (F₁₋ : F₁₀ ≡ F₁₁)
  (F₋₀ : F₀₀ ≡ F₁₀) (F₋₁ : F₀₁ ≡ F₁₁)
  → Square (cong F-ob F₀₋) (cong F-ob F₁₋) (cong F-ob F₋₀) (cong F-ob F₋₁)
  → Square F₀₋ F₁₋ F₋₀ F₋₁
FunctorSquare {C = C} {D = D} F₀₋ F₁₋ F₋₀ F₋₁ r = sqr
  where
  sqr : _
  sqr i j .F-ob = r i j
  sqr i j .F-hom {x = x} {y = y} f =
    isSet→SquareP (λ i j → D .isSetHom {x = sqr i j .F-ob x} {y = sqr i j .F-ob y})
    (λ i → F₀₋ i .F-hom f) (λ i → F₁₋ i .F-hom f) (λ i → F₋₀ i .F-hom f) (λ i → F₋₁ i .F-hom f) i j
  sqr i j .F-id {x = x} =
    isSet→SquareP (λ i j → isProp→isSet (D .isSetHom (sqr i j .F-hom (C .id)) (D .id)))
    (λ i → F₀₋ i .F-id) (λ i → F₁₋ i .F-id) (λ i → F₋₀ i .F-id) (λ i → F₋₁ i .F-id) i j
  sqr i j .F-seq f g =
    isSet→SquareP (λ i j →
      isProp→isSet (D .isSetHom (sqr i j .F-hom (f ⋆⟨ C ⟩ g)) ((sqr i j .F-hom f) ⋆⟨ D ⟩ (sqr i j .F-hom g))))
    (λ i → F₀₋ i .F-seq f g) (λ i → F₁₋ i .F-seq f g) (λ i → F₋₀ i .F-seq f g) (λ i → F₋₁ i .F-seq f g) i j

FunctorPath≡ : {F G : Functor C D}{p q : F ≡ G} → cong F-ob p ≡ cong F-ob q → p ≡ q
FunctorPath≡ {p = p} {q = q} = FunctorSquare p q refl refl


-- Helpful notation

-- action on objects
infix 30 _⟅_⟆
_⟅_⟆ : (F : Functor C D)
     → C .ob
     → D .ob
_⟅_⟆ = F-ob

-- action on morphisms
infix 30 _⟪_⟫ -- same infix level as on objects since these will never be used in the same context
_⟪_⟫ : (F : Functor C D)
     → ∀ {x y}
     → C [ x , y ]
     → D [(F ⟅ x ⟆) , (F ⟅ y ⟆)]
_⟪_⟫ = F-hom


-- Functor constructions

𝟙⟨_⟩ : ∀ (C : Category ℓ ℓ') → Functor C C
𝟙⟨ C ⟩ .F-ob x    = x
𝟙⟨ C ⟩ .F-hom f   = f
𝟙⟨ C ⟩ .F-id      = refl
𝟙⟨ C ⟩ .F-seq _ _ = refl

Id : {C : Category ℓ ℓ'} → Functor C C
Id = 𝟙⟨ _ ⟩

-- functor composition
funcComp : ∀ (G : Functor D E) (F : Functor C D) → Functor C E
(funcComp G F) .F-ob c    = G ⟅ F ⟅ c ⟆ ⟆
(funcComp G F) .F-hom f   = G ⟪ F ⟪ f ⟫ ⟫
(funcComp G F) .F-id      = cong (G ⟪_⟫) (F .F-id) ∙ G .F-id
(funcComp G F) .F-seq f g = cong (G ⟪_⟫) (F .F-seq _ _) ∙ G .F-seq _ _

infixr 30 _∘F_
_∘F_ : Functor D E → Functor C D → Functor C E
_∘F_ = funcComp

-- hacky lemma to stop Agda from computing too much
funcCompOb≡ : ∀ (G : Functor D E) (F : Functor C D) (c : ob C)
            → funcComp G F .F-ob c ≡ G .F-ob (F .F-ob c)
funcCompOb≡ G F c = refl

-- TODO: move all of this to Constructions.Opposite?
introOp : Functor (C ^op) D → Functor C (D ^op)
introOp F .F-ob = F .F-ob
introOp F .F-hom = F .F-hom
introOp F .F-id = F .F-id
introOp F .F-seq f g = F .F-seq g f

recOp : Functor C (D ^op) → Functor (C ^op) D
recOp F .F-ob = F .F-ob
recOp F .F-hom = F .F-hom
recOp F .F-id = F .F-id
recOp F .F-seq f g = F .F-seq g f

toOpOp : Functor C ((C ^op) ^op)
toOpOp = introOp Id

fromOpOp : Functor ((C ^op) ^op) C
fromOpOp = recOp Id

_^opF  : Functor C D → Functor (C ^op) (D ^op)
F ^opF = recOp (toOpOp ∘F F)

_^opF⁻ : Functor (C ^op) (D ^op) → Functor C D
F ^opF⁻ = fromOpOp ∘F introOp F

open Iso
Iso^opF : Iso (Functor C D) (Functor (C ^op) (D ^op))
Iso^opF .fun = _^opF
Iso^opF .inv = _^opF⁻
Iso^opF .sec F = Functor≡ (λ _ → refl) (λ _ → refl)
Iso^opF .ret F = Functor≡ (λ _ → refl) (λ _ → refl)

^opFEquiv : Functor C D ≃ Functor (C ^op) (D ^op)
^opFEquiv = isoToEquiv Iso^opF
