{-# OPTIONS --safe #-}

module Cubical.Categories.Adjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open Functor

open Iso
open Category

{-
==============================================
                  Overview
==============================================

This module contains two definitions for adjoint
functors, and functions witnessing their
logical (and maybe eventually actual?)
equivalence.
-}

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level

{-
==============================================
             Adjoint definitions
==============================================

We provide two alternative definitions for
adjoint functors: the unit-counit
definition, followed by the natural bijection
definition.
-}

module UnitCounit where

  -- Adjoint def 1: unit-counit
  record _⊣_ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) (G : Functor D C)
                  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    field
      -- unit
      η : 𝟙⟨ C ⟩ ⇒ (funcComp G F)
      -- counit
      ε : (funcComp F G) ⇒ 𝟙⟨ D ⟩
      -- triangle identities
      Δ₁ : PathP (λ i → NatTrans (F-lUnit {F = F} i) (F-rUnit {F = F} i))
        (seqTransP F-assoc (F ∘ʳ η) (ε ∘ˡ F))
        (1[ F ])
      Δ₂ : PathP (λ i → NatTrans (F-rUnit {F = G} i) (F-lUnit {F = G} i))
        (seqTransP (sym F-assoc) (η ∘ˡ G) (G ∘ʳ ε))
        (1[ G ])

  {-
   Helper function for building unit-counit adjunctions between categories,
   using that equality of natural transformations in a category is equality on objects
  -}

  module _ {ℓC ℓC' ℓD ℓD'}
    {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F : Functor C D} {G : Functor D C}
    (η : 𝟙⟨ C ⟩ ⇒ (funcComp G F))
    (ε : (funcComp F G) ⇒ 𝟙⟨ D ⟩)
    (Δ₁ : ∀ c → F ⟪ η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ ε ⟦ F ⟅ c ⟆ ⟧ ≡ D .id)
    (Δ₂ : ∀ d → η ⟦ G ⟅ d ⟆ ⟧ ⋆⟨ C ⟩ G ⟪ ε ⟦ d ⟧ ⟫ ≡ C .id)
    where

    make⊣ : F ⊣ G
    make⊣ ._⊣_.η = η
    make⊣ ._⊣_.ε = ε
    make⊣ ._⊣_.Δ₁ =
      makeNatTransPathP F-lUnit F-rUnit
        (funExt λ c → cong (D ._⋆_ (F ⟪ η ⟦ c ⟧ ⟫)) (transportRefl _) ∙ Δ₁ c)
    make⊣ ._⊣_.Δ₂ =
      makeNatTransPathP F-rUnit F-lUnit
        (funExt λ d → cong (C ._⋆_ (η ⟦ G ⟅ d ⟆ ⟧)) (transportRefl _) ∙ Δ₂ d)

module NaturalBijection where

  -- definitions
  module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where

    {-
      Here, we define adjunctions in terms of more general concepts:
      - Relative adjunctions (see e.g. the nLab)
      - Adhoc adjunctions: Sometimes a functor F does not have a right adjoint functor G defined on all objects, but for a
        specific object d, there may be an object gd that behaves as the image of d under the right adjoint to F.
        Examples are:
        - the local right Kan extension (when the global Kan extension does not exist)
        - a limit of a specific diagram (when not all diagrams of the same shape may have a limit).
    -}

    -- Adhoc adjunction (quite useless in itself)
    -- Note that the arrow direction is arbitrary.
    [_↦_]⊣[_↦_] : ob C → ob D → ob D → ob C → Type (ℓ-max ℓC' ℓD')
    [ c ↦ fc ]⊣[ d ↦ gd ] = Iso (D [ fc , d ]) (C [ c , gd ])
    -- Idea: We could generalize further by having a profunctor (instead of just Hom) on both sides of the iso.
    -- This way, an isomorphism with the cone profunctor could be used to define limits.

    -- Left-relative right-adhoc adjunction
    -- Note that the arrow direction is arbitrary.
    module _ {B : Category ℓB ℓB'} (I : Functor B C) (F : Functor B D) (d : ob D) (gd : ob C) where
      module _ (α : ∀ b → [ I ⟅ b ⟆ ↦ F ⟅ b ⟆ ]⊣[ d ↦ gd ]) where

        FunNatL : Type (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓC' ℓD'))
        FunNatL = ∀ {b1 b2} → (β : B [ b1 , b2 ]) → (φ : D [ F ⟅ b2 ⟆ , d ])
          → α b1 .fun (F ⟪ β ⟫ ⋆⟨ D ⟩ φ) ≡ I ⟪ β ⟫ ⋆⟨ C ⟩ α b2 .fun φ
        InvNatL : Type (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓC' ℓD'))
        InvNatL = ∀ {b1 b2} → (β : B [ b1 , b2 ]) → (ψ : C [ I ⟅ b2 ⟆ , gd ])
          → α b1 .inv (I ⟪ β ⟫ ⋆⟨ C ⟩ ψ) ≡ F ⟪ β ⟫ ⋆⟨ D ⟩ α b2 .inv ψ

        FunNatL→InvNatL : FunNatL → InvNatL
        FunNatL→InvNatL funNatL {b1} {b2} β ψ =
          α b1 .inv (I ⟪ β ⟫ ⋆⟨ C ⟩ ψ)
            ≡⟨ cong (α b1 .inv) (cong (λ ψ' → I ⟪ β ⟫ ⋆⟨ C ⟩ ψ') (sym (α b2 .rightInv ψ))) ⟩
          α b1 .inv (I ⟪ β ⟫ ⋆⟨ C ⟩ α b2 .fun (α b2 .inv ψ))
            ≡⟨ cong (α b1 .inv) (sym (funNatL β (α b2 .inv ψ))) ⟩
          α b1 .inv (α b1 .fun (F ⟪ β ⟫ ⋆⟨ D ⟩ (α b2 .inv ψ)))
            ≡⟨ α b1 .leftInv _ ⟩
          F ⟪ β ⟫ ⋆⟨ D ⟩ α b2 .inv ψ ∎

        InvNatL→FunNatL : InvNatL → FunNatL
        InvNatL→FunNatL invNatL {b1} {b2} β φ =
          α b1 .fun (F ⟪ β ⟫ ⋆⟨ D ⟩ φ)
            ≡⟨ cong (α b1 .fun) (cong (λ φ' → F ⟪ β ⟫ ⋆⟨ D ⟩ φ') (sym (α b2 .leftInv φ))) ⟩
          α b1 .fun (F ⟪ β ⟫ ⋆⟨ D ⟩ α b2 .inv (α b2 .fun φ))
            ≡⟨ cong (α b1 .fun) (sym (invNatL β (α b2 .fun φ))) ⟩
          α b1 .fun (α b1 .inv (I ⟪ β ⟫ ⋆⟨ C ⟩ (α b2 .fun φ)))
            ≡⟨ α b1 .rightInv _ ⟩
          I ⟪ β ⟫ ⋆⟨ C ⟩ α b2 .fun φ ∎

        record isLeftRelativeRightAdhocAdjunction : Type (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓC' ℓD')) where

          field
            funNatL : FunNatL -- was adjNatInC'
            invNatL : InvNatL -- was adjNatInC

        open isLeftRelativeRightAdhocAdjunction

        FunNatL→isLeftRelativeRightAdhocAdjunction : FunNatL → isLeftRelativeRightAdhocAdjunction
        funNatL (FunNatL→isLeftRelativeRightAdhocAdjunction funNatL') = funNatL'
        invNatL (FunNatL→isLeftRelativeRightAdhocAdjunction funNatL') = FunNatL→InvNatL funNatL'

        InvNatL→isLeftRelativeRightAdhocAdjunction : InvNatL → isLeftRelativeRightAdhocAdjunction
        funNatL (InvNatL→isLeftRelativeRightAdhocAdjunction invNatL') = InvNatL→FunNatL invNatL'
        invNatL (InvNatL→isLeftRelativeRightAdhocAdjunction invNatL') = invNatL'

      [_⇒_]⊣[_↦_] : Type (ℓ-max (ℓ-max (ℓ-max ℓC' ℓD') ℓB) ℓB')
      [_⇒_]⊣[_↦_] = Σ[ α ∈ _ ] isLeftRelativeRightAdhocAdjunction α

    -- Right-adhoc adjunction
    module _ (F : Functor C D) (d : ob D) (gd : ob C) where
      module _ (α : ∀ c → [ c ↦ F ⟅ c ⟆ ]⊣[ d ↦ gd ]) where
        isRightAdhocAdjunction : Type (ℓ-max (ℓ-max ℓC ℓC') ℓD')
        isRightAdhocAdjunction = isLeftRelativeRightAdhocAdjunction Id F d gd α

        module isRightAdhocAdjunction = isLeftRelativeRightAdhocAdjunction

        open isRightAdhocAdjunction

        FunNatL→isRightAdhocAdjunction : FunNatL Id F d gd α → isRightAdhocAdjunction
        FunNatL→isRightAdhocAdjunction = FunNatL→isLeftRelativeRightAdhocAdjunction Id F d gd α

        InvNatL→isRightAdhocAdjunction : InvNatL Id F d gd α → isRightAdhocAdjunction
        InvNatL→isRightAdhocAdjunction = InvNatL→isLeftRelativeRightAdhocAdjunction Id F d gd α

      open isRightAdhocAdjunction

      _⊣[_↦_] : Type (ℓ-max (ℓ-max ℓC ℓC') ℓD')
      _⊣[_↦_] = [ Id ⇒ F ]⊣[ d ↦ gd ]

      module _ (adjunction : _⊣[_↦_]) where
        private
          α = fst adjunction
          adjA = snd adjunction

        ε-adhoc : D [ F ⟅ gd ⟆ , d ]
        ε-adhoc = α gd .inv (id C)

        untransposeFromCounit : {c : ob C} → (ψ : C [ c , gd ]) → α _ .inv ψ ≡ F ⟪ ψ ⟫ ⋆⟨ D ⟩ ε-adhoc
        untransposeFromCounit {c} ψ =
          α c .inv ψ
            ≡⟨ cong (α c .inv) (sym (⋆IdR C ψ)) ⟩
          α c .inv (ψ ⋆⟨ C ⟩ id C)
            ≡⟨ invNatL {α = α} adjA ψ (id C) ⟩
          F ⟪ ψ ⟫ ⋆⟨ D ⟩ α gd .inv (id C)
            ≡⟨⟩
          F ⟪ ψ ⟫ ⋆⟨ D ⟩ ε-adhoc ∎

    -- Left-adhoc right-relative adjunction
    -- Note that the arrow direction is arbitrary.
    module _ {B : Category ℓB ℓB'} (c : ob C) (fc : ob D) (J : Functor B D) (G : Functor B C) where
      module _ (α : ∀ b → [ c ↦ fc ]⊣[ J ⟅ b ⟆ ↦ G ⟅ b ⟆ ]) where

        FunNatR : Type (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓC' ℓD'))
        FunNatR = ∀ {b1 b2} → (β : B [ b1 , b2 ]) → (φ : D [ fc , J ⟅ b1 ⟆ ])
          → α b2 .fun (φ ⋆⟨ D ⟩ J ⟪ β ⟫) ≡ α b1 .fun φ ⋆⟨ C ⟩ G ⟪ β ⟫
        InvNatR : Type (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓC' ℓD'))
        InvNatR = ∀ {b1 b2} → (β : B [ b1 , b2 ]) → (ψ : C [ c , G ⟅ b1 ⟆ ])
          → α b2 .inv (ψ ⋆⟨ C ⟩ G ⟪ β ⟫) ≡ α b1 .inv ψ ⋆⟨ D ⟩ J ⟪ β ⟫

        FunNatR→InvNatR : FunNatR → InvNatR
        FunNatR→InvNatR funNatR {b1} {b2} β ψ =
          α b2 .inv (ψ ⋆⟨ C ⟩ G ⟪ β ⟫)
            ≡⟨ cong (α b2 .inv) (cong (λ ψ' → ψ' ⋆⟨ C ⟩ G ⟪ β ⟫) (sym (α b1 .rightInv ψ))) ⟩
          α b2 .inv (α b1 .fun (α b1 .inv ψ) ⋆⟨ C ⟩ G ⟪ β ⟫)
            ≡⟨ cong (α b2 .inv) (sym (funNatR β (α b1 .inv ψ))) ⟩
          α b2 .inv (α b2 .fun (α b1 .inv ψ ⋆⟨ D ⟩ J ⟪ β ⟫))
            ≡⟨ α b2 .leftInv _ ⟩
          α b1 .inv ψ ⋆⟨ D ⟩ J ⟪ β ⟫ ∎

        InvNatR→FunNatR : InvNatR → FunNatR
        InvNatR→FunNatR invNatR {b1} {b2} β φ =
          α b2 .fun (φ ⋆⟨ D ⟩ J ⟪ β ⟫)
            ≡⟨ cong (α b2 .fun) (cong (λ φ' → φ' ⋆⟨ D ⟩ J ⟪ β ⟫) (sym (α b1 .leftInv φ))) ⟩
          α b2 .fun (α b1 .inv (α b1 .fun φ) ⋆⟨ D ⟩ J ⟪ β ⟫)
            ≡⟨ cong (α b2 .fun) (sym (invNatR β (α b1 .fun φ))) ⟩
          α b2 .fun (α b2 .inv (α b1 .fun φ ⋆⟨ C ⟩ G ⟪ β ⟫))
            ≡⟨ α b2 .rightInv _ ⟩
          α b1 .fun φ ⋆⟨ C ⟩ G ⟪ β ⟫ ∎

        record isLeftAdhocRightRelativeAdjunction : Type (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓC' ℓD')) where

          field
            funNatR : FunNatR -- was adjNatInD
            invNatR : InvNatR -- was adjNatInD'

        open isLeftAdhocRightRelativeAdjunction

        FunNatR→isLeftAdhocRightRelativeAdjunction : FunNatR → isLeftAdhocRightRelativeAdjunction
        funNatR (FunNatR→isLeftAdhocRightRelativeAdjunction funNatR') = funNatR'
        invNatR (FunNatR→isLeftAdhocRightRelativeAdjunction funNatR') = FunNatR→InvNatR funNatR'

        InvNatR→isLeftAdhocRightRelativeAdjunction : InvNatR → isLeftAdhocRightRelativeAdjunction
        funNatR (InvNatR→isLeftAdhocRightRelativeAdjunction invNatR') = InvNatR→FunNatR invNatR'
        invNatR (InvNatR→isLeftAdhocRightRelativeAdjunction invNatR') = invNatR'

      [_↦_]⊣[_⇒_] : Type (ℓ-max (ℓ-max (ℓ-max ℓC' ℓD') ℓB) ℓB')
      [_↦_]⊣[_⇒_] = Σ[ α ∈ _ ] isLeftAdhocRightRelativeAdjunction α

    -- Left-adhoc adjunction
    module _ (c : ob C) (fc : ob D) (G : Functor D C) where
      module _ (α : ∀ d → [ c ↦ fc ]⊣[ d ↦ G ⟅ d ⟆ ]) where
        isLeftAdhocAdjunction : Type (ℓ-max (ℓ-max ℓC' ℓD) ℓD')
        isLeftAdhocAdjunction = isLeftAdhocRightRelativeAdjunction c fc Id G α

        module isLeftAdhocAdjunction = isLeftAdhocRightRelativeAdjunction

        open isLeftAdhocAdjunction

        FunNatR→isLeftAdhocAdjunction : FunNatR c fc Id G α → isLeftAdhocAdjunction
        FunNatR→isLeftAdhocAdjunction = FunNatR→isLeftAdhocRightRelativeAdjunction c fc Id G α

        InvNatR→isLeftAdhocAdjunction : InvNatR c fc Id G α → isLeftAdhocAdjunction
        InvNatR→isLeftAdhocAdjunction = InvNatR→isLeftAdhocRightRelativeAdjunction c fc Id G α

      open isLeftAdhocAdjunction

      [_↦_]⊣_ : Type (ℓ-max (ℓ-max ℓC' ℓD) ℓD')
      [_↦_]⊣_ = [ c ↦ fc ]⊣[ Id ⇒ G ]

      module _ (adjunction : [_↦_]⊣_) where
        private
          α = fst adjunction
          adjA = snd adjunction

        η-adhoc : C [ c , G ⟅ fc ⟆ ]
        η-adhoc = α fc .fun (id D)

        transposeFromUnit : {d : ob D} → (φ : D [ fc , d ]) → α d .fun φ ≡ η-adhoc ⋆⟨ C ⟩ G ⟪ φ ⟫
        transposeFromUnit {d} φ =
          α d .fun φ
            ≡⟨ cong (α d .fun) (sym (⋆IdL D φ)) ⟩
          α d .fun (id D ⋆⟨ D ⟩ φ)
            ≡⟨ funNatR {α = α} adjA φ (id D) ⟩
          α fc .fun (id D) ⋆⟨ C ⟩ G ⟪ φ ⟫
            ≡⟨⟩
          η-adhoc ⋆⟨ C ⟩ G ⟪ φ ⟫ ∎

    -- Birelative adjunction
    -- Note that the arrow direction is arbitrary.
    module _ {A : Category ℓA ℓA'} {B : Category ℓB ℓB'}
      (I : Functor A C) (F : Functor A D) (J : Functor B D) (G : Functor B C) where
      module _ (α : ∀ (a : ob A) (b : ob B) → [ I ⟅ a ⟆ ↦ F ⟅ a ⟆ ]⊣[ J ⟅ b ⟆ ↦ G ⟅ b ⟆ ]) where
        isBirelativeAdjunction : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC' ℓD') ℓA) ℓA') ℓB) ℓB')
        isBirelativeAdjunction = (∀ (b : ob B) → isLeftRelativeRightAdhocAdjunction I F (J ⟅ b ⟆) (G ⟅ b ⟆) (λ a → α a b))
                               × (∀ (a : ob A) → isLeftAdhocRightRelativeAdjunction (I ⟅ a ⟆) (F ⟅ a ⟆) J G (α a))

      [_⇒_]⊣[_⇒_] : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC' ℓD') ℓA) ℓA') ℓB) ℓB')
      [_⇒_]⊣[_⇒_] = Σ[ α ∈ _ ] isBirelativeAdjunction α

      module [_⇒_]⊣[_⇒_] (adjunction : [_⇒_]⊣[_⇒_]) where

        adjIso : ∀ {a b} → Iso (D [ F ⟅ a ⟆ , J ⟅ b ⟆ ]) (C [ I ⟅ a ⟆ , G ⟅ b ⟆ ])
        adjIso {a} {b} = adjunction .fst a b
        infix 40 _♭
        infix 40 _♯
        _♭ : ∀ {a b} → (D [ F ⟅ a ⟆ , J ⟅ b ⟆ ]) → (C [ I ⟅ a ⟆ , G ⟅ b ⟆ ])
        (_♭) {_} {_} = adjIso .fun

        _♯ : ∀ {a b} → (C [ I ⟅ a ⟆ , G ⟅ b ⟆ ]) → (D [ F ⟅ a ⟆ , J ⟅ b ⟆ ])
        (_♯) {_} {_} = adjIso .inv

        module _ {a : ob A} where
          open isLeftAdhocRightRelativeAdjunction {c = I ⟅ a ⟆} {F ⟅ a ⟆} {J} {G} {λ b → adjunction .fst a b}
            (adjunction .snd .snd a) public

        module _ {b : ob B} where
          open isLeftRelativeRightAdhocAdjunction {I = I} {F} {J ⟅ b ⟆} {G ⟅ b ⟆} {λ a → adjunction .fst a b}
            (adjunction .snd .fst b) public

    -- Left-relative adjunction
    module _ {A : Category ℓA ℓA'} (I : Functor A C) (F : Functor A D) (G : Functor D C) where
      module _ (α : ∀ (a : ob A) (d : ob D) → [ I ⟅ a ⟆ ↦ F ⟅ a ⟆ ]⊣[ d ↦ G ⟅ d ⟆ ]) where
        isLeftRelativeAdjunction : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC' ℓD) ℓD') ℓA) ℓA')
        isLeftRelativeAdjunction = (∀ (d : ob D) → isLeftRelativeRightAdhocAdjunction I F d (G ⟅ d ⟆) (λ a → α a d))
                                 × (∀ (a : ob A) → isLeftAdhocAdjunction (I ⟅ a ⟆) (F ⟅ a ⟆) G (α a))
        private
          testAdjunction : isLeftRelativeAdjunction ≡ isBirelativeAdjunction I F Id G α
          testAdjunction = refl

      [_⇒_]⊣_ : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC' ℓD) ℓD') ℓA) ℓA')
      [_⇒_]⊣_ = [ I ⇒ F ]⊣[ Id ⇒ G ]

    -- Left functoriality and naturality for free for a left-relative adjunction
    -- Whoever needs this can dualize the proof below.

    -- Right-relative adjunction
    module _ {B : Category ℓB ℓB'} (F : Functor C D) (J : Functor B D) (G : Functor B C) where
      module _ (α : ∀ (c : ob C) (b : ob B) → [ c ↦ F ⟅ c ⟆ ]⊣[ J ⟅ b ⟆ ↦ G ⟅ b ⟆ ]) where
        isRightRelativeAdjunction : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓB) ℓB')
        isRightRelativeAdjunction = (∀ (b : ob B) → isRightAdhocAdjunction F (J ⟅ b ⟆) (G ⟅ b ⟆) (λ c → α c b))
                                  × (∀ (c : ob C) → isLeftAdhocRightRelativeAdjunction c (F ⟅ c ⟆) J G (α c))
        private
          testAdjunction : isRightRelativeAdjunction ≡ isBirelativeAdjunction Id F J G α
          testAdjunction = refl

      _⊣[_⇒_] : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓB) ℓB')
      _⊣[_⇒_] = [ Id ⇒ F ]⊣[ J ⇒ G ]

    -- Right functoriality and naturality for free for a right-relative adjunction
    module RightFunctoriality {B : Category ℓB ℓB'} (F : Functor C D) (J : Functor B D) (obG : ob B → ob C) where
      module _ (α : ∀ (c : ob C) (b : ob B) → [ c ↦ F ⟅ c ⟆ ]⊣[ J ⟅ b ⟆ ↦ obG b ])
               (adjA : ∀ b → isRightAdhocAdjunction F (J ⟅ b ⟆) (obG b) (λ c → α c b)) where

        homG : ∀ {b1 b2} → B [ b1 , b2 ] → C [ obG b1 , obG b2 ]
        homG {b1}{b2} β = α _ _ .fun (ε-adhoc F (J ⟅ b1 ⟆) (obG b1) ((λ c → α c b1) , (adjA b1)) ⋆⟨ D ⟩ J ⟪ β ⟫)

        open isRightAdhocAdjunction

        funNatR : ∀ {c}{b1}{b2} → (β : B [ b1 , b2 ]) → (φ : D [ F ⟅ c ⟆ , J ⟅ b1 ⟆ ]) →
          α c b2 .fun (φ ⋆⟨ D ⟩ J ⟪ β ⟫) ≡ α c b1 .fun φ ⋆⟨ C ⟩ homG β
        funNatR {c}{b1}{b2} β φ  =
          α c b2 .fun (φ ⋆⟨ D ⟩ J ⟪ β ⟫)
            ≡⟨ cong (α c b2 .fun) (cong₂ (seq' D) (sym (α c b1 .leftInv φ)) refl) ⟩
          α c b2 .fun (α c b1 .inv (α c b1 .fun φ) ⋆⟨ D ⟩ J ⟪ β ⟫)
            ≡⟨ cong (α c b2 .fun) (cong₂ (seq' D) (cong (α c b1 .inv) (sym (⋆IdR C (α c b1 .fun φ)))) refl) ⟩
          α c b2 .fun (α c b1 .inv (α c b1 .fun φ ⋆⟨ C ⟩ id C) ⋆⟨ D ⟩ J ⟪ β ⟫)
            ≡⟨ cong (α c b2 .fun) (cong₂ (seq' D)
                (invNatL {F = F} {α = λ c' → α c' b1} (adjA b1) (α c b1 .fun φ) (id C))
                refl
              ) ⟩
          α c b2 .fun ((F ⟪ α c b1 .fun φ ⟫ ⋆⟨ D ⟩ α (obG b1) b1 .inv (id C)) ⋆⟨ D ⟩ J ⟪ β ⟫)
            ≡⟨ cong (α c b2 .fun) (⋆Assoc D _ _ _) ⟩
          α c b2 .fun (F ⟪ α c b1 .fun φ ⟫ ⋆⟨ D ⟩ (α (obG b1) b1 .inv (id C) ⋆⟨ D ⟩ J ⟪ β ⟫))
            ≡⟨⟩
          α c b2 .fun (F ⟪ α c b1 .fun φ ⟫ ⋆⟨ D ⟩ (ε-adhoc F (J ⟅ b1 ⟆) (obG b1) ((λ c → α c b1) , (adjA b1)) ⋆⟨ D ⟩ J ⟪ β ⟫))
            ≡⟨ funNatL {F = F} {α = λ c' → α c' b1} (adjA b2) (α c b1 .fun φ)
               (ε-adhoc F (J ⟅ b1 ⟆) (obG b1) ((λ c → α c b1) , (adjA b1)) ⋆⟨ D ⟩ J ⟪ β ⟫) ⟩
          α c b1 .fun φ ⋆⟨ C ⟩ α (obG b1) b2 .fun (ε-adhoc F (J ⟅ b1 ⟆) (obG b1) ((λ c → α c b1) , (adjA b1)) ⋆⟨ D ⟩ J ⟪ β ⟫)
            ≡⟨⟩
          α c b1 .fun φ ⋆⟨ C ⟩ homG β ∎

        open Functor
        G : Functor B C
        F-ob G = obG
        F-hom G = homG
        F-id G {b} =
          F-hom G (B .id)
            ≡⟨⟩
          α (obG b) b .fun (α (obG b) b .inv (id C) ⋆⟨ D ⟩ F-hom J (B .id))
            ≡⟨ cong (α (obG b) b .fun) (cong₂ (seq' D) refl (F-id J)) ⟩
          α (obG b) b .fun (α (obG b) b .inv (id C) ⋆⟨ D ⟩ D .id)
            ≡⟨ cong (α (obG b) b .fun) (⋆IdR D (α (obG b) b .inv (id C))) ⟩
          α (obG b) b .fun (α (obG b) b .inv (id C))
            ≡⟨ α (obG b) b .rightInv (id C) ⟩
          C .id ∎
        F-seq G {b1}{b2}{b3} β β' =
          homG (β ⋆⟨ B ⟩ β')
            ≡⟨⟩
          α (obG b1) b3 .fun (α (obG b1) b1 .inv (id C) ⋆⟨ D ⟩ (J ⟪ β ⋆⟨ B ⟩ β' ⟫))
            ≡⟨ cong (α (obG b1) b3 .fun) (cong₂ (seq' D) refl (F-seq J β β')) ⟩
          α (obG b1) b3 .fun (α (obG b1) b1 .inv (id C) ⋆⟨ D ⟩ (J ⟪ β ⟫ ⋆⟨ D ⟩ J ⟪ β' ⟫))
            ≡⟨ cong (α (obG b1) b3 .fun) (sym (⋆Assoc D _ _ _)) ⟩
          α (obG b1) b3 .fun ((α (obG b1) b1 .inv (id C) ⋆⟨ D ⟩ J ⟪ β ⟫) ⋆⟨ D ⟩ J ⟪ β' ⟫)
            ≡⟨ funNatR β' (α (obG b1) b1 .inv (id C) ⋆⟨ D ⟩ J ⟪ β ⟫) ⟩
          α (obG b1) b2 .fun (α (obG b1) b1 .inv (id C) ⋆⟨ D ⟩ J ⟪ β ⟫) ⋆⟨ C ⟩ homG β'
            ≡⟨⟩
          homG β ⋆⟨ C ⟩ homG β' ∎

    -- Adjunction
    module _ (F : Functor C D) (G : Functor D C) where
      module _ (α : ∀ (c : ob C) (d : ob D) → [ c ↦ F ⟅ c ⟆ ]⊣[ d ↦ G ⟅ d ⟆ ]) where
        isAdjunction : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD')
        isAdjunction = (∀ (d : ob D) → isRightAdhocAdjunction F d (G ⟅ d ⟆) (λ c → α c d))
                     × (∀ (c : ob C) → isLeftAdhocAdjunction c (F ⟅ c ⟆) G (α c))
        private
          testAdjunction : isAdjunction ≡ isBirelativeAdjunction Id F Id G α
          testAdjunction = refl

      _⊣_ : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD')
      _⊣_ = [ Id ⇒ F ]⊣[ Id ⇒ G ]

      module _⊣_ (adjunction : _⊣_) where

        open [_⇒_]⊣[_⇒_] Id F Id G adjunction public

    isLeftAdjoint : (F : Functor C D) → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
    isLeftAdjoint F = Σ[ G ∈ Functor D C ] F ⊣ G

    isRightAdjoint : (G : Functor D C) → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
    isRightAdjoint G = Σ[ F ∈ Functor C D ] F ⊣ G

{-
==============================================
            Proofs of equivalence
==============================================

This first unnamed module provides a function
adj'→adj which takes you from the second
definition to the first.

The second unnamed module does the reverse.
-}

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) (G : Functor D C) where
  open UnitCounit
  open NaturalBijection renaming (_⊣_ to _⊣²_)
  module _ (adj : F ⊣² G) where
    open _⊣²_ F G adj
    open _⊣_

    -- Naturality condition implies that a commutative square in C
    -- appears iff the transpose in D is commutative as well
    -- Used in adj'→adj
    adjNat' : ∀ {c c' d d'} {f : D [ F ⟅ c ⟆ , d ]} {k : D [ d , d' ]}
            → {h : C [ c , c' ]} {g : C [ c' , G ⟅ d' ⟆ ]}
            -- commutativity of squares is iff
            → ((f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ (g ♯)) → (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g))
            × ((f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g) → (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ (g ♯)))
    adjNat' {c} {c'} {d} {d'} {f} {k} {h} {g} = D→C , C→D
      where
        D→C : (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ (g ♯)) → (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g)
        D→C eq = f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫
              ≡⟨ sym (funNatR _ _) ⟩
                ((f ⋆⟨ D ⟩ k) ♭)
              ≡⟨ cong _♭ eq ⟩
                (F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯) ♭
              ≡⟨ sym (cong _♭ (invNatL _ _)) ⟩
                (h ⋆⟨ C ⟩ g) ♯ ♭
              ≡⟨ adjIso .rightInv _ ⟩
                h ⋆⟨ C ⟩ g
              ∎
        C→D : (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g) → (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ (g ♯))
        C→D eq = f ⋆⟨ D ⟩ k
              ≡⟨ sym (adjIso .leftInv _) ⟩
                (f ⋆⟨ D ⟩ k) ♭ ♯
              ≡⟨ cong _♯ (funNatR _ _) ⟩
                (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫) ♯
              ≡⟨ cong _♯ eq ⟩
                (h ⋆⟨ C ⟩ g) ♯
              ≡⟨ invNatL _ _ ⟩
                F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯
              ∎

    open NatTrans

    -- note : had to make this record syntax because termination checker was complaining
    -- due to referencing η and ε from the definitions of Δs
    adj'→adj : F ⊣ G
    adj'→adj = record
      { η = η'
      ; ε = ε'
      ; Δ₁ = Δ₁'
      ; Δ₂ = Δ₂' }

      where
        -- ETA

        -- trivial commutative diagram between identities in D
        commInD : ∀ {x y} (f : C [ x , y ]) → D .id ⋆⟨ D ⟩ F ⟪ f ⟫ ≡ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id
        commInD f = (D .⋆IdL _) ∙ sym (D .⋆IdR _)

        sharpen1 : ∀ {x y} (f : C [ x , y ]) → F ⟪ f ⟫ ⋆⟨ D ⟩ D .id ≡ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id ♭ ♯
        sharpen1 f = cong (λ v → F ⟪ f ⟫ ⋆⟨ D ⟩ v) (sym (adjIso .leftInv _))

        η' : 𝟙⟨ C ⟩ ⇒ G ∘F F
        η' .N-ob x = D .id ♭
        η' .N-hom f = sym (fst (adjNat') (commInD f ∙ sharpen1 f))

        -- EPSILON

        -- trivial commutative diagram between identities in C
        commInC : ∀ {x y} (g : D [ x , y ]) → C .id ⋆⟨ C ⟩ G ⟪ g ⟫ ≡ G ⟪ g ⟫ ⋆⟨ C ⟩ C .id
        commInC g = (C .⋆IdL _) ∙ sym (C .⋆IdR _)

        sharpen2 : ∀ {x y} (g : D [ x , y ]) → C .id ♯ ♭ ⋆⟨ C ⟩ G ⟪ g ⟫ ≡ C .id ⋆⟨ C ⟩ G ⟪ g ⟫
        sharpen2 g = cong (λ v → v ⋆⟨ C ⟩ G ⟪ g ⟫) (adjIso .rightInv _)

        ε' : F ∘F G ⇒ 𝟙⟨ D ⟩
        ε' .N-ob x  = C .id ♯
        ε' .N-hom g = sym (snd adjNat' (sharpen2 g ∙ commInC g))

        -- DELTA 1

        expL : ∀ (c)
            → (seqTransP F-assoc (F ∘ʳ η') (ε' ∘ˡ F) .N-ob c)
              ≡ F ⟪ η' ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ ε' ⟦ F ⟅ c ⟆ ⟧
        expL c = seqTransP F-assoc (F ∘ʳ η') (ε' ∘ˡ F) .N-ob c
              ≡⟨ refl ⟩
                seqP {C = D} {p = refl} (F ⟪ η' ⟦ c ⟧ ⟫) (ε' ⟦ F ⟅ c ⟆ ⟧)
              ≡⟨ seqP≡seq {C = D} _ _ ⟩
                F ⟪ η' ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ ε' ⟦ F ⟅ c ⟆ ⟧
              ∎

        body : ∀ (c)
            → (idTrans F) ⟦ c ⟧ ≡ (seqTransP F-assoc (F ∘ʳ η') (ε' ∘ˡ F) .N-ob c)
        body c = (idTrans F) ⟦ c ⟧
              ≡⟨ refl ⟩
                D .id
              ≡⟨ sym (D .⋆IdL _) ⟩
                D .id ⋆⟨ D ⟩ D .id
              ≡⟨ snd adjNat' (cong (λ v → (η' ⟦ c ⟧) ⋆⟨ C ⟩ v) (G .F-id)) ⟩
                F ⟪ η' ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ ε' ⟦ F ⟅ c ⟆ ⟧
              ≡⟨ sym (expL c) ⟩
                seqTransP F-assoc (F ∘ʳ η') (ε' ∘ˡ F) .N-ob c
              ∎

        Δ₁' : PathP (λ i → NatTrans (F-lUnit {F = F} i) (F-rUnit {F = F} i))
                    (seqTransP F-assoc (F ∘ʳ η') (ε' ∘ˡ F))
                    (1[ F ])
        Δ₁' = makeNatTransPathP F-lUnit F-rUnit (sym (funExt body))

        -- DELTA 2

        body2 : ∀ (d)
            →  seqP {C = C} {p = refl} ((η' ∘ˡ G) ⟦ d ⟧) ((G ∘ʳ ε') ⟦ d ⟧) ≡ C .id
        body2 d = seqP {C = C} {p = refl} ((η' ∘ˡ G) ⟦ d ⟧) ((G ∘ʳ ε') ⟦ d ⟧)
                ≡⟨ seqP≡seq {C = C} _ _ ⟩
                  ((η' ∘ˡ G) ⟦ d ⟧) ⋆⟨ C ⟩ ((G ∘ʳ ε') ⟦ d ⟧)
                ≡⟨ refl ⟩
                  (η' ⟦ G ⟅ d ⟆ ⟧) ⋆⟨ C ⟩ (G ⟪ ε' ⟦ d ⟧ ⟫)
                ≡⟨ fst adjNat' (cong (λ v → v ⋆⟨ D ⟩ (ε' ⟦ d ⟧)) (sym (F .F-id))) ⟩
                  C .id ⋆⟨ C ⟩ C .id
                ≡⟨ C .⋆IdL _ ⟩
                  C .id
                ∎

        Δ₂' : PathP (λ i → NatTrans (F-rUnit {F = G} i) (F-lUnit {F = G} i))
              (seqTransP (sym F-assoc) (η' ∘ˡ G) (G ∘ʳ ε'))
              (1[ G ])
        Δ₂' = makeNatTransPathP F-rUnit F-lUnit (funExt body2)


  module _ (adj : F ⊣ G) where
    open _⊣_ adj
    open _⊣²_
    open NatTrans

    -- helper functions for working with this Adjoint definition

    δ₁ : ∀ {c} → (F ⟪ η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ ε ⟦ F ⟅ c ⟆ ⟧) ≡ D .id
    δ₁ {c} = (F ⟪ η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ ε ⟦ F ⟅ c ⟆ ⟧)
          ≡⟨ sym (seqP≡seq {C = D} _ _) ⟩
            seqP {C = D} {p = refl} (F ⟪ η ⟦ c ⟧ ⟫) (ε ⟦ F ⟅ c ⟆ ⟧)
          ≡⟨ (λ j → (Δ₁ j) .N-ob c) ⟩
            D .id
          ∎

    δ₂ : ∀ {d} → (η ⟦ G ⟅ d ⟆ ⟧ ⋆⟨ C ⟩ G ⟪ ε ⟦ d ⟧ ⟫) ≡ C .id
    δ₂ {d} = (η ⟦ G ⟅ d ⟆ ⟧ ⋆⟨ C ⟩ G ⟪ ε ⟦ d ⟧ ⟫)
        ≡⟨ sym (seqP≡seq {C = C} _ _) ⟩
          seqP {C = C} {p = refl} (η ⟦ G ⟅ d ⟆ ⟧) (G ⟪ ε ⟦ d ⟧ ⟫)
        ≡⟨ (λ j → (Δ₂ j) .N-ob d) ⟩
          C .id
        ∎


    adj→adj' : F ⊣² G
    fun (fst adj→adj' c d) f = η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ f ⟫
    inv (fst adj→adj' c d) g = F ⟪ g ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧
    rightInv (fst adj→adj' c d) g =
        η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ F ⟪ g ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧ ⟫ -- step0 ∙ step1 ∙ step2 ∙ (C .⋆IdR _)
      ≡⟨ cong (λ v → η ⟦ c ⟧ ⋆⟨ C ⟩ v) (G .F-seq _ _) ⟩
        η ⟦ c ⟧ ⋆⟨ C ⟩ (G ⟪ F ⟪ g ⟫ ⟫ ⋆⟨ C ⟩ G ⟪ ε ⟦ d ⟧ ⟫)
      ≡⟨ sym (C .⋆Assoc _ _ _) ⟩
        η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ F ⟪ g ⟫ ⟫ ⋆⟨ C ⟩ G ⟪ ε ⟦ d ⟧ ⟫
      -- apply naturality
      ≡⟨ rCatWhisker {C = C} _ _ _ natu ⟩
        (g ⋆⟨ C ⟩ η ⟦ G ⟅ d ⟆ ⟧) ⋆⟨ C ⟩ G ⟪ ε ⟦ d ⟧ ⟫
      ≡⟨ C .⋆Assoc _ _ _ ⟩
        g ⋆⟨ C ⟩ (η ⟦ G ⟅ d ⟆ ⟧ ⋆⟨ C ⟩ G ⟪ ε ⟦ d ⟧ ⟫)
      ≡⟨ lCatWhisker {C = C} _ _ _ δ₂ ⟩
        g ⋆⟨ C ⟩ C .id
      ≡⟨ C .⋆IdR _ ⟩
        g
      ∎
      where
        natu : η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ F ⟪ g ⟫ ⟫ ≡ g ⋆⟨ C ⟩ η ⟦ G ⟅ d ⟆ ⟧
        natu = sym (η .N-hom _)
    leftInv (fst adj→adj' c d) f =
        F ⟪ η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ f ⟫ ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧
      ≡⟨ cong (λ v → v ⋆⟨ D ⟩ ε ⟦ d ⟧) (F .F-seq _ _) ⟩
        F ⟪ η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ F ⟪ G ⟪ f ⟫ ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧
      ≡⟨ D .⋆Assoc _ _ _ ⟩
        F ⟪ η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ (F ⟪ G ⟪ f ⟫ ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧)
      -- apply naturality
      ≡⟨ lCatWhisker {C = D} _ _ _ natu ⟩
        F ⟪ η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ (ε ⟦ F ⟅ c ⟆ ⟧ ⋆⟨ D ⟩ f)
      ≡⟨ sym (D .⋆Assoc _ _ _) ⟩
        F ⟪ η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ ε ⟦ F ⟅ c ⟆ ⟧ ⋆⟨ D ⟩ f
      -- apply triangle identity
      ≡⟨ rCatWhisker {C = D} _ _ _ δ₁ ⟩
        D .id ⋆⟨ D ⟩ f
      ≡⟨ D .⋆IdL _ ⟩
        f
      ∎
      where
        natu : F ⟪ G ⟪ f ⟫ ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧ ≡ ε ⟦ F ⟅ c ⟆ ⟧ ⋆⟨ D ⟩ f
        natu = ε .N-hom _
    fst (snd adj→adj') d = InvNatL→isLeftRelativeRightAdhocAdjunction _ _ _ _ _
      λ {b1} {b2} β ψ → cong (λ v → v ⋆⟨ D ⟩ ε ⟦ d ⟧) (F .F-seq _ _) ∙ D .⋆Assoc _ _ _
    snd (snd adj→adj') c = FunNatR→isLeftAdhocRightRelativeAdjunction _ _ _ _ _
      λ {b1} {b2} β φ → cong (λ v → η ⟦ c ⟧ ⋆⟨ C ⟩ v) (G .F-seq _ _) ∙ (sym (C .⋆Assoc _ _ _))
