{-# OPTIONS --safe #-}

module Cubical.Categories.Adjoint.Relative where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Isomorphism

open Functor

open Iso
open Category

    {-
      Here, we define adjunctions in terms of more general concepts:
      - Relative adjunctions (see e.g. the nLab)
      - Adhoc adjunctions: Sometimes a functor F does not have a right adjoint functor G defined on all objects, but for a
        specific object d, there may be an object gd that behaves as the image of d under the right adjoint to F.
        Examples are:
        - the local right Kan extension (when the global Kan extension does not exist)
        - a limit of a specific diagram (when not all diagrams of the same shape may have a limit).
    -}

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level

module Adhoc (C : Category ℓC ℓC') (D : Category ℓD ℓD') where

    -- Adhoc adjunction (quite useless in itself)
    -- Note that the arrow direction is arbitrary.
    [_↦_]⊣[_↦_] : ob C → ob D → ob D → ob C → Type (ℓ-max ℓC' ℓD')
    [ c ↦ fc ]⊣[ d ↦ gd ] = Iso (D [ fc , d ]) (C [ c , gd ])
    -- Idea: We could generalize further by having a profunctor (instead of just Hom) on both sides of the iso.
    -- This way, an isomorphism with the cone profunctor could be used to define limits.

    AdhocAdjunction = [_↦_]⊣[_↦_]

    -- Left-relative right-adhoc adjunction
    -- Note that the arrow direction is arbitrary.
module LeftRelativeRightAdhoc
    {A : Category ℓA ℓA'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    (I : Functor A C) (F : Functor A D) where

    open Adhoc C D

    module _ (d : ob D) (gd : ob C) where
      module _ (α : ∀ a → [ I ⟅ a ⟆ ↦ F ⟅ a ⟆ ]⊣[ d ↦ gd ]) where

        FunNatL : Type (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓC' ℓD'))
        FunNatL = ∀ {a1 a2} → (β : A [ a1 , a2 ]) → (φ : D [ F ⟅ a2 ⟆ , d ])
          → α a1 .fun (F ⟪ β ⟫ ⋆⟨ D ⟩ φ) ≡ I ⟪ β ⟫ ⋆⟨ C ⟩ α a2 .fun φ
        InvNatL : Type (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓC' ℓD'))
        InvNatL = ∀ {a1 a2} → (β : A [ a1 , a2 ]) → (ψ : C [ I ⟅ a2 ⟆ , gd ])
          → α a1 .inv (I ⟪ β ⟫ ⋆⟨ C ⟩ ψ) ≡ F ⟪ β ⟫ ⋆⟨ D ⟩ α a2 .inv ψ

        FunNatL→InvNatL : FunNatL → InvNatL
        FunNatL→InvNatL funNatL {a1} {a2} β ψ =
          α a1 .inv (I ⟪ β ⟫ ⋆⟨ C ⟩ ψ)
            ≡⟨ cong (α a1 .inv) (cong (λ ψ' → I ⟪ β ⟫ ⋆⟨ C ⟩ ψ') (sym (α a2 .rightInv ψ))) ⟩
          α a1 .inv (I ⟪ β ⟫ ⋆⟨ C ⟩ α a2 .fun (α a2 .inv ψ))
            ≡⟨ cong (α a1 .inv) (sym (funNatL β (α a2 .inv ψ))) ⟩
          α a1 .inv (α a1 .fun (F ⟪ β ⟫ ⋆⟨ D ⟩ (α a2 .inv ψ)))
            ≡⟨ α a1 .leftInv _ ⟩
          F ⟪ β ⟫ ⋆⟨ D ⟩ α a2 .inv ψ ∎

        InvNatL→FunNatL : InvNatL → FunNatL
        InvNatL→FunNatL invNatL {a1} {a2} β φ =
          α a1 .fun (F ⟪ β ⟫ ⋆⟨ D ⟩ φ)
            ≡⟨ cong (α a1 .fun) (cong (λ φ' → F ⟪ β ⟫ ⋆⟨ D ⟩ φ') (sym (α a2 .leftInv φ))) ⟩
          α a1 .fun (F ⟪ β ⟫ ⋆⟨ D ⟩ α a2 .inv (α a2 .fun φ))
            ≡⟨ cong (α a1 .fun) (sym (invNatL β (α a2 .fun φ))) ⟩
          α a1 .fun (α a1 .inv (I ⟪ β ⟫ ⋆⟨ C ⟩ (α a2 .fun φ)))
            ≡⟨ α a1 .rightInv _ ⟩
          I ⟪ β ⟫ ⋆⟨ C ⟩ α a2 .fun φ ∎

        record isLeftRelativeRightAdhocAdjunction : Type (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓC' ℓD')) where

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

      [_⇒_]⊣[_↦_] : Type (ℓ-max (ℓ-max (ℓ-max ℓC' ℓD') ℓA) ℓA')
      [_⇒_]⊣[_↦_] = Σ[ α ∈ _ ] isLeftRelativeRightAdhocAdjunction α

      LeftRelativeRightAdhocAdjunction = [_⇒_]⊣[_↦_]

    -- Left-adhoc right-relative adjunction
    -- Note that the arrow direction is arbitrary.
module LeftAdhocRightRelative
    {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    (J : Functor B D) (G : Functor B C) where

    open Adhoc C D

    module _ (c : ob C) (fc : ob D) where
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

      LeftAdhocRightRelativeAdjunction = [_↦_]⊣[_⇒_]

    -- Birelative adjunction
    -- Note that the arrow direction is arbitrary.
module Birelative
    {A : Category ℓA ℓA'} {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    (I : Functor A C) (F : Functor A D) (J : Functor B D) (G : Functor B C) where

    open Adhoc C D
    open LeftRelativeRightAdhoc I F
    open LeftAdhocRightRelative J G

    module _ (α : ∀ (a : ob A) (b : ob B) → [ I ⟅ a ⟆ ↦ F ⟅ a ⟆ ]⊣[ J ⟅ b ⟆ ↦ G ⟅ b ⟆ ]) where

        isBirelativeAdjunction : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC' ℓD') ℓA) ℓA') ℓB) ℓB')
        isBirelativeAdjunction = (∀ (a : ob A) → isLeftAdhocRightRelativeAdjunction (I ⟅ a ⟆) (F ⟅ a ⟆) (α a))
                               × (∀ (b : ob B) → isLeftRelativeRightAdhocAdjunction (J ⟅ b ⟆) (G ⟅ b ⟆) (λ a → α a b))

    [_⇒_]⊣[_⇒_] : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC' ℓD') ℓA) ℓA') ℓB) ℓB')
    [_⇒_]⊣[_⇒_] = Σ[ α ∈ _ ] isBirelativeAdjunction α

    BirelativeAdjunction = [_⇒_]⊣[_⇒_]

    module BirelativeAdjunction (adjunction : [_⇒_]⊣[_⇒_]) where

        adjIso : ∀ {a b} → Iso (D [ F ⟅ a ⟆ , J ⟅ b ⟆ ]) (C [ I ⟅ a ⟆ , G ⟅ b ⟆ ])
        adjIso {a} {b} = adjunction .fst a b
        infix 40 _♭
        infix 40 _♯
        _♭ : ∀ {a b} → (D [ F ⟅ a ⟆ , J ⟅ b ⟆ ]) → (C [ I ⟅ a ⟆ , G ⟅ b ⟆ ])
        (_♭) {_} {_} = adjIso .fun

        _♯ : ∀ {a b} → (C [ I ⟅ a ⟆ , G ⟅ b ⟆ ]) → (D [ F ⟅ a ⟆ , J ⟅ b ⟆ ])
        (_♯) {_} {_} = adjIso .inv

-- Same as LeftRelativeRightAdhoc but I : A -> C is the identity now
module RightAdhoc
    {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    (F : Functor C D) where

    open LeftRelativeRightAdhoc Id F public renaming
      ( module isLeftRelativeRightAdhocAdjunction   to isRightAdhocAdjunction
      ; isLeftRelativeRightAdhocAdjunction          to isRightAdhocAdjunction
      ; FunNatL→isLeftRelativeRightAdhocAdjunction to FunNatL→isRightAdhocAdjunction
      ; InvNatL→isLeftRelativeRightAdhocAdjunction to InvNatL→isRightAdhocAdjunction
      ; [_⇒_]⊣[_↦_]                                to _⊣[_↦_]
      ; LeftRelativeRightAdhocAdjunction            to RightAdhocAdjunction
      )

    module _ (d : ob D) (gd : ob C) (adjunction : RightAdhocAdjunction d gd) where
        private
          α = fst adjunction
          adjA = snd adjunction

        open isRightAdhocAdjunction adjA

        ε-adhoc : D [ F ⟅ gd ⟆ , d ]
        ε-adhoc = α gd .inv (id C)

        untransposeFromCounit : {c : ob C} → (ψ : C [ c , gd ]) → α _ .inv ψ ≡ F ⟪ ψ ⟫ ⋆⟨ D ⟩ ε-adhoc
        untransposeFromCounit {c} ψ =
          α c .inv ψ
            ≡⟨ cong (α c .inv) (sym (⋆IdR C ψ)) ⟩
          α c .inv (ψ ⋆⟨ C ⟩ id C)
            ≡⟨ invNatL ψ (id C) ⟩
          F ⟪ ψ ⟫ ⋆⟨ D ⟩ α gd .inv (id C)
            ≡⟨⟩
          F ⟪ ψ ⟫ ⋆⟨ D ⟩ ε-adhoc ∎

-- Same as LeftAdhocRightRelative but J : B -> D is the identity now
module LeftAdhoc
    {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    (G : Functor D C) where

    open LeftAdhocRightRelative Id G public renaming
      ( module isLeftAdhocRightRelativeAdjunction   to isLeftAdhocAdjunction
      ; isLeftAdhocRightRelativeAdjunction          to isLeftAdhocAdjunction
      ; FunNatR→isLeftAdhocRightRelativeAdjunction to FunNatR→isLeftAdhocAdjunction
      ; InvNatR→isLeftAdhocRightRelativeAdjunction to InvNatR→isLeftAdhocAdjunction
      ; [_↦_]⊣[_⇒_]                                to [_↦_]⊣_
      ; LeftAdhocRightRelativeAdjunction            to LeftAdhocAdjunction
      )

    module _ (c : ob C) (fc : ob D) (adjunction : LeftAdhocAdjunction c fc) where
        private
          α = fst adjunction
          adjA = snd adjunction

        open isLeftAdhocAdjunction adjA

        η-adhoc : C [ c , G ⟅ fc ⟆ ]
        η-adhoc = α fc .fun (id D)

        transposeFromUnit : {d : ob D} → (φ : D [ fc , d ]) → α d .fun φ ≡ η-adhoc ⋆⟨ C ⟩ G ⟪ φ ⟫
        transposeFromUnit {d} φ =
          α d .fun φ
            ≡⟨ cong (α d .fun) (sym (⋆IdL D φ)) ⟩
          α d .fun (id D ⋆⟨ D ⟩ φ)
            ≡⟨ funNatR φ (id D) ⟩
          α fc .fun (id D) ⋆⟨ C ⟩ G ⟪ φ ⟫
            ≡⟨⟩
          η-adhoc ⋆⟨ C ⟩ G ⟪ φ ⟫ ∎

-- Same as Birelative but I : A -> C is the identity now
module RightRelative
    {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    (F : Functor C D) (J : Functor B D) (G : Functor B C) where

    open Birelative Id F J G public renaming
      ( isBirelativeAdjunction to isRightRelativeAdjunction
      ; [_⇒_]⊣[_⇒_] to _⊣[_⇒_]
      ; BirelativeAdjunction to RightRelativeAdjunction
      ; module BirelativeAdjunction to RightRelativeAdjunction
      )

-- Same as Birelative but J : B -> D is the identity now
module LeftRelative
    {A : Category ℓA ℓA'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    (I : Functor A C) (F : Functor A D) (G : Functor D C) where

    open Birelative I F Id G public renaming
      ( isBirelativeAdjunction to isLeftRelativeAdjunction
      ; [_⇒_]⊣[_⇒_] to [_⇒_]⊣_
      ; BirelativeAdjunction to LeftRelativeAdjunction
      ; module BirelativeAdjunction to LeftRelativeAdjunction
      )

-- Same as Birelative but I and J the identity now
module Plain
    {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    (F : Functor C D) (G : Functor D C) where

    open Birelative Id F Id G public renaming
      ( isBirelativeAdjunction to isAdjunction
      ; [_⇒_]⊣[_⇒_] to _⊣_
      ; BirelativeAdjunction to Adjunction
      ; module BirelativeAdjunction to Adjunction
      )


-- Turning a right adhoc adjunction into a right relative adjunction, generating functoriality
module RightFunctoriality
    {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    (F : Functor C D) (J : Functor B D) (obG : ob B → ob C) where
    module _ (α : let open Adhoc C D in ∀ (c : ob C) (b : ob B) → [ c ↦ F ⟅ c ⟆ ]⊣[ J ⟅ b ⟆ ↦ obG b ])
             (adjA : let open RightAdhoc F in ∀ b → isRightAdhocAdjunction (J ⟅ b ⟆) (obG b) (λ c → α c b)) where

        open RightAdhoc F

        homG : ∀ {b1 b2} → B [ b1 , b2 ] → C [ obG b1 , obG b2 ]
        homG {b1}{b2} β = α _ _ .fun (ε-adhoc (J ⟅ b1 ⟆) (obG b1) ((λ c → α c b1) , (adjA b1)) ⋆⟨ D ⟩ J ⟪ β ⟫)

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
                (invNatL (adjA b1) (α c b1 .fun φ) (id C))
                refl
              ) ⟩
          α c b2 .fun ((F ⟪ α c b1 .fun φ ⟫ ⋆⟨ D ⟩ α (obG b1) b1 .inv (id C)) ⋆⟨ D ⟩ J ⟪ β ⟫)
            ≡⟨ cong (α c b2 .fun) (⋆Assoc D _ _ _) ⟩
          α c b2 .fun (F ⟪ α c b1 .fun φ ⟫ ⋆⟨ D ⟩ (α (obG b1) b1 .inv (id C) ⋆⟨ D ⟩ J ⟪ β ⟫))
            ≡⟨⟩
          α c b2 .fun (F ⟪ α c b1 .fun φ ⟫ ⋆⟨ D ⟩ (ε-adhoc (J ⟅ b1 ⟆) (obG b1) ((λ c → α c b1) , (adjA b1)) ⋆⟨ D ⟩ J ⟪ β ⟫))
            ≡⟨ funNatL (adjA b2) (α c b1 .fun φ)
               (ε-adhoc (J ⟅ b1 ⟆) (obG b1) ((λ c → α c b1) , (adjA b1)) ⋆⟨ D ⟩ J ⟪ β ⟫) ⟩
          α c b1 .fun φ ⋆⟨ C ⟩ α (obG b1) b2 .fun (ε-adhoc (J ⟅ b1 ⟆) (obG b1) ((λ c → α c b1) , (adjA b1)) ⋆⟨ D ⟩ J ⟪ β ⟫)
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

