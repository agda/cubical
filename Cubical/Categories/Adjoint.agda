{-# OPTIONS --safe #-}

module Cubical.Categories.Adjoint where

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
    ℓC ℓC' ℓD ℓD' : Level

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
  -- Adjoint def 2: natural bijection
  record _⊣_ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) (G : Functor D C) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    field
      adjIso : ∀ {c d} → Iso (D [ F ⟅ c ⟆ , d ]) (C [ c , G ⟅ d ⟆ ])

    infix 40 _♭
    infix 40 _♯
    _♭ : ∀ {c d} → (D [ F ⟅ c ⟆ , d ]) → (C [ c , G ⟅ d ⟆ ])
    (_♭) {_} {_} = adjIso .fun

    _♯ : ∀ {c d} → (C [ c , G ⟅ d ⟆ ]) → (D [ F ⟅ c ⟆ , d ])
    (_♯) {_} {_} = adjIso .inv

    field
      adjNatInD : ∀ {c : C .ob} {d d'} (f : D [ F ⟅ c ⟆ , d ]) (k : D [ d , d' ])
                → (f ⋆⟨ D ⟩ k) ♭ ≡ f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫

      adjNatInC : ∀ {c' c d} (g : C [ c , G ⟅ d ⟆ ]) (h : C [ c' , c ])
                → (h ⋆⟨ C ⟩ g) ♯ ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯

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
    open _⊣²_ adj
    open _⊣_

    -- Naturality condition implies that a commutative square in C
    -- appears iff the transpose in D is commutative as well
    -- Used in adj'→adj
    adjNat' : ∀ {c c' d d'} {f : D [ F ⟅ c ⟆ , d ]} {k : D [ d , d' ]}
            → {h : C [ c , c' ]} {g : C [ c' , G ⟅ d' ⟆ ]}
            -- commutativity of squares is iff
            → ((f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯) → (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g))
            × ((f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g) → (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯))
    adjNat' {c} {c'} {d} {d'} {f} {k} {h} {g} = D→C , C→D
      where
        D→C : (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯) → (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g)
        D→C eq = f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫
              ≡⟨ sym (adjNatInD _ _) ⟩
                ((f ⋆⟨ D ⟩ k) ♭)
              ≡⟨ cong _♭ eq ⟩
                (F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯) ♭
              ≡⟨ sym (cong _♭ (adjNatInC _ _)) ⟩
                (h ⋆⟨ C ⟩ g) ♯ ♭
              ≡⟨ adjIso .rightInv _ ⟩
                h ⋆⟨ C ⟩ g
              ∎
        C→D : (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g) → (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯)
        C→D eq = f ⋆⟨ D ⟩ k
              ≡⟨ sym (adjIso .leftInv _) ⟩
                (f ⋆⟨ D ⟩ k) ♭ ♯
              ≡⟨ cong _♯ (adjNatInD _ _) ⟩
                (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫) ♯
              ≡⟨ cong _♯ eq ⟩
                (h ⋆⟨ C ⟩ g) ♯
              ≡⟨ adjNatInC _ _ ⟩
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
    -- ∀ {c d} → Iso (D [ F ⟅ c ⟆ , d ]) (C [ c , G ⟅ d ⟆ ])
    -- takes f to Gf precomposed with the unit
    adj→adj' .adjIso {c = c} .fun f = η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ f ⟫
    -- takes g to Fg postcomposed with the counit
    adj→adj' .adjIso {d = d} .inv g = F ⟪ g ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧
    -- invertibility follows from the triangle identities
    adj→adj' .adjIso {c = c} {d} .rightInv g
      = η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ F ⟪ g ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧ ⟫ -- step0 ∙ step1 ∙ step2 ∙ (C .⋆IdR _)
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
    adj→adj' .adjIso {c = c} {d} .leftInv f
      = F ⟪ η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ f ⟫ ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧
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
    -- follows directly from functoriality
    adj→adj' .adjNatInD {c = c} f k = cong (λ v → η ⟦ c ⟧ ⋆⟨ C ⟩ v) (G .F-seq _ _) ∙ (sym (C .⋆Assoc _ _ _))
    adj→adj' .adjNatInC {d = d} g h = cong (λ v → v ⋆⟨ D ⟩ ε ⟦ d ⟧) (F .F-seq _ _) ∙ D .⋆Assoc _ _ _
