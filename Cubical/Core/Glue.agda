{-

This file contains:

- Definitions of fibers and equivalences

- Glue types

- The identity equivalence and the ua constant

- Proof of univalence using that unglue is an equivalence ([EquivContr])

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Core.Glue where

open import Cubical.Core.Prelude
open import Agda.Builtin.Cubical.Glue public
  using ( isEquiv       -- ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ ⊔ ℓ')

        ; equiv-proof   -- ∀ (y : B) → isContr (fiber f y)

        ; _≃_           -- ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')

        ; equivFun      -- ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B

        ; equivProof    -- ∀ {ℓ ℓ'} (T : Set ℓ) (A : Set ℓ') (w : T ≃ A) (a : A) φ →
                        -- Partial φ (fiber (equivFun w) a) → fiber (equivFun w) a

        ; primGlue      -- ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I} (T : Partial φ (Set ℓ'))
                        -- → (e : PartialP φ (λ o → T o ≃ A)) → Set ℓ'

        ; prim^unglue   -- ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I} {T : Partial φ (Set ℓ')}
                        -- → {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A

        -- The ∀ operation on I. This is commented out as it is not currently used for anything
        -- ; primFaceForall -- (I → I) → I
        )
  renaming ( prim^glue   to glue         -- ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I} {T : Partial φ (Set ℓ')}
                                         -- → {e : PartialP φ (λ o → T o ≃ A)}
                                         -- → PartialP φ T → A → primGlue A T e

           ; pathToEquiv to lineToEquiv  -- ∀ {ℓ : → Level} (P : (i : I) → Set (ℓ i)) → P i0 ≃ P i1
           )

private
  variable
    ℓ ℓ' : Level

fiber : ∀ {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

equivIsEquiv : ∀ {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = snd e

equivCtr : ∀ {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .snd .equiv-proof y .fst

equivCtrPath : ∀ {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) (y : B) →
  (v : fiber (equivFun e) y) → Path _ (equivCtr e y) v
equivCtrPath e y = e .snd .equiv-proof y .snd

-- Uncurry Glue to make it more pleasant to use
Glue : ∀ (A : Set ℓ) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Set ℓ' ] T ≃ A))
       → Set ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

-- Make the φ argument of prim^unglue explicit
unglue : ∀ {A : Set ℓ} (φ : I) {T : Partial φ (Set ℓ')}
           {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}

-- The identity equivalence
idfun : ∀ {ℓ} → (A : Set ℓ) → A → A
idfun _ x = x

idIsEquiv : ∀ (A : Set ℓ) → isEquiv (idfun A)
equiv-proof (idIsEquiv A) y =
  ((y , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ i ∨ j))

idEquiv : ∀ (A : Set ℓ) → A ≃ A
idEquiv A = (idfun A , idIsEquiv A)

-- The ua constant
ua : ∀ {A B : Set ℓ} → A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                   ; (i = i1) → (B , idEquiv B) })


-- Proof of univalence using that unglue is an equivalence:

-- unglue is an equivalence
unglueIsEquiv : ∀ (A : Set ℓ) (φ : I)
                (f : PartialP φ (λ o → Σ[ T ∈ Set ℓ ] T ≃ A)) →
                isEquiv {A = Glue A f} (unglue φ)
equiv-proof (unglueIsEquiv A φ f) = λ (b : A) →
  let u : I → Partial φ A
      u i = λ{ (φ = i1) → equivCtr (f 1=1 .snd) b .snd (~ i) }
      ctr : fiber (unglue φ) b
      ctr = ( glue (λ { (φ = i1) → equivCtr (f 1=1 .snd) b .fst }) (hcomp u b)
            , λ j → hfill u (inc b) (~ j))
  in ( ctr
     , λ (v : fiber (unglue φ) b) i →
         let u' : I → Partial (φ ∨ ~ i ∨ i) A
             u' j = λ { (φ = i1) → equivCtrPath (f 1=1 .snd) b v i .snd (~ j)
                      ; (i = i0) → hfill u (inc b) j
                      ; (i = i1) → v .snd (~ j) }
         in ( glue (λ { (φ = i1) → equivCtrPath (f 1=1 .snd) b v i .fst }) (hcomp u' b)
            , λ j → hfill u' (inc b) (~ j)))

-- Any partial family of equivalences can be extended to a total one
-- from Glue [ φ ↦ (T,f) ] A to A
unglueEquiv : ∀ (A : Set ℓ) (φ : I)
              (f : PartialP φ (λ o → Σ[ T ∈ Set ℓ ] T ≃ A)) →
              (Glue A f) ≃ A
unglueEquiv A φ f = ( unglue φ , unglueIsEquiv A φ f )


-- The following is a formulation of univalence proposed by Martín Escardó:
-- https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ
-- See also Theorem 5.8.4 of the HoTT Book.
--
-- The reason we have this formulation in the core library and not the
-- standard one is that this one is more direct to prove using that
-- unglue is an equivalence. The standard formulation can be found in
-- Cubical/Basics/Univalence.
--
EquivContr : ∀ (A : Set ℓ) → isContr (Σ[ T ∈ Set ℓ ] T ≃ A)
EquivContr {ℓ = ℓ} A =
  ( ( A , idEquiv A)
  , λ w i → let f : PartialP (~ i ∨ i) (λ x → Σ[ T ∈ Set ℓ ] T ≃ A)
                f = λ { (i = i0) → A , idEquiv A ; (i = i1) → w }
            in ( Glue A f , unglueEquiv _ _ f) )
