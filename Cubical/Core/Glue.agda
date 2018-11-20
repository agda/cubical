{-

This file contains:

- Definitions of fibers and equivalences

- Glue types

- The identity equivalence and the ua constant

- Proof of univalence using that unglue is an equivalence ([EquivContr])


It should *not* depend on the Agda standard library

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Core.Glue where

open import Cubical.Core.Prelude

fiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y


private
  internalFiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
  internalFiber {A = A} f y = Σ[ x ∈ A ] y ≡ f x

  toInternalFiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → fiber f y → internalFiber f y
  toInternalFiber f y (x , p) = (x , sym p)

  fromInternalFiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {y : B} → internalFiber f y → fiber f y
  fromInternalFiber (x , p) = (x , sym p)

  toInternalFiberContr : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → isContr (fiber f y) → isContr (internalFiber f y)
  toInternalFiberContr f y (c , p) = toInternalFiber f y c , \ fb → cong (toInternalFiber f y) (p (fb .fst , sym (fb .snd)))

-- Make this a record so that isEquiv can be proved using
-- copatterns. This is good because copatterns don't get unfolded
-- unless a projection is applied so it should be more efficient.
record isEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ-max ℓ ℓ') where
  field
    equiv-proof : (y : B) → isContr (fiber f y)

open isEquiv public

infix 4 _≃_

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
A ≃ B = Σ[ f ∈ (A → B) ] (isEquiv f)

equivFun : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B
equivFun e = fst e

equivProof : ∀ {la lt} (T : Set la) (A : Set lt) → (w : T ≃ A) → (a : A)
            → ∀ ψ → (Partial ψ (internalFiber (w .fst) a)) → internalFiber (w .fst) a
equivProof A B w a ψ fb = contr' {A = internalFiber (w .fst) a} (toInternalFiberContr (w .fst) a (w .snd .equiv-proof a)) ψ fb
  where
    contr' : ∀ {ℓ} {A : Set ℓ} → isContr A → (φ : I) → (u : Partial φ A) → A
    contr' {A = A} (c , p) φ u = hcomp (λ i o → p (u o) i) c

equivIsEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = snd e

equivCtr : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .snd .equiv-proof y .fst

equivCtrPath : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) (y : B) →
  (v : fiber (equivFun e) y) → Path _ (equivCtr e y) v
equivCtrPath e y = e .snd .equiv-proof y .snd

-- TODO: Maybe change the internal definition of equivalence to "any
-- partial element can be extended to a total one"?
{-# BUILTIN EQUIV _≃_ #-}
{-# BUILTIN EQUIVFUN  equivFun #-}
{-# BUILTIN EQUIVPROOF equivProof #-}

-- This is a module so we can easily rename the primitives.
module GluePrims where
  primitive
    primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
      → (T : Partial φ (Set ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
      → Set ℓ'
    prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → PartialP φ T → A → primGlue A T e
    prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → primGlue A T e → A

    -- Needed for transp in Glue.
    primFaceForall : (I → I) → I

-- It doesn't seem necessary to uncurry glue and unglue as the curried
-- arguments are implicit
open GluePrims public
  renaming ( prim^glue to glue
           ; prim^unglue to unglue)

-- We uncurry Glue to make it a bit more pleasant to use
Glue : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Set ℓ' ] T ≃ A))
       → Set ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)


-- The identity equivalence
idIsEquiv : ∀ {ℓ} → (A : Set ℓ) → isEquiv (λ (a : A) → a)
equiv-proof (idIsEquiv A) y = (y , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ i ∨ j)

idEquiv : ∀ {ℓ} → (A : Set ℓ) → A ≃ A
idEquiv A = (λ a → a) , idIsEquiv A

-- The ua constant
ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
ua {_} {A} {B} e i =
  Glue B (λ {(i = i0) → _ , e ; (i = i1) → _ , idEquiv B})

-- Proof of univalence using that unglue is an equivalence:

-- unglue is an equivalence
unglueIsEquiv : ∀ {ℓ} (A : Set ℓ) (φ : I)
  (f : PartialP φ (λ o → Σ[ T ∈ Set ℓ ] T ≃ A)) → isEquiv {A = Glue A f} (unglue {φ = φ})
equiv-proof (unglueIsEquiv A φ f) = λ (b : A) →
  let u : I → Partial φ A
      u i = λ{ (φ = i1) → equivCtr (f 1=1 .snd) b .snd (~ i) }
      ctr : fiber (unglue {φ = φ}) b
      ctr = (glue (λ { (φ = i1) → equivCtr (f 1=1 .snd) b .fst }) (hcomp u b)
            , λ j → hfill u (inc b) (~ j))
  in ( ctr
     , λ (v : fiber (unglue {φ = φ}) b) i →
         let u' : I → Partial (φ ∨ ~ i ∨ i) A
             u' j = λ { (φ = i1) → equivCtrPath (f 1=1 .snd) b v i .snd (~ j)
                      ; (i = i0) → hfill u (inc b) j
                      ; (i = i1) → v .snd (~ j) }
         in ( glue (λ { (φ = i1) → equivCtrPath (f 1=1 .snd) b v i .fst }) (hcomp u' b)
            , λ j → hfill u' (inc b) (~ j)))

-- Any partial family of equivalences can be extended to a total one
-- from Glue [ φ ↦ (T,f) ] A to A
unglueEquiv : ∀ {ℓ} (A : Set ℓ) (φ : I)
                (f : PartialP φ (λ o → Σ[ T ∈ Set ℓ ] T ≃ A)) →
                (Glue A f) ≃ A
unglueEquiv A φ f = unglue {φ = φ} , unglueIsEquiv A φ f


-- The following is a formulation of univalence proposed by Martín Escardó:
-- https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ
-- See also Theorem 5.8.4 of the HoTT Book.
--
-- The reason we have this formulation in the core library and not the
-- standard one is that this one is more direct to prove using that
-- unglue is an equivalence. The standard formulation can (soon) be
-- found in Cubical/Basics/Univalence.
--
EquivContr : ∀ {ℓ} (A : Set ℓ) → isContr (Σ[ T ∈ Set ℓ ] T ≃ A)
EquivContr {ℓ} A = ( A , idEquiv A)
               , λ w i → let f : PartialP (~ i ∨ i) (λ x → Σ[ T ∈ Set ℓ ] T ≃ A)
                             f = λ { (i = i0) → A , idEquiv A ; (i = i1) → w }
                         in ( Glue A f , unglueEquiv _ _ f)

module _ {ℓ : I → Level} (P : (i : I) → Set (ℓ i)) where
  private
    E : (i : I) → Set (ℓ i)
    E  = λ i → P i
    ~E : (i : I) → Set (ℓ (~ i))
    ~E = λ i → P (~ i)

    A = P i0
    B = P i1

    f : A → B
    f x = transp E i0 x

    g : B → A
    g y = transp ~E i0 y

    u : ∀ i → A → E i
    u i x = transp (λ j → E (i ∧ j)) (~ i) x

    v : ∀ i → B → E i
    v i y = transp (λ j → ~E ( ~ i ∧ j)) i y

    fiberPath : (y : B) → (xβ0 xβ1 : fiber f y) → xβ0 ≡ xβ1
    fiberPath y (x0 , β0) (x1 , β1) k = ω , λ j → δ (~ j) where
      module _ (j : I) where
        private
          sys : A → ∀ i → PartialP (~ j ∨ j) (λ _ → E (~ i))
          sys x i (j = i0) = v (~ i) y
          sys x i (j = i1) = u (~ i) x
        ω0 = comp ~E (sys x0) (inc (β0 (~ j)))
        ω1 = comp ~E (sys x1) (inc (β1 (~ j)))
        θ0 = fill ~E (sys x0) (inc (β0 (~ j)))
        θ1 = fill ~E (sys x1) (inc (β1 (~ j)))
      sys = λ {j (k = i0) → ω0 j ; j (k = i1) → ω1 j}
      ω = hcomp sys (g y)
      θ = hfill sys (inc (g y))
      δ = λ (j : I) → comp E
            (λ i → λ { (j = i0) → v i y ; (k = i0) → θ0 j (~ i)
                     ; (j = i1) → u i ω ; (k = i1) → θ1 j (~ i) })
             (inc (θ j))

    γ : (y : B) → y ≡ f (g y)
    γ y j = comp E (λ i → λ { (j = i0) → v i y
                            ; (j = i1) → u i (g y) }) (inc (g y))

  lineToisEquiv : isEquiv f
  lineToisEquiv .equiv-proof y .fst .fst = g y
  lineToisEquiv .equiv-proof y .fst .snd = sym (γ y)
  lineToisEquiv .equiv-proof y .snd = fiberPath y _

  lineToEquiv : A ≃ B
  lineToEquiv .fst = f
  lineToEquiv .snd = lineToisEquiv

{-# BUILTIN PATHTOEQUIV lineToEquiv #-}
