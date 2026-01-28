{-

Please do not move this file. Changes should only be made if necessary.

This file contains pointers to the code examples and main results from
the paper:

Cellular Methods in Homotopy Type Theory


 ------------------------ How to read this file ---------------------------
|                                                                          |
|  Each definition, lemma, proposition, and theorem in the paper has a     |
|  corresponding term in this file. For instance, Definition 20 in the     |
|  paper corresponds to the Agda term Definition-20 below.                 |
|                                                                          |
|  A result ending with an asterisk (e.g. Definition-1*) is one that was   |
|  available in the Cubical Library prior to our formalisation.            |
|                                                                          |
|  Some results are not merged into the main part of the cubical library   |
|  and are directly formalised in this file instead.                       |
 --------------------------------------------------------------------------

 --------------- Differences between formalisation and paper --------------
|                                                                          |
|  The formalisation diverge (minimally) in places. In the paper, we have  |
|  prioritised readability to having a 1-1 correspondence with the         |
|  formalisation. Most notably, some smaller results and definitions that  |
|  appear in the paper are only used implicitly in the formalisation (for  |
|  instance, the definition of `good' CW complexes).                       |
 --------------------------------------------------------------------------

 -------------------------- Indexing conventions --------------------------
|                                                                          |
|  Note that certain indexing is off by 1 or 2:                            |
|  a) CW structure are off by one. Ex:                                     |
|       In Agda: C₀                                                        |
|       In the paper: C₋₁                                                  |
|  b) The definitions of truncations and connectedness are off by two. Ex: |
|       In Agda: 2-connected/truncated                                     |
|       In the paper: 0-connected/truncated                                |
|  c) Homotopy groups are off by 1. Ex:                                    |
|       In Agda: π₀                                                        |
|       In the paper: π₁                                                   |
 --------------------------------------------------------------------------
-}

module Cubical.Papers.CellularMethods where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed hiding (const∙)

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.HITs.Pushout hiding (cfcod)
open import Cubical.HITs.Wedge
open import Cubical.HITs.Susp
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.Truncation as TR hiding (∣_∣)
open import Cubical.HITs.PropositionalTruncation
  as PT renaming (∥_∥₁ to ∥_∥₋₁ ; ∣_∣₁ to ∣_∣₋₁)
open import Cubical.HITs.SetTruncation
  as ST renaming (∥_∥₂ to ∥_∥₀)
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.ChainComplex
open import Cubical.CW.Map
open import Cubical.CW.Homotopy
open import Cubical.CW.Connected
open import Cubical.CW.HurewiczTheorem
open import Cubical.CW.Approximation
open import Cubical.CW.Instances.Pushout
open import Cubical.CW.Homology.Groups.Sn
open import Cubical.CW.Homology.Groups.CofibFinSphereBouquetMap
open import Cubical.CW.Homology.Groups.Subcomplex
open import Cubical.CW.Instances.Unit
open import Cubical.CW.Homology.Base

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.PiSphereBouquet
open import Cubical.Homotopy.Group.PiCofibFinSphereBouquetMap

open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Int hiding (_+_)

open import Cubical.Relation.Nullary

open import Cubical.Algebra.ChainComplex
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup.FinitePresentation


-- some setup and abbreviations
private
  variable
    ℓ ℓ' : Level
    A B C : Type

open Iso

_↔_ : Type ℓ → Type ℓ' → Type _
A ↔ B = (A → B) × (B → A)

cfcod : {f : A → B} → B → cofib f
cfcod = inr

foldCofib : {f : A → B} → cofib f → Susp A
foldCofib (inl x) = north
foldCofib (inr x) = south
foldCofib (push a i) = merid a i

omitted : Unit
omitted = tt

CW₀ = CW ℓ-zero

-- As clarified in the paper, 'projective set' in the formalisation
-- only refers to finite sets for computational reasons:
pSet : Type₁
pSet = Σ[ A ∈ Type ] Σ[ n ∈ ℕ ] (A ≡ Fin n)

∣_∣ : pSet → ℕ
∣ (_ , n , _) ∣ = n

π'₊₂AbGr : (n : ℕ) (A : Pointed₀) → AbGroup ℓ-zero
π'₊₂AbGr n A = Group→AbGroup (π'Gr (suc n) A) (π'-comm n {A = A})

-------- 2 BACKGROUND --------
Definition-1* = Pushout

module Lemma-2 (f : A → B) where
    -- Lemma 2 (1) and (2) are re-formalised here to match the the
    -- statement in the article (in the library formalisation, A is
    -- assumed to be pointed which is superfluous)

  Lemma-2-[1] : cofib (cfcod {f = f}) ≃ Susp A
  Lemma-2-[1] = isoToEquiv main
    where
    C→ΣA : cofib cfcod → Susp A
    C→ΣA (inl x) = south
    C→ΣA (inr x) = foldCofib x
    C→ΣA (push a i) = south

    ΣA→C : Susp A → cofib cfcod
    ΣA→C north = inr (inl tt)
    ΣA→C south = inl tt
    ΣA→C (merid a i) = ((λ i → inr (push a i)) ∙ sym (push (f a))) i

    main : Iso (cofib cfcod) (Susp A)
    main .fun = C→ΣA
    main .inv = ΣA→C
    main .sec north = refl
    main .sec south = refl
    main .sec (merid a i) j = s j i
      where
      s : cong C→ΣA (cong ΣA→C (merid a)) ≡ merid a
      s = cong-∙ C→ΣA (λ i → inr (push a i)) (sym (push (f a)))
                 ∙ sym (rUnit _)
    main .ret (inl x) = refl
    main .ret (inr (inl x)) = refl
    main .ret (inr (inr x)) = push x
    main .ret (inr (push a i)) j =
      compPath-filler (λ i → inr (push a i)) (sym (push (f a))) (~ j) i
    main .ret (push a i) j = push a (i ∧ j)

  Lemma-2-[2] : (b : B) (p : f ≡ λ _ → b) → cofib f ≃ (Susp∙ A ⋁ (B , b))
  Lemma-2-[2] b p =
    compEquiv (pathToEquiv (cong cofib p))
              (isoToEquiv main)
    where
    C→⋁ : (cofib λ (a : A) → b) → (Susp∙ A ⋁ (B , b))
    C→⋁ (inl x) = inl south
    C→⋁ (inr x) = inr x
    C→⋁ (push a i) = ((λ j → inl (merid a (~ j))) ∙ push tt) i

    ⋁→C : Susp∙ A ⋁ (B , b) → cofib λ (a : A) → b
    ⋁→C (inl north) = inr b
    ⋁→C (inl south) = inl tt
    ⋁→C (inl (merid a i)) = push a (~ i)
    ⋁→C (inr x) = inr x
    ⋁→C (push a i) = inr b

    main : Iso (cofib λ _ → b) (Susp∙ A ⋁ (B , b))
    main .fun = C→⋁
    main .inv = ⋁→C
    main .sec (inl north) = sym (push tt)
    main .sec (inl south) = refl
    main .sec (inl (merid a i)) j =
      compPath-filler (λ j₁ → inl (merid a (~ j₁)))
                      (push tt) (~ j) (~ i)
    main .sec (inr x) = refl
    main .sec (push a i) j = push tt (~ j ∨ i)
    main .ret (inl x) = refl
    main .ret (inr x) = refl
    main .ret (push a i) j =
      ⋁→C (compPath-filler (λ j₁ → inl (merid a (~ j₁)))
                            (push tt) (~ j) i)

Lemma-3* = 3x3-span.3x3-Iso

CWstr = CWskel ℓ-zero

Lemma-4 = sphereToTrunc


------- 3 CW COMPLEXES IN HOTT -------

-- Note: CW structure are called `CWskel' in the library
Definition-5 = CWstr

-- Sequential colimits (for all types)
SeqColim* : Sequence ℓ-zero → Type
SeqColim* = SeqColim

-- For CW complexes
Definition-6 : CWstr → Type
Definition-6 = realise

Definition-7 = CW ℓ-zero

Definition-8 = cellMap

-- CW structures for pushouts.

-- Note: the formalisation uses a trick where the CW structures are
-- strictified (i.e. where the pushout condition is made to hold
-- strictly) and similarly for maps of CW structures -- in other
-- words, how structures and maps are treated in informal presentation
-- in the paper.

-- Basic idea: for every arrow C f→ D of CW structures, there is a
-- map.

-- See the following file for the strictification machinery (which we
-- omitted from the paper for the sake of conciseness).

open import Cubical.CW.Strictification
  using (strictCWskel ; strict≡ ; strictCwMap ; strictCwMap≡)

Definition-9 = CWPushout.pushoutSkel

-- A1 not mentioned explicitly because it holds trivially by
-- construction
Proposition-10 = CWPushout.pushoutIsoₜ

-- For completeness: pushouts of CW complexes are pushouts (no
-- strictification assumptions)
CWPushout = isPushoutᶜʷ

-- n-approximations: the presentation here is slightly different from
-- the paper (instead of saying that an n-approximation is a map on
-- subcomplexes f' : C⁽ⁿ⁾ -> D, we define it to be cellular map f_i :
-- C_i -> D_i which only is defined up for i ≤ n. This is of course
-- trivially equivalent but circumvents some of the technicalities of
-- working with subcomplexes explicitly.
Definition-11 = finCellApprox

Lemma-12 = isConnected-CW↪

Lemma-13 = isConnected-CW↪∞

Theorem-14 = CWmap→finCellMap

Corollary-15 = isPushoutᶜʷ

-- Definition 17 is included for the sake of presentation only and is
-- never actually used explicitly in the formalisation.
Definition-17 = omitted

Theorem-18 : ¬ ((C : CWstr) (D : CWstr)
               (f : realise C → realise D) (m : ℕ)
               → ∥ finCellApprox C D f m ∥₀)
Theorem-18 asm = snotz 0≡1
  where
  S¹fam : ℕ → Type
  S¹fam zero = ⊥
  S¹fam (suc zero) = Unit
  S¹fam (suc (suc n)) = S¹

  S¹card : ℕ → ℕ
  S¹card zero = 1
  S¹card (suc zero) = 1
  S¹card (suc (suc a)) = 0

  S¹str : CWstr
  S¹str .fst = S¹fam
  S¹str .snd .fst = S¹card
  S¹str .snd .snd .fst (suc zero) x = tt
  S¹str .snd .snd .snd .fst x = x
  S¹str .snd .snd .snd .snd zero =
    compEquiv Unit≃Fin1
      (compEquiv (isoToEquiv (PushoutEmptyFam (λ()) λ()))
        (symPushout _ _))
  S¹str .snd .snd .snd .snd (suc zero) =
    compEquiv
      (isoToEquiv (IsoSucSphereSusp 0))
       (compEquiv (Susp≃PushoutSusp* {ℓ-zero} {ℓ-zero} {ℓ-zero})
        (pushoutEquiv _ _ _ _
          (compEquiv (isoToEquiv (invIso lUnit×Iso))
            (Σ-cong-equiv Unit≃Fin1 λ _ → idEquiv _))
          (invEquiv Unit≃Unit*)
          (compEquiv (invEquiv Unit≃Unit*) Unit≃Fin1)
          refl refl))

  S¹str .snd .snd .snd .snd (suc (suc n)) =
    isoToEquiv (PushoutEmptyFam (λ()) λ())

  S¹str∞ : S¹ ≃ realise S¹str
  S¹str∞ = _ , converges→isEquivIncl 2 λ m
    → transport (λ i → isEquiv (CW↪ S¹str (+-comm 2 m i)))
                 (idEquiv _ .snd)

  open FinSequenceMap
  module _ (x : realise S¹str)
    (ϕ : finCellApprox {ℓ-zero} CWskelUnit* S¹str (λ _ → x) 2) where

    const∙ : finCellMap 2 {ℓ = ℓ-zero} CWskelUnit* S¹str
    const∙ .fmap (suc zero , s) x = tt
    const∙ .fmap (suc (suc zero) , s) x = base
    const∙ .fcomm (suc zero , s) x = refl

    const∙≡ϕ : fst ϕ ≡ const∙
    const∙≡ϕ i .fmap (suc zero , s) t = tt
    const∙≡ϕ i .fmap (suc (suc zero) , tt) tt* =
      fcomm (fst ϕ) 1 tt* (~ i)
    const∙≡ϕ i .fcomm (suc zero , s) tt* j =
      fcomm (fst ϕ) 1 tt* (~ i ∧ j)

    lem2 : (x : FinSeqColim {ℓ-zero} 2 (realiseSeq CWskelUnit*)) →
        FinSeqColim→Colim 2
         (finCellMap→FinSeqColim CWskelUnit* S¹str const∙ x)
      ≡ incl {n = suc zero} tt
    lem2 (fincl (suc zero , tt) x) = refl
    lem2 (fincl (suc (suc zero) , t) x) j =
      FinSeqColim→Colim 2 ((sym (fpush 1 tt) ∙ refl) j)
    lem2 (fpush (suc zero , t) x i) j =
      FinSeqColim→Colim 2 ((sym (fpush 1 tt) ∙ refl) (~ i ∨ j))

    contrS¹ : incl base ≡ x
    contrS¹ = sym (push tt)
            ∙ funExt⁻ (sym (funExt lem2)
            ∙ (λ i x → FinSeqColim→Colim 2
                        (finCellMap→FinSeqColim CWskelUnit* S¹str
                         (const∙≡ϕ (~ i)) x))
            ∙ snd ϕ) (fincl 1 tt*)

  main : isSet S¹
  main = subst isSet (sym (ua S¹str∞))
           (PT.rec (isPropIsOfHLevel 2)
           (λ F → subst isSet (ua S¹str∞) (isProp→isSet (isContr→isProp (base , F))))
           (sphereToTrunc 2 lem'))
    where
    lem : (x : realise S¹str) → ∥ incl base ≡ x ∥ 2
    lem x = ST.rec (isOfHLevelTrunc 2) (∣_∣ₕ ∘ contrS¹ x)
                   (asm (CWskelUnit* {ℓ-zero}) S¹str (λ _ → x) 2)

    lem' : (x : S¹) → ∥ base ≡ x ∥ 2
    lem' = transport (λ i → (x : ua S¹str∞ (~ i))
                          → ∥ ua-gluePt S¹str∞ (~ i) base ≡ x ∥ 2)
                     lem


  0≡1 : suc zero ≡ zero
  0≡1 i = abs (transport (cong helix (main _ _ loop refl i)) 0)


Definition-19 = cellHom

-- Note: The same comment as the one above Definition-11 applies to
-- the definition of n-approximations of homotopies too.
Definition-20 = finCellHomRel

-- Note: for the second cellular approximation theorem, the square in
-- the definition of cellular n-approximations is omitted – it is only
-- there to strengthen the induction hypothesis of the proof and is
-- never actually used later on. For the technical statement (the main
-- part of the proof) where this square is present, see
-- pathToCellularHomotopy-main.
Theorem-21 = pathToCellularHomotopy

-- Corollary 22 is only included for the sake of presentation and is
-- never used in the formalisation
Corollary-22 = omitted

-------- 4 Cellular homology --------
Definition-23* = ChainComplex

Definition-24* = ChainComplexMap

Definition-25* = ChainHomotopy

Definition-26* = homology

Definition-27 = SphereBouquet

Proposition-28-[1] = degreeSusp
Proposition-28-[2] = degreeComp

Proposition-29 = πₙ⋁Sⁿ≅ℤ[]

-- defintion of bouquet degree
bdeg = bouquetDegree

Proposition-30-[1] = bouquetDegree∙Π
Proposition-30-[2] = bouquetDegreeSusp
Proposition-30-[3] = bouquetDegreeComp

Proposition-31 = ∂∂≡0

-- Note: To fit better into the library, the following lemma is proved
-- for finite maps (since this is the only application). The proof is
-- completely modular and does not rely on this finiteness assumption.
Proposition-32 = cellHom-to-ChainHomotopy

-- For completeness, here is the final homology functor:
on-object = H̃ᶜʷ
on-arrow = H̃ᶜʷ→
functoriality-[id] = H̃ᶜʷ→id
functoriality-[comp] = H̃ᶜʷ→comp


------- 5 THE HUREWICZ THEOREMS -------
Definition-34 : ∀ {ℓ} (n : ℕ) → Type ℓ → Type (ℓ-suc ℓ)
Definition-34 n C = ∥ isConnectedCW n C ∥₋₁
-- renaming
isHurewicz_-Connected = Definition-34

Lemma-35-[1] = connectedCWContr
Lemma-35-[2] = connectedCW≃SphereBouquet

-- The following 5 results are only included to increase readability
-- of the proof and are only used implicitly in the formalisation.
Lemma-35-[3] = omitted
Proposition-36 = omitted
Definition-37 = omitted
Lemma-38 = omitted
Proposition-39 = omitted

Theorem-39 = makeConnectedCW

Corollary-40 : ∀ {ℓ} (n : ℕ) {C : Type ℓ}
  → hasCWskel C
  → isConnected (2 + n) C
  ↔ isHurewicz n -Connected C
Corollary-40 n {C} Cstr .fst = makeConnectedCW n Cstr
Corollary-40 n {C} Cstr' .snd =
  PT.rec isPropIsContr
    λ { ((C' , ((card , α , emp' , e') , pted , p)) , e)
      → subst (isConnected (2 + n)) (ua e)
         (isOfHLevelRetractFromIso 0
           (compIso (invIso (connectedTruncIso _ _
             (isConnected-CW↪∞ (2 + n) (C' , card , α , emp' , e'))))
              (mapCompIso (equivToIso (connectedCW≃SphereBouquet n C
                ((C' , (card , α , emp' , e') , pted , p) , e)))))
           isConnectedSphereBouquet')}

Definition-42 = HurewiczHomAb

-- The following result is included for the sake of presentation only
-- and is only used implicitly in the proof of the Hurewicz theorem.
Proposition-43 = omitted

Theorem-44 = HurewiczTheorem

Theorem-45 : (C : CW₀) (⋆ : fst C) (n : ℕ) → isConnected (3 + n) (fst C)
  → ∃[ A ∈ pSet ] ∃[ B ∈ pSet ]
     ∃[ α ∈ AbGroupHom ℤ[Fin ∣ A ∣ ] ℤ[Fin ∣ B ∣ ] ]
     AbGroupIso (π'₊₂AbGr n ((fst C) , ⋆)) (ℤ[Fin ∣ B ∣ ] /Im α)
Theorem-45 (C , isCW) ⋆ n isc =
  PT.rec squash₁
    (λ { record { nGens = n
                ; nRels = m
                ; rels = r
                ; fpiso = e } →
    ∣ (Fin m , m , refl)
  , ∣ (((Fin n) , (n , refl))
  , ∣ r , e ∣₋₁) ∣₋₁ ∣₋₁})
    (isFinitelyPresented-π'connectedCW (C , ⋆) isCW n isc)
  where
  open FinitePresentation
