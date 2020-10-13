{-

Automatically generating proofs of UnivalentStr for records

-}
{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Structures.Record where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.List as List
open import Cubical.Data.Bool
open import Cubical.Data.Maybe
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro

import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base

-- Magic number
private
  FUEL = 10000

-- Types for specifying inputs to the tactics

data AutoFieldSpec : Typeω where
  autoFieldSpec : ∀ {ℓ ℓ₁ ℓ₂} (R : Type ℓ → Type ℓ₁) {S : Type ℓ → Type ℓ₂}
    → ({X : Type ℓ} → R X → S X)
    → AutoFieldSpec

module _ {ℓ ℓ₁ ℓ₁'} where

  data AutoDataFields (R : Type ℓ → Type ℓ₁) (ι : StrEquiv R ℓ₁')
    : Typeω
    where
    [] : AutoDataFields R ι
    data[_∣_]∷_ : ∀ {ℓ₂ ℓ₂'} {S : Type ℓ → Type ℓ₂} {ι' : StrEquiv S ℓ₂'}
      → (f : {X : Type ℓ} → R X → S X)
      → ({A B : TypeWithStr ℓ R} {e : typ A ≃ typ B} → ι A B e → ι' (map-snd f A) (map-snd f B) e)
      → AutoDataFields R ι
      → AutoDataFields R ι

  GatherDataFieldsLevel : {R : Type ℓ → Type ℓ₁} {ι : StrEquiv R ℓ₁'}
    → AutoDataFields R ι
    → Level
  GatherDataFieldsLevel [] = ℓ-zero
  GatherDataFieldsLevel (data[_∣_]∷_ {ℓ₂ = ℓ₂} _ _ fs) = ℓ-max ℓ₂ (GatherDataFieldsLevel fs)

  GatherDataFields : {R : Type ℓ → Type ℓ₁} {ι : StrEquiv R ℓ₁'}
    (dat : AutoDataFields R ι)
    → Type ℓ → Type (GatherDataFieldsLevel dat)
  GatherDataFields [] X = Unit
  GatherDataFields (data[_∣_]∷_ {S = S} _ _ fs) X = S X × GatherDataFields fs X

  projectDataFields : {R : Type ℓ → Type ℓ₁} {ι : StrEquiv R ℓ₁'}
    (fs : AutoDataFields R ι)
    → {X : Type ℓ} → R X → GatherDataFields fs X
  projectDataFields [] = _
  projectDataFields (data[ f ∣ _ ]∷ fs) r =
    f r , projectDataFields fs r

  isPropProperty : ∀ {ℓ₂} (R : Type ℓ → Type ℓ₁)
    (ι : StrEquiv R ℓ₁')
    (fs : AutoDataFields R ι)
    (P : (X : Type ℓ) → GatherDataFields fs X → Type ℓ₂)
    → Type (ℓ-max (ℓ-suc ℓ) (ℓ-max ℓ₁ ℓ₂))
  isPropProperty R ι fs P =
    {X : Type ℓ} (r : R X) → isProp (P X (projectDataFields fs r))

  data AutoPropertyFields (R : Type ℓ → Type ℓ₁) (ι : StrEquiv R ℓ₁')
    (fs : AutoDataFields R ι)
    : Typeω
    where
    [] : AutoPropertyFields R ι fs
    prop[_∣_]∷_ : ∀ {ℓ₂} {P : (X : Type ℓ) → GatherDataFields fs X → Type ℓ₂}
      → ({X : Type ℓ} (r : R X) → P X (projectDataFields fs r))
      → isPropProperty R ι fs P
      → AutoPropertyFields R ι fs
      → AutoPropertyFields R ι fs

  data AutoRecordSpec : Typeω where
    autoRecordSpec : (R : Type ℓ → Type ℓ₁) (ι : StrEquiv R ℓ₁')
      (fs : AutoDataFields R ι)
      → AutoPropertyFields R ι fs
      → AutoRecordSpec

-- Some reflection utilities
private
  tApply : R.Term → List (R.Arg R.Term) → R.Term
  tApply t l = R.def (quote idfun) (R.unknown v∷ t v∷ l)

  tStrMap : R.Term → R.Term → R.Term
  tStrMap A f = R.def (quote map-snd) (f v∷ A v∷ [])

  tStrProj : R.Term → R.Name → R.Term
  tStrProj A sfield = tStrMap A (R.def sfield [])

  Fun : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
  Fun A B = A → B

-- Helper functions used in the generated univalence proof
private
  pathMap : ∀ {ℓ ℓ'} {S : I → Type ℓ} {T : I → Type ℓ'} (f : {i : I} → S i → T i)
    {x : S i0} {y : S i1} → PathP S x y → PathP T (f x) (f y)
  pathMap f p i = f (p i)

  -- Property fields
  module _
    {ℓ ℓ₁ ℓ₁' ℓ₂}
    (R : Type ℓ → Type ℓ₁) -- Structure record
    (ι : StrEquiv R ℓ₁') -- Equivalence record
    (fs : AutoDataFields R ι) -- Data fields
    (P : (X : Type ℓ) → GatherDataFields fs X → Type ℓ₂) -- Property type
    (f : {X : Type ℓ} (r : R X) → P X (projectDataFields fs r)) -- Property projection
    where

    dat = projectDataFields fs
    Dat = GatherDataFields fs

    PropHelperCenterType : Type _
    PropHelperCenterType =
      (A B : TypeWithStr ℓ R) (e : A .fst ≃ B .fst)
      (p : PathP (λ i → Dat (ua e i)) (dat (A .snd)) (dat (B .snd)))
      → PathP (λ i → P (ua e i) (p i)) (f (A .snd)) (f (B .snd))

    PropHelperContractType : PropHelperCenterType → Type _
    PropHelperContractType c =
      (A B : TypeWithStr ℓ R) (e : A .fst ≃ B .fst)
      {p₀ : PathP (λ i → Dat (ua e i)) (dat (A .snd)) (dat (B .snd))}
      (q : PathP (λ i → R (ua e i)) (A .snd) (B .snd))
      (p : p₀ ≡ (λ i → projectDataFields fs (q i)))
      → PathP (λ k → PathP (λ i → P (ua e i) (p k i)) (f (A .snd)) (f (B .snd)))
        (c A B e p₀)
        (λ i → f (q i))

    PropHelperType : Type _
    PropHelperType =
      Σ PropHelperCenterType PropHelperContractType

    derivePropHelper : isPropProperty R ι fs P → PropHelperType
    derivePropHelper propP .fst A B e p =
      isOfHLevelPathP' 0 (propP _) (f (A .snd)) (f (B .snd)) .fst
    derivePropHelper propP .snd A B e q p =
      isOfHLevelPathP' 0 (isOfHLevelPathP 1 (propP _) _ _) _ _ .fst

  -- Build proof of univalence from an isomorphism
  module _ {ℓ ℓ₁ ℓ₁'} (S : Type ℓ → Type ℓ₁) (ι : StrEquiv S ℓ₁') where

    fwdShape : Type _
    fwdShape =
      (A B : TypeWithStr ℓ S) (e : typ A ≃ typ B) → ι A B e → PathP (λ i → S (ua e i)) (str A) (str B)

    bwdShape : Type _
    bwdShape =
      (A B : TypeWithStr ℓ S) (e : typ A ≃ typ B) → PathP (λ i → S (ua e i)) (str A) (str B) → ι A B e

    fwdBwdShape : fwdShape → bwdShape → Type _
    fwdBwdShape fwd bwd =
      (A B : TypeWithStr ℓ S) (e : typ A ≃ typ B) → ∀ p → fwd A B e (bwd A B e p) ≡ p

    bwdFwdShape : fwdShape → bwdShape → Type _
    bwdFwdShape fwd bwd =
      (A B : TypeWithStr ℓ S) (e : typ A ≃ typ B) → ∀ r → bwd A B e (fwd A B e r) ≡ r

    -- The implicit arguments A,B in UnivalentStr make some things annoying so let's avoid them
    ExplicitUnivalentStr : Type _
    ExplicitUnivalentStr =
      (A B : TypeWithStr _ S) (e : typ A ≃ typ B) → ι A B e ≃ PathP (λ i → S (ua e i)) (str A) (str B)

    explicitUnivalentStr : (fwd : fwdShape) (bwd : bwdShape)
      → fwdBwdShape fwd bwd → bwdFwdShape fwd bwd
      → ExplicitUnivalentStr
    explicitUnivalentStr fwd bwd fwdBwd bwdFwd A B e = isoToEquiv isom
      where
      open Iso
      isom : Iso _ _
      isom .fun = fwd A B e
      isom .inv = bwd A B e
      isom .rightInv = fwdBwd A B e
      isom .leftInv = bwdFwd A B e

  ExplicitUnivalentDesc : ∀ ℓ → (d : Desc ℓ) → Type _
  ExplicitUnivalentDesc _ d =
    ExplicitUnivalentStr (MacroStructure d) (MacroEquivStr d)

  explicitUnivalentDesc : ∀ ℓ → (d : Desc ℓ) → ExplicitUnivalentDesc ℓ d
  explicitUnivalentDesc _ d A B e = MacroUnivalentStr d e

-- Internal record specification type
private
  record TypedTerm : Type where
    field
      type : R.Term
      term : R.Term

  record InternalDatumField (A : Type) : Type where
    field
      sfield : R.Name -- name of structure field
      efield : R.Name -- name of equivalence field
      payload : A

  record InternalPropField (A : Type) : Type where
    field
      sfield : R.Name -- name of structure field
      payload : A

  record InternalSpec (A : Type) : Type where
    field
      srec : R.Term -- structure record type
      erec : R.Term -- equivalence record type
      datums : List (InternalDatumField A)
      props : List (InternalPropField A)

  open TypedTerm
  open InternalDatumField
  open InternalPropField

  mapDatumField : ∀ {A B : Type} → (A → B) → InternalDatumField A → InternalDatumField B
  mapDatumField f dat .sfield = dat .sfield
  mapDatumField f dat .efield = dat .efield
  mapDatumField f dat .payload = f (dat .payload)

  mapPropField : ∀ {A B : Type} → (A → B) → InternalPropField A → InternalPropField B
  mapPropField f prop .sfield = prop .sfield
  mapPropField f prop .payload = f (prop .payload)

-- Parse a field and record specifications
private
  findName : R.Term → R.TC R.Name
  findName (R.def name _) = R.returnTC name
  findName (R.lam R.hidden (R.abs _ t)) = findName t
  findName t = R.typeError (R.strErr "Not a name + spine: " ∷ R.termErr t ∷ [])

  parseFieldSpec : R.Term → R.TC (R.Term × R.Term × R.Term × R.Term)
  parseFieldSpec (R.con (quote autoFieldSpec) (ℓ h∷ ℓ₁ h∷ ℓ₂ h∷ R v∷ S h∷ f v∷ [])) =
    R.reduce ℓ >>= λ ℓ →
    R.returnTC (ℓ , ℓ₂ , S , f)
  parseFieldSpec t =
    R.typeError (R.strErr "Malformed field specification: " ∷ R.termErr t ∷ [])

  parseSpec : R.Term → R.TC (InternalSpec TypedTerm)
  parseSpec (R.con (quote autoRecordSpec) (ℓ h∷ ℓ₁ h∷ ℓ₁' h∷ srecTerm v∷ erecTerm v∷ fs v∷ ps v∷ [])) =
    parseData fs >>= λ fs' →
    parseProperties ps >>= λ ps' →
    R.returnTC λ { .srec → srecTerm ; .erec → erecTerm ; .datums → fs' ; .props → ps' }
    where
    open InternalSpec

    parseData : R.Term → R.TC (List (InternalDatumField TypedTerm))
    parseData (R.con (quote AutoDataFields.[]) _) = R.returnTC []
    parseData (R.con (quote data[_∣_]∷_)
      (ℓ h∷ ℓ₁ h∷ ℓ₁' h∷ R h∷ ι h∷ ℓ₂ h∷ ℓ₂' h∷ S h∷ ι' h∷ sfieldTerm v∷ efieldTerm v∷ fs v∷ []))
      =
      R.reduce ℓ >>= λ ℓ →
      findName sfieldTerm >>= λ sfieldName →
      findName efieldTerm >>= λ efieldName →
      buildDesc FUEL ℓ ℓ₂ S >>= λ d →
      let
        f : InternalDatumField TypedTerm
        f = λ
          { .sfield → sfieldName
          ; .efield → efieldName
          ; .payload .type → R.def (quote ExplicitUnivalentDesc) (ℓ v∷ d v∷ [])
          ; .payload .term → R.def (quote explicitUnivalentDesc) (ℓ v∷ d v∷ [])
          }
      in
      liftTC (f ∷_) (parseData fs)
    parseData t = R.typeError (R.strErr "Malformed autoRecord specification (1): " ∷ R.termErr t ∷ [])

    parseProperties : R.Term → R.TC (List (InternalPropField TypedTerm))
    parseProperties (R.con (quote AutoPropertyFields.[]) _) = R.returnTC []
    parseProperties (R.con (quote prop[_∣_]∷_)
      (ℓ h∷ ℓ₁ h∷ ℓ₁' h∷ R h∷ ι h∷ _ h∷ ℓ₂ h∷ P h∷ fieldTerm v∷ prop v∷ ps v∷ []))
      =
      findName fieldTerm >>= λ fieldName →
      let
        p : InternalPropField TypedTerm
        p = λ
          { .sfield → fieldName
          ; .payload .type →
            R.def (quote PropHelperType) (srecTerm v∷ erecTerm v∷ fs v∷ P v∷ fieldTerm v∷ [])
          ; .payload .term →
            R.def (quote derivePropHelper) (srecTerm v∷ erecTerm v∷ fs v∷ P v∷ fieldTerm v∷ prop v∷ [])
          }
      in
      liftTC (p ∷_) (parseProperties ps)
    parseProperties t = R.typeError (R.strErr "Malformed autoRecord specification (2): " ∷ R.termErr t ∷ [])

  parseSpec t = R.typeError (R.strErr "Malformed autoRecord specification (3): " ∷ R.termErr t ∷ [])

-- Build a proof of univalence from an InternalSpec
module _ (spec : InternalSpec ℕ) where
  open InternalSpec spec
  private

    fwdDatum : (A B e streq i : R.Term) → InternalDatumField ℕ → R.Term
    fwdDatum A B e streq i dat =
      R.def (quote equivFun)
        (tApply (v (dat .payload)) (tStrProj A (dat .sfield) v∷ tStrProj B (dat .sfield) v∷ e v∷ [])
          v∷ R.def (dat .efield) (streq v∷ [])
          v∷ i
          v∷ [])

    fwdProperty : (dataPath A B e streq i : R.Term) → InternalPropField ℕ → R.Clause
    fwdProperty dataPath A B e streq i prop =
      R.clause [] (R.proj (prop .sfield) v∷ [])
        (R.def (quote fst) (v (prop .payload) v∷ A v∷ B v∷ e v∷ dataPath v∷ i v∷ []))

    bwdDatum : (A B e q : R.Term) → InternalDatumField ℕ → R.Clause
    bwdDatum A B e q dat =
      R.clause [] (R.proj (dat .efield) v∷ [])
        (R.def (quote invEq)
          (tApply
            (v (dat .payload))
            (tStrProj A (dat .sfield) v∷ tStrProj B (dat .sfield) v∷ e v∷ [])
            v∷ R.def (quote pathMap) (R.def (dat .sfield) [] v∷ q v∷ [])
            v∷ []))

    fwdBwdDatum : (A B e q k i : R.Term) → InternalDatumField ℕ → R.Term
    fwdBwdDatum A B e q k i dat =
      R.def (quote retEq)
        (tApply
          (v (dat .payload))
          (tStrProj A (dat .sfield) v∷ tStrProj B (dat .sfield) v∷ e v∷ [])
          v∷ R.def (quote pathMap) (R.def (dat .sfield) [] v∷ q v∷ [])
          v∷ k v∷ i
          v∷ [])

    fwdBwdProperty : (dataPath A B e q k i : R.Term) → InternalPropField ℕ → R.Clause
    fwdBwdProperty dataPath A B e q k i prop =
      R.clause [] (R.proj (prop .sfield) v∷ [])
        (R.def (quote snd) (v (prop .payload) v∷ A v∷ B v∷ e v∷ q v∷ dataPath v∷ k v∷ i v∷ []))

    bwdFwdDatum : (A B e streq k : R.Term) → InternalDatumField ℕ → R.Clause
    bwdFwdDatum A B e streq k dat =
      R.clause [] (R.proj (dat .efield) v∷ [])
        (R.def (quote secEq)
          (tApply
            (v (dat .payload))
            (tStrProj A (dat .sfield) v∷ tStrProj B (dat .sfield) v∷ e v∷ [])
            v∷ R.def (dat .efield) (streq v∷ [])
            v∷ k
            v∷ []))

    dataSigmaPatterns : List (List (R.Arg R.Pattern))
    dataSigmaPatterns = go (List.length datums) []
      where
      go : ℕ → List (R.Arg R.Pattern) → List (List (R.Arg R.Pattern))
      go zero prefix = [ prefix ]
      go (suc n) prefix =
        (prefix ∷ʳ varg (R.proj (quote fst)))
        ∷ go n (prefix ∷ʳ varg (R.proj (quote snd)))

    fwd : R.Term
    fwd =
      vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "i" (R.pat-lam body [])))))
      where
      dataClauses : List R.Clause
      dataClauses =
        List.map
          (λ dat →
            R.clause [] [ varg (R.proj (dat .sfield)) ]
              (fwdDatum (v 4) (v 3) (v 2) (v 1) (v 0) (mapDatumField (5 +_) dat)))
          datums

      dataSigmaTerm : R.Term
      dataSigmaTerm =
        vlam "i"
          (R.pat-lam
            (List.map2 (R.clause [])
              dataSigmaPatterns
              (List.map (fwdDatum (v 5) (v 4) (v 3) (v 2) (v 0) ∘ mapDatumField (6 +_)) datums
                ∷ʳ R.con (quote tt) []))
            [])

      body : List R.Clause
      body =
        dataClauses
        ++
        List.map
          (fwdProperty dataSigmaTerm (v 4) (v 3) (v 2) (v 1) (v 0) ∘ mapPropField (5 +_))
          props

    bwd : R.Term
    bwd =
      vlam "A" (vlam "B" (vlam "e" (vlam "q" (R.pat-lam body []))))
      where
      body : List R.Clause
      body = List.map (bwdDatum (v 3) (v 2) (v 1) (v 0) ∘ mapDatumField (4 +_)) datums

    fwdBwd : R.Term
    fwdBwd =
      vlam "A" (vlam "B" (vlam "e" (vlam "q" (vlam "k" (vlam "i" (R.pat-lam body []))))))
      where
      dataClauses : List R.Clause
      dataClauses =
        List.map
          (λ dat →
            R.clause [] [ varg (R.proj (dat .sfield)) ]
              (fwdBwdDatum (v 5) (v 4) (v 3) (v 2) (v 1) (v 0) (mapDatumField (6 +_) dat)))
          datums

      dataSigmaTerm : R.Term
      dataSigmaTerm =
        vlam "k"
          (vlam "i"
            (R.pat-lam
              (List.map2 (R.clause [])
                dataSigmaPatterns
                (List.map (fwdBwdDatum (v 7) (v 6) (v 5) (v 4) (v 1) (v 0) ∘ mapDatumField (8 +_)) datums
                  ∷ʳ R.con (quote tt) []))
              []))

      body : List R.Clause
      body =
        dataClauses
        ++
        List.map
          (fwdBwdProperty dataSigmaTerm (v 5) (v 4) (v 3) (v 2) (v 1) (v 0) ∘ mapPropField (6 +_))
          props

    bwdFwd : R.Term
    bwdFwd =
      vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "k" (R.pat-lam body [])))))
      where
      body : List R.Clause
      body = List.map (bwdFwdDatum (v 4) (v 3) (v 2) (v 1) (v 0) ∘ mapDatumField (5 +_)) datums

  univalentRecord : R.Term
  univalentRecord =
    R.def (quote explicitUnivalentStr)
      (R.unknown v∷ R.unknown v∷ fwd v∷ bwd v∷ fwdBwd v∷ bwdFwd v∷ [])

macro
  autoFieldEquiv : R.Term → R.Term → R.Term → R.Term → R.TC Unit
  autoFieldEquiv spec A B hole =
    (R.reduce spec >>= parseFieldSpec) >>= λ (ℓ , ℓ₂ , S , f) →
    buildDesc FUEL ℓ ℓ₂ S >>= λ d →
    R.unify hole (R.def (quote MacroEquivStr) (d v∷ tStrMap A f v∷ tStrMap B f v∷ []))

  autoUnivalentRecord : R.Term → R.Term → R.TC Unit
  autoUnivalentRecord t hole =
    (R.reduce t >>= parseSpec) >>= λ spec → R.unify (main spec) hole
    where
    module _ (spec : InternalSpec TypedTerm) where
      open InternalSpec spec

      mapDown : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (ℕ → A → B) → ℕ → List A → List B
      mapDown f _ [] = []
      mapDown f n (x ∷ xs) = f (predℕ n) x ∷ mapDown f (predℕ n) xs

      closureSpec : InternalSpec ℕ
      closureSpec .InternalSpec.srec = srec
      closureSpec .InternalSpec.erec = erec
      closureSpec .InternalSpec.datums =
        mapDown (λ n → mapDatumField (λ _ → n)) (List.length datums + List.length props) datums
      closureSpec .InternalSpec.props =
        mapDown (λ n → mapPropField (λ _ → n)) (List.length props) props

      closure : R.Term
      closure =
        iter (List.length datums + List.length props) (vlam "") (univalentRecord closureSpec)

      env : List (R.Arg R.Term)
      env = List.map (varg ∘ term ∘ payload) datums ++ List.map (varg ∘ term ∘ payload) props

      closureTy : R.Term
      closureTy =
        List.foldr
          (λ ty cod → R.def (quote Fun) (ty v∷ cod v∷ []))
          (R.def (quote ExplicitUnivalentStr) (srec v∷ erec v∷ []))
          (List.map (type ∘ payload) datums ++ List.map (type ∘ payload) props)

      main : R.Term
      main = R.def (quote idfun) (closureTy v∷ closure v∷ env)
