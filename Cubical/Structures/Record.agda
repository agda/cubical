{-

Automatically generating proofs of UnivalentStr for records

-}
{-# OPTIONS --no-exact-split --safe #-}
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
open import Cubical.Data.Vec as Vec
open import Cubical.Data.Bool
open import Cubical.Data.Maybe
open import Cubical.Data.Sum
open import Cubical.Structures.Auto
import Cubical.Structures.Macro as M
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
  mutual
    data AutoFields (R : Type ℓ → Type ℓ₁) (ι : StrEquiv R ℓ₁') : Typeω
      where
      fields: : AutoFields R ι
      _data[_∣_] : (fs : AutoFields R ι)
        → ∀ {ℓ₂ ℓ₂'} {S : Type ℓ → Type ℓ₂} {ι' : StrEquiv S ℓ₂'}
        → (f : {X : Type ℓ} → R X → S X)
        → ({A B : TypeWithStr ℓ R} {e : typ A ≃ typ B} → ι A B e → ι' (map-snd f A) (map-snd f B) e)
        → AutoFields R ι
      _prop[_∣_] : (fs : AutoFields R ι)
        → ∀ {ℓ₂} {P : (X : Type ℓ) → GatherFields fs X → Type ℓ₂}
        → ({X : Type ℓ} (r : R X) → P X (projectFields fs r))
        → isPropProperty R ι fs P
        → AutoFields R ι

    GatherFieldsLevel : {R : Type ℓ → Type ℓ₁} {ι : StrEquiv R ℓ₁'}
      → AutoFields R ι
      → Level
    GatherFieldsLevel fields: = ℓ-zero
    GatherFieldsLevel (_data[_∣_] fs {ℓ₂ = ℓ₂} _ _) = ℓ-max (GatherFieldsLevel fs) ℓ₂
    GatherFieldsLevel (_prop[_∣_] fs {ℓ₂ = ℓ₂} _ _) = ℓ-max (GatherFieldsLevel fs) ℓ₂

    GatherFields : {R : Type ℓ → Type ℓ₁} {ι : StrEquiv R ℓ₁'}
      (dat : AutoFields R ι)
      → Type ℓ → Type (GatherFieldsLevel dat)
    GatherFields fields: X = Unit
    GatherFields (_data[_∣_] fs {S = S} _ _) X = GatherFields fs X × S X
    GatherFields (_prop[_∣_] fs {P = P} _ _) X =
      Σ[ s ∈ GatherFields fs X ] (P X s)

    projectFields : {R : Type ℓ → Type ℓ₁} {ι : StrEquiv R ℓ₁'}
      (fs : AutoFields R ι)
      → {X : Type ℓ} → R X → GatherFields fs X
    projectFields fields: = _
    projectFields (fs data[ f ∣ _ ]) r = projectFields fs r , f r
    projectFields (fs prop[ f ∣ _ ]) r = projectFields fs r , f r

    isPropProperty : ∀ {ℓ₂} (R : Type ℓ → Type ℓ₁)
      (ι : StrEquiv R ℓ₁')
      (fs : AutoFields R ι)
      (P : (X : Type ℓ) → GatherFields fs X → Type ℓ₂)
      → Type (ℓ-max (ℓ-suc ℓ) (ℓ-max ℓ₁ ℓ₂))
    isPropProperty R ι fs P =
      {X : Type ℓ} (r  : R X) → isProp (P X (projectFields fs r))

  data AutoRecordSpec : Typeω where
    autoRecordSpec : (R : Type ℓ → Type ℓ₁) (ι : StrEquiv R ℓ₁')
      → AutoFields R ι
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

  -- Property field helper functions
  module _
    {ℓ ℓ₁ ℓ₁' ℓ₂}
    (R : Type ℓ → Type ℓ₁) -- Structure record
    (ι : StrEquiv R ℓ₁') -- Equivalence record
    (fs : AutoFields R ι) -- Prior fields
    (P : (X : Type ℓ) → GatherFields fs X → Type ℓ₂) -- Property type
    (f : {X : Type ℓ} (r : R X) → P X (projectFields fs r)) -- Property projection
    where

    prev = projectFields fs
    Prev = GatherFields fs

    PropHelperCenterType : Type _
    PropHelperCenterType =
      (A B : TypeWithStr ℓ R) (e : A .fst ≃ B .fst)
      (p : PathP (λ i → Prev (ua e i)) (prev (A .snd)) (prev (B .snd)))
      → PathP (λ i → P (ua e i) (p i)) (f (A .snd)) (f (B .snd))

    PropHelperContractType : PropHelperCenterType → Type _
    PropHelperContractType c =
      (A B : TypeWithStr ℓ R) (e : A .fst ≃ B .fst)
      {p₀ : PathP (λ i → Prev (ua e i)) (prev (A .snd)) (prev (B .snd))}
      (q : PathP (λ i → R (ua e i)) (A .snd) (B .snd))
      (p : p₀ ≡ (λ i → prev (q i)))
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

  ExplicitUnivalentDesc : ∀ ℓ {ℓ₁ ℓ₁'} → (d : M.Desc ℓ ℓ₁ ℓ₁') → Type _
  ExplicitUnivalentDesc _ d =
    ExplicitUnivalentStr (M.MacroStructure d) (M.MacroEquivStr d)

  explicitUnivalentDesc : ∀ ℓ {ℓ₁ ℓ₁'} → (d : M.Desc ℓ ℓ₁ ℓ₁') → ExplicitUnivalentDesc ℓ d
  explicitUnivalentDesc _ d A B e = M.MacroUnivalentStr d e

-- Internal record specification type
private
  record TypedTerm : Type where
    field
      type : R.Term
      term : R.Term

  record InternalDatumField : Type where
    field
      sfield : R.Name -- name of structure field
      efield : R.Name -- name of equivalence field

  record InternalPropField : Type where
    field
      sfield : R.Name -- name of structure field

  InternalField : Type
  InternalField = InternalDatumField ⊎ InternalPropField

  record InternalSpec (A : Type) : Type where
    field
      srec : R.Term -- structure record type
      erec : R.Term -- equivalence record type
      fields : List (InternalField × A) -- in reverse order

  open TypedTerm
  open InternalDatumField
  open InternalPropField

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
  parseSpec (R.con (quote autoRecordSpec) (ℓ h∷ ℓ₁ h∷ ℓ₁' h∷ srecTerm v∷ erecTerm v∷ fs v∷ [])) =
    parseFields fs >>= λ fs' →
    R.returnTC λ { .srec → srecTerm ; .erec → erecTerm ; .fields → fs'}
    where
    open InternalSpec

    parseFields : R.Term → R.TC (List (InternalField × TypedTerm))
    parseFields (R.con (quote fields:) _) = R.returnTC []
    parseFields (R.con (quote _data[_∣_])
      (ℓ h∷ ℓ₁ h∷ ℓ₁' h∷ R h∷ ι h∷ fs v∷ ℓ₂ h∷ ℓ₂' h∷ S h∷ ι' h∷ sfieldTerm v∷ efieldTerm v∷ []))
      =
      R.reduce ℓ >>= λ ℓ →
      findName sfieldTerm >>= λ sfieldName →
      findName efieldTerm >>= λ efieldName →
      buildDesc FUEL ℓ ℓ₂ S >>= λ d →
      let
        f : InternalField × TypedTerm
        f = λ
          { .fst → inl λ { .sfield → sfieldName ; .efield → efieldName }
          ; .snd .type → R.def (quote ExplicitUnivalentDesc) (ℓ v∷ d v∷ [])
          ; .snd .term → R.def (quote explicitUnivalentDesc) (ℓ v∷ d v∷ [])
          }
      in
      liftTC (f ∷_) (parseFields fs)
    parseFields (R.con (quote _prop[_∣_])
      (ℓ h∷ ℓ₁ h∷ ℓ₁' h∷ R h∷ ι h∷ fs v∷ ℓ₂ h∷ P h∷ fieldTerm v∷ prop v∷ []))
      =
      findName fieldTerm >>= λ fieldName →
      let
        p : InternalField × TypedTerm
        p = λ
          { .fst → inr λ { .sfield → fieldName }
          ; .snd .type →
            R.def (quote PropHelperType) (srecTerm v∷ erecTerm v∷ fs v∷ P v∷ fieldTerm v∷ [])
          ; .snd .term →
            R.def (quote derivePropHelper) (srecTerm v∷ erecTerm v∷ fs v∷ P v∷ fieldTerm v∷ prop v∷ [])
          }
      in
      liftTC (p ∷_) (parseFields fs)

    parseFields t = R.typeError (R.strErr "Malformed autoRecord specification (1): " ∷ R.termErr t ∷ [])

  parseSpec t = R.typeError (R.strErr "Malformed autoRecord specification (2): " ∷ R.termErr t ∷ [])

-- Build a proof of univalence from an InternalSpec
module _ (spec : InternalSpec ℕ) where
  open InternalSpec spec
  private

    fwdDatum : Vec R.Term 4 → R.Term → InternalDatumField × ℕ → R.Term
    fwdDatum (A ∷ B ∷ e ∷ streq ∷ _) i (dat , n) =
      R.def (quote equivFun)
        (tApply (v n) (tStrProj A (dat .sfield) v∷ tStrProj B (dat .sfield) v∷ e v∷ [])
          v∷ R.def (dat .efield) (streq v∷ [])
          v∷ i
          v∷ [])

    fwdProperty : Vec R.Term 4 → R.Term → R.Term → InternalPropField × ℕ → R.Term
    fwdProperty (A ∷ B ∷ e ∷ streq ∷ _) i prevPath prop =
      R.def (quote fst) (v (prop .snd) v∷ A v∷ B v∷ e v∷ prevPath v∷ i v∷ [])

    bwdClause : Vec R.Term 4 → InternalDatumField × ℕ → R.Clause
    bwdClause (A ∷ B ∷ e ∷ q ∷ _) (dat , n) =
      R.clause [] (R.proj (dat .efield) v∷ [])
        (R.def (quote invEq)
          (tApply
            (v n)
            (tStrProj A (dat .sfield) v∷ tStrProj B (dat .sfield) v∷ e v∷ [])
            v∷ R.def (quote pathMap) (R.def (dat .sfield) [] v∷ q v∷ [])
            v∷ []))

    fwdBwdDatum : Vec R.Term 4 → R.Term → R.Term → InternalDatumField × ℕ → R.Term
    fwdBwdDatum (A ∷ B ∷ e ∷ q ∷ _) j i (dat , n) =
      R.def (quote secEq)
        (tApply
          (v n)
          (tStrProj A (dat .sfield) v∷ tStrProj B (dat .sfield) v∷ e v∷ [])
          v∷ R.def (quote pathMap) (R.def (dat .sfield) [] v∷ q v∷ [])
          v∷ j v∷ i
          v∷ [])

    fwdBwdProperty : Vec R.Term 4 → (j i prevPath : R.Term) → InternalPropField × ℕ → R.Term
    fwdBwdProperty (A ∷ B ∷ e ∷ q ∷ _) j i prevPath prop =
      R.def (quote snd) (v (prop .snd) v∷ A v∷ B v∷ e v∷ q v∷ prevPath v∷ j v∷ i v∷ [])

    bwdFwdClause : Vec R.Term 4 → R.Term → InternalDatumField × ℕ → R.Clause
    bwdFwdClause (A ∷ B ∷ e ∷ streq ∷ _) j (dat , n) =
      R.clause [] (R.proj (dat .efield) v∷ [])
        (R.def (quote retEq)
          (tApply
            (v n)
            (tStrProj A (dat .sfield) v∷ tStrProj B (dat .sfield) v∷ e v∷ [])
            v∷ R.def (dat .efield) (streq v∷ [])
            v∷ j
            v∷ []))

    makeVarsFrom : {n : ℕ} → ℕ → Vec R.Term n
    makeVarsFrom {zero} k = []
    makeVarsFrom {suc n} k = v (n + k) ∷ (makeVarsFrom k)

    fwd : R.Term
    fwd =
      vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "i" (R.pat-lam body [])))))
      where
      -- input list is in reverse order
      fwdClauses : ℕ → List (InternalField × ℕ) → List (R.Name × R.Term)
      fwdClauses k [] = []
      fwdClauses k ((inl f , n) ∷ fs) =
        fwdClauses k fs
        ∷ʳ (f .sfield , fwdDatum (makeVarsFrom k) (v 0) (map-snd (4 + k +_) (f , n)))
      fwdClauses k ((inr p , n) ∷ fs) =
        fwdClauses k fs
        ∷ʳ (p .sfield , fwdProperty (makeVarsFrom k) (v 0) prevPath (map-snd (4 + k +_) (p , n)))
        where
        prevPath =
          vlam "i"
            (List.foldl
              (λ t (_ , t') → R.con (quote _,_) (t v∷ t' v∷ []))
              (R.con (quote tt) [])
              (fwdClauses (suc k) fs))

      body =
        List.map (λ (n , t) → R.clause [] [ varg (R.proj n) ] t) (fwdClauses 1 fields)

    bwd : R.Term
    bwd =
      vlam "A" (vlam "B" (vlam "e" (vlam "q" (R.pat-lam (bwdClauses fields) []))))
      where
      -- input is in reverse order
      bwdClauses : List (InternalField × ℕ) → List R.Clause
      bwdClauses [] = []
      bwdClauses ((inl f , n) ∷ fs) =
        bwdClauses fs
        ∷ʳ bwdClause (makeVarsFrom 0) (map-snd (4 +_) (f , n))
      bwdClauses ((inr p , n) ∷ fs) = bwdClauses fs

    fwdBwd : R.Term
    fwdBwd =
      vlam "A" (vlam "B" (vlam "e" (vlam "q" (vlam "j" (vlam "i" (R.pat-lam body []))))))
      where
      -- input is in reverse order
      fwdBwdClauses : ℕ →  List (InternalField × ℕ) → List (R.Name × R.Term)
      fwdBwdClauses k [] = []
      fwdBwdClauses k ((inl f , n) ∷ fs) =
        fwdBwdClauses k fs
        ∷ʳ (f .sfield , fwdBwdDatum (makeVarsFrom k) (v 1) (v 0) (map-snd (4 + k +_) (f , n)))
      fwdBwdClauses k ((inr p , n) ∷ fs) =
        fwdBwdClauses k fs
        ∷ʳ ((p .sfield , fwdBwdProperty (makeVarsFrom k) (v 1) (v 0) prevPath (map-snd (4 + k +_) (p , n))))
        where
        prevPath =
          vlam "j"
            (vlam "i"
              (List.foldl
                (λ t (_ , t') → R.con (quote _,_) (t v∷ t' v∷ []))
                (R.con (quote tt) [])
                (fwdBwdClauses (2 + k) fs)))

      body = List.map (λ (n , t) → R.clause [] [ varg (R.proj n) ] t) (fwdBwdClauses 2 fields)

    bwdFwd : R.Term
    bwdFwd =
      vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "j" (R.pat-lam (bwdFwdClauses fields) [])))))
      where
      bwdFwdClauses : List (InternalField × ℕ) → List R.Clause
      bwdFwdClauses [] = []
      bwdFwdClauses ((inl f , n) ∷ fs) =
        bwdFwdClauses fs
        ∷ʳ bwdFwdClause (makeVarsFrom 1) (v 0) (map-snd (5 +_) (f , n))
      bwdFwdClauses ((inr _ , n) ∷ fs) = bwdFwdClauses fs

  univalentRecord : R.Term
  univalentRecord =
    R.def (quote explicitUnivalentStr)
      (R.unknown v∷ R.unknown v∷ fwd v∷ bwd v∷ fwdBwd v∷ bwdFwd v∷ [])

macro
  autoFieldEquiv : R.Term → R.Term → R.Term → R.Term → R.TC Unit
  autoFieldEquiv spec A B hole =
    (R.reduce spec >>= parseFieldSpec) >>= λ (ℓ , ℓ₂ , S , f) →
    buildDesc FUEL ℓ ℓ₂ S >>= λ d →
    R.unify hole (R.def (quote M.MacroEquivStr) (d v∷ tStrMap A f v∷ tStrMap B f v∷ []))

  autoUnivalentRecord : R.Term → R.Term → R.TC Unit
  autoUnivalentRecord t hole =
    (R.reduce t >>= parseSpec) >>= λ spec →
    -- R.typeError (R.strErr "WOW: " ∷ R.termErr (main spec) ∷ [])
    R.unify (main spec) hole
    where
    module _ (spec : InternalSpec TypedTerm) where
      open InternalSpec spec

      mapUp : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (ℕ → A → B) → ℕ → List A → List B
      mapUp f _ [] = []
      mapUp f n (x ∷ xs) = f n x ∷ mapUp f (suc n) xs

      closureSpec : InternalSpec ℕ
      closureSpec .InternalSpec.srec = srec
      closureSpec .InternalSpec.erec = erec
      closureSpec .InternalSpec.fields = mapUp (λ n → map-snd (λ _ → n)) 0 fields

      closure : R.Term
      closure =
        iter (List.length fields) (vlam "") (univalentRecord closureSpec)

      env : List (R.Arg R.Term)
      env = List.map (varg ∘ term ∘ snd) (List.rev fields)

      closureTy : R.Term
      closureTy =
        List.foldr
          (λ ty cod → R.def (quote Fun) (ty v∷ cod v∷ []))
          (R.def (quote ExplicitUnivalentStr) (srec v∷ erec v∷ []))
          (List.map (type ∘ snd) (List.rev fields))

      main : R.Term
      main = R.def (quote idfun) (closureTy v∷ closure v∷ env)
