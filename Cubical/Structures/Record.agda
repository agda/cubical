{-

Generating univalent structures for records

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
open import Agda.Builtin.String

-- Magic number
private
  FUEL = 10000

data AutoFieldDatum (R : Type → Type) (ι : StrEquiv R ℓ-zero) : Type₁ where
  datum : {S : Type → Type} {ι' : StrEquiv S ℓ-zero}
    → (f : {X : Type} → R X → S X)
    → ({A B : TypeWithStr ℓ-zero R} {e : typ A ≃ typ B} → ι A B e → ι' (map-snd f A) (map-snd f B) e)
    → AutoFieldDatum R ι

private
  GatherDataFields : {R : Type → Type} {ι : StrEquiv R ℓ-zero}
    → List (AutoFieldDatum R ι)
    → Type → Type
  GatherDataFields [] X = Unit
  GatherDataFields (datum {S = S} _ _ ∷ fs) X =
    S X × GatherDataFields fs X

  projectDataFieldsTy : (R : Type → Type) (ι : StrEquiv R ℓ-zero)
    (fs : List (AutoFieldDatum R ι))
    → Type₁
  projectDataFieldsTy R ι fs =
    {X : Type} → R X → GatherDataFields fs X

  projectDataFields : {R : Type → Type} {ι : StrEquiv R ℓ-zero}
    (fs : List (AutoFieldDatum R ι))
    → {X : Type} → R X → GatherDataFields fs X
  projectDataFields [] = _
  projectDataFields (datum f _ ∷ fs) r =
    f r , projectDataFields fs r

  isPropProperty : (R : Type → Type)
    (ι : StrEquiv R ℓ-zero)
    (fs : List (AutoFieldDatum R ι))
    (P : (X : Type) → GatherDataFields fs X → Type)
    → Type₁
  isPropProperty R ι fs P =
    {X : Type} (r : R X) → isProp (P X (projectDataFields fs r))

data AutoFieldProperty
  (R : Type → Type)
  (ι : StrEquiv R ℓ-zero)
  (fs : List (AutoFieldDatum R ι))
  : Type₁
  where
  property : {P : (X : Type) → GatherDataFields fs X → Type}
    → ({X : Type} (r : R X) → P X (projectDataFields fs r))
    → isPropProperty R ι fs P
    → AutoFieldProperty R ι fs

data AutoRecordSpec : Type₁ where
  autoRecordSpec : (R : Type → Type) (ι : StrEquiv R ℓ-zero)
    (fs : List (AutoFieldDatum R ι))
    → List (AutoFieldProperty R ι fs)
    → AutoRecordSpec

-- Some reflection utilities
private
  _>>=_ = R.bindTC
  _<|>_ = R.catchTC
    
  _$_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → A → B
  f $ a = f a

  _>>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → R.TC A → R.TC B → R.TC B
  f >> g = f >>= λ _ → g

  mapDown : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (ℕ → A → B) → ℕ → List A → List B
  mapDown f _ [] = []
  mapDown f n (x ∷ xs) = f (predℕ n) x ∷ mapDown f (predℕ n) xs

  infixl 4 _>>=_ _>>_
  infixr 3 _$_

  mapTC : ∀ {ℓ} {A : Type ℓ} → List (R.TC A) → R.TC (List A)
  mapTC [] = R.returnTC []
  mapTC (r ∷ rs) = r >>= λ x → mapTC rs >>= λ xs → R.returnTC (x ∷ xs)

  liftTC : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → R.TC A → R.TC B
  liftTC f ta = ta >>= λ a → R.returnTC (f a)

  v : ℕ → R.Term
  v n = R.var n []

  pattern varg t = R.arg (R.arg-info R.visible R.relevant) t
  pattern harg t = R.arg (R.arg-info R.hidden R.relevant) t
  pattern _v∷_ a l = varg a ∷ l
  pattern _h∷_ a l = harg a ∷ l

  infixr 5 _v∷_ _h∷_

  vlam : String → R.Term → R.Term
  vlam str t = R.lam R.visible (R.abs str t)

  tI = R.def (quote I) []
  tLevel = R.def (quote Level) []
  tℓ₀ = R.def (quote ℓ-zero) []

  tType : R.Term → R.Term
  tType ℓ = R.def (quote Type) (ℓ v∷ [])

  tDesc : R.Term → R.Term
  tDesc ℓ = R.def (quote Desc) (ℓ v∷ [])

  func : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
  func A B = A → B

  tStruct : R.Term → R.Term → R.Term
  tStruct ℓ ℓ' = R.def (quote func) (tType ℓ v∷ tType ℓ' v∷ [])

  tTypeWithStr : R.Term → R.Term
  tTypeWithStr S = R.def (quote TypeWithStr) (tℓ₀ v∷ S v∷ [])

  tTyp : R.Term → R.Term
  tTyp A = R.def (quote typ) (varg A ∷ [])

  tStrEquiv : R.Term → R.Term
  tStrEquiv S = R.def (quote StrEquiv) (S v∷ tℓ₀ v∷ [])

  idfun' : ∀ {ℓ} {A : Type ℓ} → A → A
  idfun' x = x

  tApply : R.Term → List (R.Arg R.Term) → R.Term
  tApply t l = R.def (quote idfun') (varg t ∷ l)

  tStrProj : R.Term → R.Name → R.Term
  tStrProj A sfield = R.def (quote map-snd) (R.def sfield [] v∷ A v∷ [])

  newMeta = R.checkType R.unknown

private
  fieldShape : (Type → Type) → (Type → Type) → Type₁
  fieldShape R S = {X : Type} → R X → S X

  propFieldShape : (R R' : Type → Type) (proj : {X : Type} → R X → R' X)
    → (P : (X : Type) → R' X → Type) → Type₁
  propFieldShape R R' proj P =
    {X : Type} → (r : R X) → P X (proj r)

  isPropFieldShape : (R R' : Type → Type) (proj : {X : Type} → R X → R' X)
    → (P : (X : Type) → R' X → Type) → Type₁
  isPropFieldShape R R' proj P =
    {X : Type} → (r : R X) → isProp (P X (proj r))

  module _
    (R : Type → Type) -- Structure record
    (ι : StrEquiv R ℓ-zero) -- Equivalence record
    (fs : List (AutoFieldDatum R ι)) -- Data fields
    {P : (X : Type) → GatherDataFields fs X → Type} -- Property type
    (f : {X : Type} (r : R X) → P X (projectDataFields fs r)) -- Property projection
    where

    private
      dat = projectDataFields fs
      Dat = GatherDataFields fs

    PropFieldCenterType : Type₁
    PropFieldCenterType =
      (A B : TypeWithStr ℓ-zero R) (e : A .fst ≃ B .fst)
      (p : PathP (λ i → Dat (ua e i)) (dat (A .snd)) (dat (B .snd)))
      → PathP (λ i → P (ua e i) (p i)) (f (A .snd)) (f (B .snd))

    PropFieldContractType : PropFieldCenterType → Type₁
    PropFieldContractType c =
      (A B : TypeWithStr ℓ-zero R) (e : A .fst ≃ B .fst)
      {p₀ p₁ : PathP (λ i → Dat (ua e i)) (dat (A .snd)) (dat (B .snd))}
      (p : p₀ ≡ p₁)
      (q : PathP (λ i → P (ua e i) (p₁ i)) (f (A .snd)) (f (B .snd)))
      → PathP (λ k → PathP (λ i → P (ua e i) (p k i)) (f (A .snd)) (f (B .snd))) (c A B e p₀) q

    PropFieldHelperType : Type₁
    PropFieldHelperType =
      Σ PropFieldCenterType PropFieldContractType

    derivePropHelper : isPropProperty R ι fs P → PropFieldHelperType
    derivePropHelper propP .fst A B e p =
      isOfHLevelPathP' 0 (propP _) (f (A .snd)) (f (B .snd)) .fst
    derivePropHelper propP .snd A B e p q =
      isOfHLevelPathP' 0 (isOfHLevelPathP 1 (propP _) _ _) _ _ .fst

  pathMap : (S : Type → Type) {T : Type → Type} {A B : Type}
    (e : A ≃ B) (f : {X : Type} → S X → T X) {x : S A} {y : S B}
    → PathP (λ i → S (ua e i)) x y
    → PathP (λ i → T (ua e i)) (f x) (f y)
  pathMap S e f p i = f (p i)

  pathPShape : (S : Type → Type) (A B : TypeWithStr ℓ-zero S) (e : typ A ≃ typ B) → Type
  pathPShape S A B e = PathP (λ i → S (ua e i)) (str A) (str B)

  fwdShape : (S : Type → Type) (ι : StrEquiv S ℓ-zero) → Type₁
  fwdShape S ι =
    (A B : TypeWithStr ℓ-zero S) (e : typ A ≃ typ B) → ι A B e → PathP (λ i → S (ua e i)) (str A) (str B)

  bwdShape : (S : Type → Type) (ι : StrEquiv S ℓ-zero) → Type₁
  bwdShape S ι =
    (A B : TypeWithStr ℓ-zero S) (e : typ A ≃ typ B) → PathP (λ i → S (ua e i)) (str A) (str B) → ι A B e

  fwdBwdShape : (S : Type → Type) (ι : StrEquiv S ℓ-zero) → fwdShape S ι → bwdShape S ι → Type₁
  fwdBwdShape S ι fwd bwd =
    (A B : TypeWithStr ℓ-zero S) (e : typ A ≃ typ B) → ∀ p → fwd A B e (bwd A B e p) ≡ p

  bwdFwdShape : (S : Type → Type) (ι : StrEquiv S ℓ-zero) → fwdShape S ι → bwdShape S ι → Type₁
  bwdFwdShape S ι fwd bwd =
    (A B : TypeWithStr ℓ-zero S) (e : typ A ≃ typ B) → ∀ r → bwd A B e (fwd A B e r) ≡ r

  ExplicitUnivalentStr : ∀ {ℓ ℓ₁ ℓ₁'} (S : Type ℓ → Type ℓ₁) (ι : StrEquiv S ℓ₁') → Type _
  ExplicitUnivalentStr S ι =
    (A B : TypeWithStr _ S) (e : typ A ≃ typ B) → ι A B e ≃ PathP (λ i → S (ua e i)) (str A) (str B)

  ExplicitUnivalentDesc : ∀ {ℓ} (d : Desc ℓ) → Type _
  ExplicitUnivalentDesc d =
    ExplicitUnivalentStr (MacroStructure d) (MacroEquivStr d)

  explicitUnivalentDesc : ∀ {ℓ} (d : Desc ℓ) → ExplicitUnivalentDesc d
  explicitUnivalentDesc d A B e = MacroUnivalentStr d e

  mkUnivalentStr : (S : Type → Type) (ι : StrEquiv S ℓ-zero)
    (fwd : fwdShape S ι) (bwd : bwdShape S ι)
    → fwdBwdShape S ι fwd bwd → bwdFwdShape S ι fwd bwd
    → ExplicitUnivalentStr S ι
  mkUnivalentStr S ι fwd bwd fwdBwd bwdFwd A B e = isoToEquiv isom
    where
    open Iso
    isom : Iso _ _
    isom .fun = fwd A B e
    isom .inv = bwd A B e
    isom .rightInv = fwdBwd A B e
    isom .leftInv = bwdFwd A B e

-- Derive a structure descriptor for a field of a record
private
  fieldStructure : R.Name → R.Name → R.TC R.Term
  fieldStructure srec sfield =
    R.getType sfield >>= λ A →
    newMeta (tStruct tℓ₀ tℓ₀) >>= λ S →
    R.unify (R.def (quote fieldShape) (R.def srec [] v∷ S v∷ [])) A >>
    R.returnTC S

  fieldDesc : R.Name → R.Name → R.TC R.Term
  fieldDesc srec sfield =
    fieldStructure srec sfield >>= buildDesc FUEL tℓ₀ tℓ₀

-- Parse an AutoRecordSpec and derive the terms needed to build a record univalence proof
private
  record InternalDatumField : Type where
    field
      sfield : R.Name
      efield : R.Name
      univalentType : R.Term
      univalent : R.Term

  record InternalPropField : Type where
    field
      sfield : R.Name
      helperType : R.Term
      helper : R.Term

  record InternalSpec : Type where
    field
      srec : R.Name
      erec : R.Name
      datums : List InternalDatumField
      props : List InternalPropField

  open InternalDatumField
  open InternalPropField

  parseSpec : R.Term → R.TC InternalSpec
  parseSpec (R.con (quote autoRecordSpec) (R.def sr [] v∷ R.def er [] v∷ fs v∷ ps v∷ [])) =
    parseList parseDatum fs >>= λ fs' →
    parseList parseProp ps >>= λ ps' →
    R.returnTC λ { .srec → sr ; .erec → er ; .datums → fs' ; .props → ps' }
    where
    open InternalSpec

    findName : R.Term → R.TC R.Name
    findName (R.def name _) = R.returnTC name
    findName (R.lam R.hidden (R.abs _ t)) = findName t
    findName t = R.typeError (R.strErr "Malformed autoRecord specification (0): " ∷ R.termErr t ∷ [])

    projData : R.Term
    projData = R.def (quote projectDataFields) (fs v∷ [])

    projDataTy : R.Term
    projDataTy = R.def (quote projectDataFieldsTy) (R.def sr [] v∷ R.def er [] v∷ fs v∷ [])

    parseDatum : R.Term → R.TC InternalDatumField
    parseDatum (R.con (quote datum) (_ h∷ _ h∷ S h∷ _ h∷ sfieldTerm v∷ efieldTerm v∷ [])) =
      findName sfieldTerm >>= λ sfieldName →
      findName efieldTerm >>= λ efieldName →
      buildDesc FUEL tℓ₀ tℓ₀ S >>= λ d →
      R.returnTC λ
      { .sfield → sfieldName
      ; .efield → efieldName
      ; .univalentType → R.def (quote ExplicitUnivalentDesc) (d v∷ [])
      ; .univalent → R.def (quote explicitUnivalentDesc) (d v∷ [])
      }
    parseDatum t = R.typeError (R.strErr "Malformed autoRecord specification (1): " ∷ R.termErr t ∷ [])

    parseProp : R.Term → R.TC InternalPropField
    parseProp (R.con (quote property) (R h∷ ι h∷ fs h∷ S h∷ fieldTerm v∷ prop v∷ [])) =
      findName fieldTerm >>= λ fieldName →
      R.returnTC λ
      { .sfield → fieldName
      ; .helperType → R.def (quote PropFieldHelperType) (R v∷ ι v∷ fs v∷ fieldTerm v∷ [])
      ; .helper → R.def (quote derivePropHelper) (R v∷ ι v∷ fs v∷ fieldTerm v∷ prop v∷ [])
      }
    parseProp t = R.typeError (R.strErr "Malformed autoRecord specification (2): " ∷ R.termErr t ∷ [])

    parseList : {A : Type} → (R.Term → R.TC A) → R.Term → R.TC (List A)
    parseList f (R.con (quote _∷_) (_ h∷ _ h∷ t v∷ ts v∷ [])) =
      f t >>= λ t' →
      parseList f ts >>= λ ts' →
      R.returnTC (t' ∷ ts')
    parseList f (R.con (quote []) _) = R.returnTC []
    parseList f t = R.typeError (R.strErr "Malformed autoRecord specification (3): " ∷ R.termErr t ∷ [])

  parseSpec t = R.typeError (R.strErr "Malformed autoRecord specification (4): " ∷ R.termErr t ∷ [])

-- Build a proof of univalence from an InternalSpec
module _ (srec erec : R.Name)
  (nfs : List (ℕ × InternalDatumField)) (nps : List (ℕ × InternalPropField))
  where

  univalentRecordFwdDatum : (A B e streq i : R.Term) → ℕ × InternalDatumField → R.Term
  univalentRecordFwdDatum A B e streq i (n , dat) =
    R.def (quote equivFun)
      (tApply (v (5 + n)) (tStrProj A (dat .sfield) v∷ tStrProj B (dat .sfield) v∷ e v∷ [])
        v∷ R.def (dat .efield) (streq v∷ [])
        v∷ i
        v∷ [])

  univalentRecordFwdProperty : (dataPath A B e streq i : R.Term) → ℕ × InternalPropField → R.Clause
  univalentRecordFwdProperty dataPath A B e streq i (n , prop) =
    R.clause [] (R.proj (prop .sfield) v∷ [])
      (R.def (quote fst) (v (5 + n) v∷ A v∷ B v∷ e v∷ dataPath v∷ i v∷ []))

  univalentRecordBwdDatum : (A B e q : R.Term) → ℕ × InternalDatumField → R.Clause
  univalentRecordBwdDatum A B e q (n , dat) =
    R.clause [] (R.proj (dat .efield) v∷ [])
      (R.def (quote invEq)
        (tApply (v (4 + n)) (tStrProj A (dat .sfield) v∷ tStrProj B (dat .sfield) v∷ e v∷ [])
          v∷ R.def (quote pathMap) (R.def srec [] v∷ e v∷ R.def (dat .sfield) [] v∷ q v∷ [])
          v∷ []))

  univalentRecordFwdBwdDatum : (A B e q k i : R.Term) → ℕ × InternalDatumField → R.Term
  univalentRecordFwdBwdDatum A B e q k i (n , dat) =
    R.def (quote retEq)
      (tApply (v (6 + n)) (tStrProj A (dat .sfield) v∷ tStrProj B (dat .sfield) v∷ e v∷ [])
        v∷ R.def (quote pathMap) (R.def srec [] v∷ e v∷ R.def (dat .sfield) [] v∷ q v∷ [])
        v∷ k v∷ i
        v∷ [])

  univalentRecordFwdBwdProperty : (dataPath A B e q k i : R.Term) → ℕ × InternalPropField → R.Clause
  univalentRecordFwdBwdProperty dataPath A B e q k i (n , prop) =
    R.clause [] (R.proj (prop .sfield) v∷ [])
      (R.def (quote snd)
        (v (6 + n) v∷ A v∷ B v∷ e v∷ dataPath
          v∷ R.def (quote pathMap) (R.def srec [] v∷ e v∷ R.def (prop .sfield) [] v∷ q v∷ [])
          v∷ []))

  univalentRecordBwdFwdDatum : (A B e streq k : R.Term) → ℕ × InternalDatumField → R.Clause
  univalentRecordBwdFwdDatum A B e streq k (n , dat) =
    R.clause [] (R.proj (dat .efield) v∷ [])
      (R.def (quote secEq)
        (tApply (v (5 + n)) (tStrProj A (dat .sfield) v∷ tStrProj B (dat .sfield) v∷ e v∷ [])
          v∷ R.def (dat .efield) (streq v∷ [])
          v∷ k
          v∷ []))

  dataSigmaPatterns : List (List (R.Arg R.Pattern))
  dataSigmaPatterns = go (List.length nfs) []
    where
    go : ℕ → List (R.Arg R.Pattern) → List (List (R.Arg R.Pattern))
    go zero prefix = [ prefix ]
    go (suc n) prefix =
      (prefix ∷ʳ varg (R.proj (quote fst)))
      ∷ go n (prefix ∷ʳ varg (R.proj (quote snd)))

  univalentRecordFwd : R.Term
  univalentRecordFwd =
    vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "i" (R.pat-lam body [])))))
    where
    dataTerms : List R.Term
    dataTerms =
      List.map (univalentRecordFwdDatum (v 4) (v 3) (v 2) (v 1) (v 0)) nfs

    dataSigmaTerm : R.Term
    dataSigmaTerm =
      vlam "i" (R.pat-lam (List.map2 (R.clause []) dataSigmaPatterns dataTerms) [])

    body : List R.Clause
    body =
      List.map2 (λ (_ , dat) t → R.clause [] (R.proj (dat .sfield) v∷ []) t) nfs dataTerms
      ++
      List.map (univalentRecordFwdProperty dataSigmaTerm (v 4) (v 3) (v 2) (v 1) (v 0)) nps

  univalentRecordBwd : R.Term
  univalentRecordBwd =
    vlam "A" (vlam "B" (vlam "e" (vlam "p" (R.pat-lam body []))))
    where
    body : List R.Clause
    body = List.map (univalentRecordBwdDatum (v 3) (v 2) (v 1) (v 0)) nfs

  univalentRecordFwdBwd : R.Term
  univalentRecordFwdBwd =
    vlam "A" (vlam "B" (vlam "e" (vlam "p" (vlam "k" (vlam "i" (R.pat-lam body []))))))
    where
    dataTerms : List R.Term
    dataTerms =
      List.map (univalentRecordFwdBwdDatum (v 5) (v 4) (v 3) (v 2) (v 1) (v 0)) nfs

    dataSigmaTerm : R.Term
    dataSigmaTerm =
      vlam "k" (vlam "i" (R.pat-lam (List.map2 (R.clause []) dataSigmaPatterns dataTerms) []))

    body : List R.Clause
    body =
      List.map2 (λ (_ , dat) t → R.clause [] (R.proj (dat .sfield) v∷ []) t) nfs dataTerms
      ++
      List.map (univalentRecordFwdBwdProperty dataSigmaTerm (v 5) (v 4) (v 3) (v 2) (v 1) (v 0)) nps

  univalentRecordBwdFwd : R.Term
  univalentRecordBwdFwd =
    vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "k" (R.pat-lam body [])))))
    where
    body : List R.Clause
    body = List.map (univalentRecordBwdFwdDatum (v 4) (v 3) (v 2) (v 1) (v 0)) nfs

  univalentRecord : R.Term
  univalentRecord =
    R.def (quote mkUnivalentStr)
      (R.def srec []
        v∷ R.def erec []
        v∷ univalentRecordFwd
        v∷ univalentRecordBwd
        v∷ univalentRecordFwdBwd
        v∷ univalentRecordBwdFwd
        v∷ [])

macro
  autoFieldEquiv : R.Name → R.Name → R.Term → R.Term → R.Term → R.TC Unit
  autoFieldEquiv srec sfield A B hole =
    newMeta (tDesc tℓ₀) >>= λ d →
    R.unify hole
      (R.def (quote MacroEquivStr) (d v∷ tStrProj A sfield v∷ tStrProj B sfield v∷ [])) >>
    fieldDesc srec sfield >>=
    R.unify d

  autoUnivalentRecord : R.Term → R.Term → R.TC Unit
  autoUnivalentRecord term hole =
    (R.reduce term >>= parseSpec) >>= λ spec →
    caseBool
      (R.typeError [ R.termErr (main spec) ])
      (R.unify (main spec) hole)
      true -- DEBUG
    where
    module _ (spec : InternalSpec) where
      open InternalSpec spec

      body : R.Term
      body =
        univalentRecord srec erec
          (mapDown _,_ (List.length datums + List.length props) datums)
          (mapDown _,_ (List.length props) props)

      args : List (R.Arg R.Term)
      args = List.map (varg ∘ univalent) datums ++ List.map (varg ∘ helper) props

      innerTy : R.Term
      innerTy =
        List.foldr
          (λ ty cod → R.def (quote func) (ty v∷ cod v∷ []))
          (R.def (quote ExplicitUnivalentStr) (R.def srec [] v∷ R.def erec [] v∷ []))
          (List.map univalentType datums ++ List.map helperType props)

      main : R.Term
      main =
        R.def (quote idfun)
          (innerTy
            v∷ iter (List.length datums + List.length props) (vlam "") body
            v∷ args)


record Monoid (X : Type) : Type where
  field
    unit : X
    mult : X → X → X
    is-set : isSet X
    -- unitl : ∀ x → mult unit x ≡ x
    -- unitr : ∀ x → mult x unit ≡ x
    -- assoc : ∀ x y z → mult x (mult y z) ≡ mult (mult x y) z

open Monoid

record MonoidEquiv (A B : TypeWithStr ℓ-zero Monoid) (e : typ A ≃ typ B) : Type where
  field
    unit : autoFieldEquiv Monoid unit A B e
    mult : autoFieldEquiv Monoid mult A B e

open MonoidEquiv

testSpec : AutoRecordSpec
testSpec =
  autoRecordSpec Monoid MonoidEquiv
    ( datum unit unit
    ∷ datum mult mult
    ∷ []
    )
    ( property is-set (λ _ → isPropIsSet)
    -- ∷ property unitl (λ m → isPropΠ λ _ → m .is-set _ _)
    -- ∷ property unitr (λ m → isPropΠ λ _ → m .is-set _ _)
    -- ∷ property assoc (λ m → isPropΠ3 λ _ _ _ → m .is-set _ _)
    ∷ []
    )

test : UnivalentStr Monoid MonoidEquiv
test = autoUnivalentRecord testSpec _ _
