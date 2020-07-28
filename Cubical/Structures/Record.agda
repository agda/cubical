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

data AutoField (R : Type → Type) (ι : StrEquiv R ℓ-zero) : Type₁ where
  structure : {S : Type → Type} {ι' : StrEquiv S ℓ-zero}
    → (f : {X : Type} → R X → S X)
    → ({A B : TypeWithStr ℓ-zero R} {e : typ A ≃ typ B} → ι A B e → ι' (map-snd f A) (map-snd f B) e)
    → AutoField R ι
  property : {S : Type → Type}
    → ({X : Type} → R X → S X)
    → ({X : Type} → R X → isProp (S X))
    → AutoField R ι

abstract
  autoRecordSpec : (S : Type → Type) (ι : StrEquiv S ℓ-zero)
    → List (AutoField S ι) → List (AutoField S ι )
  autoRecordSpec _ _ = idfun _

private
  data InternalAutoField : Type where
    istructure : R.Name → R.Name → InternalAutoField
    iproperty : R.Name → R.Term → InternalAutoField

-- Some reflection utilities
private
  _>>=_ = R.bindTC
  _<|>_ = R.catchTC
    
  _$_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → A → B
  f $ a = f a

  _>>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → R.TC A → R.TC B → R.TC B
  f >> g = f >>= λ _ → g

  mapi : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (ℕ → A → B) → List A → List B
  mapi {A = A} {B} f = mapi' 0
    where
    mapi' : ℕ → List A → List B
    mapi' _ [] = []
    mapi' n (x ∷ xs) = f n x ∷ mapi' (suc n) xs

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

  _t≃_ : R.Term → R.Term → R.Term
  A t≃ B = R.def (quote _≃_) (A v∷ B v∷ [])

  newMeta = R.checkType R.unknown

private
  fieldShape : (Type → Type) → (Type → Type) → Type₁
  fieldShape R S = {X : Type} → R X → S X

  fieldPropShape : (Type → Type) → (Type → Type) → Type₁
  fieldPropShape R S = {X : Type} → R X → isProp (S X)

  fieldPropMk : {R S : Type → Type} (A B : TypeWithStr ℓ-zero R) (e : A .fst ≃ B .fst)
    (f : fieldShape R S)
    → fieldPropShape R S
    → PathP (λ i → S (ua e i)) (f (A .snd)) (f (B .snd))
  fieldPropMk A B e f p =
    isOfHLevelPathP' 0 (p (B .snd)) (f (A .snd)) (f (B .snd)) .fst

  fieldPropPath : {R S : Type → Type} (A B : TypeWithStr ℓ-zero R) (e : A .fst ≃ B .fst)
    (f : fieldShape R S) (p : fieldPropShape R S)
    (q : PathP (λ i → S (ua e i)) (f (A .snd)) (f (B .snd)))
    → fieldPropMk A B e f p ≡ q
  fieldPropPath A B e f p q =
    isOfHLevelPathP' 0 (p (B .snd)) (f (A .snd)) (f (B .snd)) .snd q

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

  uStrShape : ∀ {ℓ ℓ₁ ℓ₁'} (S : Type ℓ → Type ℓ₁) (ι : StrEquiv S ℓ₁') → Type _
  uStrShape S ι =
    (A B : TypeWithStr _ S) (e : typ A ≃ typ B) → ι A B e ≃ PathP (λ i → S (ua e i)) (str A) (str B)

  mkUnivalentStr : (S : Type → Type) (ι : StrEquiv S ℓ-zero)
    (fwd : fwdShape S ι) (bwd : bwdShape S ι)
    → fwdBwdShape S ι fwd bwd → bwdFwdShape S ι fwd bwd
    → uStrShape S ι
  mkUnivalentStr S ι fwd bwd fwdBwd bwdFwd A B e = isoToEquiv isom
    where
    open Iso
    isom : Iso _ _
    isom .fun = fwd A B e
    isom .inv = bwd A B e
    isom .rightInv = fwdBwd A B e
    isom .leftInv = bwdFwd A B e

private
  fieldStructure : R.Name → R.Name → R.TC R.Term
  fieldStructure srec sfield =
    R.getType sfield >>= λ A →
    newMeta (tStruct tℓ₀ tℓ₀) >>= λ S →
    R.unify (R.def (quote fieldShape) (R.def srec [] v∷ S v∷ [])) A >>
    R.returnTC S

  fieldDesc : R.Name → R.Name → R.TC R.Term
  fieldDesc srec sfield =
    fieldStructure srec sfield >>= λ S →
    buildDesc FUEL tℓ₀ tℓ₀ S

  parseSpec : R.Term → R.TC (R.Name × R.Name × List InternalAutoField)
  parseSpec (R.def (quote autoRecordSpec) (R.def srec [] v∷ R.def erec [] v∷ fs v∷ [])) =
    liftTC (λ fs → srec , erec , fs) (parseFields fs)
    where
    findName : R.Term → R.TC R.Name
    findName (R.def name _) = R.returnTC name
    findName (R.lam R.hidden (R.abs _ t)) = findName t
    findName t = R.typeError (R.strErr "Malformed autoRecord specification: " ∷ R.termErr t ∷ [])

    parseField : R.Term → R.TC InternalAutoField
    parseField (R.con (quote structure) (_ h∷ _ h∷ _ h∷ _ h∷ sterm v∷ eterm v∷ [])) =
      findName sterm >>= λ sfield →
      findName eterm >>= λ efield →
      R.returnTC (istructure sfield efield)
    parseField (R.con (quote property) (_ h∷ _ h∷ _ h∷ sterm v∷ prop v∷ [])) =
      findName sterm >>= λ sfield →
      R.returnTC (iproperty sfield prop)
    parseField t = R.typeError (R.strErr "Malformed autoRecord specification: " ∷ R.termErr t ∷ [])

    parseFields : R.Term → R.TC (List InternalAutoField)
    parseFields (R.con (quote _∷_) (_ h∷ _ h∷ f v∷ fs v∷ [])) =
      parseField f >>= λ f' →
      parseFields fs >>= λ fs' →
      R.returnTC (f' ∷ fs')
    parseFields (R.con (quote []) _) = R.returnTC []
    parseFields t = R.typeError (R.strErr "Malformed autoRecord specification: " ∷ R.termErr t ∷ [])
  parseSpec t = R.typeError (R.strErr "Malformed autoRecord specification: " ∷ R.termErr t ∷ [])

module _ (srec erec : R.Name) where

  univalentRecordFwdClause : (A B e streq i : R.Term) → ℕ × InternalAutoField → R.Clause
  univalentRecordFwdClause A B e streq i (n , istructure sfield efield) =
    R.clause [] (R.proj sfield v∷ [])
      (R.def (quote equivFun)
        (tApply (v (5 + n)) (tStrProj A sfield v∷ tStrProj B sfield v∷ e v∷ [])
          v∷ R.def efield (streq v∷ [])
          v∷ i
          v∷ []))
  univalentRecordFwdClause A B e _ i (n , iproperty sfield _) =
    R.clause [] (R.proj sfield v∷ [])
      (R.def (quote fieldPropMk)
        (A v∷ B v∷ e v∷ R.def sfield [] v∷ v (5 + n) v∷ i v∷ []))

  univalentRecordFwd : List (ℕ × InternalAutoField) → R.Term
  univalentRecordFwd nfs =
    vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "i" (R.pat-lam body [])))))
    where
    body : List R.Clause
    body = List.map (univalentRecordFwdClause (v 4) (v 3) (v 2) (v 1) (v 0)) nfs

  univalentRecordBwdClause : (A B e p : R.Term)
    → ℕ × InternalAutoField → Maybe R.Clause
  univalentRecordBwdClause A B e p (n , istructure sfield efield) =
    just
      (R.clause [] (R.proj efield v∷ [])
        (R.def (quote invEq)
          (tApply (v (4 + n)) (tStrProj A sfield v∷ tStrProj B sfield v∷ e v∷ [])
            v∷ R.def (quote pathMap) (R.def srec [] v∷ e v∷ R.def sfield [] v∷ p v∷ [])
            v∷ [])))
  univalentRecordBwdClause A B e p (n , iproperty sfield _) =
    nothing

  univalentRecordBwd : List (ℕ × InternalAutoField) → R.Term
  univalentRecordBwd nfs =
    vlam "A" (vlam "B" (vlam "e" (vlam "p" (R.pat-lam body []))))
    where
    body : List R.Clause
    body = List.filterMap (univalentRecordBwdClause (v 3) (v 2) (v 1) (v 0)) nfs

  univalentRecordFwdBwdClause : (A B e p k i : R.Term)
    → ℕ × InternalAutoField → R.Clause
  univalentRecordFwdBwdClause A B e p k i (n , istructure sfield efield) =
    R.clause [] (R.proj sfield v∷ [])
      (R.def (quote retEq)
        (tApply (v (6 + n)) (tStrProj A sfield v∷ tStrProj B sfield v∷ e v∷ [])
          v∷ R.def (quote pathMap) (R.def srec [] v∷ e v∷ R.def sfield [] v∷ p v∷ [])
          v∷ k
          v∷ i
          v∷ []))
  univalentRecordFwdBwdClause A B e p k i (n , iproperty sfield _) =
    R.clause [] (R.proj sfield v∷ [])
      (R.def (quote fieldPropPath)
        (A v∷ B v∷ e v∷ R.def sfield [] v∷ v (6 + n)
          v∷ R.def (quote pathMap) (R.def srec [] v∷ e v∷ R.def sfield [] v∷ p v∷ [])
          v∷ k
          v∷ i
          v∷ []))

  univalentRecordFwdBwd : List (ℕ × InternalAutoField) → R.Term
  univalentRecordFwdBwd nfs =
    vlam "A" (vlam "B" (vlam "e" (vlam "p" (vlam "k" (vlam "i" (R.pat-lam body []))))))
    where
    body : List R.Clause
    body = List.map (univalentRecordFwdBwdClause (v 5) (v 4) (v 3) (v 2) (v 1) (v 0)) nfs

  univalentRecordBwdFwdClause : (A B e streq k : R.Term)
    → ℕ × InternalAutoField → Maybe R.Clause
  univalentRecordBwdFwdClause A B e streq k (n , istructure sfield efield) =
    just
      (R.clause [] (R.proj efield v∷ [])
        (R.def (quote secEq)
          (tApply (v (5 + n)) (tStrProj A sfield v∷ tStrProj B sfield v∷ e v∷ [])
            v∷ R.def efield (streq v∷ [])
            v∷ k
            v∷ [])))
  univalentRecordBwdFwdClause A B e streq k (n , iproperty sfield _) =
    nothing

  univalentRecordBwdFwd : List (ℕ × InternalAutoField) → R.Term
  univalentRecordBwdFwd nfs =
    vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "k" (R.pat-lam body [])))))
    where
    body : List R.Clause
    body = List.filterMap (univalentRecordBwdFwdClause (v 4) (v 3) (v 2) (v 1) (v 0)) nfs

  autoUnivalentRecord' : List (ℕ × InternalAutoField) → R.Term
  autoUnivalentRecord' nfs =
    R.def (quote mkUnivalentStr)
      (withRecs
        (univalentRecordFwd nfs
          v∷ univalentRecordBwd nfs
          v∷ univalentRecordFwdBwd nfs
          v∷ univalentRecordBwdFwd nfs
          v∷ []))
    where
    withRecs : List (R.Arg R.Term) → List (R.Arg R.Term)
    withRecs l = R.def srec [] v∷ R.def erec [] v∷ l

MacroUnivalentStr' : (d : Desc ℓ-zero) → uStrShape (MacroStructure d) (MacroEquivStr d)
MacroUnivalentStr' d A B e = MacroUnivalentStr d e

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
    parseSpec term >>= λ (srec , erec , fs) →
    innerTyTC srec erec fs (R.def (quote uStrShape) (R.def srec [] v∷ R.def erec [] v∷ [])) >>= λ innerTy →
    argsTC srec erec fs [] >>= λ args →
    let body = autoUnivalentRecord' srec erec (mapi _,_ fs) in
    R.unify
    -- R.typeError ([_] (R.termErr (
      (R.def (quote idfun) (innerTy v∷ iter (List.length fs) (vlam "") body v∷ List.map varg args))
      -- )))
      hole
    where
    module _ (srec erec : R.Name) where
      argsTC : List InternalAutoField → List R.Term → R.TC (List R.Term)
      argsTC [] acc = R.returnTC acc
      argsTC (istructure sfield _ ∷ fs) acc =
        fieldDesc srec sfield >>= λ d →
        argsTC fs (R.def (quote MacroUnivalentStr') (d v∷ []) ∷ acc)
      argsTC (iproperty _ prop ∷ fs) acc =
        argsTC fs (prop ∷ acc)

      innerTyTC : List InternalAutoField → R.Term → R.TC R.Term
      innerTyTC [] acc = R.returnTC acc
      innerTyTC (istructure sfield _ ∷ fs) acc =
        fieldDesc srec sfield >>= λ d →
        let
          ty =
            R.def (quote uStrShape)
              (R.def (quote MacroStructure) (tℓ₀ h∷ d v∷ []) v∷ R.def (quote MacroEquivStr) (d v∷ []) v∷ [])
        in
        innerTyTC fs (R.def (quote func) (ty v∷ acc v∷ []))
      innerTyTC (iproperty sfield _ ∷ fs) acc =
        fieldStructure srec sfield >>= λ S →
        let
          ty = R.def (quote fieldPropShape) (R.def srec [] v∷ S v∷ [])
        in
        innerTyTC fs (R.def (quote func) (ty v∷ acc v∷ []))

record Dog (X : Type) : Type where
  field
    cat : X
    adult : X → (X → X) → X
    wolf : ℕ → ℕ
    hat : isSet X

open Dog

record DogEquiv (A B : TypeWithStr ℓ-zero Dog) (e : typ A ≃ typ B) : Type where
  field
    cat : autoFieldEquiv Dog cat A B e
    adult : autoFieldEquiv Dog adult A B e
    wolf : autoFieldEquiv Dog wolf A B e

open DogEquiv

test : UnivalentStr Dog DogEquiv
test =
  autoUnivalentRecord
    (autoRecordSpec Dog DogEquiv
      (structure cat cat
        ∷ structure adult adult
        ∷ structure wolf wolf
        ∷ property hat (λ _ → isPropIsSet)
        ∷ []))
    _ _
