{-

Generating univalent structures for records

-}
{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Structures.Record where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
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

data AutoField (S : Type → Type) (ι : StrEquiv S ℓ-zero) : Type₁ where
  structure : {S' : Type → Type} {ι' : StrEquiv S ℓ-zero}
    → ({X : Type} → S X → S' X)
    → ({A B : TypeWithStr ℓ-zero S} {e : typ A ≃ typ B} → ι A B e → ι' A B e)
    → AutoField S ι
  property : {S' : Type → Type} {ι' : StrEquiv S ℓ-zero}
    → ({X : Type} → S X → S' X)
    → ({X : Type} → S X → isProp (S' X))
    → AutoField S ι

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

  idfun' : ∀ {ℓ} {A : Type ℓ} → A → A
  idfun' x = x

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

  _t≃_ : R.Term → R.Term → R.Term
  A t≃ B = R.def (quote _≃_) (A v∷ B v∷ [])

  newMeta = R.checkType R.unknown

private
  fieldShape : (Type → Type) → (Type → Type) → Type₁
  fieldShape R S = {X : Type} → R X → S X

  strProj : R.Term → R.Name → R.Term
  strProj A sfield =
    R.def (quote map-snd) (R.def sfield [] v∷ A v∷ [])

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
  fieldDesc : R.Name → R.Name → R.TC R.Term
  fieldDesc srec sfield =
    R.getType sfield >>= λ A → 
    newMeta (tStruct tℓ₀ tℓ₀) >>= λ S →
    R.unify (R.def (quote fieldShape) (R.def srec [] v∷ S v∷ [])) A >>
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

  univalentRecordFwdClause : (A B e streq i : R.Term) → ℕ × InternalAutoField → R.TC R.Clause
  univalentRecordFwdClause A B e streq i (n , istructure sfield efield) =
    R.returnTC
      (R.clause [] (R.proj sfield v∷ [])
        (R.def (quote equivFun)
          (R.def (quote idfun') (v (5 + n) v∷ strProj A sfield v∷ strProj B sfield v∷ e v∷ [])
            v∷ R.def efield (streq v∷ [])
            v∷ i
            v∷ [])))
  univalentRecordFwdClause A B e streq i (n , iproperty sfield _) =
    {!!}

  univalentRecordFwd : List (ℕ × InternalAutoField) → R.TC R.Term
  univalentRecordFwd nfs =
    bodyTC >>= λ body →
    R.returnTC (vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "i" (R.pat-lam body []))))))
    where
    bodyTC : R.TC (List R.Clause)
    bodyTC =
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTyp (v 1) t≃ tTyp (v 0))) $
      R.extendContext (varg (R.def erec (v 2 v∷ v 1 v∷ v 0 v∷ []))) $
      R.extendContext (varg tI) $
      mapTC (List.map (univalentRecordFwdClause (v 4) (v 3) (v 2) (v 1) (v 0)) nfs)

  univalentRecordBwdClause : (A B e p : R.Term)
    → ℕ × InternalAutoField → R.TC R.Clause
  univalentRecordBwdClause A B e p (n , istructure sfield efield) =
    R.returnTC
      (R.clause [] (R.proj efield v∷ [])
        (R.def (quote invEq)
          (R.def (quote idfun') (v (4 + n) v∷ strProj A sfield v∷ strProj B sfield v∷ e v∷ [])
            v∷ R.def (quote pathMap) (R.def srec [] v∷ e v∷ R.def sfield [] v∷ p v∷ [])
            v∷ [])))
  univalentRecordBwdClause A B e p (n , iproperty sfield _) =
    {!!}

  univalentRecordBwd : List (ℕ × InternalAutoField) → R.TC R.Term
  univalentRecordBwd nfs =
    bodyTC >>= λ body →
    R.returnTC (vlam "A" (vlam "B" (vlam "e" (vlam "p" (R.pat-lam body [])))))
    where
    bodyTC : R.TC (List R.Clause)
    bodyTC =
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTyp (v 1) t≃ tTyp (v 0))) $
      R.extendContext (varg (R.def (quote pathPShape) (R.def srec [] v∷ v 2 v∷ v 1 v∷ v 0 v∷ []))) $
      mapTC (List.map (univalentRecordBwdClause (v 3) (v 2) (v 1) (v 0)) nfs)

  univalentRecordFwdBwdClause : (A B e p k i : R.Term)
    → ℕ × InternalAutoField → R.TC R.Clause
  univalentRecordFwdBwdClause A B e p k i (n , istructure sfield efield) =
      R.returnTC
      (R.clause [] (R.proj sfield v∷ [])
        (R.def (quote retEq)
          (R.def (quote idfun') (v (6 + n) v∷ strProj A sfield v∷ strProj B sfield v∷ e v∷ [])
            v∷ R.def (quote pathMap) (R.def srec [] v∷ e v∷ R.def sfield [] v∷ p v∷ [])
            v∷ k
            v∷ i
            v∷ [])))
  univalentRecordFwdBwdClause A B e p k i (n , iproperty sfield _) =
    {!!}

  univalentRecordFwdBwd : List (ℕ × InternalAutoField) → R.TC R.Term
  univalentRecordFwdBwd nfs =
    bodyTC >>= λ body →
    R.returnTC (vlam "A" (vlam "B" (vlam "e" (vlam "p" (vlam "k" (vlam "i" (R.pat-lam body [])))))))
    where
    bodyTC : R.TC (List R.Clause)
    bodyTC =
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTyp (v 1) t≃ tTyp (v 0))) $
      R.extendContext (varg (R.def (quote pathPShape) (R.def srec [] v∷ v 2 v∷ v 1 v∷ v 0 v∷ []))) $
      R.extendContext (varg tI) $
      R.extendContext (varg tI) $
      mapTC (List.map (univalentRecordFwdBwdClause (v 5) (v 4) (v 3) (v 2) (v 1) (v 0)) nfs)

  univalentRecordBwdFwdClause : (A B e streq k : R.Term)
    → ℕ × InternalAutoField → R.TC R.Clause
  univalentRecordBwdFwdClause A B e streq k (n , istructure sfield efield) =
    R.returnTC
      (R.clause [] (R.proj efield v∷ [])
        (R.def (quote secEq)
          (R.def (quote idfun') (v (5 + n) v∷ strProj A sfield v∷ strProj B sfield v∷ e v∷ [])
            v∷ R.def efield (streq v∷ [])
            v∷ k
            v∷ [])))
  univalentRecordBwdFwdClause A B e streq k (n , iproperty sfield _) =
    {!!}

  univalentRecordBwdFwd : List (ℕ × InternalAutoField) → R.TC R.Term
  univalentRecordBwdFwd nfs =
    bodyTC >>= λ body →
    R.returnTC (vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "k" (R.pat-lam body []))))))
    where
    bodyTC : R.TC (List R.Clause)
    bodyTC =
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTyp (v 1) t≃ tTyp (v 0))) $
      R.extendContext (varg (R.def erec (v 2 v∷ v 1 v∷ v 0 v∷ []))) $
      R.extendContext (varg tI) $
      mapTC (List.map (univalentRecordBwdFwdClause (v 4) (v 3) (v 2) (v 1) (v 0)) nfs)

  autoUnivalentRecord' : List (ℕ × InternalAutoField) → R.TC R.Term
  autoUnivalentRecord' nfs =
    univalentRecordFwd nfs >>= λ fwd →
    univalentRecordBwd nfs >>= λ bwd →
    univalentRecordFwdBwd nfs >>= λ fwdBwd →
    univalentRecordBwdFwd nfs >>= λ bwdFwd →
    R.returnTC (R.def (quote mkUnivalentStr) (withRecs (fwd v∷ bwd v∷ fwdBwd v∷ bwdFwd v∷ [])))
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
      (R.def (quote MacroEquivStr) (d v∷ strProj A sfield v∷ strProj B sfield v∷ [])) >>
    fieldDesc srec sfield >>=
    R.unify d

  autoUnivalentRecord : R.Term → R.Term → R.TC Unit
  autoUnivalentRecord term hole =
    parseSpec term >>= λ (srec , erec , fs) →
    argsTC srec erec fs [] >>= λ univalents →
    R.getContext >>= λ ctx₀ →
    contextTC srec erec fs >>= λ ctx₁ →
    R.inContext (ctx₀ ++ ctx₁) (autoUnivalentRecord' srec erec (mapi _,_ fs)) >>= λ body →
    innerTyTC srec erec fs (R.def (quote uStrShape) (R.def srec [] v∷ R.def erec [] v∷ [])) >>= λ innerTy →
    R.unify
    -- R.typeError ([_] (R.termErr (
      (R.def (quote idfun)
        (innerTy v∷ iter (List.length fs) (vlam "") body v∷ List.map varg univalents))
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

      contextTC : List InternalAutoField → R.TC (List (R.Arg R.Term))
      contextTC [] = R.returnTC []
      contextTC (istructure sfield _ ∷ fs) =
        fieldDesc srec sfield >>= λ d →
        let
          ty =
            R.def (quote uStrShape)
              (R.def (quote MacroStructure) (tℓ₀ h∷ d v∷ []) v∷ R.def (quote MacroEquivStr) (d v∷ []) v∷ [])
        in
        liftTC (ty v∷_) (contextTC fs)
      contextTC (iproperty sfield prop ∷ fs) =
        {!!}

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
        {!!}

record Dog (X : Type) : Type where
  field
    cat : X
    adult : X → (X → X) → X
    wolf : ℕ → ℕ

open Dog

record DogEquiv (A B : TypeWithStr ℓ-zero Dog) (e : typ A ≃ typ B) : Type where
  field
    cat : autoFieldEquiv Dog cat A B e
    adult : autoFieldEquiv Dog adult A B e
    wolf : autoFieldEquiv Dog wolf A B e

open DogEquiv

test : (A B : TypeWithStr ℓ-zero Dog) (e : typ A ≃ typ B)
  → DogEquiv A B e ≃ PathP (λ i → Dog (ua e i)) (str A) (str B)
test =
  autoUnivalentRecord
    (autoRecordSpec Dog DogEquiv
      (structure cat cat
        ∷ structure adult adult
        ∷ structure wolf wolf
        ∷ []))
