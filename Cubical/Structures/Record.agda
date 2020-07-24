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

-- Some reflection utilities
private
  _>>=_ = R.bindTC
    
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

  varg : ∀ {ℓ} {A : Type ℓ} → A → R.Arg A
  varg = R.arg (R.arg-info R.visible R.relevant)

  harg : ∀ {ℓ} {A : Type ℓ} → A → R.Arg A
  harg = R.arg (R.arg-info R.hidden R.relevant)

  vlam : String → R.Term → R.Term
  vlam str t = R.lam R.visible (R.abs str t)

  tI = R.def (quote I) []

  tLevel = R.def (quote Level) []

  tℓ₀ = R.def (quote ℓ-zero) []

  tType : R.Term → R.Term
  tType ℓ = R.def (quote Type) [ varg ℓ ]

  tDesc : R.Term → R.Term
  tDesc ℓ = R.def (quote Desc) [ varg ℓ ]

  func : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
  func A B = A → B

  tStruct : R.Term → R.Term → R.Term
  tStruct ℓ ℓ' = R.def (quote func) (varg (tType ℓ) ∷ varg (tType ℓ') ∷ [])

  tTypeWithStr : R.Term → R.Term
  tTypeWithStr S = R.def (quote TypeWithStr) (varg tℓ₀ ∷ varg S ∷ [])

  tTyp : R.Term → R.Term
  tTyp A = R.def (quote typ) (varg A ∷ [])

  tStrEquiv : R.Term → R.Term
  tStrEquiv S = R.def (quote StrEquiv) (varg S ∷ varg tℓ₀ ∷ [])

  newMeta = R.checkType R.unknown

private
  fieldShape : (Type → Type) → (Type → Type) → Type₁
  fieldShape R S = {X : Type} → R X → S X

  withStrProj : R.Term → R.Name → R.Term
  withStrProj A sfield =
    R.def (quote map-snd) (varg (R.def sfield []) ∷ varg A ∷ [])

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
  fieldDesc' : R.Name → R.Name → R.TC R.Term
  fieldDesc' srec sfield =
    R.getType sfield >>= λ A → 
    newMeta (tStruct tℓ₀ tℓ₀) >>= λ S →
    R.unify (R.def (quote fieldShape) (varg (R.def srec []) ∷ varg S ∷ [])) A >>
    buildDesc FUEL tℓ₀ tℓ₀ S

module _ (srec erec : R.Name) where

  univalentRecordFwdClause : (A B e streq i : R.Term) → ℕ × R.Name × R.Name → R.TC R.Clause
  univalentRecordFwdClause A B e streq i (n , sfield , efield) =
    R.returnTC
      (R.clause [] [ varg (R.proj sfield) ]
        (R.def (quote equivFun)
          (varg (R.def (quote idfun') (varg (v (5 + n)) ∷ varg (withStrProj A sfield) ∷ varg (withStrProj B sfield) ∷ varg e ∷ []))
            ∷ varg (R.def efield [ varg streq ])
            ∷ varg i
            ∷ [])))

  univalentRecordFwd : List (ℕ × R.Name × R.Name) → R.TC R.Term
  univalentRecordFwd nfs =
    bodyTC >>= λ body →
    R.returnTC (vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "i" (R.pat-lam body []))))))
    where
    bodyTC : R.TC (List R.Clause)
    bodyTC =
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (R.def (quote _≃_) (varg (tTyp (v 1)) ∷ varg (tTyp (v 0)) ∷ []))) $
      R.extendContext (varg (R.def erec (varg (v 2) ∷ varg (v 1) ∷ varg (v 0) ∷ []))) $
      R.extendContext (varg tI) $
      mapTC (List.map (univalentRecordFwdClause (v 4) (v 3) (v 2) (v 1) (v 0)) nfs)

  univalentRecordBwdClause : (A B e p : R.Term)
    → ℕ × R.Name × R.Name → R.TC R.Clause
  univalentRecordBwdClause A B e p (n , sfield , efield) =
    R.returnTC
      (R.clause [] [ varg (R.proj efield) ]
        (R.def (quote invEq)
          (varg (R.def (quote idfun') (varg (v (4 + n)) ∷ varg (withStrProj A sfield) ∷ varg (withStrProj B sfield) ∷ varg e ∷ []))
            ∷ varg (R.def (quote pathMap) (varg (R.def srec []) ∷ varg e ∷ varg (R.def sfield []) ∷ varg p ∷ []))
            ∷ [])))

  univalentRecordBwd : List (ℕ × R.Name × R.Name) → R.TC R.Term
  univalentRecordBwd nfs =
    bodyTC >>= λ body →
    R.returnTC (vlam "A" (vlam "B" (vlam "e" (vlam "p" (R.pat-lam body [])))))
    where
    bodyTC : R.TC (List R.Clause)
    bodyTC =
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (R.def (quote _≃_) (varg (tTyp (v 1)) ∷ varg (tTyp (v 0)) ∷ []))) $
      R.extendContext
        (varg
          (R.def (quote pathPShape)
            (varg (R.def srec []) ∷ varg (v 2) ∷ varg (v 1) ∷ varg (v 0) ∷ []))) $
      mapTC
        (List.map
          (univalentRecordBwdClause (v 3) (v 2) (v 1) (v 0))
          nfs)

  univalentRecordFwdBwdClause : (A B e p k i : R.Term)
    → ℕ × R.Name × R.Name → R.TC R.Clause
  univalentRecordFwdBwdClause A B e p k i (n , sfield , efield) =
      R.returnTC
      (R.clause [] [ varg (R.proj sfield) ]
        (R.def (quote retEq)
          (varg
            (R.def (quote idfun')
              (varg (v (6 + n)) ∷ varg (withStrProj A sfield) ∷ varg (withStrProj B sfield) ∷ varg e ∷ []))
            ∷ varg (R.def (quote pathMap) (varg (R.def srec []) ∷ varg e ∷ varg (R.def sfield []) ∷ varg p ∷ []))
            ∷ varg k
            ∷ varg i
            ∷ [])))

  univalentRecordFwdBwd : List (ℕ × R.Name × R.Name) → R.TC R.Term
  univalentRecordFwdBwd nfs =
    bodyTC >>= λ body →
    R.returnTC (vlam "A" (vlam "B" (vlam "e" (vlam "p" (vlam "k" (vlam "i" (R.pat-lam body [])))))))
    where
    bodyTC : R.TC (List R.Clause)
    bodyTC =
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (R.def (quote _≃_) (varg (tTyp (v 1)) ∷ varg (tTyp (v 0)) ∷ []))) $
      R.extendContext
        (varg
          (R.def (quote pathPShape)
            (varg (R.def srec []) ∷ varg (v 2) ∷ varg (v 1) ∷ varg (v 0) ∷ []))) $
      R.extendContext (varg tI) $
      R.extendContext (varg tI) $
      mapTC
        (List.map
          (univalentRecordFwdBwdClause
            (v 5) (v 4) (v 3) (v 2) (v 1) (v 0))
          nfs)

  univalentRecordBwdFwdClause : (A B e streq k : R.Term)
    → ℕ × R.Name × R.Name → R.TC R.Clause
  univalentRecordBwdFwdClause A B e streq k (n , sfield , efield) =
    R.returnTC
      (R.clause [] [ varg (R.proj efield) ]
        (R.def (quote secEq)
          (varg
            (R.def (quote idfun')
              (varg (v (5 + n)) ∷ varg (withStrProj A sfield) ∷ varg (withStrProj B sfield) ∷ varg e ∷ []))
            ∷ varg (R.def efield [ varg streq ])
            ∷ varg k
            ∷ [])))

  univalentRecordBwdFwd : List (ℕ × R.Name × R.Name) → R.TC R.Term
  univalentRecordBwdFwd nfs =
    bodyTC >>= λ body →
    R.returnTC (vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "k" (R.pat-lam body []))))))
    where
    bodyTC : R.TC (List R.Clause)
    bodyTC =
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (R.def (quote _≃_) (varg (tTyp (v 1)) ∷ varg (tTyp (v 0)) ∷ []))) $
      R.extendContext
        (varg (R.def erec (varg (v 2) ∷ varg (v 1) ∷ varg (v 0) ∷ []))) $
      R.extendContext (varg tI) $
      mapTC
        (List.map
          (univalentRecordBwdFwdClause
            (v 4) (v 3) (v 2) (v 1) (v 0))
          nfs)

  autoUnivalentRecord' : List (ℕ × R.Name × R.Name) → R.TC R.Term
  autoUnivalentRecord' nfs =
    univalentRecordFwd nfs >>= λ fwd →
    univalentRecordBwd nfs >>= λ bwd →
    univalentRecordFwdBwd nfs >>= λ fwdBwd →
    univalentRecordBwdFwd nfs >>= λ bwdFwd →
    R.returnTC
      (R.def (quote mkUnivalentStr) (withRecs (varg fwd ∷ varg bwd ∷ varg fwdBwd ∷ varg bwdFwd ∷ [])))
    where
    withRecs : List (R.Arg R.Term) → List (R.Arg R.Term)
    withRecs l = varg (R.def srec []) ∷ varg (R.def erec []) ∷ l

MacroUnivalentStr' : (d : Desc ℓ-zero) → uStrShape (MacroStructure d) (MacroEquivStr d)
MacroUnivalentStr' d A B e = MacroUnivalentStr d e

macro
  autoFieldEquiv : R.Name → R.Name → R.Term → R.Term → R.Term → R.TC Unit
  autoFieldEquiv srec sfield A B hole =
    newMeta (tDesc tℓ₀) >>= λ d →
    R.unify hole
      (R.def (quote MacroEquivStr)
        (varg d ∷ varg (withStrProj A sfield) ∷ varg (withStrProj B sfield) ∷ [])) >>
    fieldDesc' srec sfield >>=
    R.unify d

  autoUnivalentRecord : R.Name → R.Name → List (R.Name × R.Name) → R.Term → R.TC Unit
  autoUnivalentRecord srec erec fs hole =
    univalentsTC >>= λ univalents →
    R.getContext >>= λ ctx₀ →
    contextTC fs >>= λ ctx₁ →
    R.inContext (ctx₀ ++ ctx₁) (autoUnivalentRecord' srec erec (mapi _,_ fs)) >>= λ body →
    innerTyTC fs (R.def (quote uStrShape) (varg (R.def srec []) ∷ varg (R.def erec []) ∷ [])) >>= λ innerTy →
    R.unify
    -- R.typeError ([_] (R.termErr (
      (R.def (quote idfun)
        (varg innerTy
          ∷ varg (List.foldl (λ body (sfield , _) → vlam "univa" body) body fs)
          ∷ List.map varg (List.rev univalents)))
      -- )))
      hole
    where
    univalentsTC : R.TC (List R.Term)
    univalentsTC =
      mapTC
        (List.map
          (λ (sfield , _) →
            fieldDesc' srec sfield >>= λ d →
            R.returnTC (R.def (quote MacroUnivalentStr') [ varg d ]))
          fs)

    contextTC : List (R.Name × R.Name) → R.TC (List (R.Arg R.Term))
    contextTC [] = R.returnTC []
    contextTC ((sfield , _) ∷ fs) =
      fieldDesc' srec sfield >>= λ d →
      let ty = R.def (quote uStrShape) (varg (R.def (quote MacroStructure) (harg tℓ₀ ∷ varg d ∷ [])) ∷ varg (R.def (quote MacroEquivStr) [ varg d ]) ∷ []) in
      liftTC (varg ty ∷_) (contextTC fs)

    innerTyTC : List (R.Name × R.Name) → R.Term → R.TC R.Term
    innerTyTC [] acc = R.returnTC acc
    innerTyTC ((sfield , _) ∷ fs) acc =
      fieldDesc' srec sfield >>= λ d →
      let ty = R.def (quote uStrShape) (varg (R.def (quote MacroStructure) (harg tℓ₀ ∷ varg d ∷ [])) ∷ varg (R.def (quote MacroEquivStr) [ varg d ]) ∷ []) in
      innerTyTC fs (R.def (quote func) (varg ty ∷ varg acc ∷ []))

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
  autoUnivalentRecord Dog DogEquiv
    ((quote Dog.cat , quote DogEquiv.cat)
      ∷ (quote Dog.adult , quote DogEquiv.adult)
      ∷ (quote Dog.wolf , quote DogEquiv.wolf)
      ∷ [])
