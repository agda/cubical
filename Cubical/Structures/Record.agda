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

  _>>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → R.TC A → R.TC B → R.TC B
  f >> g = f >>= λ _ → g

  infixl 4 _>>=_ _>>_
  infixr 3 _$_

  mapTC : ∀ {ℓ} {A : Type ℓ} → List (R.TC A) → R.TC (List A)
  mapTC [] = R.returnTC []
  mapTC (r ∷ rs) = r >>= λ x → mapTC rs >>= λ xs → R.returnTC (x ∷ xs)

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

  func : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  func ℓ ℓ' = Type ℓ → Type ℓ'

  tStruct : R.Term → R.Term → R.Term
  tStruct ℓ ℓ' = R.def (quote func) (varg ℓ ∷ varg ℓ' ∷ [])

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

  uStrShape : (S : Type → Type) (ι : StrEquiv S ℓ-zero) → Type₁
  uStrShape S ι =
    (A B : TypeWithStr ℓ-zero S) (e : typ A ≃ typ B) → ι A B e ≃ PathP (λ i → S (ua e i)) (str A) (str B)

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

  univalentRecordFwdClause : (e streq i : R.Term) → R.Name × R.Name × R.Term → R.TC R.Clause
  univalentRecordFwdClause e streq i (sfield , efield , d) =
    R.returnTC
      (R.clause [] [ varg (R.proj sfield) ]
        (R.def (quote equivFun)
          (varg (R.def (quote MacroUnivalentStr) (varg d ∷ varg e ∷ []))
            ∷ varg (R.def efield [ varg streq ])
            ∷ varg i
            ∷ [])))

  univalentRecordFwd : List (R.Name × R.Name × R.Term) → R.TC R.Term
  univalentRecordFwd fds =
    bodyTC >>= λ body →
    R.returnTC (vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "i" (R.pat-lam body []))))))
    where
    bodyTC : R.TC (List R.Clause)
    bodyTC =
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (R.def (quote _≃_) (varg (tTyp (R.var 1 [])) ∷ varg (tTyp (R.var 0 [])) ∷ []))) $
      R.extendContext (varg (R.def erec (varg (R.var 2 []) ∷ varg (R.var 1 []) ∷ varg (R.var 0 []) ∷ []))) $
      R.extendContext (varg tI) $
      mapTC (List.map (univalentRecordFwdClause (R.var 2 []) (R.var 1 []) (R.var 0 [])) fds)

  univalentRecordBwdClause : (e : R.Term) (p : R.Term)
    → R.Name × R.Name × R.Term → R.TC R.Clause
  univalentRecordBwdClause e p (sfield , efield , d) =
    R.returnTC
      (R.clause [] [ varg (R.proj efield) ]
        (R.def (quote invEq)
          (varg (R.def (quote MacroUnivalentStr) (varg d ∷ varg e ∷ []))
            ∷ varg (R.def (quote pathMap) (varg (R.def srec []) ∷ varg e ∷ varg (R.def sfield []) ∷ varg p ∷ []))
            ∷ [])))

  univalentRecordBwd : List (R.Name × R.Name × R.Term) → R.TC R.Term
  univalentRecordBwd fds =
    bodyTC >>= λ body →
    R.returnTC (vlam "A" (vlam "B" (vlam "e" (vlam "p" (R.pat-lam body [])))))
    where
    bodyTC : R.TC (List R.Clause)
    bodyTC =
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (R.def (quote _≃_) (varg (tTyp (R.var 1 [])) ∷ varg (tTyp (R.var 0 [])) ∷ []))) $
      R.extendContext
        (varg
          (R.def (quote pathPShape)
            (varg (R.def srec []) ∷ varg (R.var 2 []) ∷ varg (R.var 1 []) ∷ varg (R.var 0 []) ∷ []))) $
      mapTC
        (List.map
          (univalentRecordBwdClause (R.var 1 []) (R.var 0 []))
          fds)

  univalentRecordFwdBwdClause : (A B e p k i : R.Term)
    → R.Name × R.Name × R.Term → R.TC R.Clause
  univalentRecordFwdBwdClause A B e p k i (sfield , efield , d) =
      R.returnTC
      (R.clause [] [ varg (R.proj sfield) ]
        (R.def (quote retEq)
          (varg
            (R.def (quote MacroUnivalentStr)
              (varg d ∷ harg (withStrProj A sfield) ∷ harg (withStrProj B sfield) ∷ varg e ∷ []))
            ∷ varg (R.def (quote pathMap) (varg (R.def srec []) ∷ varg e ∷ varg (R.def sfield []) ∷ varg p ∷ []))
            ∷ varg k
            ∷ varg i
            ∷ [])))

  univalentRecordFwdBwd : List (R.Name × R.Name × R.Term) → R.TC R.Term
  univalentRecordFwdBwd fds =
    bodyTC >>= λ body →
    R.returnTC (vlam "A" (vlam "B" (vlam "e" (vlam "p" (vlam "k" (vlam "i" (R.pat-lam body [])))))))
    where
    bodyTC : R.TC (List R.Clause)
    bodyTC =
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (R.def (quote _≃_) (varg (tTyp (R.var 1 [])) ∷ varg (tTyp (R.var 0 [])) ∷ []))) $
      R.extendContext
        (varg
          (R.def (quote pathPShape)
            (varg (R.def srec []) ∷ varg (R.var 2 []) ∷ varg (R.var 1 []) ∷ varg (R.var 0 []) ∷ []))) $
      R.extendContext (varg tI) $
      R.extendContext (varg tI) $
      mapTC
        (List.map
          (univalentRecordFwdBwdClause
            (R.var 5 []) (R.var 4 []) (R.var 3 []) (R.var 2 []) (R.var 1 []) (R.var 0 []))
          fds)

  univalentRecordBwdFwdClause : (A B e streq k : R.Term)
    → R.Name × R.Name × R.Term → R.TC R.Clause
  univalentRecordBwdFwdClause A B e streq k (sfield , efield , d) =
    R.returnTC
      (R.clause [] [ varg (R.proj efield) ]
        (R.def (quote secEq)
          (varg
            (R.def (quote MacroUnivalentStr)
              (varg d ∷ harg (withStrProj A sfield) ∷ harg (withStrProj B sfield) ∷ varg e ∷ []))
            ∷ varg (R.def efield [ varg streq ])
            ∷ varg k
            ∷ [])))

  univalentRecordBwdFwd : List (R.Name × R.Name × R.Term) → R.TC R.Term
  univalentRecordBwdFwd fds =
    bodyTC >>= λ body →
    R.returnTC (vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "k" (R.pat-lam body []))))))
    where
    bodyTC : R.TC (List R.Clause)
    bodyTC =
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (tTypeWithStr (R.def srec []))) $
      R.extendContext (varg (R.def (quote _≃_) (varg (tTyp (R.var 1 [])) ∷ varg (tTyp (R.var 0 [])) ∷ []))) $
      R.extendContext
        (varg (R.def erec (varg (R.var 2 []) ∷ varg (R.var 1 []) ∷ varg (R.var 0 []) ∷ []))) $
      R.extendContext (varg tI) $
      mapTC
        (List.map
          (univalentRecordBwdFwdClause
            (R.var 4 []) (R.var 3 []) (R.var 2 []) (R.var 1 []) (R.var 0 []))
          fds)

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
    mapTC (List.map addDesc fs) >>= λ fds →
    newMeta (R.def (quote fwdShape) (withRecs [])) >>= λ fwd →
    newMeta (R.def (quote bwdShape) (withRecs [])) >>= λ bwd →
    newMeta (R.def (quote fwdBwdShape) (withRecs (varg fwd ∷ varg bwd ∷ []))) >>= λ fwdBwd →
    newMeta (R.def (quote bwdFwdShape) (withRecs (varg fwd ∷ varg bwd ∷ []))) >>= λ bwdFwd →
    R.unify hole (R.def (quote mkUnivalentStr) (withRecs (varg fwd ∷ varg bwd ∷ varg fwdBwd ∷ varg bwdFwd ∷ []))) >>
    (univalentRecordFwd srec erec fds >>= R.unify fwd) >>
    (univalentRecordBwd srec erec fds >>= R.unify bwd) >>
    (univalentRecordFwdBwd srec erec fds >>= R.unify fwdBwd) >>
    (univalentRecordBwdFwd srec erec fds >>= R.unify bwdFwd)
    where
    addDesc : R.Name × R.Name → R.TC (R.Name × R.Name × R.Term)
    addDesc (sfield , efield) = fieldDesc' srec sfield >>= λ d → R.returnTC (sfield , efield , d)

    withRecs : List (R.Arg R.Term) → List (R.Arg R.Term)
    withRecs l = varg (R.def srec []) ∷ varg (R.def erec []) ∷ l

record Dog (X : Type) : Type where
  field
    cat : X → X → X
    adult : X

open Dog

record DogEquiv (A B : TypeWithStr ℓ-zero Dog) (e : typ A ≃ typ B) : Type where
  field
    cat : autoFieldEquiv Dog cat A B e
    adult : autoFieldEquiv Dog adult A B e

open DogEquiv

test : (A B : TypeWithStr ℓ-zero Dog) (e : typ A ≃ typ B)
  → DogEquiv A B e ≃ PathP (λ i → Dog (ua e i)) (str A) (str B)
test A B =
  autoUnivalentRecord Dog DogEquiv
    ((quote Dog.cat , quote DogEquiv.cat)
      ∷ (quote Dog.adult , quote DogEquiv.adult)
      ∷ [])
    A B
