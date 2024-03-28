{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.Solver3 where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li
open import Cubical.Data.Maybe as Mb


open import Cubical.HITs.Interval

open import Cubical.Relation.Nullary

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.WildCatSolver.Reflection
open import Cubical.Tactics.Reflection
open import Agda.Builtin.String


private
  variable
    ℓ ℓ' : Level
    A A' : Type ℓ


infixr 5 _∷Tω_

data [Typeₙ] : Typeω where
 [] : [Typeₙ]
 _∷Tω_ : ∀ {ℓ} → Type ℓ → [Typeₙ] → [Typeₙ]

maxℓ : [Typeₙ] → Level
maxℓ [] = ℓ-zero
maxℓ (_∷Tω_ {ℓ} _ x₁) = ℓ-max ℓ (maxℓ x₁)

lookupTₙ : (Ts : [Typeₙ]) → ℕ → Type (maxℓ Ts)
lookupTₙ [] x = ⊥*
lookupTₙ (x₁ ∷Tω Ts) zero = Lift {_} {maxℓ Ts} x₁
lookupTₙ (_∷Tω_ {ℓ} x₁ Ts) (suc x) = Lift {_} {ℓ} (lookupTₙ Ts x)

ℓAt : (Ts : [Typeₙ]) → ℕ → Level
ℓAt [] x = ℓ-zero
ℓAt (_∷Tω_ {ℓ} x₁ Ts) zero = ℓ
ℓAt (x₁ ∷Tω Ts) (suc x) = ℓAt Ts x

TyAt : (Ts : [Typeₙ]) → ∀ k → Type (ℓAt Ts k)
TyAt [] k = ⊥*
TyAt (x ∷Tω Ts) zero = x
TyAt (x ∷Tω Ts) (suc k) = TyAt Ts k

cast↓ : ∀ Ts k → lookupTₙ Ts k → TyAt Ts k
cast↓ [] k ()
cast↓ (x₁ ∷Tω Ts) zero x = lower x
cast↓ (x₁ ∷Tω Ts) (suc k) x = cast↓ Ts k (lower x)

cast↓Inj : ∀ {[T] A x y} → cast↓ [T] A x ≡ cast↓ [T] A y → x ≡ y
cast↓Inj {[]} {A = A} {()}
cast↓Inj {_ ∷Tω [T]} {A = zero} {lift lower₁} {lift lower₂} = cong lift
cast↓Inj {_ ∷Tω [T]} {A = suc A} {lift lower₁} {lift lower₂} p =
  cong lift (cast↓Inj {[T] = [T]} {A = A} p)

cast↓Inj-sec : ∀ {[T] A x y} p →
 cast↓Inj {[T]} {A} {x} {y} (cong (cast↓ [T] A ) p) ≡ p 
cast↓Inj-sec {x ∷Tω [T]} {A = zero} p = refl
cast↓Inj-sec {x ∷Tω [T]} {A = suc A} p =
 cong (cong lift) $ cast↓Inj-sec {[T]} {A} (cong lower p) 

cast↓Inj-∙∙ : ∀ {[T] A x y z w} p q r →
   cast↓Inj {[T]} {A} {x} {w} (p ∙∙ q ∙∙ r)
     ≡ (cast↓Inj p ∙∙ cast↓Inj {[T]} {A} {y} {z}  q ∙∙ cast↓Inj r)
   
     
cast↓Inj-∙∙ {x ∷Tω [T]} {zero} p q r = cong-∙∙ lift _ _ _
cast↓Inj-∙∙ {_ ∷Tω [T]} {suc A} p q r =
 cong (cong lift) (cast↓Inj-∙∙  {[T]} {A} p q r) ∙ cong-∙∙ lift _ _ _ 


cast↑ : ∀ Ts k → TyAt Ts k → lookupTₙ Ts k
cast↑ [] k ()
cast↑ (x₁ ∷Tω Ts) zero x = lift x
cast↑ (x₁ ∷Tω Ts) (suc k) x = lift $ cast↑ Ts k x

-- Ts-arr : (Ts : [Typeₙ]) → ∀ s t → Type (ℓ-max (ℓAt Ts s) (ℓAt Ts t))
-- Ts-arr Ts s t = TyAt Ts s → TyAt Ts t


-- Ts-arr' : (Ts : [Typeₙ]) → ℕ → ℕ → Type (maxℓ Ts)
-- Ts-arr' [] x x₁ = Unit
-- Ts-arr' (x₂ ∷Tω Ts) zero zero = Lift {_} {maxℓ Ts} (x₂ → x₂)
-- Ts-arr' (x₂ ∷Tω Ts) zero (suc x₁) = {!Ts!} 
-- Ts-arr' (x₂ ∷Tω Ts) (suc x) zero = {!!}
-- Ts-arr' (_∷Tω_ {ℓ} x₂ Ts) (suc x) (suc x₁) = 
--  Lift {_} {ℓ} (Ts-arr' (Ts) (x) (x₁))

-- Ts-arr' : (Ts : [Typeₙ]) → ∀ s t →
--  (lookupTₙ Ts s → lookupTₙ Ts t) → Ts-arr Ts s t
-- Ts-arr' Ts s t x x₁ = {!!}



data PathCase : {ℓ : Level} {A : Type ℓ} {a₀ a₁ : A} → a₀ ≡ a₁ → Typeω where
 reflCase : ∀ {ℓ A x} → PathCase {ℓ} {A} (refl {x = x})
 compCase : ∀ {ℓ A x y z w} → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
            →  PathCase {ℓ} {A = A} (p ∙∙ q ∙∙ r)
 congCase : ∀ {ℓ ℓ' A A'} (f : A → A') {x y}
                 → (p : Path {ℓ} A x y)  → PathCase {ℓ'} {A = A'} (cong f p)


module _ {ℓ ℓ'} {A : Type ℓ} {A' : Type ℓ'} (f : A → A') {x y}
                   (p : Path {ℓ} A x y) where

 pathCaseCongTest : PathCase (cong f p)
 pathCaseCongTest = congCase f λ z → p z


infixl 5 _fp∷_
infixl 5 _fp++_

data FlatPath {ℓ} (A : Type ℓ) : Bool → (a₀ a₁ : A) → Type ℓ where
 [] : ∀ {x b} → FlatPath A b x x
 _fp∷_ : ∀ {x y z b} → FlatPath A b x y → y ≡ z → FlatPath A b x z
 _invol∷_ : ∀ {x y z} → FlatPath A true x y → y ≡ z → FlatPath A true x y 


FP⟦_⟧ : {a₀ a₁ : A} → FlatPath A false a₀ a₁ → a₀ ≡ a₁
FP⟦ [] ⟧ = refl
FP⟦ x fp∷ x₁ ⟧ = FP⟦ x ⟧ ∙ x₁

pattern fp[_] x = [] fp∷ x

_fp++_ : ∀ {x y z}
 → FlatPath A false x y
 → FlatPath A false y z
 → FlatPath A false x z
x fp++ [] = x
x fp++ (x₁ fp∷ x₂) = x fp++ x₁ fp∷ x₂

fp++∙ : {a₀ a₁ a₂ : A} → (fp : FlatPath A false a₀ a₁)
             (fp' : FlatPath A false a₁ a₂)
          → FP⟦ fp ⟧ ∙ FP⟦ fp' ⟧ ≡ FP⟦ fp fp++ fp' ⟧
fp++∙ fp [] = sym (rUnit _)
fp++∙ fp (fp' fp∷ x) = assoc _ _ _ ∙ cong (_∙ x) (fp++∙ fp fp')

module _ ([T] : [Typeₙ]) where

 data PathExpr : (k : ℕ) (a₀ a₁ : lookupTₙ [T] k) → Type (maxℓ [T]) where
  reflExpr : ∀ {A x} → PathExpr A x x
  atomExpr : ∀ {A x y} → (p : x ≡ y) → PathExpr A x y
  compExpr : ∀ {A x y z w} 
   → PathExpr A x y → PathExpr A y z → PathExpr A z w
   → PathExpr A x w
  congExpr : ∀ {A A' x y} → (f : lookupTₙ [T] A → lookupTₙ [T] A') 
   → PathExpr A x y 
   → PathExpr A' (f x) (f y)


 PE⟦_⟧ : ∀ {A a₀ a₁} → PathExpr A a₀ a₁ →
  (cast↓ [T] A a₀) ≡  (cast↓ [T] A a₁)
 PE⟦ reflExpr ⟧ = refl
 PE⟦ atomExpr p ⟧ = cong _ p
 PE⟦ compExpr x x₁ x₂ ⟧ = PE⟦ x ⟧ ∙∙ PE⟦ x₁ ⟧ ∙∙ PE⟦ x₂ ⟧
 PE⟦ congExpr f x ⟧ = cong _ (cast↓Inj {[T]} PE⟦ x ⟧)

 cong-flat : ∀ {A A₁ a₀ a₁ } → (f : lookupTₙ [T] A₁ → lookupTₙ [T] A)
               → PathExpr A₁ a₀ a₁
              
              → FlatPath (TyAt [T] A) false (cast↓ [T] A (f a₀))
                    (cast↓ [T] A (f a₁))
 cong-flat f reflExpr = []
 cong-flat f (atomExpr p) = fp[ cong _ p ]
 cong-flat f (compExpr x x₁ x₂) =
   cong-flat f x fp++ cong-flat f x₁ fp++ cong-flat f x₂
 cong-flat f (congExpr f₁ x) = cong-flat (f ∘ f₁) x

 flat⟦_⟧ : ∀ {A a₀ a₁} → PathExpr A a₀ a₁
              → FlatPath (TyAt [T] A) false (cast↓ [T] A a₀) (cast↓ [T] A a₁)
 flat⟦ reflExpr ⟧ = []
 flat⟦ atomExpr p ⟧ = fp[ cong (cast↓ [T] _) p ]
 flat⟦ compExpr x x₁ x₂ ⟧ = flat⟦ x ⟧ fp++ flat⟦ x₁ ⟧ fp++ flat⟦ x₂ ⟧
 flat⟦ congExpr f x ⟧ = cong-flat f x


 cong-flat≡ : ∀ {A₁ A a₀ a₁} → (pe : PathExpr A₁ a₀ a₁) →
                 (f   : lookupTₙ [T] A₁ → lookupTₙ [T] A) → 
                 (λ i → cast↓ [T] A (f (cast↓Inj PE⟦ pe ⟧ i))) ≡
                  FP⟦ cong-flat f pe ⟧
 cong-flat≡ reflExpr f = cong (cong (cast↓ [T] _ ∘ f)) (cast↓Inj-sec _)
 cong-flat≡ (atomExpr p) f =
   cong (cong (cast↓ [T] _ ∘ f)) (cast↓Inj-sec _) ∙ lUnit _
 cong-flat≡ (compExpr pe pe₁ pe₂) f =
    (cong (cong (cast↓ [T] _ ∘ f)) (cast↓Inj-∙∙ _ _ _) ∙∙
      cong-∙∙ ((cast↓ [T] _ ∘ f)) _ _ _ ∙∙ 
        (λ i → doubleCompPath-elim
           (cong-flat≡ pe f i)
           (cong-flat≡ pe₁ f i)
           (cong-flat≡ pe₂ f i) i))
      ∙∙ cong (_∙ FP⟦ cong-flat f  pe₂ ⟧)
       (fp++∙ (cong-flat f pe) (cong-flat f pe₁))
     ∙∙ fp++∙ _ (cong-flat f pe₂)
 cong-flat≡ (congExpr f₁ pe) f =
  cong (cong (cast↓ [T] _ ∘ f)) (cast↓Inj-sec _) ∙ cong-flat≡ pe (f ∘ f₁)
  
 pe≡flat : ∀ {A a₀ a₁} → (pe : PathExpr A a₀ a₁) →
                   PE⟦ pe ⟧ ≡ FP⟦ flat⟦ pe ⟧ ⟧
 pe≡flat reflExpr = refl
 pe≡flat (atomExpr p) = lUnit _
 pe≡flat (compExpr pe pe₁ pe₂) =
   (λ i → doubleCompPath-elim
           (pe≡flat pe i)
           (pe≡flat pe₁ i)
           (pe≡flat pe₂ i) i)
   ∙∙ cong (_∙ FP⟦ flat⟦ pe₂ ⟧ ⟧) (fp++∙ flat⟦ pe ⟧ flat⟦ pe₁ ⟧)
     ∙∙ fp++∙ _ flat⟦ pe₂ ⟧

 pe≡flat (congExpr f pe) = cong-flat≡ pe f

-- data PathExprω : {ℓ : Level} (A : Type ℓ) {a₀ a₁ : A} → a₀ ≡ a₁ → Typeω where
--  reflExpr : ∀ {ℓ A x} → PathExprω {ℓ} A (refl {x = x})
--  atomExpr : ∀ {ℓ A x y} → (p : x ≡ y) → PathExprω {ℓ} A p
--  compExpr : ∀ {ℓ A x y z w} → {p : x ≡ y} {q : y ≡ z} {r : z ≡ w}
--   → PathExprω {ℓ} A p → PathExprω {ℓ} A q → PathExprω {ℓ} A r
--   → PathExprω {ℓ} A (p ∙∙ q ∙∙ r)
--  congExpr : ∀ {ℓ ℓ' A A' x y} → (f : A → A') {p : x ≡ y}
--   → PathExprω {ℓ} A p 
--   → PathExprω {ℓ'} A' (cong f p) 


-- data PathExpr {ℓ : Level} : (A : Type ℓ) {a₀ a₁ : A} → a₀ ≡ a₁ → Type (ℓ-suc ℓ) where
--  reflExpr : ∀ {A x} → PathExpr A (refl {x = x})
--  atomExpr : ∀ {A x y} → (p : x ≡ y) → PathExpr A p
--  compExpr : ∀ {A x y z w} → {p : x ≡ y} {q : y ≡ z} {r : z ≡ w}
--   → PathExpr A p → PathExpr A q → PathExpr A r
--   → PathExpr A (p ∙∙ q ∙∙ r)
--  congExpr : ∀ {A A' x y} → (f : A → A') {p : x ≡ y}
--   → PathExpr {ℓ} A {x} {y} p 
--   → PathExpr A' (cong f p) 



-- PEω⟦_⟧ : {ℓ : Level} {A : Type ℓ} {a₀ a₁ : A} → {p : a₀ ≡ a₁} →
--            PathExprω A p → a₀ ≡ a₁
-- PEω⟦ reflExpr ⟧ = refl
-- PEω⟦ atomExpr p ⟧ = p
-- PEω⟦ compExpr x x₁ x₂ ⟧ = PEω⟦ x ⟧ ∙∙ PEω⟦ x₁ ⟧ ∙∙ PEω⟦ x₂ ⟧
-- PEω⟦ congExpr f x ⟧ = cong f PEω⟦ x ⟧



-- record ΣPathExprω : Typeω where
--  field
--   ℓa : Level
--   A : Type ℓa
--   a₀ a₁ : A
--   p : a₀ ≡ a₁
--   expr : PathExprω A p

--  ΣPEω⟦_⟧ : a₀ ≡ a₁
--  ΣPEω⟦_⟧ = PEω⟦ expr ⟧

-- record ΣPathExpr {ℓ} : Type (ℓ-suc ℓ) where
--  constructor Σpe
--  field
--   {A} : Type ℓ
--   {a₀ a₁} : A
--   {p} : a₀ ≡ a₁
--   expr : PathExpr A p

--  ΣPE⟦_⟧ : a₀ ≡ a₁
--  ΣPE⟦_⟧ = PE⟦ expr ⟧



module PathTrm (A B : Type ℓ) where
 data PathTrm : Type ℓ where
  reflTrm : PathTrm
  atomTrm : A → PathTrm
  compTrm : PathTrm → PathTrm → PathTrm → PathTrm
  congTrm : B → PathTrm → PathTrm  

 module showPathTrm (showA : A → String) (showB : B → String) where  
  showPT : PathTrm → String 
  showPT reflTrm = "refl"
  showPT (atomTrm x) = showA x
  showPT (compTrm x x₁ x₂) =
    "(" <> showPT x <> "∙∙" <> showPT x₁ <> "∙∙" <> showPT x₂ <> ")"
  showPT (congTrm x x₁) =
    "(" <> showB x <> "⟪" <> showPT x₁ <> "⟫)"    


module _ {ℓ ℓ'}
       {A B : Type ℓ}
       {A' B' : Type ℓ'}
       (f : A → R.TC A')
       (g : B → R.TC B') where
 open PathTrm
 mmapPT : PathTrm A B → R.TC $ PathTrm A' B'
 mmapPT reflTrm = pure reflTrm
 mmapPT (atomTrm x) = ⦇ atomTrm (f x) ⦈ 
 mmapPT (compTrm x x₁ x₂) =
  ⦇ compTrm (mmapPT x) (mmapPT x₁) (mmapPT x₂) ⦈
 mmapPT (congTrm x x₁) =
  ⦇ congTrm (g x) (mmapPT x₁) ⦈


module RTrm = PathTrm R.Term R.Term
module StrTrm = PathTrm String String

-- unqouteRTrm : ∀ {ℓ} → RTrm.PathTrm → R.TC (ΣPathExpr {ℓ})
-- unqouteRTrm PathTrm.reflTrm = pure $ Σpe {A = Unit*} reflExpr
-- unqouteRTrm (PathTrm.atomTrm x) =
--   ⦇ (Σpe ∘ atomExpr)  {!x!} ⦈
-- unqouteRTrm (PathTrm.compTrm x x₁ x₂) = {!!}
-- unqouteRTrm (PathTrm.congTrm x x₁) = {!!}

showRTrmTC : RTrm.PathTrm → R.TC String
showRTrmTC =
  mmapPT
  (R.formatErrorParts ∘ [_]ₑ) (R.formatErrorParts ∘ [_]ₑ)
  >=> (pure ∘ StrTrm.showPathTrm.showPT (idfun _) (idfun _) )



module tryPathE where

 try≡ : ℕ → R.Term → R.TC (RTrm.PathTrm)


 tryRefl : R.Term → R.TC (RTrm.PathTrm)
 tryRefl t = do
       _ ← R.noConstraints $ R.checkType
             (R.con (quote reflCase) [])
             (R.def (quote PathCase) ([ varg t ]))
       R.returnTC (RTrm.reflTrm)

 tryComp : ℕ → R.Term → R.TC (RTrm.PathTrm)
 tryComp zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 tryComp (suc k) t = do
       tm ← R.noConstraints $ R.checkType
             (R.con (quote compCase) (R.unknown v∷ R.unknown v∷ [ varg R.unknown ]))
             (R.def (quote PathCase) ([ varg t ]))
       (t1 , t2 , t3) ← h tm
       (t1') ← try≡ k t1
       (t2') ← try≡ k t2
       (t3') ← try≡ k t3
       R.returnTC (RTrm.compTrm t1' t2' t3')

  where

  h : R.Term → R.TC (R.Term × R.Term × R.Term)
  h (R.con (quote compCase) l) = match3Vargs l
  h _ = R.typeError [ (R.strErr "tryCompFail-h") ]


 atom : R.Term → R.TC (RTrm.PathTrm)
 atom x = R.returnTC (RTrm.atomTrm x)


 try≡ zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 try≡ (suc k) t =
   R.catchTC
    (tryRefl t)
    (R.catchTC (tryComp k t) (atom t))









 -- data IsPathTrmReg : {a₀ a₁ : A} → a₀ ∼ a₁ → Type (ℓ-max ℓ ℓ') where
 --  isReflTrmReg : ∀ {x} → IsPathTrmReg (∼refl {x = x})
 --  isAtomTrmReg : ∀ {x y} → (p : x ∼ y) → IsPathTrmReg p
 --  isCompTrmReg : ∀ {x y z : _} → {p : x ∼ y} {q : y ∼ z}
 --   → IsPathTrmReg p → IsPathTrmReg q → IsPathTrmReg (p ∼∙ q)

 -- data IsPathTrmDeas : {a₀ a₁ : A} → a₀ ∼ a₁ → Type (ℓ-max ℓ ℓ') where
 --  nilTrmDeasRefl : ∀ {x} → IsPathTrmDeas (∼refl {x = x})
 --  consTrmDeas : ∀ {x y z : _} → {p : x ∼ y} → IsPathTrmDeas p → (q : y ∼ z) → IsPathTrmDeas (p ∼∙ q)

 -- data IsPathTrmInvol : (a₀ a₁ : A) → Type (ℓ-max ℓ ℓ') where
 --  nilTrmInvolRefl : ∀ {x} → IsPathTrmInvol x x
 --  consTrmInvol : ∀ {x y z : _}  →
 --   IsPathTrmInvol x y → (q : y ∼ z) → IsPathTrmInvol x z
 --  involTrmInvol : ∀ {x y z : _} → IsPathTrmInvol x y → (q : y ∼ z) →
 --    IsPathTrmInvol x y


--  module show (showA : ∀ {ℓ} A {a₀ a₁ : A} → (p : a₀ ≡ a₁) → String) where
--   showIPT : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → IsPathTrm p → String
--   showIPT isReflTrm = "refl"
--   showIPT (isAtomTrm x) = showA x
--   showIPT (isCompTrm isReflTrm x₁ x₂) =
--         "(" <> showIPT x₁ <> "∙" <> showIPT x₂ <> ")"
--   showIPT (isCompTrm x x₁ isReflTrm) =
--          "(" <> showIPT x <> "∙'" <> showIPT x₁ <> ")"
--   showIPT (isCompTrm x x₁ x₂) =
--         "(" <> showIPT x <> "∙∙" <> showIPT x₁ <> "∙∙" <> showIPT x₂ <> ")"

--   -- showIPTD : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → IsPathTrmDeas p → String

--   -- showIPTD nilTrmDeasRefl = "refl"
--   -- showIPTD (consTrmDeas x q) = showIPTD x <> "∙" <> showA q

--   -- showIPTI : {a₀ a₁ : A} → IsPathTrmInvol a₀ a₁ → String
--   -- showIPTI nilTrmInvolRefl = "refl"
--   -- showIPTI (consTrmInvol x q) = showIPTI x <> "∙" <> showA q
--   -- showIPTI (involTrmInvol x q) = showIPTI x <> "∙⟦" <> showA q <> "∙" <> showA q  <> "⁻¹⟧"


--  -- depthIsPathTrmDeas : ∀ {a₀ a₁ : A} → ∀ {p : a₀ ∼ a₁}
--  --                          → IsPathTrmDeas p → ℕ
--  -- depthIsPathTrmDeas nilTrmDeasRefl = zero
--  -- depthIsPathTrmDeas (consTrmDeas x q) = suc (depthIsPathTrmDeas x)

--  -- hasRedexes : ∀ {a₀ a₁} → IsPathTrmInvol a₀ a₁ → Bool
--  -- hasRedexes nilTrmInvolRefl = false
--  -- hasRedexes (consTrmInvol x q) = hasRedexes x
--  -- hasRedexes (involTrmInvol x q) = true

--  -- Deas→Invol : ∀ {a₀ a₁ : A} → ∀ {p} → IsPathTrmDeas {a₀ = a₀} {a₁ = a₁} p → IsPathTrmInvol a₀ a₁
--  -- Deas→Invol nilTrmDeasRefl = nilTrmInvolRefl
--  -- Deas→Invol (consTrmDeas x q) = consTrmInvol (Deas→Invol x) q

--  -- IsPathTrmDeas∙ : ∀ {x y z : _} → {p : x ∼ y} {q : y ∼ z} →
--  --   IsPathTrmDeas p → IsPathTrmDeas q → Σ _ λ p∙q → IsPathTrmDeas {x} {z} p∙q
--  -- IsPathTrmDeas∙ p' nilTrmDeasRefl = _ , p'
--  -- IsPathTrmDeas∙ nilTrmDeasRefl q'@(consTrmDeas _ _) = _ , q'
--  -- IsPathTrmDeas∙ p' (consTrmDeas q' q'') =
--  --   let (_ , u) = IsPathTrmDeas∙ p' q'
--  --   in _ , consTrmDeas u q''


--  -- Invol→Deas↓ : ∀ {a₀ a₁ : A} → IsPathTrmInvol a₀ a₁ → Σ _ $ IsPathTrmDeas {a₀ = a₀} {a₁ = a₁}

--  -- Invol→Deas↓ nilTrmInvolRefl = _ , nilTrmDeasRefl
--  -- Invol→Deas↓ (consTrmInvol x q) =
--  --   IsPathTrmDeas∙ (snd (Invol→Deas↓ x)) (consTrmDeas nilTrmDeasRefl q)
--  -- Invol→Deas↓ (involTrmInvol x q) = Invol→Deas↓ x

--  -- ⟦_⟧r : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → IsPathTrm p → (Σ _ λ r → (IsPathTrmReg r × (p ≡ r)))
--  -- ⟦ isReflTrm ⟧r = ∼refl , isReflTrmReg , refl
--  -- ⟦ isAtomTrm p ⟧r = p , isAtomTrmReg _ , refl
--  -- ⟦ isCompTrm {p = p} {q = q} {r = r} p' q' r' ⟧r =
--  --   let (_ , pR , p=) = ⟦ p' ⟧r ; (_ , qR , q=) = ⟦ q' ⟧r ; (_ , rR , r=) = ⟦ r' ⟧r
--  --   in _ , isCompTrmReg (isCompTrmReg pR qR) rR ,
--  --            λ i → ∼doubleCompPath-elim (p= i) (q= i) (r= i) i


--  -- ⟦_⟧da : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → IsPathTrmReg p → (Σ _ λ r → (IsPathTrmDeas r))
--  -- ⟦ isReflTrmReg ⟧da = _ , nilTrmDeasRefl
--  -- ⟦ isAtomTrmReg p ⟧da = _ ,  consTrmDeas nilTrmDeasRefl p
--  -- ⟦ isCompTrmReg p' q' ⟧da =
--  --   let (_ , qD) = ⟦ q' ⟧da
--  --       (_ , pD) = ⟦ p' ⟧da
--  --       (_ , p∙qD) = IsPathTrmDeas∙ pD qD
--  --   in _ , p∙qD

--  -- ⟦_⟧da∘r : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → IsPathTrm p → (Σ _ IsPathTrmDeas)
--  -- ⟦ x ⟧da∘r =  ⟦ fst (snd (⟦ x ⟧r)) ⟧da
--  -- module PT≡ (∼rUnit : ∀ {x y} → (p : x ∼ y) → p ≡ p ∼∙ ∼refl)
--  --            (∼lUnit : ∀ {x y} → (p : x ∼ y) → p ≡  ∼refl ∼∙ p) where

--  --  IsPathTrmDeas∙≡ : ∀ {x y z : _} → {p : x ∼ y} {q : y ∼ z} →
--  --    (p' : IsPathTrmDeas p) → (q' : IsPathTrmDeas q) →
--  --      (fst (IsPathTrmDeas∙ p' q') ≡ (p ∼∙ q))
--  --  IsPathTrmDeas∙≡ _ nilTrmDeasRefl = ∼rUnit _
--  --  IsPathTrmDeas∙≡ nilTrmDeasRefl (consTrmDeas p q) = ∼lUnit _
--  --  IsPathTrmDeas∙≡ (consTrmDeas p q) (consTrmDeas p' q') =
--  --    cong (_∼∙ q')  ( (IsPathTrmDeas∙≡ (consTrmDeas p q) p')) ∙
--  --      sym (∼assoc _ _ _)

--  --  ⟦_⟧da≡ : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → (p' : IsPathTrmReg p) →
--  --           fst ⟦ p' ⟧da ≡ p
--  --  ⟦ isReflTrmReg ⟧da≡ = refl
--  --  ⟦ isAtomTrmReg _ ⟧da≡ = sym (∼lUnit _)
--  --  ⟦ isCompTrmReg p' q' ⟧da≡ =
--  --     IsPathTrmDeas∙≡ (snd ⟦ p' ⟧da) (snd ⟦ q' ⟧da) ∙ cong₂ _∼∙_ ⟦ p' ⟧da≡ ⟦ q' ⟧da≡

--  --  daSingl : {a₀ a₁ : A} → {p : a₀ ∼ a₁} → (q : IsPathTrm p) → p ≡ fst ⟦ fst (snd ⟦ q ⟧r) ⟧da
--  --  daSingl x = let (_ , x' , x=) = ⟦ x ⟧r in x= ∙ sym (⟦ x' ⟧da≡)



-- -- module _ {A : Type ℓ} where

-- --  open PT {A = A} _≡_ refl _∙_ _∙∙_∙∙_ doubleCompPath-elim assoc public
-- --  open PT≡ rUnit lUnit public



-- --  ⟦_,_⟧ti : {a₀ a₁ : A} → IsPathTrmInvol a₀ a₁ → Interval → a₀ ≡ a₁
-- --  ⟦ nilTrmInvolRefl , _ ⟧ti = refl
-- --  ⟦ consTrmInvol x q , 𝓲 ⟧ti = ⟦ x , 𝓲 ⟧ti ∙ q
-- --  ⟦ involTrmInvol x q , zero ⟧ti = (⟦ x , zero ⟧ti ∙ q) ∙ sym q
-- --  ⟦ involTrmInvol x q , one ⟧ti = ⟦ x , one ⟧ti
-- --  ⟦ involTrmInvol x q , seg j ⟧ti i =
-- --    hcomp (λ k → λ { (j = i1) → ⟦ x , one ⟧ti i
-- --                   ; (i = i1) → q (~ k ∧ ~ j)
-- --                   ; (i = i0) → ⟦ x , seg j ⟧ti i0
-- --                   }) (compPath-filler ⟦ x , seg j ⟧ti q (~ j) i)

-- --  ⟦_⟧ti≡ : {a₀ a₁ : A} → (x : IsPathTrmInvol a₀ a₁) → ⟦ x , zero ⟧ti ≡ ⟦ x , one ⟧ti
-- --  ⟦_⟧ti≡ x i = ⟦ x , (seg i) ⟧ti



-- module _ (A : Type ℓ) (a : A) where
--  module PTG = PT {A = Unit} (λ _ _ → A)
--                   (a)
--                   (λ _ _ → a)
--                   (λ _ _ _ → a)
--                   (λ _ _ _ → refl)
--                   (λ _ _ _ → refl)

-- module PTrm = PTG R.Term R.unknown

-- module Pℕ = PTG (Bool × ℕ) (true , 0)

-- module PℕS = Pℕ.show (λ (b , i) → let v = mkNiceVar i in if b then v else (v <> "⁻¹"))


-- -- module _ (f : (Bool × ℕ) → R.Term) where
-- --  mapPTG : Pℕ.IsPathTrmInvol _ _ → PTrm.IsPathTrmInvol _ _
-- --  mapPTG PT.nilTrmInvolRefl = PT.nilTrmInvolRefl
-- --  mapPTG (PT.consTrmInvol x q) = PT.consTrmInvol (mapPTG x) (f q)
-- --  mapPTG (PT.involTrmInvol x q) = PT.involTrmInvol (mapPTG x) (f q)


-- IsRedex? : ∀ x x' → Dec (Path (Bool × ℕ) x (not (fst x') , snd x'))
-- IsRedex? _ _ = discreteΣ 𝟚._≟_ (λ _ → discreteℕ) _ _

-- -- ℕDeas→ℕInvol : ∀ {p} → Pℕ.IsPathTrmDeas p → Pℕ.IsPathTrmInvol _ _

-- -- consInvolℕ : ∀ {p} → Pℕ.IsPathTrmDeas p → (Bool × ℕ) → Pℕ.IsPathTrmInvol _ _
-- -- consInvolℕ PT.nilTrmDeasRefl x = PT.consTrmInvol PT.nilTrmInvolRefl x
-- -- consInvolℕ q'@(PT.consTrmDeas x q) x₁ =
-- --     decRec (λ _ → Pℕ.involTrmInvol (ℕDeas→ℕInvol x) q)
-- --               (λ _ → Pℕ.consTrmInvol (ℕDeas→ℕInvol q') x₁) (IsRedex? q x₁ )



-- -- ℕDeas→ℕInvol PT.nilTrmDeasRefl = PT.nilTrmInvolRefl
-- -- ℕDeas→ℕInvol (PT.consTrmDeas p' q') = consInvolℕ p' q'

-- module tryPathE where

--  try≡ : ℕ → R.Term → R.TC (Σ _ PTrm.IsPathTrm)


--  tryRefl : R.Term → R.TC (Σ _ PTrm.IsPathTrm)
--  tryRefl t = do
--        _ ← R.noConstraints $ R.checkType
--              (R.con (quote reflCase) [])
--              (R.def (quote PathCase) ([ varg t ]))
--        R.returnTC (_ , PTrm.isReflTrm)

--  tryComp : ℕ → R.Term → R.TC (Σ _ PTrm.IsPathTrm)
--  tryComp zero _ = R.typeError [ (R.strErr "Magic number to low") ]
--  tryComp (suc k) t = do
--        tm ← R.noConstraints $ R.checkType
--              (R.con (quote compCase) (R.unknown v∷ R.unknown v∷ [ varg R.unknown ]))
--              (R.def (quote PathCase) ([ varg t ]))
--        (t1 , t2 , t3) ← h tm
--        (_ , t1') ← try≡ k t1
--        (_ , t2') ← try≡ k t2
--        (_ , t3') ← try≡ k t3
--        R.returnTC (_ , PTrm.isCompTrm t1' t2' t3')

--   where

--   h : R.Term → R.TC (R.Term × R.Term × R.Term)
--   h (R.con (quote compCase) l) = match3Vargs l
--   h _ = R.typeError [ (R.strErr "tryCompFail-h") ]


--  atom : R.Term → R.TC (Σ _ PTrm.IsPathTrm)
--  atom x = R.returnTC (_ , PTrm.isAtomTrm x)


--  try≡ zero _ = R.typeError [ (R.strErr "Magic number to low") ]
--  try≡ (suc k) t =
--    R.catchTC
--     (tryRefl t)
--     (R.catchTC (tryComp k t) (atom t))

-- lamWrap' : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → x ≡ y
-- lamWrap' p i = p i


-- lamWrap : R.Term → R.Term
-- lamWrap t = R.def (quote lamWrap') (t v∷ [])

-- unLam : R.Term → R.TC R.Term
-- unLam (R.lam _ (R.abs _ t)) = R.returnTC t
-- unLam t = R.typeError ((R.strErr "unLam-fail") ∷ [ R.termErr t  ])

-- appendIfUniqe : R.Term → List R.Term →   R.TC (List R.Term)
-- appendIfUniqe x [] = R.returnTC [ x ]
-- appendIfUniqe x xs@(x₁ ∷ xs') = do
--  x' ← R.checkType x (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>=
--           λ u → R.catchTC (unLam u) (R.typeError [ R.strErr "aiu x'" ])
--  x₁' ← R.checkType x₁ (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>= unLam
--  sym[x₁'] ← R.checkType (R.def (quote sym) [ varg x₁ ]) (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>= unLam
--  R.catchTC (R.extendContext "i" (varg (R.def (quote I) [])) $
--                 ( R.noConstraints $ R.unify (x') (x₁') >> R.returnTC xs))
--     (
--       R.catchTC
--      (R.extendContext "i" (varg (R.def (quote I) [])) $
--                 ( R.noConstraints $ R.unify (x') sym[x₁'] >> R.returnTC xs))
--         (appendIfUniqe x xs' >>= (R.returnTC ∘ (x₁ ∷_))  )
--         )

-- comparePathTerms : R.Term → R.Term → R.TC (Maybe Bool)
-- comparePathTerms x x₁ = do
--  x' ← R.withNormalisation true $ R.checkType (lamWrap x) (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>=
--          λ u → R.catchTC (unLam u) (R.typeError [ R.strErr "cpt x'" ])
--  x₁' ← R.withNormalisation true $ R.checkType (lamWrap x₁) (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>=
--          λ u → R.catchTC (unLam u) (R.typeError (R.strErr "cpt x₁'" ∷ R.termErr x ∷ [ R.termErr x₁ ]))
--  sym[x₁'] ← R.checkType (R.def (quote sym) [ varg x₁ ]) (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>= unLam
--  R.catchTC (R.extendContext "i" (varg (R.def (quote I) [])) $
--                 ( R.noConstraints $ R.unify (x') (x₁') >> R.returnTC (just true)))
--     (
--       R.catchTC
--      (R.extendContext "i" (varg (R.def (quote I) [])) $
--                 ( R.noConstraints $ R.unify (x') sym[x₁'] >> R.returnTC (just false)))
--         (R.returnTC nothing)
--         )

-- concatUniq : List R.Term → List R.Term →  R.TC (List R.Term)
-- concatUniq [] = R.returnTC
-- concatUniq (x ∷ x₂) x₁  = appendIfUniqe x x₁ >>= concatUniq x₂

-- indexOfAlways : R.Term → List R.Term →   R.TC ((List R.Term) × (Bool × ℕ))
-- indexOfAlways t [] = R.returnTC ([ t ] , (true , 0))
-- indexOfAlways t xs@(x ∷ xs') =
--   comparePathTerms t x >>=
--    Mb.rec ((λ (l , (b , k) ) → (x ∷ l) , (b , (suc k))) <$> indexOfAlways t xs' )
--           (λ b → R.returnTC (xs , (b , 0)))

-- unMapAtoms : List R.Term → ∀ {p} → PTrm.IsPathTrm p →
--      (R.TC ((List R.Term) × (Σ _ Pℕ.IsPathTrm)))
-- unMapAtoms l PT.isReflTrm = R.returnTC (l , _ , Pℕ.isReflTrm)
-- unMapAtoms l (PT.isAtomTrm x) =
--   do (l' , y) ← indexOfAlways x l
--      R.returnTC (l' , _ , Pℕ.isAtomTrm y)
-- unMapAtoms l (PT.isCompTrm e e₁ e₂) =
--   do (l' , _ , e') ← unMapAtoms l e
--      (l'' , _ , e₁') ← unMapAtoms l' e₁
--      (l''' , _ , e₂') ← unMapAtoms l'' e₂
--      (R.returnTC (l''' , _ , Pℕ.isCompTrm e' e₁' e₂'))


-- -- unquotePathTrm : ∀ {p} → PTrm.IsPathTrm p → R.Term
-- -- unquotePathTrm PT.isReflTrm = R.con (quote (isReflTrm)) []
-- -- unquotePathTrm (PT.isAtomTrm p) = R.con (quote isAtomTrm) (p v∷ [])
-- -- unquotePathTrm (PT.isCompTrm x x₁ x₂) =
-- --  let x' = unquotePathTrm x
-- --      x₁' = unquotePathTrm x₁
-- --      x₂' = unquotePathTrm x₂
-- --  in R.con (quote isCompTrm) (x' v∷ x₁' v∷ x₂' v∷ [])

-- -- module _ (l : List R.Term) where
-- --   lk : (Bool × ℕ) → R.Term
-- --   lk (b , n) = if b then z else (R.def (quote sym) (z v∷ []))
-- --     where
-- --     z = lookupWithDefault R.unknown l n



-- --   mkTrmsInvol' :  ∀ {p} → ℕ → Pℕ.IsPathTrmDeas p → List (Pℕ.IsPathTrmInvol _ _)
-- --   mkTrmsInvol' zero _ = []
-- --   mkTrmsInvol' (suc k) u =
-- --     let pi = ℕDeas→ℕInvol u
-- --     in if (Pℕ.hasRedexes pi) then (pi ∷ mkTrmsInvol' k (snd (Pℕ.Invol→Deas↓ pi))) else []

-- --   mkTrmsInvol* : ∀ {p} → Pℕ.IsPathTrmDeas p → List (Pℕ.IsPathTrmInvol _ _)
-- --   mkTrmsInvol* x = mkTrmsInvol' (Pℕ.depthIsPathTrmDeas x) x

-- --   unquoteTrmInvol : PTrm.IsPathTrmInvol tt tt → R.Term
-- --   -- unquoteTrmInvol (PT.nilTrmInvol p) = R.con (quote nilTrmInvol) (p v∷ [])
-- --   -- unquoteTrmInvol (PT.nilInvolTrmInvol p) = R.con (quote nilInvolTrmInvol) (p v∷ [])
-- --   unquoteTrmInvol PT.nilTrmInvolRefl = R.con (quote nilTrmInvolRefl) []
-- --   unquoteTrmInvol (PT.consTrmInvol x q) =
-- --     R.con (quote consTrmInvol) (unquoteTrmInvol x v∷ q v∷ [])
-- --   unquoteTrmInvol (PT.involTrmInvol x q) =
-- --    R.con (quote involTrmInvol) (unquoteTrmInvol x v∷ q v∷ [])

-- --   mkTrmsInvol :  ∀ {p} → Pℕ.IsPathTrmDeas p → List (R.Term)
-- --   mkTrmsInvol x = Li.map ((λ y → R.def (quote ⟦_⟧ti≡) (y v∷ []))
-- --     ∘ unquoteTrmInvol ∘ mapPTG lk) $ mkTrmsInvol* x

-- --   foldPathCompTerm : List R.Term → R.Term
-- --   foldPathCompTerm [] = R.def (quote refl) []
-- --   foldPathCompTerm (x ∷ []) = x
-- --   foldPathCompTerm (x ∷ xs@(_ ∷ _)) = R.def (quote _∙_) (x v∷ foldPathCompTerm xs v∷ [])

-- --   mkTrmInvol :  ∀ {p} → Pℕ.IsPathTrmDeas p → (List (Pℕ.IsPathTrmInvol _ _) × R.Term)
-- --   mkTrmInvol x = ( mkTrmsInvol* x) , foldPathCompTerm (mkTrmsInvol x)


groupoidSolverTerm : Bool → R.Term → R.TC (R.Term × List R.ErrorPart)
groupoidSolverTerm debugFlag  hole = do

 (t0 , t1) ← R.inferType hole >>= wait-for-type >>= (get-boundary ) >>= Mb.rec
     (R.typeError [ R.strErr "unable to get boundary" ])
     (λ x → R.returnTC x)

 r0 ← tryPathE.try≡ 100 t0
 r1 ← tryPathE.try≡ 100 t1


 -- (aL' , (_ , e0)) ← unMapAtoms [] r0'
 -- (aL , (_ , e1)) ← unMapAtoms aL' r1'
 -- let (_ , e0deas) =  (Pℕ.⟦ e0 ⟧da∘r)
 -- let (_ , e1deas) =  (Pℕ.⟦ e1 ⟧da∘r)
 show0 ← showRTrmTC r0
 show1 ← showRTrmTC r1

 let dbgInfo =   ("LHS: ") ∷ₑ show0 ∷nl
                 ("RHS: ") ∷ₑ show1 ∷nl []
               -- ∷ (R.strErr "RHS: ") ∷ (R.termErr $ t1)
               -- ∷ (R.strErr "\n")
               -- ∷ (R.strErr "LHS: ") ∷ (R.strErr $ PℕS.showIPT (e0))
               -- ∷ (R.strErr "\n")
               -- ∷ (R.strErr "RHS: ") ∷ (R.strErr $ PℕS.showIPT (e1))
               -- ∷ (R.strErr "\n")
               -- ∷ (R.strErr "LHS: ") ∷ (R.strErr $ PℕS.showIPTD (e0deas))
               -- ∷ (R.strErr "\n")
               -- ∷ (R.strErr "RHS: ") ∷ (R.strErr $ PℕS.showIPTD (e1deas))
               -- ∷ (R.strErr "\n")
               -- ∷ (R.strErr "LHS: ") ∷ (R.strErr $ PℕS.showIPTI (ℕDeas→ℕInvol e0deas))
               -- ∷ (R.strErr "\n")
               -- ∷ (R.strErr "RHS: ") ∷ (R.strErr $ PℕS.showIPTI (ℕDeas→ℕInvol e1deas))

               -- ∷ (R.strErr "\n")
               -- (niceAtomList aL)

 R.typeError dbgInfo


groupoidSolverMain : Bool → R.Term → R.TC Unit
groupoidSolverMain debugFlag  hole = do
  ty ← R.withNormalisation true $  R.inferType hole >>= wait-for-type
  hole' ← R.withNormalisation true $ R.checkType hole ty
  (solution , msg) ← groupoidSolverTerm debugFlag hole'
  R.catchTC
   (R.unify hole solution)
   (R.typeError msg)

squareSolverMain : Bool → R.Term → R.TC Unit
squareSolverMain debugFlag  hole = do
  ty ← R.inferType hole >>= wait-for-type
  hole' ← R.checkType (R.def (quote compPathR→PathP∙∙) (R.unknown v∷ [])) ty >>= extractMeta

  (solution , msg) ← groupoidSolverTerm debugFlag  hole'
  R.catchTC
   (R.unify hole' solution)
   (R.typeError msg)

  R.catchTC
   (R.unify hole (R.def (quote compPathR→PathP∙∙) (hole' v∷ [])))
   (R.typeError [ R.strErr "xxx" ] )
 where
  extractMeta : R.Term → R.TC R.Term
  extractMeta (R.def _ tl) = matchVarg tl
  extractMeta t =
   R.typeError (R.strErr "extractMetaFail :" ∷ [ R.termErr t ])

macro
 solveGroupoidDebug : R.Term → R.TC Unit
 solveGroupoidDebug = groupoidSolverMain true

 -- solveSquareDebug : R.Term → R.TC Unit
 -- solveSquareDebug = squareSolverMain false

 -- solveGroupoid : R.Term → R.TC Unit
 -- solveGroupoid = groupoidSolverMain true

 -- solveSquare : R.Term → R.TC Unit
 -- solveSquare = squareSolverMain false


-- module Examples (A : Type ℓ) (x y z w : A) (p p' : x ≡ y) (q : y ≡ z) (q' : z ≡ y) (r : w ≡ z) where

--   pA pB pC : x ≡ w
--   pA = (p ∙∙ refl ∙∙ q) ∙ sym r
--   pB = (p ∙ (q ∙ sym (sym r ∙  r) ∙ sym q) ∙∙ q ∙∙ refl) ∙∙ sym r ∙∙ refl
--   pC = refl ∙∙ p' ∙ q ∙ sym q ∙ sym p' ∙∙ p ∙∙ q ∙∙ sym q ∙ q ∙ sym r

--   pA=pB : pA ≡ pB
--   pA=pB = solveGroupoidDebug
