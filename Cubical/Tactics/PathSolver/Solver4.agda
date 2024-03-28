{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.Solver4 where


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

infixr 5 _∷fn_


data [Typeₙ] : Typeω where
 [Tω] : [Typeₙ]
 _∷Tω_ : ∀ {ℓ} → Type ℓ → [Typeₙ] → [Typeₙ]

data [Fns] : Typeω where
 [fn] : [Fns]
 _∷fn_ : ∀ {ℓ ℓ'} → {A : Type ℓ} {A' : Type ℓ'} → (A → A') → [Fns] → [Fns]


reflected[Typeₙ]→[reflectedTy] : R.Term → R.TC (List R.Term)
reflected[Typeₙ]→[reflectedTy] (R.con (quote [Tω]) args) = pure []
reflected[Typeₙ]→[reflectedTy] (R.con (quote _∷Tω_) (_ h∷ x v∷ x₁ v∷ [])) =
  (x ∷_) <$> reflected[Typeₙ]→[reflectedTy] x₁
reflected[Typeₙ]→[reflectedTy] (R.con (quote _∷Tω_) (x v∷ x₁ v∷ [])) =
  (x ∷_) <$> reflected[Typeₙ]→[reflectedTy] x₁ 
reflected[Typeₙ]→[reflectedTy] _ =
 R.typeError [ "reflected[Typeₙ]→[reflectedTy] - FAIL" ]ₑ


-- macro
--  test-refl[T]macro : R.Term → R.Term → R.TC Unit
--  test-refl[T]macro inp hole = do
--    l ← reflected[Typeₙ]→[reflectedTy] inp
--    R.typeError (niceAtomList l)

-- module _ (ℓ ℓ' : Level) where 
--   test-refl[T] : Unit
--   test-refl[T] = test-refl[T]macro (Type ℓ ∷Tω (Type ℓ' → Type) ∷Tω Type₂ ∷Tω [])


reflected[Fns]→[reflectedFn] : R.Term → R.TC (List R.Term)
reflected[Fns]→[reflectedFn] (R.con (quote [fn]) args) = pure []
reflected[Fns]→[reflectedFn] (R.con (quote _∷fn_) (_ h∷ _ h∷ _ h∷ _ h∷ x v∷ x₁ v∷ [])) = (x ∷_) <$> reflected[Fns]→[reflectedFn] x₁
reflected[Fns]→[reflectedFn] (R.con (quote _∷fn_) (_ h∷ _ h∷ _ h∷ x v∷ x₁ v∷ [])) =
  (x ∷_) <$> reflected[Fns]→[reflectedFn] x₁
reflected[Fns]→[reflectedFn] (R.con (quote _∷fn_) (_ h∷ _ h∷ x v∷ x₁ v∷ [])) =
  (x ∷_) <$> reflected[Fns]→[reflectedFn] x₁
reflected[Fns]→[reflectedFn] (R.con (quote _∷fn_) (_ h∷ x v∷ x₁ v∷ [])) =
  (x ∷_) <$> reflected[Fns]→[reflectedFn] x₁
reflected[Fns]→[reflectedFn] (R.con (quote _∷fn_) (x v∷ x₁ v∷ [])) =
  (x ∷_) <$> reflected[Fns]→[reflectedFn] x₁
reflected[Fns]→[reflectedFn] _ = R.typeError [ "reflected[Fns]→[reflectedFn] - FAIL" ]ₑ

-- macro
--  test-refl[Fn]macro : R.Term → R.Term → R.TC Unit
--  test-refl[Fn]macro inp hole = do
--    l ← reflected[Fns]→[reflectedFn] inp
--    R.typeError (niceAtomList l)

-- module _ (ℓ ℓ' : Level) where 
--   test-refl[Fn] : Unit
--   test-refl[Fn] = test-refl[Fn]macro
--     (suc ∷fn (λ (T : Type ℓ') → (T → Type ℓ)) ∷fn [fn])


maxℓ : [Typeₙ] → Level
maxℓ [Tω] = ℓ-zero
maxℓ (_∷Tω_ {ℓ} _ x₁) = ℓ-max ℓ (maxℓ x₁)

lookupTₙ : (Ts : [Typeₙ]) → ℕ → Type (maxℓ Ts)
lookupTₙ [Tω] x = ⊥*
lookupTₙ (x₁ ∷Tω Ts) zero = Lift {_} {maxℓ Ts} x₁
lookupTₙ (_∷Tω_ {ℓ} x₁ Ts) (suc x) = Lift {_} {ℓ} (lookupTₙ Ts x)

ℓAt : (Ts : [Typeₙ]) → ℕ → Level
ℓAt [Tω] x = ℓ-zero
ℓAt (_∷Tω_ {ℓ} x₁ Ts) zero = ℓ
ℓAt (x₁ ∷Tω Ts) (suc x) = ℓAt Ts x

TyAt : (Ts : [Typeₙ]) → ∀ k → Type (ℓAt Ts k)
TyAt [Tω] k = ⊥*
TyAt (x ∷Tω Ts) zero = x
TyAt (x ∷Tω Ts) (suc k) = TyAt Ts k

cast↓ : ∀ Ts k → lookupTₙ Ts k → TyAt Ts k
cast↓ [Tω] k ()
cast↓ (x₁ ∷Tω Ts) zero x = lower x
cast↓ (x₁ ∷Tω Ts) (suc k) x = cast↓ Ts k (lower x)

cast↓Inj : ∀ {[T] A x y} → cast↓ [T] A x ≡ cast↓ [T] A y → x ≡ y
cast↓Inj {[Tω]} {A = A} {()}
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
cast↑ [Tω] k ()
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
 congCase : ∀ {ℓ ℓ' A A'} {x y} (f : A → A')
                 → (p : Path {ℓ} A x y)  → PathCase {ℓ'} {A = A'} (cong f p)


module _ {ℓ ℓ'} {A : Type ℓ} {A' : Type ℓ'} (f : A → A') {x y}
                   (p : Path {ℓ} A x y) where

 -- pathCaseCongTest : PathCase λ i → f (p i)
 -- pathCaseCongTest = congCase f {!!}


infixl 5 _fp∷_
infixl 5 _fp++_

data FlatPath {ℓ} (A : Type ℓ) : Bool → (a₀ a₁ : A) → Type ℓ where
 [fp] : ∀ {x b} → FlatPath A b x x
 _fp∷_ : ∀ {x y z b} → FlatPath A b x y → y ≡ z → FlatPath A b x z
 _invol∷_ : ∀ {x y z} → FlatPath A true x y → y ≡ z → FlatPath A true x y 

magicNumber = 100

mb-invol : ℕ → R.Term → R.TC (Maybe (R.Term × R.Term))
mb-invol zero _ = R.typeError ("magic number too low in mb-invol" ∷ₑ [])
mb-invol _ (R.con (quote [fp]) _) = R.returnTC nothing
mb-invol (suc n) (R.con (quote _fp∷_) tl) = match2Vargs tl >>= w
  where
  w : (R.Term × R.Term) → R.TC (Maybe (R.Term × R.Term))
  w (R.con (quote [fp]) _ , _) = R.returnTC nothing
  w (xs'@(R.con (quote _fp∷_) tl') , y) =
    match2Vargs tl' >>= λ (xs , x) →
     R.catchTC
       (R.noConstraints $ R.unify
         (R.def (quote sym) (x v∷ [])) y
          >> (Mb.rec (xs , xs) (idfun _) <$> mb-invol n xs)
          >>= λ (xs* , xs*↑) →
             R.returnTC
              (just ((R.con (quote _invol∷_) (xs* v∷ x v∷ []))
               , xs*↑ )
               ))
       (map-Maybe (map-both (λ xs* → R.con (quote _fp∷_)
         ((xs* v∷ y v∷ []))))
         <$> mb-invol n xs')
  w (x , y) = R.typeError ("Imposible!!₁ : " ∷ₑ x ∷ₑ "\n\n " ∷ₑ y ∷ₑ [])
mb-invol _ x = R.typeError ("Imposible!!₂ : " ∷ₑ x ∷ₑ [])

mb-invol' : R.Term → R.TC (Maybe (R.Term × R.Term))
mb-invol' = mb-invol magicNumber


redList : ℕ → R.Term → R.TC (List R.Term)
redList = h
 where
 h : ℕ → R.Term →  R.TC (List R.Term)
 h zero _ = R.typeError ("magic number too low in mb-invol" ∷ₑ [])
 h (suc k) t =
   (mb-invol' t) >>=
     Mb.rec
       (R.returnTC [])
       λ (t' , t'↓) → do
         p' ← h k t'↓
         R.returnTC (t' ∷ p')


redList' : R.Term → R.TC (List R.Term)
redList' = redList magicNumber


pattern fp[_] x = [fp] fp∷ x 

FP⟦_⟧ : {a₀ a₁ : A} → FlatPath A false a₀ a₁ → a₀ ≡ a₁
FP⟦ [fp] ⟧ = refl
FP⟦ x fp∷ x₁ ⟧ = FP⟦ x ⟧ ∙ x₁

-- FP⟦_⟧t : {a₀ a₁ : A} → FlatPath A true a₀ a₁ → a₀ ≡ a₁
-- FP⟦ [] ⟧t = refl
-- FP⟦ x fp∷ x₁ ⟧t = FP⟦ x ⟧t ∙ x₁
-- FP⟦ x invol∷ x₁ ⟧t = (FP⟦ x ⟧t ∙ x₁) ∙ sym x₁


fpF→T : {a₀ a₁ : A} → FlatPath A false a₀ a₁ → FlatPath A true a₀ a₁
fpF→T [fp] = [fp]
fpF→T (x fp∷ x₁) = fpF→T x fp∷ x₁

fpT→F : {a₀ a₁ : A} → Bool → FlatPath A true a₀ a₁ → FlatPath A false a₀ a₁
fpT→F _ [fp] = [fp]
fpT→F b (x₁ fp∷ x₂) = fpT→F b x₁ fp∷ x₂
fpT→F false (x₁ invol∷ x₂) = fpT→F false x₁ fp∷ x₂ fp∷ sym x₂
fpT→F true (x₁ invol∷ x₂) = fpT→F true x₁ 

fpT≡F :  {a₀ a₁ : A} → (fp : FlatPath A true a₀ a₁) →
             FP⟦ fpT→F false fp ⟧ ≡ FP⟦ fpT→F true fp ⟧
fpT≡F [fp] = refl
fpT≡F (fp fp∷ x) i = fpT≡F fp i ∙ x  
fpT≡F {a₀ = a₀} {a₁} (fp invol∷ x) i j =
  hcomp
    (λ k → λ { (i = i1) → FP⟦ fpT→F true fp ⟧ j
              ; (j = i0) → a₀
              ; (j = i1) → x (~ k ∧ ~ i)
              })
    (hcomp (λ k → λ { (i = i1) → FP⟦ fpT→F true fp ⟧ j
              ; (j = i0) → a₀
              ; (j = i1) → x (~ i ∧ k)
              })
              (fpT≡F fp i j))

_fp++_ : ∀ {x y z}
 → FlatPath A false x y
 → FlatPath A false y z
 → FlatPath A false x z
x fp++ [fp] = x
x fp++ (x₁ fp∷ x₂) = x fp++ x₁ fp∷ x₂

fp++∙ : {a₀ a₁ a₂ : A} → (fp : FlatPath A false a₀ a₁)
             (fp' : FlatPath A false a₁ a₂)
          → FP⟦ fp ⟧ ∙ FP⟦ fp' ⟧ ≡ FP⟦ fp fp++ fp' ⟧
fp++∙ fp [fp] = sym (rUnit _)
fp++∙ fp (fp' fp∷ x) = assoc _ _ _ ∙ cong (_∙ x) (fp++∙ fp fp')

module PE ([T] : [Typeₙ]) where

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
 cong-flat f reflExpr = [fp]
 cong-flat f (atomExpr p) = fp[ cong _ p ]
 cong-flat f (compExpr x x₁ x₂) =
   cong-flat f x fp++ cong-flat f x₁ fp++ cong-flat f x₂
 cong-flat f (congExpr f₁ x) = cong-flat (f ∘ f₁) x

 flat⟦_⟧ : ∀ {A a₀ a₁} → PathExpr A a₀ a₁
              → FlatPath (TyAt [T] A) false (cast↓ [T] A a₀) (cast↓ [T] A a₁)
 flat⟦ reflExpr ⟧ = [fp]
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
module RTrm' = PathTrm (ℕ × R.Term) (ℕ × R.Term)
module StrTrm = PathTrm String String

showRTrmTC : RTrm.PathTrm → R.TC String
showRTrmTC =
  mmapPT
  (R.formatErrorParts ∘ [_]ₑ) (R.formatErrorParts ∘ [_]ₑ)
  >=> (pure ∘ StrTrm.showPathTrm.showPT (idfun _) (idfun _) )

showRTrmTC' : RTrm'.PathTrm → R.TC String
showRTrmTC' =
  let q = λ (k , t) →
        R.formatErrorParts (primShowNat k <> " " ∷ₑ [ t ]ₑ) 
  in mmapPT
       q q
       >=> (pure ∘ StrTrm.showPathTrm.showPT (idfun _) (idfun _) )

module _ ([T] : [Typeₙ]) where
 reflExpr' : ∀ A (x : TyAt [T] A) → PE.PathExpr [T] A (cast↑ [T] A x) (cast↑ [T] A x)
 reflExpr' A x = PE.reflExpr {[T] = [T]} {A} {cast↑ [T] A x}


 atomExpr' : ∀ A {x y} → (p : x ≡ y) →
   PE.PathExpr [T] A (cast↑ [T] A x) (cast↑ [T] A y)
 atomExpr' A p = PE.atomExpr {[T] = [T]} {A} (cong (cast↑ [T] A) p)
 
 compExpr' : ∀ A {x y z w} 
  → PE.PathExpr [T] A x y → PE.PathExpr [T] A y z → PE.PathExpr [T] A z w
  → PE.PathExpr [T] A x w
 compExpr' A = PE.compExpr {[T] = [T]} {A = A}
 
 congExpr' : ∀ A A' {x y} → (f : TyAt [T] A → TyAt [T] A') 
  → PE.PathExpr [T] A (cast↑ [T] A x) (cast↑ [T] A y)
  → PE.PathExpr [T] A' (cast↑ [T] A' (f (cast↓ [T] A (cast↑ [T] A x))))
                       (cast↑ [T] A' (f (cast↓ [T] A (cast↑ [T] A y))))
 congExpr' A A' f x = PE.congExpr {[T] = [T]} {A = A} {A'}
               (cast↑ [T] A' ∘ f ∘ cast↓ [T] A) x
   
getEnd : ∀ {x y : A} → x ≡ y → A
getEnd p = p i0

module tryPathE --([T] : [Typeₙ])
                (TC[T]trm : R.Term)
                ([TC[T]trm] [fns] : List R.Term) where
                
 inferA : R.Term → R.TC ℕ
 inferA x = tryAllTC (R.typeError [ "notRecignisedType" ]ₑ)
               (zipWithIndex [TC[T]trm])
               λ (k , Ty) →
                  R.checkType x (R.def (quote Path)
                    (Ty v∷ R.unknown v∷ R.unknown v∷ []) )
                  >> pure k 

 inferA' : R.Term → R.TC R.Term
 inferA' = inferA >=> R.quoteTC



 try≡ : ℕ → R.Term → R.TC (RTrm.PathTrm × R.Term)


 tryRefl : R.Term → R.TC (RTrm.PathTrm × R.Term)
 tryRefl t = do
       _ ← R.noConstraints $ R.checkType
             (R.con (quote reflCase) [])
             (R.def (quote PathCase) ([ varg t ]))
       let x₀ = R.def (quote getEnd) v[ t ]
       A ← inferA' t
       ⦇ (RTrm.reflTrm , R.def (quote reflExpr')
          (TC[T]trm v∷ A v∷ x₀ v∷ [])) ⦈

 tryComp : ℕ → R.Term → R.TC (RTrm.PathTrm × R.Term)
 tryComp zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 tryComp (suc k) t = do
       tm ← R.noConstraints $ R.checkType
             (R.con (quote compCase) (R.unknown v∷ R.unknown v∷ [ varg R.unknown ]))
             (R.def (quote PathCase) ([ varg t ]))
       (t1 , t2 , t3) ← h tm
       (t1 , t1') ← (try≡ k t1)
       (t2 , t2') ← (try≡ k t2)
       (t3 , t3') ← (try≡ k t3)
       A ← inferA' t
       pure (RTrm.compTrm t1 t2 t3 ,
         R.def (quote compExpr')
          (TC[T]trm v∷ A v∷ t1' v∷ t2' v∷ t3' v∷  []))

  where

  h : R.Term → R.TC (R.Term × R.Term × R.Term)
  h (R.con (quote compCase) l) = match3Vargs l
  h _ = R.typeError [ (R.strErr "tryCompFail-h") ]


 tryCong : ℕ → R.Term → R.TC (RTrm.PathTrm × R.Term)
 tryCong zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 tryCong (suc k) t =
      tryAllTC (R.typeError [ "not cong case" ]ₑ)
      (zipWithIndex [fns])
       (λ (m , f) → do
               tm ← R.noConstraints $ R.checkType
                     (R.con (quote congCase) (f v∷ [ varg R.unknown ]))
                     (R.def (quote PathCase) ([ varg t ]))
               (_ , t*) ← h tm
               A ← inferA' t*
               A' ← inferA' t
               (t0 , t0') ← (try≡ k t*)
               pure (RTrm.congTrm f t0 ,
                 R.def (quote congExpr')
                  (TC[T]trm v∷ A v∷ A' v∷ f v∷ t0' v∷  [])))
               
  where

  h : R.Term → R.TC (R.Term × R.Term)
  h (R.con (quote congCase) l) = match2Vargs l
  h _ = R.typeError [ (R.strErr "tryCompFail-h") ]



 atom : R.Term → R.TC (RTrm.PathTrm × R.Term)
 atom x = do
  A ← inferA' x
  pure (RTrm.atomTrm x , R.def (quote atomExpr')
          (TC[T]trm v∷ A v∷ x v∷ []))


 try≡ zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 try≡ (suc k) t =
   R.catchTC
    (tryRefl t)
    (R.catchTC (tryComp k t)
       (R.catchTC (tryCong k t) (atom t)))



module tryTermE --([T] : [Typeₙ])
                --(TC[T]trm : R.Term)
                ([TC[T]trm] [fns] : List R.Term) where
                
 try≡ : ℕ → R.Term → R.TC (RTrm'.PathTrm)


 tryRefl : R.Term → R.TC (RTrm'.PathTrm)
 tryRefl t = do
       _ ← R.noConstraints $ R.checkType
             (R.con (quote reflCase) [])
             (R.def (quote PathCase) ([ varg t ]))
       ⦇ RTrm'.reflTrm ⦈

 tryComp : ℕ → R.Term → R.TC (RTrm'.PathTrm)
 tryComp zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 tryComp (suc k) t = do
       tm ← R.noConstraints $ R.checkType
             (R.con (quote compCase) (R.unknown v∷ R.unknown v∷ [ varg R.unknown ]))
             (R.def (quote PathCase) ([ varg t ]))
       (t1 , t2 , t3) ← h tm
       ⦇ RTrm'.compTrm (try≡ k t1) (try≡ k t2) (try≡ k t3) ⦈

  where

  h : R.Term → R.TC (R.Term × R.Term × R.Term)
  h (R.con (quote compCase) l) = match3Vargs l
  h _ = R.typeError [ (R.strErr "tryCompFail-h") ]


 tryCong : ℕ → R.Term → R.TC (RTrm'.PathTrm)
 tryCong zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 tryCong (suc k) t =
      tryAllTC (R.typeError [ "not cong case" ]ₑ)
      (zipWithIndex [fns])
       (λ (m , f) → do
               tm ← R.noConstraints $ R.checkType
                     (R.con (quote congCase) (f v∷ [ varg R.unknown ]))
                     (R.def (quote PathCase) ([ varg t ]))
               (_ , t) ← h tm
               ⦇ (RTrm'.congTrm (m , f)) (try≡ k t) ⦈)
               
  where

  h : R.Term → R.TC (R.Term × R.Term)
  h (R.con (quote congCase) l) = match2Vargs l
  h _ = R.typeError [ (R.strErr "tryCompFail-h") ]



 atom : R.Term → R.TC (RTrm'.PathTrm)
 atom x = do
  k ← tryAllTC (R.typeError [ "notRecignisedType" ]ₑ)
               (zipWithIndex [TC[T]trm])
               λ (k , Ty) →
                  R.checkType x (R.def (quote Path)
                    (Ty v∷ R.unknown v∷ R.unknown v∷ []) )
                  >> pure k
  R.returnTC (RTrm'.atomTrm (k , x))


 try≡ zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 try≡ (suc k) t =
   R.catchTC
    (tryRefl t)
    (R.catchTC (tryComp k t)
       (R.catchTC (tryCong k t) (atom t)))



-- funTypeView : R.Type → R.TC (Maybe (R.Type × R.Type))
-- funTypeView = {!!}

groupoidSolverTerm : Bool → R.Term → R.Term → R.Term → R.TC (R.Term × List R.ErrorPart)
groupoidSolverTerm debugFlag  inp₀ inpF hole = do

 -- inp₀ ← wait-for-type inp₀'
 
 -- R.typeError (niceAtomList [)
 (A' , (t0' , t1')) ← R.inferType hole >>= wait-for-type >>= (get-boundaryWithDom ) >>= Mb.rec
     (R.typeError [ R.strErr "unable to get boundary" ])
     (λ x → R.returnTC x)
 
 -- A ← wait-for-type A'
 -- t0 ← wait-for-type t0'
 -- t1 ← wait-for-type t1'

 let t0 = t0'
 let t1 = t1'

 (AA , _) ← get-boundaryWithDom A' >>= Mb.rec
     (R.typeError [ R.strErr "unable to get boundary2" ])
     (λ x → R.returnTC x)
 
 let inp = (R.con (quote _∷Tω_) (AA v∷ inp₀ v∷ []))
 -- (R.typeError [ inp ]ₑ)

 

 [t] ← reflected[Typeₙ]→[reflectedTy] inp
 [f] ← reflected[Fns]→[reflectedFn] inpF

 (r0 , r0') ← R.runSpeculative ((_, false) <$> tryPathE.try≡ inp [t] [f] 100 t0)
 (r1 , r1') ← R.runSpeculative ((_, false) <$> tryPathE.try≡ inp [t] [f] 100 t1)

 

 -- (aL' , (_ , e0)) ← unMapAtoms [] r0'
 -- (aL , (_ , e1)) ← unMapAtoms aL' r1'
 -- let (_ , e0deas) =  (Pℕ.⟦ e0 ⟧da∘r)
 -- let (_ , e1deas) =  (Pℕ.⟦ e1 ⟧da∘r)
 show0 ← showRTrmTC r0
 show1 ← showRTrmTC r1

 red0 ← (R.normalise $ R.def (quote fpF→T) v[ R.def (quote PE.flat⟦_⟧) (inp v∷ r0' v∷ [])]) >>= redList' 
 red1 ← (R.normalise $ R.def (quote fpF→T) v[ R.def (quote PE.flat⟦_⟧) (inp v∷ r1' v∷ [])]) >>= redList' 


 let invPa0 = Li.map
         (λ t' → just (R.def (quote fpT≡F) (t' v∷ [])))
         red0
     invPa1 = Li.map
         (λ t' → just (R.def (quote fpT≡F) (t' v∷ [])))
         red1

 let dbgInfo =   --("r0Ty: ") ∷ₑ r0'Ty ∷nl
                 ("LHS: ") ∷ₑ show0 ∷nl
                 ("RHS: ") ∷ₑ show1 ∷nl
                 (niceAtomList red0 ++ ("" ∷nl niceAtomList red1))
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

 let finalTrm0 =
        just (R.def (quote PE.pe≡flat) (inp v∷ r0' v∷ []))
         ∷ invPa0

     finalTrm1 =
        just (R.def (quote PE.pe≡flat) (inp v∷ r1' v∷ []))
        ∷  invPa1

 let finalTrm = fromMaybe (R.def (quote refl) []) $ foldPathTerms
        (finalTrm0 ++ symPathTerms finalTrm1)
 
 pure (finalTrm , dbgInfo)


groupoidSolverMain : Bool → R.Term → R.Term → R.Term → R.TC Unit
groupoidSolverMain debugFlag inp inpF hole = do
  ty ← R.withNormalisation true $  R.inferType hole >>= wait-for-type
  hole' ← R.withNormalisation true $ R.checkType hole ty
  (solution , msg) ← groupoidSolverTerm debugFlag inp inpF hole'
  R.catchTC
   (R.unify hole solution)
   (R.typeError msg)

groupoidSolverMain' : Bool → R.Term → R.TC Unit
groupoidSolverMain' debugFlag hole = do
  
  let inpF = R.con (quote [fn]) []
  let inp = R.con (quote [Tω]) []
  ty ← R.withNormalisation true $  R.inferType hole >>= wait-for-type
  hole' ← R.withNormalisation true $ R.checkType hole ty
  R.commitTC
  (solution , msg) ←  groupoidSolverTerm debugFlag inp inpF hole'
  -- R.typeError [ solution ]ₑ
  R.catchTC
    (R.unify hole solution)
    (R.typeError msg)


-- -- squareSolverMain : Bool → R.Term → R.Term → R.TC Unit
-- -- squareSolverMain debugFlag inp  hole = do
-- --   ty ← R.inferType hole >>= wait-for-type
-- --   hole' ← R.checkType (R.def (quote compPathR→PathP∙∙) (R.unknown v∷ [])) ty >>= extractMeta

-- --   (solution , msg) ← groupoidSolverTerm debugFlag inp  hole'
-- --   R.catchTC
-- --    (R.unify hole' solution)
-- --    (R.typeError msg)

-- --   R.catchTC
-- --    (R.unify hole (R.def (quote compPathR→PathP∙∙) (hole' v∷ [])))
-- --    (R.typeError [ R.strErr "xxx" ] )
-- --  where
-- --   extractMeta : R.Term → R.TC R.Term
-- --   extractMeta (R.def _ tl) = matchVarg tl
-- --   extractMeta t =
-- --    R.typeError (R.strErr "extractMetaFail :" ∷ [ R.termErr t ])

macro
 solveGroupoidDebug : R.Term → R.Term → R.Term → R.TC Unit
 solveGroupoidDebug = groupoidSolverMain true

 ≡! : R.Term → R.TC Unit
 ≡! = groupoidSolverMain' true

--  -- solveSquareDebug : R.Term → R.TC Unit
--  -- solveSquareDebug = squareSolverMain false

--  -- solveGroupoid : R.Term → R.TC Unit
--  -- solveGroupoid = groupoidSolverMain true

--  -- solveSquare : R.Term → R.TC Unit
--  -- solveSquare = squareSolverMain false


module SimpleTest  where

  module _ (n : ℕ) where

   data AA : Type where
    x y z w : AA
    p p' : x ≡ y
    q : y ≡ z
    q' : z ≡ y
    r : z ≡ w



  pA pB : Path (AA 3) (x) (w)
  pA = ((refl ∙ p) ∙ q) ∙ r
  pB = ((refl ∙ p) ∙ q) ∙ r


  pA=pB : Path (Path (AA 3) x y)
             (refl ∙ p)
             (p)
  pA=pB = ≡! 


module Examples (A : Type ℓ) (x y z w : A) (p p' : x ≡ y) (q : y ≡ z) (q' : z ≡ y) (r : w ≡ z) where

  pA pB pC : x ≡ w
  pA = (p ∙∙ refl ∙∙ q) ∙ sym r
  pB = (p ∙ (q ∙ sym (sym r ∙  r) ∙ sym q) ∙∙ q ∙∙ refl) ∙∙ sym r ∙∙ refl
  pC = refl ∙∙ p' ∙ q ∙ sym q ∙ sym p' ∙∙ p ∙∙ q ∙∙ sym q ∙ q ∙ sym r

  pA=pB : pA ≡ pB
  pA=pB = ≡!


module Examples' (A : ℕ → Type ℓ)
                 (x y z w : ∀ {n} → A n)
                 (p p' : ∀ {n} → x {n} ≡ y)
                 (q : ∀ {n} → y {n} ≡ z)
                 (q' : ∀ {n} → z {n} ≡ y)
                 (r : ∀ {n} → w {n} ≡ z) where

  pA pB : Path (A 3) x w
  pA = (p ∙∙ refl ∙∙ q) ∙ sym r
  pB = (p ∙ (q ∙ sym (sym r ∙  r) ∙ sym q) ∙∙ q ∙∙ refl) ∙∙ sym r ∙∙ refl

  pA=pB : pA ≡ pB
  pA=pB = ≡!


module Examplesℕ'  where

  data AA  : (n : ℕ) → Type where
   x y z w : ∀ {n} → AA n
   p p' : ∀ {n} → x {n} ≡ y
   q : ∀ {n} → y {n} ≡ z
   q' : ∀ {n} → z {n} ≡ y
   r : ∀ {n} → w {n} ≡ z



  pA pB : Path (AA 3) (x) (w)
  pA = (p ∙∙ refl ∙∙ q) ∙ sym (r)
  pB = ((p) ∙ ((q) ∙ sym (sym (r) ∙  (r)) ∙ sym (q))
           ∙∙ (q) ∙∙ refl) ∙∙ sym (r) ∙∙ refl

  pA=pB : pA ≡ pB
  pA=pB = ≡!


module Examplesℕ''  where

  module _ (n : ℕ) where

   data AA : Type where
    x y z w : AA
    p p' : x ≡ y
    q : y ≡ z
    q' : z ≡ y
    r : w ≡ z



  pA pB : Path (AA 3) (x) (w)
  pA = (p ∙∙ refl ∙∙ q) ∙ sym (r)
  pB = ((p) ∙ ((q) ∙ sym (sym (r) ∙  (r)) ∙ sym (q))
           ∙∙ (q) ∙∙ refl) ∙∙ sym (r) ∙∙ refl


  pA=pB : pA ≡ pB
  pA=pB = ≡!


-- module Examplesℕ  where

--   data AA (n : ℕ) : Type where
--    x y z w : AA n
--    p p' : x ≡ y
--    q : y ≡ z
--    q' : z ≡ y
--    r : w ≡ z



--   pA pB : Path (AA 3) (x) (w)
--   pA = (p ∙∙ refl ∙∙ q) ∙ sym (r)
--   pB = ((p) ∙ ((q) ∙ sym (sym (r) ∙  (r)) ∙ sym (q))
--            ∙∙ (q) ∙∙ refl) ∙∙ sym (r) ∙∙ refl
-- -- --   -- pC = refl ∙∙ p' ∙ q ∙ sym q ∙ sym p' ∙∙ p ∙∙ q ∙∙ sym q ∙ q ∙ sym r

--   pA=pB : pA ≡ pB
--   pA=pB = ≡!




-- -- -- -- -- -- -- -- module Examples2 (A B : Type ℓ) (x y z : B) (w : A) (f g : B → A)
-- -- -- -- -- -- -- --   (p p' : x ≡ y) (q : y ≡ z) (q' : z ≡ y) (r : w ≡ f z) where

-- -- -- -- -- -- -- --   pA pB : f x ≡ w
-- -- -- -- -- -- -- --   pA = cong f (p ∙∙ refl ∙∙ q) ∙ sym r
-- -- -- -- -- -- -- --   pB = (cong f p ∙ (cong f q ∙ (sym (sym r ∙ (refl ∙ refl) ∙ refl ∙  r)) ∙ cong f (sym q)) ∙∙ cong f q ∙∙ refl) ∙∙ sym r ∙∙ refl


-- -- -- -- -- -- -- --   pA=pB : pA ≡ pB
-- -- -- -- -- -- -- --   pA=pB = solveGroupoidDebug (B ∷Tω A ∷Tω [Tω]) (g ∷fn f ∷fn [fn])

