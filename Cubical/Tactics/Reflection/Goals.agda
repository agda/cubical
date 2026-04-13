{-# OPTIONS --quote-metas #-}
module Cubical.Tactics.Reflection.Goals where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function

open import Agda.Builtin.Reflection renaming (Type to TypeTm)


open import Cubical.Reflection.Base
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Reflection.Sugar
open import Cubical.Data.List as L
open import Cubical.Data.Unit
open import Cubical.Data.List.Dependent as DL
open import Cubical.Data.Maybe as Mb
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Error

private
 variable
  ℓ ℓ' : Level

module _ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} where

 filterOutDone : ∀ {xs} →  ListP (Maybe ∘ B) xs → List A
 filterOutDone {[]} _ = []
 filterOutDone {x ∷ _} (nothing ∷ xs) = x ∷ filterOutDone xs
 filterOutDone {x ∷ _} (just _ ∷ xs) = filterOutDone xs

 satisfySome : ∀ {xs} → (mbXS : ListP (Maybe ∘ B) xs) → ListP B (filterOutDone mbXS) → ListP B xs
 satisfySome [] _ = []
 satisfySome (nothing ∷ _) (y ∷ x) = y ∷ satisfySome _ x
 satisfySome (just x ∷ _) xs = x ∷ satisfySome _ xs

maybeSolveMaybe : (Term → TypeTm →  TC Bool) → Term → TC Unit
maybeSolveMaybe tactic' Maybe-hole = do
   s' ← (runSpeculative $ do
           holeTy ← inferType Maybe-hole
           (h , hTy) ← newHole
           unify (def (quote Maybe) v[ hTy ]) holeTy
           sucess ← tactic' h hTy
           if sucess
            then (do unify Maybe-hole (con (quote just) v[ h ])
                     pure (sucess , sucess))
            else (pure (sucess , sucess)))
   when (not s') (unify Maybe-hole (con (quote nothing) []))



refineListPHole' : ℕ → Term → TC Unit
refineListPHole' (ℕ.suc n) tm = unify (con (quote DL.[]) []) tm <|> do
  (holeL , _) ← newHole
  (holeR , _) ← newHole
  (unify (con (quote DL._∷_) (holeL v∷ v[ holeR ])) tm >> refineListPHole' n holeR) <|> pure _
refineListPHole' ℕ.zero _ = returnTC _

refineListPHole : Term → TC Unit
refineListPHole = refineListPHole' 1000000


satisfySomeTC : (Term → TypeTm → TC Bool) → Term → TC Term
satisfySomeTC tactic' hole = do
  (maybeSolved , _) ← newHole
  (stillMissing , _) ← newHole
  unify hole (def (quote satisfySome) (maybeSolved v∷ v[ stillMissing ]))
  go 100000 maybeSolved
  refineListPHole stillMissing
  pure stillMissing

 where
  go : ℕ → Term → TC (Maybe Term)
  go 0 _ = typeError [ "no more fuel in satisfySomeTC , Cubical.Tactics.Reflection.Goals" ]ₑ
  go (suc fuel) tm = (unify (con (quote DL.[]) []) tm >> pure nothing) <|> do
     (holeL , _) ← newHole
     (holeR , _) ← newHole
     (unify (con (quote DL._∷_) (holeL v∷ v[ holeR ])) tm)
     maybeSolveMaybe tactic' holeL
     go fuel holeR





macro
 testSatisfySomeTC' : Term → Term → TC Unit
 testSatisfySomeTC' lemHole hole = do
   lemHole' ← satisfySomeTC
     (λ h _ → pure false)
     hole
   unify lemHole' lemHole



zzz' : ListP (idfun _) ((2 ≡ 2) ∷ (1 ≡ 1) ∷ (3 ≡ 3) ∷ [])
zzz' = testSatisfySomeTC' (refl ∷ refl ∷ P[ refl ])

macro
 testSatisfySomeTC : Term → Term → TC Unit
 testSatisfySomeTC lemHole hole = do
   lemHole' ← satisfySomeTC
     (λ h _ → sucesfullM? (unify h (def (quote refl) [])))
     hole
   unify lemHole' lemHole


module _ (p : _) (q : _) where
 zzz : ListP (idfun _) ((2 ≡ 3) ∷ (1 ≡ 1) ∷ (1 ≡ 3) ∷ [])
 zzz = testSatisfySomeTC (p ∷ q ∷ [])
