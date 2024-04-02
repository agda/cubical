{-

This file contains:
  - The inductive family 𝕁 can be constructed by iteratively applying pushouts;
  - The special cases of 𝕁 n for n = 0, 1 and 2;
  - Connectivity of inclusion maps.

  Easy, almost direct consequences of the very definition.

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.James.Inductive.PushoutFormula where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed hiding (pt)

open import Cubical.Data.Nat
open import Cubical.Tactics.NatSolver
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.Pushout.PushoutProduct
import Cubical.HITs.SequentialColimit as SColim
open import Cubical.HITs.James.Inductive.Base
  renaming (𝕁ames to 𝕁amesContruction ; 𝕁ames∞ to 𝕁ames∞Contruction)

open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level

module _
  (X∙@(X , x₀) : Pointed ℓ) where

  private
    𝕁ames  = 𝕁amesContruction  (X , x₀)
    𝕁ames∞ = 𝕁ames∞Contruction (X , x₀)

  𝕁amesPush : (n : ℕ) → Type ℓ
  𝕁amesPush n = Pushout {A = 𝕁ames n} {B = X × 𝕁ames n} {C = 𝕁ames (1 + n)} (λ xs → x₀ , xs) incl

  X→𝕁ames1 : X → 𝕁ames 1
  X→𝕁ames1 x = x ∷ []

  𝕁ames1→X : 𝕁ames 1 → X
  𝕁ames1→X (x ∷ []) = x
  𝕁ames1→X (incl []) = x₀
  𝕁ames1→X (unit [] i) = x₀

  X→𝕁ames1→X : (x : X) → 𝕁ames1→X (X→𝕁ames1 x) ≡ x
  X→𝕁ames1→X x = refl

  𝕁ames1→X→𝕁ames1 : (xs : 𝕁ames 1) → X→𝕁ames1 (𝕁ames1→X xs) ≡ xs
  𝕁ames1→X→𝕁ames1 (x ∷ []) = refl
  𝕁ames1→X→𝕁ames1 (incl []) i = unit [] (~ i)
  𝕁ames1→X→𝕁ames1 (unit [] i) j = unit [] (i ∨ ~ j)

  leftMap  : {n : ℕ} → 𝕁amesPush n → X × 𝕁ames (1 + n)
  leftMap  (inl (x , xs)) = x , incl xs
  leftMap  (inr ys) = x₀ , ys
  leftMap  (push xs i) = x₀ , incl xs

  rightMap : {n : ℕ} → 𝕁amesPush n → 𝕁ames (1 + n)
  rightMap (inl (x , xs)) = x ∷ xs
  rightMap (inr ys) = ys
  rightMap (push xs i) = unit xs (~ i)

  PushMap : {n : ℕ} → Pushout {A = 𝕁amesPush n} leftMap rightMap → 𝕁ames (2 + n)
  PushMap (inl (x , xs)) = x ∷ xs
  PushMap (inr ys) = incl ys
  PushMap (push (inl (x , xs)) i) = incl∷ x xs (~ i)
  PushMap (push (inr ys) i) = unit ys (~ i)
  PushMap (push (push xs i) j) = coh xs (~ i) (~ j)

  PushInv : {n : ℕ} → 𝕁ames (2 + n) → Pushout {A = 𝕁amesPush n} leftMap rightMap
  PushInv (x ∷ xs) = inl (x , xs)
  PushInv (incl xs) = inr xs
  PushInv (incl∷ x xs i) = push (inl (x , xs)) (~ i)
  PushInv (unit xs i) = push (inr xs) (~ i)
  PushInv (coh xs i j) = push (push xs (~ i)) (~ j)

  PushInvMapInv : {n : ℕ}(xs : 𝕁ames (2 + n)) → PushMap (PushInv xs) ≡ xs
  PushInvMapInv (x ∷ xs) = refl
  PushInvMapInv (incl xs) = refl
  PushInvMapInv (incl∷ x xs i) = refl
  PushInvMapInv (unit xs i) = refl
  PushInvMapInv (coh xs i j) = refl

  PushMapInvMap : {n : ℕ}(xs : Pushout {A = 𝕁amesPush n} leftMap rightMap) → PushInv (PushMap xs) ≡ xs
  PushMapInvMap (inl (x , xs)) = refl
  PushMapInvMap (inr ys) = refl
  PushMapInvMap (push (inl (x , xs)) i) = refl
  PushMapInvMap (push (inr ys) i) = refl
  PushMapInvMap (push (push xs i) j) = refl

  -- The special case 𝕁ames 2

  P0→X⋁X : 𝕁amesPush 0 → X∙ ⋁ X∙
  P0→X⋁X (inl (x , []))  = inl x
  P0→X⋁X (inr (x ∷ []))  = inr x
  P0→X⋁X (inr (incl [])) = inr x₀
  P0→X⋁X (inr (unit [] i)) = inr x₀
  P0→X⋁X (push [] i) = push tt i

  X⋁X→P0 : X∙ ⋁ X∙ → 𝕁amesPush 0
  X⋁X→P0 (inl x) = inl (x , [])
  X⋁X→P0 (inr x) = inr (x ∷ [])
  X⋁X→P0 (push tt i) = (push [] ∙ (λ i → inr (unit [] i))) i

  P0→X⋁X→P0 : (x : 𝕁amesPush 0) → X⋁X→P0 (P0→X⋁X x) ≡ x
  P0→X⋁X→P0 (inl (x , [])) = refl
  P0→X⋁X→P0 (inr (x ∷ [])) = refl
  P0→X⋁X→P0 (inr (incl [])) i = inr (unit [] (~ i))
  P0→X⋁X→P0 (inr (unit [] i)) j = inr (unit [] (i ∨ ~ j))
  P0→X⋁X→P0 (push [] i) j =
    hcomp (λ k → λ
      { (i = i0) → inl (x₀ , [])
      ; (i = i1) → inr (unit [] (~ j ∧ k))
      ; (j = i0) → compPath-filler (push []) (λ i → inr (unit [] i)) k i
      ; (j = i1) → push [] i })
    (push [] i)

  X⋁X→P0→X⋁X : (x : X∙ ⋁ X∙) → P0→X⋁X (X⋁X→P0 x) ≡ x
  X⋁X→P0→X⋁X (inl x) = refl
  X⋁X→P0→X⋁X (inr x) = refl
  X⋁X→P0→X⋁X (push tt i) j =
    hcomp (λ k → λ
      { (i = i0) → inl x₀
      ; (i = i1) → inr x₀
      ; (j = i0) → P0→X⋁X (compPath-filler (push []) refl k i)
      ; (j = i1) → push tt i })
    (push tt i)

  P0≃X⋁X : 𝕁amesPush 0 ≃ X∙ ⋁ X∙
  P0≃X⋁X = isoToEquiv (iso P0→X⋁X X⋁X→P0 X⋁X→P0→X⋁X P0→X⋁X→P0)

  -- The type family 𝕁ames can be constructed by iteratively using pushouts

  𝕁ames0≃ : 𝕁ames 0 ≃ Unit
  𝕁ames0≃ = isoToEquiv (iso (λ { [] → tt }) (λ { tt → [] }) (λ { tt → refl }) (λ { [] → refl }))

  𝕁ames1≃ : 𝕁ames 1 ≃ X
  𝕁ames1≃ = isoToEquiv (iso 𝕁ames1→X X→𝕁ames1 X→𝕁ames1→X 𝕁ames1→X→𝕁ames1)

  𝕁ames2+n≃ : (n : ℕ) → 𝕁ames (2 + n) ≃ Pushout leftMap rightMap
  𝕁ames2+n≃ n = isoToEquiv (iso PushInv PushMap PushMapInvMap PushInvMapInv)

  private
    left≃ : X × 𝕁ames 1 ≃ X × X
    left≃ = ≃-× (idEquiv _) 𝕁ames1≃

    lComm : (x : 𝕁amesPush 0) → left≃ .fst (leftMap x) ≡ ⋁↪ (P0→X⋁X x)
    lComm (inl (x , []))  = refl
    lComm (inr (x ∷ []))  = refl
    lComm (inr (incl [])) = refl
    lComm (inr (unit [] i)) = refl
    lComm (push [] i) = refl

    rComm : (x : 𝕁amesPush 0) → 𝕁ames1≃ .fst (rightMap x) ≡ fold⋁ (P0→X⋁X x)
    rComm (inl (x , []))  = refl
    rComm (inr (x ∷ []))  = refl
    rComm (inr (incl [])) = refl
    rComm (inr (unit [] i)) = refl
    rComm (push [] i) = refl

  𝕁ames2≃ : 𝕁ames 2 ≃ Pushout {A = X∙ ⋁ X∙} ⋁↪ fold⋁
  𝕁ames2≃ =
    compEquiv (𝕁ames2+n≃ 0)
      (pushoutEquiv _ _ _ _ P0≃X⋁X left≃ 𝕁ames1≃ (funExt lComm) (funExt rComm))

  -- The leftMap can be seen as pushout-product

  private
    Unit×-≃ : {A : Type ℓ} → A ≃ Unit × A
    Unit×-≃ = isoToEquiv (invIso lUnit×Iso)

    pt : Unit → X
    pt _ = x₀

  𝕁amesPush' : (n : ℕ) → Type ℓ
  𝕁amesPush' n = PushProd {X = Unit} {A = X} {Y = 𝕁ames n} {B = 𝕁ames (1 + n)} pt incl

  leftMap' : {n : ℕ} → 𝕁amesPush' n → X × 𝕁ames (1 + n)
  leftMap' = pt ×̂ incl

  𝕁amesPush→Push' : (n : ℕ) → 𝕁amesPush n → 𝕁amesPush' n
  𝕁amesPush→Push' n (inl x) = inr x
  𝕁amesPush→Push' n (inr x) = inl (tt , x)
  𝕁amesPush→Push' n (push x i) = push (tt , x) (~ i)

  𝕁amesPush'→Push : (n : ℕ) → 𝕁amesPush' n → 𝕁amesPush n
  𝕁amesPush'→Push n (inl (tt , x)) = inr x
  𝕁amesPush'→Push n (inr x) = inl x
  𝕁amesPush'→Push n (push (tt , x) i) = push x (~ i)

  𝕁amesPush≃ : (n : ℕ) → 𝕁amesPush n ≃ 𝕁amesPush' n
  𝕁amesPush≃ n = isoToEquiv
    (iso (𝕁amesPush→Push' n) (𝕁amesPush'→Push n)
         (λ { (inl x) → refl ; (inr x) → refl ; (push x i) → refl })
         (λ { (inl x) → refl ; (inr x) → refl ; (push x i) → refl }))

  ≃𝕁ames1 : X ≃ 𝕁ames 1
  ≃𝕁ames1 = isoToEquiv (iso X→𝕁ames1 𝕁ames1→X 𝕁ames1→X→𝕁ames1 X→𝕁ames1→X)

  ≃𝕁ames2+n : (n : ℕ) → Pushout leftMap rightMap ≃ 𝕁ames (2 + n)
  ≃𝕁ames2+n n = isoToEquiv (iso PushMap PushInv PushInvMapInv PushMapInvMap)

  -- The connectivity of inclusion

  private
    comp1 : (n : ℕ) → leftMap' ∘ 𝕁amesPush≃ n .fst ≡ leftMap
    comp1 n = funExt (λ { (inl x) → refl ; (inr x) → refl ; (push x i) → refl })

    comp2 : (n : ℕ) → ≃𝕁ames2+n n .fst ∘ inr ≡ incl
    comp2 n = funExt (λ _ → refl)

    comp3 : ≃𝕁ames1 .fst ∘ pt ∘ 𝕁ames0≃ .fst ≡ incl
    comp3 i [] = unit [] (~ i)

    isConnIncl0 :
        (n : ℕ) → isConnected (1 + n) X
      → isConnectedFun n (incl {X∙ = X∙} {n = 0})
    isConnIncl0 n conn =
      subst (isConnectedFun _) comp3
        (isConnectedComp _ _ _ (isEquiv→isConnected _ (≃𝕁ames1 .snd) _)
          (isConnectedComp _ _ _ (isConnectedPoint _ conn _)
            (isEquiv→isConnected _ (𝕁ames0≃ .snd) _)))

    isConnIncl-ind :
        (m n k : ℕ) → isConnected (1 + m) X
      → isConnectedFun n (incl {X∙ = X∙} {n = k})
      → isConnectedFun (m + n) (incl {X∙ = X∙} {n = 1 + k})
    isConnIncl-ind m n k connX connf =
      subst (isConnectedFun _) (comp2 _)
        (isConnectedComp _ _ _ (isEquiv→isConnected _ (≃𝕁ames2+n k .snd) _)
          (inrConnected _ _ _
            (subst (isConnectedFun _) (comp1 _)
              (isConnectedComp _ _ _
                (isConnected×̂ (isConnectedPoint _ connX _) connf)
                  (isEquiv→isConnected _ (𝕁amesPush≃ k .snd) _)))))

    nat-path : (n m k : ℕ) → (1 + (k + m)) · n ≡ k · n + (1 + m) · n
    nat-path _ _ _ = solveℕ!

  -- Connectivity results

  isConnectedIncl : (n : ℕ) → isConnected (1 + n) X
    → (m : ℕ) → isConnectedFun ((1 + m) · n) (incl {X∙ = X∙} {n = m})
  isConnectedIncl n conn 0 = subst (λ d → isConnectedFun d _) (sym (+-zero n)) (isConnIncl0 n conn)
  isConnectedIncl n conn (suc m) = isConnIncl-ind _ _ _ conn (isConnectedIncl n conn m)

  isConnectedIncl>n : (n : ℕ) → isConnected (1 + n) X
    → (m k : ℕ) → isConnectedFun ((1 + m) · n) (incl {X∙ = X∙} {n = k + m})
  isConnectedIncl>n n conn m k = isConnectedFunSubtr _ (k · n) _
    (subst (λ d → isConnectedFun d (incl {X∙ = X∙} {n = k + m}))
      (nat-path n m k) (isConnectedIncl n conn (k + m)))

  private
    inl∞ : (n : ℕ) → 𝕁ames n → 𝕁ames∞
    inl∞ _ = SColim.incl

  isConnectedInl : (n : ℕ) → isConnected (1 + n) X
    → (m : ℕ) → isConnectedFun ((1 + m) · n) (inl∞ m)
  isConnectedInl n conn m = SColim.isConnectedIncl∞ _ _ _ (isConnectedIncl>n _ conn _)
