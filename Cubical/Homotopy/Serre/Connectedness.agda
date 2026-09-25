{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.Connectedness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as Trunc

open import Cubical.Homotopy.Serre.PointedHITs

private
  variable
    ℓ : Level

-- TODO: the following is in a where-clause in "Cubical.Cohomology.EilenbergMacLane.Groups.Unit"
--       This should be proved in full generality as below and then just instantiated
-- isConnected2Unit : isConnected 2 Unit
-- fst isConnected2Unit = ∣ tt ∣
-- snd isConnected2Unit = Trunc.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _) λ _ → refl

isConnectedUnit : (n : ℕ) → isConnected n Unit
isConnectedUnit n = isContr→isContr∥ n isContrUnit

-- join of Unit
joinUnit : Iso (join Unit Unit) Unit
Iso.fun joinUnit (inl tt) = tt
Iso.fun joinUnit (inr tt) = tt
Iso.fun joinUnit (push tt tt i) = tt
Iso.inv joinUnit tt = inl tt
Iso.sec joinUnit tt = refl
Iso.ret joinUnit (inl tt) = refl
Iso.ret joinUnit (inr tt) = push tt tt
Iso.ret joinUnit (push tt tt i) = λ j → push tt tt (i ∧ j)

join→Unit : {X₀ X₁ : Type ℓ}
             → (Iso.fun joinUnit) ∘ (join→ {A = X₀} {B = X₁}
                                             (λ _ → tt)
                                             (λ _ → tt))
              ≡ (λ _ → tt)
join→Unit = refl

-- functoriality of join
joinFunctExt : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level}
               {X₀ : Type ℓ} {X₁ : Type ℓ₁}
               {Y₀ : Type ℓ₂} {Y₁ : Type ℓ₃}
               {Z₀ : Type ℓ₄} {Z₁ : Type ℓ₅}
               (f₀ : X₀ → Y₀) (f₁ : X₁ → Y₁)
               (g₀ : Y₀ → Z₀) (g₁ : Y₁ → Z₁)
               (x : join X₀ X₁)
             → (join→ (g₀ ∘ f₀) (g₁ ∘ f₁)) x ≡ ((join→ g₀ g₁) ∘ (join→ f₀ f₁)) x
joinFunctExt f₀ f₁ g₀ g₁ (inl x) = refl
joinFunctExt f₀ f₁ g₀ g₁ (inr x) = refl
joinFunctExt f₀ f₁ g₀ g₁ (push a b i) = refl

-- commutativity of join→
join→-commExt : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
                {W : Type ℓ₁} {X : Type ℓ₂} {Y : Type ℓ₃} {Z : Type ℓ₄}
                (f : W → Y) (g : X → Z) (x : join X W)
              → (join-commFun ∘ (join→ f g) ∘ join-commFun) x ≡ (join→ g f) x
join→-commExt f g (inl x) = refl
join→-commExt f g (inr x) = refl
join→-commExt f g (push a b i) = refl

join→-comm : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
             {W : Type ℓ₁} {X : Type ℓ₂} {Y : Type ℓ₃} {Z : Type ℓ₄}
             (f : W → Y) (g : X → Z)
           → join-commFun ∘ (join→ f g) ∘ join-commFun ≡ (join→ g f)
join→-comm f g = funExt (join→-commExt f g)

joinFunct : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level}
            {X₀ : Type ℓ} {X₁ : Type ℓ₁}
            {Y₀ : Type ℓ₂} {Y₁ : Type ℓ₃}
            {Z₀ : Type ℓ₄} {Z₁ : Type ℓ₅}
            (f₀ : X₀ → Y₀) (f₁ : X₁ → Y₁)
            (g₀ : Y₀ → Z₀) (g₁ : Y₁ → Z₁)
          → join→ (g₀ ∘ f₀) (g₁ ∘ f₁) ≡ (join→ g₀ g₁) ∘ (join→ f₀ f₁)
joinFunct f₀ f₁ g₀ g₁ = funExt (joinFunctExt f₀ f₁ g₀ g₁)

-- connectivity facts
connectedMin : {ℓ₁ ℓ₂ ℓ₃ : Level} (n₁ n₂ : ℕ)
               {X : Type ℓ₁} {Y : Type ℓ₂} {Z : Type ℓ₃}
               (f : X → Y) (g : Y → Z)
            → isConnectedFun n₁ f → isConnectedFun n₂ g
            → (k : ℕ) → k ≤ n₁ → k ≤ n₂
            → isConnectedFun k (g ∘ f)
connectedMin n₁ n₂ f g hf hg k (m₁ , p₁) (m₂ , p₂) =
  isConnectedComp g f k
    (isConnectedFunSubtr k m₂ g
       (transport (λ i → isConnectedFun (p₂ (~ i)) g) hg))
    (isConnectedFunSubtr k m₁ f
       (transport (λ i → isConnectedFun (p₁ (~ i)) f) hf))

isConnectedFunPushout : {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type ℓ}
  (f₁ : X₀ → X₁) (f₂ : X₀ → X₂) (g₁ : Y₀ → Y₁) (g₂ : Y₀ → Y₂)
  (h₀ : X₀ → Y₀) (h₁ : X₁ → Y₁) (h₂ : X₂ → Y₂)
  (e₁ : h₁ ∘ f₁ ≡ g₁ ∘ h₀) (e₂ : h₂ ∘ f₂ ≡ g₂ ∘ h₀)
  (n : HLevel)
  → isConnectedFun n h₀ → isConnectedFun (1 + n) h₁ → isConnectedFun (1 + n) h₂
  → isConnectedFun (1 + n) (Pushout→ f₁ f₂ g₁ g₂ h₀ h₁ h₂ e₁ e₂)
isConnectedFunPushout = isConnectedPushout→

isConnectedFunS∙ : {X Y : Pointed ℓ} (f : X →∙ Y) (n : HLevel)
  → isConnectedFun n (fst f)
  → isConnectedFun n (fst (S∙→ f))
isConnectedFunS∙ f n con b =
  isConnectedSubtr n 1 (isConnectedSuspFun (fst f) n con b)

joinConnected' : {ℓ₁ ℓ₂ ℓ₃ : Level} (m n : ℕ)
                 {A : Type ℓ₁} {A' : Type ℓ₂} (B : Type ℓ₃)
                 (v : A → A')
               → isConnectedFun m v
               → isConnected n B
               → isConnectedFun (m + n) (join→ (idfun B) v)
joinConnected' m n B v hv hB =
  transport (λ i → isConnectedFun (m + n) (join→-comm v (idfun B) i))
            (isConnectedComp (join-commFun ∘ (join→ v (idfun B)))
                             join-commFun
                             (m + n)
                             (isConnectedComp
                                join-commFun
                                (join→ v (idfun B))
                                (m + n)
                                (isEquiv→isConnected join-commFun
                                   (isIsoToIsEquiv (IsoToIsIso join-comm))
                                   (m + n))
                                (joinConnected m n hv hB))
                             (isEquiv→isConnected join-commFun
                                (isIsoToIsEquiv (IsoToIsIso join-comm))
                                (m + n)))

isConnectedFunJoin : {ℓ' : Level} {X₁ X₂ : Type ℓ} {Y₁ Y₂ : Type ℓ'}
    (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂)
    (n₁ n₂ m₁ m₂ : HLevel)
    (k : HLevel) (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ n₂ + m₁)
    → isConnectedFun n₁ f₁ → isConnectedFun n₂ f₂
    → isConnected m₁ X₁ → isConnected m₂ Y₂
    → isConnectedFun k (join→ f₁ f₂)
isConnectedFunJoin {ℓ} {ℓ'} f₁ f₂ n₁ n₂ m₁ m₂ k hk₁ hk₂ hf₁ hf₂ hX₁ hY₂ =
  transport (λ i → isConnectedFun k
                    (joinFunct (idfun _) f₂ f₁ (idfun _) (~ i)))
            (connectedMin (n₂ + m₁) (n₁ + m₂)
              (join→ (idfun _) f₂) (join→ f₁ (idfun _))
              (joinConnected' n₂ m₁ _ _ hf₂ hX₁)
              (joinConnected n₁ m₂ hf₁ hY₂)
              k hk₂ hk₁)

isConnectedJoin : {X₁ X₂ : Type ℓ} (n₁ n₂ : HLevel) (k : HLevel)
                  (hk : k ≤ n₁ + n₂)
                  → isConnected n₁ X₁
                  → isConnected n₂ X₂
                  → isConnected k (join X₁ X₂)
isConnectedJoin {ℓ} {X₁} {X₂} n₁ n₂ k hk cX₁ cX₂ =
  isConnectedFun→isConnected k
    (transport (λ i → isConnectedFun k (join→Unit {X₀ = X₁} {X₁ = X₂} i))
       (isConnectedComp (Iso.fun (joinUnit)) (join→ (λ _ → tt) (λ _ → tt))
                        k (isEquiv→isConnected (Iso.fun (joinUnit))
                             (isIsoToIsEquiv (IsoToIsIso joinUnit))
                             k)
                       (isConnectedFunJoin _ _ n₁ n₂ n₁ n₂ k hk
                         (transport (λ i → k ≤ (+-comm n₁ n₂ i))
                                    hk)
                       (isConnected→isConnectedFun n₁ cX₁)
                       (isConnected→isConnectedFun n₂ cX₂)
                       cX₁ (isConnectedUnit n₂))))
