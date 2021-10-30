{-# OPTIONS  --cubical --without-K --safe #-}

open import Cubical.Core.Everything 

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.GroupoidLaws 
open import Cubical.Foundations.HLevels 

open import Cubical.Foundations.Equiv 
open import Cubical.Foundations.Isomorphism 
open import Cubical.Foundations.Univalence 

open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma 

open import Cubical.Homotopy.Connected 


module Cubical.Homotopy.BlakersMassey {ℓ₁ ℓ₂ ℓ₃ : Level}
  (X : Type ℓ₁)(Y : Type ℓ₂)(Q : X → Y → Type ℓ₃) 
  {m : HLevel} (leftConn  : (x : X) → isConnected (1 + m) (Σ[ y ∈ Y ] Q x y))
  {n : HLevel} (rightConn : (y : Y) → isConnected (1 + n) (Σ[ x ∈ X ] Q x y))
  where
    
ℓ : Level 
ℓ = ℓ-max (ℓ-max ℓ₁ ℓ₂) ℓ₃ 

leftFiber  : X → Type (ℓ-max ℓ₂ ℓ₃)
leftFiber x  = Σ[ y ∈ Y ] Q x y 

rightFiber : Y → Type (ℓ-max ℓ₁ ℓ₃)
rightFiber y = Σ[ x ∈ X ] Q x y 


{- An alternative formulation of pushout with fewer parameters -}

data Pushout : Type ℓ 
  where
    inl : X → Pushout
    inr : Y → Pushout
    push : {x : X}{y : Y} → Q x y → inl x ≡ inr y 

{- 
_∙sq_ : {ℓ' : Level}{A : Type ℓ'}
      → (n : HLevel) → ((x : A) → (y : B x) → isOfHLevel n (C x y))
      → isOfHLevel n ((x : A) → (y : B x) → C x y) 
isOfHLevelΠ₂ n f = isOfHLevelΠ n (λ x → isOfHLevelΠ n (f x)) -} 

isOfHLevelΠ₂ : {ℓ' ℓ'' ℓ''' : Level}{A : Type ℓ'}{B : A → Type ℓ''}{C : (x : A) → B x → Type ℓ'''}
             → (n : HLevel) → ((x : A) → (y : B x) → isOfHLevel n (C x y))
             → isOfHLevel n ((x : A) → (y : B x) → C x y) 
isOfHLevelΠ₂ n f = isOfHLevelΠ n (λ x → isOfHLevelΠ n (f x))


open import Cubical.HITs.Truncation renaming (hLevelTrunc to Trunc)
open import Cubical.Foundations.Function 

recUniq : {ℓ' ℓ'' : Level}{n : HLevel}{A : Type ℓ'}{B : Type ℓ''}
        → (h : isOfHLevel n B) 
        → (g : A → B) 
        → (x : A)
        → rec h g ∣ x ∣ₕ ≡ g x 
recUniq {n = zero} h g x = h .snd (g x)
recUniq {n = suc n} _ _ _ = refl 

∘rec : {ℓ' ℓ'' ℓ''' : Level}{n : HLevel}{A : Type ℓ'}{B : Type ℓ''}{C : Type ℓ'''}
     → (h : isOfHLevel n B) 
     → (h' : isOfHLevel n C) 
     → (g : A → B) 
     → (f : B → C) 
     → (x : Trunc n A)
     → rec h' (f ∘ g) x ≡ f (rec h g x)
∘rec {n = zero} h h' g f x = h' .snd (f (rec h g x))
∘rec {n = suc n} h h' g f = elim (λ _ → isOfHLevelPath _ h' _ _) (λ _ → refl)

recId : {ℓ' : Level}{n : HLevel}{A : Type ℓ'} 
      → (f : A → Trunc n A) 
      → ((x : A) → f x ≡ ∣ x ∣ₕ) 
      → rec (isOfHLevelTrunc _) f ≡ idfun _
recId {n = n} f h i x = 
  elim {B = λ a → rec (isOfHLevelTrunc _) f a ≡ a} 
       (λ _ → isOfHLevelTruncPath) (λ a → recUniq {n = n} (isOfHLevelTrunc _) f a ∙ h a) x i 


fiberSquare : {x₀ x₁ : X}{y₀ : Y}{p : Pushout}(q₀₀ : Q x₀ y₀)(q₁₀ : Q x₁ y₀) 
            → inl x₁ ≡ p → inl x₀ ≡ p → Type ℓ 
fiberSquare q₀₀ q₁₀ r' r = 
  PathP (λ i → push q₀₀ (~ i) ≡ r' i) (sym (push q₁₀)) r

fiberSquarePush : {x₀ x₁ : X}{y₀ y₁ : Y}(q₀₀ : Q x₀ y₀)(q₁₀ : Q x₁ y₀)(q₁₁ : Q x₁ y₁)
                → inl x₀ ≡ inr y₁ → Type ℓ 
fiberSquarePush q₀₀ q₁₀ q₁₁ = fiberSquare q₀₀ q₁₀ (push q₁₁)   

fiber' : {x₀ : X}{y₀ : Y}(q₀₀ : Q x₀ y₀){x₁ : X}{p : Pushout} → inl x₁ ≡ p → inl x₀ ≡ p → Type ℓ 
fiber' {y₀ = y₀} q₀₀ {x₁ = x₁} r' r = 
  Σ[ q₁₀ ∈ Q x₁ y₀ ] fiberSquare q₀₀ q₁₀ r' r 

fiber'Push : {x₀ x₁ : X}{y₀ y₁ : Y}(q₀₀ : Q x₀ y₀)(q₁₁ : Q x₁ y₁) → inl x₀ ≡ inr y₁ → Type ℓ 
fiber'Push q₀₀ q₁₁ = fiber' q₀₀ (push q₁₁)

leftCodeExtended : {x₀ : X}{y₀ : Y}(q₀₀ : Q x₀ y₀)(x₁ : X){p : Pushout} → inl x₁ ≡ p → inl x₀ ≡ p → Type ℓ 
leftCodeExtended {y₀ = y₀} q₀₀ x₁ r' r = 
  Trunc (m + n) (fiber' q₀₀ r' r)

rightCode : {x₀ : X}(y : Y) → inl x₀ ≡ inr y → Type ℓ 
rightCode y r = 
  Trunc (m + n) (fiber push r) 


{- Definitions of fiber→ -}

module _ 
  {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) where 

  {- (x₀ , q₀₀) = (x₁ , q₁₀) -}
  module _ 
    {y₁ : Y}(q₁₁ : Q x₁ y₁) 
    (r : inl x₁ ≡ inr y₁) 
    (p : fiberSquarePush q₁₀ q₁₀ q₁₁ r) where 

    fiber→[q₀₀=q₁₀]-filler : (i j k : I) → Pushout 
    fiber→[q₀₀=q₁₀]-filler i j k' = 
      hfill (λ k → λ { (i = i0) → push q₁₁ (j ∧ k) 
                     ; (i = i1) → p k j 
                     ; (j = i0) → push q₁₀ (i ∧ ~ k) 
                     ; (j = i1) → push q₁₁ k }) 
            (inS (push q₁₀ (i ∧ ~ j))) k'

    fiber→[q₀₀=q₁₀] : fiber push r 
    fiber→[q₀₀=q₁₀] .fst = q₁₁ 
    fiber→[q₀₀=q₁₀] .snd i j = fiber→[q₀₀=q₁₀]-filler i j i1 

    ∣fiber→[q₀₀=q₁₀]∣ : rightCode _ r 
    ∣fiber→[q₀₀=q₁₀]∣ = ∣ fiber→[q₀₀=q₁₀] ∣ₕ 

  {- (y₁ , q₁₁) = (y₀ , q₁₀) -}
  module _ 
    {x₀ : X}(q₀₀ : Q x₀ y₀) 
    (r : inl x₀ ≡ inr y₀) 
    (p : fiberSquarePush q₀₀ q₁₀ q₁₀ r) where 

    fiber→[q₁₁=q₁₀]-filler : (i j k : I) → Pushout 
    fiber→[q₁₁=q₁₀]-filler i j k' = 
      hfill (λ k → λ { (i = i0) → push q₀₀ (j ∨ ~ k) 
                     ; (i = i1) → p k j 
                     ; (j = i0) → push q₀₀ (~ k) 
                     ; (j = i1) → push q₁₀ (~ i ∨ k) }) 
            (inS (push q₁₀ (~ i ∨ ~ j))) k' 

    fiber→[q₁₁=q₁₀] : fiber push r 
    fiber→[q₁₁=q₁₀] .fst = q₀₀ 
    fiber→[q₁₁=q₁₀] .snd i j = fiber→[q₁₁=q₁₀]-filler i j i1 

    ∣fiber→[q₁₁=q₁₀]∣ : rightCode _ r 
    ∣fiber→[q₁₁=q₁₀]∣ = ∣ fiber→[q₁₁=q₁₀] ∣ₕ 

  {- q₀₀ = q₁₁ = q₁₀ -} 
  fiber→[q₀₀=q₁₀=q₁₁]-filler : 
      (r : inl x₁ ≡ inr y₀) 
    → (p : fiberSquarePush q₁₀ q₁₀ q₁₀ r)
    → (i j k l : I) → Pushout 
  fiber→[q₀₀=q₁₀=q₁₁]-filler r p i j k l' = 
    hfill (λ l → λ { (i = i0) → fiber→[q₀₀=q₁₀]-filler q₁₀ r p j k l 
                   ; (i = i1) → fiber→[q₁₁=q₁₀]-filler q₁₀ r p j k l 
                   ; (j = i0) → push q₁₀ ((i ∨ (k ∧ l)) ∧ (k ∨ (i ∧ ~ l))) 
                   ; (j = i1) → p l k  
                   ; (k = i0) → push q₁₀ ((i ∨ j) ∧ ~ l) 
                   ; (k = i1) → push q₁₀ ((i ∧ ~ j) ∨ l) }) 
          (inS (push q₁₀ ((i ∨ (~ k ∧ j)) ∧ (~ k ∨ (i ∧ ~ j))))) l'

  fiber→[q₀₀=q₁₀=q₁₁] : fiber→[q₀₀=q₁₀] q₁₀ ≡ fiber→[q₁₁=q₁₀] q₁₀  
  fiber→[q₀₀=q₁₀=q₁₁] i r p .fst = q₁₀ 
  fiber→[q₀₀=q₁₀=q₁₁] i r p .snd j k = fiber→[q₀₀=q₁₀=q₁₁]-filler r p i j k i1

  ∣fiber→[q₀₀=q₁₀=q₁₁]∣ : ∣fiber→[q₀₀=q₁₀]∣ q₁₀ ≡ ∣fiber→[q₁₁=q₁₀]∣ q₁₀ 
  ∣fiber→[q₀₀=q₁₀=q₁₁]∣ i r p = ∣ fiber→[q₀₀=q₁₀=q₁₁] i r p ∣ₕ 


{- Definitions of fiber← -}

{- (x₁ , q₁₁) = (x₀ , q₀₁) -} 
module _ 
  {x₀ : X}{y₁ : Y}(q₀₁ : Q x₀ y₁) where 

  {- (x₁ , q₁₁) = (x₀ , q₀₁) -} 
  module _ 
    {y₀ : Y}(q₀₀ : Q x₀ y₀) 
    (r : inl x₀ ≡ inr y₁) 
    (p : push q₀₁ ≡ r) where 
  
    fiber←[q₁₁=q₀₁]-filler : (i j k : I) → Pushout 
    fiber←[q₁₁=q₀₁]-filler i j k' = 
      hfill (λ k → λ { (i = i0) → push q₀₀ (~ j ∧ k) 
                     ; (i = i1) → p k j 
                     ; (j = i0) → push q₀₀ (~ i ∧ k) 
                     ; (j = i1) → push q₀₁ i }) 
            (inS (push q₀₁ (i ∧ j))) k' 

    fiber←[q₁₁=q₀₁] : fiber'Push  q₀₀ q₀₁ r 
    fiber←[q₁₁=q₀₁] .fst = q₀₀ 
    fiber←[q₁₁=q₀₁] .snd i j = fiber←[q₁₁=q₀₁]-filler i j i1 

    ∣fiber←[q₁₁=q₀₁]∣ : leftCodeExtended q₀₀ _ (push q₀₁) r 
    ∣fiber←[q₁₁=q₀₁]∣ = ∣ fiber←[q₁₁=q₀₁] ∣ₕ 

  {- (y₀ , q₀₀) = (y₁ , q₀₁) -} 
  module _ 
    {x₁ : X}(q₁₁ : Q x₁ y₁) 
    (r : inl x₀ ≡ inr y₁) 
    (p : push q₀₁ ≡ r) where 

    fiber←[q₀₀=q₀₁]-filler : (i j k : I) → Pushout 
    fiber←[q₀₀=q₀₁]-filler i j k' = 
      hfill (λ k → λ { (i = i0) → push q₁₁ (~ j ∨ ~ k) 
                     ; (i = i1) → p k j 
                     ; (j = i0) → push q₀₁ (~ i)
                     ; (j = i1) → push q₁₁ (i ∨ ~ k) }) 
            (inS (push q₀₁ (~ i ∨ j))) k' 

    fiber←[q₀₀=q₀₁] : fiber'Push q₀₁ q₁₁ r 
    fiber←[q₀₀=q₀₁] .fst = q₁₁   
    fiber←[q₀₀=q₀₁] .snd i j = fiber←[q₀₀=q₀₁]-filler i j i1 

    ∣fiber←[q₀₀=q₀₁]∣ : leftCodeExtended q₀₁ _ (push q₁₁) r 
    ∣fiber←[q₀₀=q₀₁]∣ = ∣ fiber←[q₀₀=q₀₁] ∣ₕ 

  {- q₀₀ = q₀₁ = q₁₁ -}
  fiber←[q₀₀=q₀₁=q₁₁]-filler : 
      (r : inl x₀ ≡ inr y₁) 
    → (p : push q₀₁ ≡ r)
    → (i j k l : I) → Pushout 
  fiber←[q₀₀=q₀₁=q₁₁]-filler r p i j k l' = 
    hfill (λ l → λ { (i = i0) → fiber←[q₁₁=q₀₁]-filler q₀₁ r p j k l 
                   ; (i = i1) → fiber←[q₀₀=q₀₁]-filler q₀₁ r p j k l 
                   ; (j = i0) → push q₀₁ ((i ∨ (~ k ∧ l)) ∧ (~ k ∨ (i ∧ ~ l))) 
                   ; (j = i1) → p l k 
                   ; (k = i0) → push q₀₁ ((i ∨ l) ∧ ~ j)
                   ; (k = i1) → push q₀₁ ((i ∧ ~ l) ∨ j) }) 
          (inS (push q₀₁ ((i ∨ (k ∧ j)) ∧ (k ∨ (i ∧ ~ j))))) l' 

  fiber←[q₀₀=q₀₁=q₁₁] : fiber←[q₁₁=q₀₁] q₀₁ ≡ fiber←[q₀₀=q₀₁] q₀₁ 
  fiber←[q₀₀=q₀₁=q₁₁] i r p .fst = q₀₁  
  fiber←[q₀₀=q₀₁=q₁₁] i r p .snd j k = fiber←[q₀₀=q₀₁=q₁₁]-filler r p i j k i1 

  ∣fiber←[q₀₀=q₀₁=q₁₁]∣ : ∣fiber←[q₁₁=q₀₁]∣ q₀₁ ≡ ∣fiber←[q₀₀=q₀₁]∣ q₀₁ 
  ∣fiber←[q₀₀=q₀₁=q₁₁]∣ i r p = ∣ fiber←[q₀₀=q₀₁=q₁₁] i r p ∣ₕ 




open import Cubical.Homotopy.WedgeConnectivity 

module Fiber→ 
  {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) = 
  WedgeConnectivity m n 
    (leftFiber  x₁ , (y₀ , q₁₀)) (leftConn  x₁)
    (rightFiber y₀ , (x₁ , q₁₀)) (rightConn y₀)
    (λ (y₁ , q₁₁) (x₀ , q₀₀) → 
      (((r : inl x₀ ≡ inr y₁) → fiberSquarePush q₀₀ q₁₀ q₁₁ r → rightCode _ r) 
      , isOfHLevelΠ₂ _ (λ x y → isOfHLevelTrunc _)))
    (λ (y₁ , q₁₁) → ∣fiber→[q₀₀=q₁₀]∣ q₁₀ q₁₁)
    (λ (x₀ , q₀₀) → ∣fiber→[q₁₁=q₁₀]∣ q₁₀ q₀₀)
    (∣fiber→[q₀₀=q₁₀=q₁₁]∣ q₁₀) 

fiber→ : 
    {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) 
  → {x₀ : X}(q₀₀ : Q x₀ y₀) → {y₁ : Y}(q₁₁ : Q x₁ y₁) 
  → (r : inl x₀ ≡ inr y₁) 
  → fiberSquarePush q₀₀ q₁₀ q₁₁ r → rightCode _ r 
fiber→ q₁₀ q₀₀ q₁₁ = Fiber→.extension q₁₀ (_ , q₁₁) (_ , q₀₀) 


module Fiber← 
  {x₀ : X}{y₁ : Y}(q₀₁ : Q x₀ y₁) = 
  WedgeConnectivity m n 
    (leftFiber  x₀ , (y₁ , q₀₁)) (leftConn  x₀)
    (rightFiber y₁ , (x₀ , q₀₁)) (rightConn y₁)
    (λ (y₀ , q₀₀) (x₁ , q₁₁) → 
      (((r : inl x₀ ≡ inr y₁) → push q₀₁ ≡ r → leftCodeExtended q₀₀ _ (push q₁₁) r) 
      , isOfHLevelΠ₂ _ (λ x y → isOfHLevelTrunc _)))
    (λ (y₀ , q₀₀) → ∣fiber←[q₁₁=q₀₁]∣ q₀₁ q₀₀)
    (λ (x₁ , q₁₁) → ∣fiber←[q₀₀=q₀₁]∣ q₀₁ q₁₁)
    (∣fiber←[q₀₀=q₀₁=q₁₁]∣ q₀₁) 

fiber← : 
    {x₀ : X}{y₁ : Y}(q₀₁ : Q x₀ y₁) 
  → {y₀ : Y}(q₀₀ : Q x₀ y₀) → {x₁ : X}(q₁₁ : Q x₁ y₁) 
  → (r : inl x₀ ≡ inr y₁)
  → push q₀₁ ≡ r → leftCodeExtended q₀₀ _ (push q₁₁) r 
fiber← q₀₁ q₀₀ q₁₁ = Fiber←.extension q₀₁ (_ , q₀₀) (_ , q₁₁) 



left→rightCodeExtended : 
    {x₀ x₁ : X}{y₀ y₁ : Y}
  → (q₀₀ : Q x₀ y₀)(q₁₁ : Q x₁ y₁) 
  → (r : inl x₀ ≡ inr y₁) 
  → leftCodeExtended q₀₀ _ (push q₁₁) r → rightCode _ r 
left→rightCodeExtended q₀₀ q₁₁ r = 
  rec (isOfHLevelTrunc _) (λ (q₁₀ , p) → fiber→ q₁₀ q₀₀ q₁₁ r p) 

right→leftCodeExtended : 
    {x₀ x₁ : X}{y₀ y₁ : Y}
  → (q₀₀ : Q x₀ y₀)(q₁₁ : Q x₁ y₁) 
  → (r : inl x₀ ≡ inr y₁) 
  → rightCode _ r → leftCodeExtended q₀₀ _ (push q₁₁) r 
right→leftCodeExtended q₀₀ q₁₁ r = 
  rec (isOfHLevelTrunc _) (λ (q₀₁ , p) → fiber← q₀₁ q₀₀ q₁₁ r p) 


module _ 
  {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) where 

  {- (x₀ , q₀₀) = (x₁ , q₁₀) -}
  module _ 
    {y₁ : Y}(q₁₁ : Q x₁ y₁) 
    (r : inl x₁ ≡ inr y₁) 
    (p : fiberSquarePush q₁₀ q₁₀ q₁₁ r) where 

    fiber→←[q₀₀=q₁₀]-filler : (i j k l : I) → Pushout 
    fiber→←[q₀₀=q₁₀]-filler i j k l' = 
      let p' = fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p .snd in 
      hfill (λ l → λ { (i = i0) → fiber←[q₁₁=q₀₁]-filler q₁₁ q₁₀ r p' j k l 
                     ; (i = i1) → fiber→[q₀₀=q₁₀]-filler q₁₀ q₁₁ r p l k j 
                     ; (j = i0) → push q₁₀ (~ k ∧ l)
                     ; (j = i1) → p' l k  
                     ; (k = i0) → push q₁₀ (~ j ∧ l)
                     ; (k = i1) → push q₁₁ j }) 
            (inS (push q₁₁ (j ∧ k))) l' 

    fiber→←[q₀₀=q₁₀] : fiber←[q₁₁=q₀₁] q₁₁ q₁₀ r (fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p .snd) .snd ≡ p 
    fiber→←[q₀₀=q₁₀] i j k = fiber→←[q₀₀=q₁₀]-filler i j k i1 

  {- (y₁ , q₁₁) = (y₀ , q₁₀) -}
  module _ 
    {x₀ : X}(q₀₀ : Q x₀ y₀) 
    (r : inl x₀ ≡ inr y₀) 
    (p : fiberSquarePush q₀₀ q₁₀ q₁₀ r) where 

    fiber→←[q₁₁=q₁₀]-filler : (i j k l : I) → Pushout 
    fiber→←[q₁₁=q₁₀]-filler i j k l' = 
      let p' = fiber→[q₁₁=q₁₀] q₁₀ q₀₀ r p .snd in 
      hfill (λ l → λ { (i = i0) → fiber←[q₀₀=q₀₁]-filler q₀₀ q₁₀ r p' j k l 
                     ; (i = i1) → fiber→[q₁₁=q₁₀]-filler q₁₀ q₀₀ r p l k j 
                     ; (j = i0) → push q₁₀ (~ k ∨ ~ l) 
                     ; (j = i1) → p' l k  
                     ; (k = i0) → push q₀₀ (~ j) 
                     ; (k = i1) → push q₁₀ (j ∨ ~ l) }) 
            (inS (push q₀₀ (~ j ∨ k))) l'

    fiber→←[q₁₁=q₁₀] : fiber←[q₀₀=q₀₁] q₀₀ q₁₀ r (fiber→[q₁₁=q₁₀] q₁₀ q₀₀ r p .snd) .snd ≡ p 
    fiber→←[q₁₁=q₁₀] i j k = fiber→←[q₁₁=q₁₀]-filler i j k i1 

  fiber→←Hypercube : 
      (r : inl x₁ ≡ inr y₀) 
    → (p : fiberSquarePush q₁₀ q₁₀ q₁₀ r) 
    → PathP (λ i → fiber←[q₀₀=q₀₁=q₁₁] q₁₀ i r (fiber→[q₀₀=q₁₀=q₁₁] q₁₀ i r p .snd) .snd ≡ p) 
            (fiber→←[q₀₀=q₁₀] q₁₀ r p) (fiber→←[q₁₁=q₁₀] q₁₀ r p) 
  fiber→←Hypercube r p i j u v = 
    hcomp (λ l → λ { (i = i0) → fiber→←[q₀₀=q₁₀]-filler q₁₀ r p j u v l 
                   ; (i = i1) → fiber→←[q₁₁=q₁₀]-filler q₁₀ r p j u v l 
                   ; (j = i0) → fiber←[q₀₀=q₀₁=q₁₁]-filler q₁₀ r (fiber→[q₀₀=q₁₀=q₁₁] q₁₀ i r p .snd) i u v l 
                   ; (j = i1) → fiber→[q₀₀=q₁₀=q₁₁]-filler q₁₀ r p i l v u 
                   ; (u = i0) → push q₁₀ ((i ∨ (~ v ∧ l)) ∧ (~ v ∨ (i ∧ ~ l)))
                   ; (u = i1) → fiber→[q₀₀=q₁₀=q₁₁] q₁₀ i r p .snd l v     
                   ; (v = i0) → push q₁₀ ((i ∨ l) ∧ ~ u)
                   ; (v = i1) → push q₁₀ ((i ∧ ~ l) ∨ u) }) 
          (push q₁₀ ((i ∨ (v ∧ u)) ∧ (v ∨ (i ∧ ~ u)))) 


module fiber→←Square'  
  {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) 
  (r : inl x₁ ≡ inr y₀) 
  (p : fiberSquarePush q₁₀ q₁₀ q₁₀ r) where 

  leftwall : (i j k l : I) → Pushout 
  leftwall i j k l = fiber→←[q₀₀=q₁₀]-filler q₁₀ q₁₀ r p i k l j 

  rightwall : (i j k l : I) → Pushout 
  rightwall i j k l = fiber→←[q₁₁=q₁₀]-filler q₁₀ q₁₀ r p i k l j 

  frontwall : (i j k l : I) → Pushout 
  frontwall i j k l = fiber←[q₀₀=q₀₁=q₁₁]-filler q₁₀ r (fiber→[q₀₀=q₁₀=q₁₁] q₁₀ i r p .snd) i k l j 

  l=f : (i j k : I) → leftwall i0 i j k ≡ frontwall i0 i j k 
  l=f i j k = refl 

  r=f : (i j k : I) → rightwall i0 i j k ≡ frontwall i1 i j k 
  r=f i j k = refl 

  bottom : (i j k : I) → Pushout
  bottom i j k = push q₁₀ ((i ∨ (k ∧ j)) ∧ (k ∨ (i ∧ ~ j)))

  backwall : (i j k l : I) → Pushout 
  backwall i j k l = fiber→[q₀₀=q₁₀=q₁₁]-filler q₁₀ r p i j l k  

  l=b : (i j k : I) → leftwall i1 i j k ≡ backwall i0 i j k 
  l=b i j k = refl 

  r=b : (i j k : I) → rightwall i1 i j k ≡ backwall i1 i j k 
  r=b i j k = refl 

  bottom=back : (i j k : I) → bottom i j k ≡ backwall i i0 j k
  bottom=back i j k = refl 



module ∣fiber→←[q₀₀=q₁₀]∣ 
  {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) 
  {y₁ : Y}(q₁₁ : Q x₁ y₁) 
  (r : inl x₁ ≡ inr y₁) 
  (p : fiberSquarePush q₁₀ q₁₀ q₁₁ r) where 

  path1 : right→leftCodeExtended q₁₀ q₁₁ r (fiber→ q₁₀ q₁₀ q₁₁ r p) ≡ right→leftCodeExtended q₁₀ q₁₁ r (∣fiber→[q₀₀=q₁₀]∣ q₁₀ q₁₁ r p) 
  path1 i = right→leftCodeExtended q₁₀ q₁₁ r (Fiber→.left q₁₀ (_ , q₁₁) i r p) 

  path2 : right→leftCodeExtended q₁₀ q₁₁ r (∣fiber→[q₀₀=q₁₀]∣ q₁₀ q₁₁ r p) ≡ right→leftCodeExtended q₁₀ q₁₁ r ∣ fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p ∣ₕ 
  path2 = refl 

  path3 : right→leftCodeExtended q₁₀ q₁₁ r ∣ fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p ∣ₕ ≡ fiber← q₁₁ q₁₀ q₁₁ r (fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p .snd) 
  path3 = recUniq {n = m + n} _ _ _ 

  path4 : fiber← q₁₁ q₁₀ q₁₁ r (fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p .snd) ≡ ∣ fiber←[q₁₁=q₀₁] q₁₁ q₁₀ r (fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p .snd) ∣ₕ 
  path4 i = Fiber←.left q₁₁ (_ , q₁₀) i r (fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p .snd) 

  path5 : ∣ fiber←[q₁₁=q₀₁] q₁₁ q₁₀ r (fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p .snd) ∣ₕ ≡ ∣_∣ₕ {n = m + n} (q₁₀ , p)
  path5 i = ∣ (q₁₀ , fiber→←[q₀₀=q₁₀] q₁₀ q₁₁ r p i) ∣ₕ 

  path' : right→leftCodeExtended q₁₀ q₁₁ r (fiber→ q₁₀ q₁₀ q₁₁ r p) ≡ ∣ (q₁₀ , p) ∣ₕ 
  path' = path1 ∙ path2 ∙ path3 ∙ path4 ∙ path5 

  path : right→leftCodeExtended q₁₀ q₁₁ r (fiber→ q₁₀ q₁₀ q₁₁ r p) ≡ ∣ (q₁₀ , p) ∣ₕ 
  path = 
      (λ i → right→leftCodeExtended q₁₀ q₁₁ r (Fiber→.left q₁₀ (_ , q₁₁) i r p)) 
    ∙ recUniq {n = m + n} _ _ _ 
    ∙ (λ i → Fiber←.left q₁₁ (_ , q₁₀) i r (fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p .snd)) 
    ∙ (λ i → ∣ (q₁₀ , fiber→←[q₀₀=q₁₀] q₁₀ q₁₁ r p i) ∣ₕ)


module ∣fiber→←[q₁₁=q₁₀]∣  
  {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) 
  {x₀ : X}(q₀₀ : Q x₀ y₀) 
  (r : inl x₀ ≡ inr y₀) 
  (p : fiberSquarePush q₀₀ q₁₀ q₁₀ r) where 

  path1 : right→leftCodeExtended q₀₀ q₁₀ r (fiber→ q₁₀ q₀₀ q₁₀ r p) ≡ right→leftCodeExtended q₀₀ q₁₀ r (∣fiber→[q₁₁=q₁₀]∣ q₁₀ q₀₀ r p) 
  path1 i = right→leftCodeExtended q₀₀ q₁₀ r (Fiber→.right q₁₀ (_ , q₀₀) i r p) 

  path2 : right→leftCodeExtended q₀₀ q₁₀ r (∣fiber→[q₁₁=q₁₀]∣ q₁₀ q₀₀ r p) ≡ right→leftCodeExtended q₀₀ q₁₀ r ∣ fiber→[q₁₁=q₁₀] q₁₀ q₀₀ r p ∣ₕ 
  path2 = refl 

  path3 : right→leftCodeExtended q₀₀ q₁₀ r ∣ fiber→[q₁₁=q₁₀] q₁₀ q₀₀ r p ∣ₕ ≡ fiber← q₀₀ q₀₀ q₁₀ r (fiber→[q₁₁=q₁₀] q₁₀ q₀₀ r p .snd) 
  path3 = recUniq {n = m + n} _ _ _ 

  path4 : fiber← q₀₀ q₀₀ q₁₀ r (fiber→[q₁₁=q₁₀] q₁₀ q₀₀ r p .snd) ≡ ∣ fiber←[q₀₀=q₀₁] q₀₀ q₁₀ r (fiber→[q₁₁=q₁₀] q₁₀ q₀₀ r p .snd) ∣ₕ 
  path4 i = Fiber←.right q₀₀ (_ , q₁₀) i r (fiber→[q₁₁=q₁₀] q₁₀ q₀₀ r p .snd) 

  path5 : ∣ fiber←[q₀₀=q₀₁] q₀₀ q₁₀ r (fiber→[q₁₁=q₁₀] q₁₀ q₀₀ r p .snd) ∣ₕ ≡ ∣_∣ₕ {n = m + n} (q₁₀ , p)
  path5 i = ∣ (q₁₀ , fiber→←[q₁₁=q₁₀] q₁₀ q₀₀ r p i) ∣ₕ 

  path : right→leftCodeExtended q₀₀ q₁₀ r (fiber→ q₁₀ q₀₀ q₁₀ r p) ≡ ∣ (q₁₀ , p) ∣ₕ 
  path = path1 ∙ path2 ∙ path3 ∙ path4 ∙ path5 


module ∣fiber→[q₀₀=q₁₀=q₁₁]∣ 
  {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) where 

  path : ∣fiber→←[q₀₀=q₁₀]∣.path q₁₀ q₁₀ ≡ ∣fiber→←[q₁₁=q₁₀]∣.path q₁₀ q₁₀ 
  path = {!!} 




fiber→← : 
    {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) 
  → {x₀ : X}(q₀₀ : Q x₀ y₀) → {y₁ : Y}(q₁₁ : Q x₁ y₁) 
  → (r : inl x₀ ≡ inr y₁) 
  → (p : fiberSquarePush q₀₀ q₁₀ q₁₁ r)
  → right→leftCodeExtended q₀₀ q₁₁ r (fiber→ q₁₀ q₀₀ q₁₁ r p) ≡ ∣ (q₁₀ , p) ∣ₕ 
fiber→← {x₁ = x₁} {y₀ = y₀} q₁₀ q₀₀' q₁₁' = 
  WedgeConnectivity.extension m n 
    (leftFiber  x₁ , (y₀ , q₁₀)) (leftConn  x₁)
    (rightFiber y₀ , (x₁ , q₁₀)) (rightConn y₀)
    (λ (y₁ , q₁₁) (x₀ , q₀₀) → 
      (((r : inl x₀ ≡ inr y₁) → (p : fiberSquarePush q₀₀ q₁₀ q₁₁ r) → right→leftCodeExtended q₀₀ q₁₁ r (fiber→ q₁₀ q₀₀ q₁₁ r p) ≡ ∣ (q₁₀ , p) ∣ₕ ) 
      , isOfHLevelΠ₂ _ (λ x y → isOfHLevelTruncPath)))
    (λ (y₁ , q₁₁) → ∣fiber→←[q₀₀=q₁₀]∣.path q₁₀ q₁₁)
    (λ (x₀ , q₀₀) → ∣fiber→←[q₁₁=q₁₀]∣.path q₁₀ q₀₀)
    (∣fiber→[q₀₀=q₁₀=q₁₁]∣.path q₁₀) 
    (_ , q₁₁') (_ , q₀₀') 



left→right→leftCodeExtended : 
    {x₀ x₁ : X}{y₀ y₁ : Y}
  → (q₀₀ : Q x₀ y₀)(q₁₁ : Q x₁ y₁) 
  → (r : inl x₀ ≡ inr y₁) 
  → (a : leftCodeExtended q₀₀ _ (push q₁₁) r)
  → right→leftCodeExtended q₀₀ q₁₁ r (left→rightCodeExtended q₀₀ q₁₁ r a) ≡ a 
left→right→leftCodeExtended q₀₀ q₁₁ r a = 
  sym (∘rec _ _ _ (right→leftCodeExtended q₀₀ q₁₁ r) a) ∙ 
  (λ i → recId _ (λ (q₁₀ , p) → fiber→← q₁₀ q₀₀ q₁₁ r p) i a) 



right→left→rightCodeExtended : 
    {x₀ x₁ : X}{y₀ y₁ : Y}
  → (q₀₀ : Q x₀ y₀)(q₁₁ : Q x₁ y₁) 
  → (r : inl x₀ ≡ inr y₁) 
  → (a : rightCode _ r)
  → left→rightCodeExtended q₀₀ q₁₁ r (right→leftCodeExtended q₀₀ q₁₁ r a) ≡ a 
right→left→rightCodeExtended q₀₀ q₁₁ r a = {!!} 

fiberEquiv₀ : {x₀ : X}{y₁ : Y} → (q₀₁ : Q x₀ y₁) 
            → {y₀ : Y}(q₀₀ : Q x₀ y₀) 
            → leftCodeExtended q₀₀ x₀ (push q₀₁) (push q₀₁) ≃ rightCode y₁ (push q₀₁) 
fiberEquiv₀ q = {!!} 


{-
fiberEquiv : {x₀ : X}{y₁ : Y} → (r : inl x₀ ≡ inr y₁) 
           → {y₀ : Y}(q₀₀ : Q x₀ y₀) → {x₁ : X}(q₁₁ : Q x₁ y₁) 
           → leftCodeExtended q₀₀ x₁ (push q₁₁) r ≃ rightCode y₁ r 
fiberEquiv q = {!!} -}


{-
module _ (x₀ : X) (y₀ : Y) (q₀₀ : Q x₀ y₀) where


  leftCodeExtended : (x : X){p : Pushout} → inl x ≡ p → inl x₀ ≡ p → Type ℓ 
  leftCodeExtended x r' r = 
    Trunc (2 + m + n) (fiber (λ q₁₀ → push q₀₀ ∙∙ sym (push q₁₀) ∙∙ r') r) 

  leftCode  : (x : X) → inl x₀ ≡ inl x → Type ℓ 
  leftCode  x = 
    leftCodeExtended x refl 

  rightCode : (y : Y) → inl x₀ ≡ inr y → Type ℓ 
  rightCode y r = 
    Trunc (2 + m + n) (fiber push r) 


  open import Cubical.Foundations.Function 
  open import Cubical.Foundations.Transport 


  transpLeftCode : {x : X}{p : Pushout} → (r' : inl x ≡ p) 
                 → transport (λ i → inl x₀ ≡ r' i → Type ℓ) (leftCode x) ≡ leftCodeExtended x r' 
  transpLeftCode = 
    J (λ p r → transport (λ i → inl x₀ ≡ r i → Type ℓ) (leftCode _) ≡ leftCodeExtended _ r) 
      (transportRefl (leftCode _))   


  open import Cubical.Homotopy.WedgeConnectivity 

  --wedgeConn : 


  --MainEquiv : {x0 x1 : X}{y0 y1 : Y} → (q00 : Q x0 y0)(q11 : Q x1 y1) → (q10 : Q x1 y0) → Q x0 y1 
  --MainEquiv 

  fiberEquiv : {x : X}{y : Y} → (q : Q x y) 
             → (r : inl x₀ ≡ inr y) → leftCodeExtended x (push q) r ≃ rightCode y r 
  fiberEquiv q = {!!}


  fiberPath : {x : X}{y : Y} → (q : Q x y) → leftCodeExtended x (push q) ≡ rightCode y 
  fiberPath q i r = ua (fiberEquiv q r) i 


  pushCode : {x : X}{y : Y} → (q : Q x y) 
           → PathP (λ i → inl x₀ ≡ push q i → Type ℓ) (leftCode x) (rightCode y) 
  pushCode {x = x} q i = 
    hcomp (λ j → λ { (i = i0) → leftCode x 
                   ; (i = i1) → (transpLeftCode (push q) ∙ fiberPath q) j }) 
          (transport-filler (λ i → inl x₀ ≡ push q i → Type ℓ) (leftCode x) i)



  Code : (p : Pushout) → inl x₀ ≡ p → Type ℓ 
  Code (inl x) = leftCode  x 
  Code (inr x) = rightCode x 
  Code (push q i) = pushCode q i 

  centerCode : {p : Pushout} → (r : inl x₀ ≡ p) → Code p r 
  centerCode = 
    let q' = push q₀₀ 
    in  J (λ p r → Code p r) ∣(q₀₀ , sym (compPath≡compPath' q' (sym q')) ∙ rCancel q')∣ 

  --contractionCode : isContr (Code (inr y₀) (push q₀₀)) 
  --contractionCode = {!!} 

  contractionCode : (y : Y) → (r : inl x₀ ≡ inr y) → (c : Code _ r) → c ≡ centerCode r 
  contractionCode = {!!} 

  contractionCode' : (y : Y) → (r : inl x₀ ≡ inr y) 
                    → (c : fiber push r) → ∣ c ∣ ≡ centerCode r 
  contractionCode' y r (q , refl) = {!!} 

  contractionCodeRefl : (y : Y) → (q : Q x₀ y) → ∣(q , refl)∣ ≡ centerCode (push q)
  contractionCodeRefl y r = {!!} 

  --pushCodeExtended : 

  -}