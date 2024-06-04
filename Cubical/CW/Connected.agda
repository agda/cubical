{-# OPTIONS --safe --lossy-unification #-}

module Cubical.CW.Connected where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout

open import Cubical.Axiom.Choice

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Relation.Nullary

open import Cubical.CW.Base


open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Foundations.Equiv

-- connected comp
open import Cubical.Homotopy.Connected
open import Cubical.CW.Properties
open import Cubical.HITs.Truncation as TR
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Fin.Inductive.Properties as Ind


open import Cubical.Data.Bool
open import Cubical.Data.Nat.Order.Inductive
-- open import Cubical.Data.Dec

open import Cubical.Relation.Nullary.Base
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Fin.Inductive.Properties as Ind

open Sequence

open import Cubical.Foundations.Equiv.HalfAdjoint

private
  variable
    ℓ ℓ' ℓ'' : Level

------ Definitions ------

-- An n-connected CW complex has one 0-cell and no m<n-cells.
yieldsConnectedCWskel : (A : ℕ → Type ℓ) (n : ℕ) → Type _
yieldsConnectedCWskel A k =
  Σ[ sk ∈ yieldsCWskel A ] ((sk .fst 0 ≡ 1) × ((n : ℕ) → n <ᵗ k → sk .fst (suc n) ≡ 0))

-- Alternatively, we may say that its colimit is n-connected
yieldsConnectedCWskel' : (A : ℕ → Type ℓ) (n : ℕ) → Type _
yieldsConnectedCWskel' A n = Σ[ sk ∈ yieldsCWskel A ] isConnected (2 +ℕ n) (realise (_ , sk))

connectedCWskel : (ℓ : Level) (n : ℕ) → Type (ℓ-suc ℓ)
connectedCWskel ℓ n = Σ[ X ∈ (ℕ → Type ℓ) ] (yieldsConnectedCWskel X n)

connectedCWskel' : (ℓ : Level) (n : ℕ) → Type (ℓ-suc ℓ)
connectedCWskel' ℓ n = Σ[ X ∈ (ℕ → Type ℓ) ] (yieldsConnectedCWskel' X n)

isConnectedCW : ∀ {ℓ} (n : ℕ) → Type ℓ → Type (ℓ-suc ℓ)
isConnectedCW {ℓ = ℓ} n A = Σ[ sk ∈ connectedCWskel ℓ n ] realise (_ , (snd sk .fst)) ≃ A

isConnectedCW' : ∀ {ℓ} (n : ℕ) → Type ℓ → Type (ℓ-suc ℓ)
isConnectedCW' {ℓ = ℓ} n A = Σ[ sk ∈ connectedCWskel' ℓ n ] realise (_ , (snd sk .fst)) ≃ A

--- Goal: show that these two definitions coincide (note that indexing is off by 2) ---
-- For the base case, we need to analyse α₀ : Fin n × S⁰ → X₁ (recall,
-- indexing of skeleta is shifted by 1). In partiuclar, we will need
-- to show that if X is connected, then either X₁ is contractible or
-- there is some a ∈ Fin n s.t. α₀(a,-) is injective. This will allow
-- us to iteratively shrink X₁ by contracting the image of α₀(a,-).

-- Decision producedures
hasDecidableImage-Fin×S⁰ : {A : Type ℓ}
  (da : Discrete A) (n : ℕ) (f : Fin n × S₊ 0 → A)
  → hasDecidableImage f
hasDecidableImage-Fin×S⁰ {A = A} da n =
  subst (λ C → (f : C → A) → hasDecidableImage f)
        (isoToPath (invIso Iso-Fin×Bool-Fin))
        (hasDecidableImageFin da _)

private
  allConst? : {A : Type ℓ} {n : ℕ} (dis : Discrete A)
    → (t : Fin n → S₊ 0 → A)
    → ((x : Fin n) → t x ≡ λ _ → t x true)
     ⊎ (Σ[ x ∈ Fin n ] ¬ (t x true ≡ t x false))
  allConst? {n = zero} dis t = inl λ {()}
  allConst? {n = suc n} dis t
    with (dis (t fzero true) (t fzero false))
       | (allConst? {n = n} dis λ x p → t (fsuc x) p)
  ... | yes p | inl x =
    inl (Ind.elimFin-alt (funExt
          (λ { false → sym p ; true → refl})) x)
  ... | yes p | inr x = inr (_ , (snd x))
  ... | no ¬p | q = inr (_ , ¬p)

-- α₀ must be is surjective
isSurj-α₀ : (n m : ℕ) (f : Fin n × S₊ 0 → Fin (suc (suc m)))
  → isConnected 2 (Pushout f fst)
  → (y : _) → Σ[ x ∈ _ ] f x ≡ y
isSurj-α₀ n m f c y with (hasDecidableImage-Fin×S⁰ DiscreteFin n f y)
... | inl x = x
isSurj-α₀ n m f c x₀ | inr q = ⊥.rec nope
  where
  F∘inl : Fin (suc (suc m)) → Type
  F∘inl = elimFinChoose x₀ ⊥ λ _ _ → Unit

  lem : (fa : _) (a : _) → f a ≡ fa → F∘inl fa ≡ Unit
  lem = elimFinChoose x₀
        (λ s t → ⊥.rec (q _ t))
         λ s t b c → elimFinChooseβ x₀ ⊥ (λ _ _ → Unit) .snd s t

  F : Pushout f fst → Type
  F (inl x) = F∘inl x
  F (inr x) = Unit
  F (push a i) = lem (f a) a refl i

  nope : ⊥
  nope = TR.rec isProp⊥
            (λ q → transport (elimFinChooseβ x₀ ⊥ (λ _ _ → Unit) .fst)
                     (subst F (sym q)
                       (transport (sym (elimFinChooseβ x₀ ⊥
                         (λ _ _ → Unit) .snd _
                           (containsTwoFin x₀ .snd ∘ sym))) tt)))
            (Iso.fun (PathIdTruncIso 1)
              (isContr→isProp c
               ∣ inl x₀ ∣
               ∣ inl (containsTwoFin x₀ .fst) ∣))

-- α₀ can't be constant in every component (as this would imply that
-- the 1-skeleton X₂ is a disconnected set of loops).
notAllLoops-α₀ : (n m : ℕ) (f : Fin n × S₊ 0 → Fin (suc (suc m)))
  → isConnected 2 (Pushout f fst)
  → Σ[ x ∈ Fin n ] (¬ f (x , true) ≡ f (x , false))
notAllLoops-α₀ n m f c with (allConst? DiscreteFin (λ x y → f (x , y)))
... | inr x = x
notAllLoops-α₀ n m f c | inl q =
  ⊥.rec (TR.rec isProp⊥ (λ p → subst T p tt)
           (Iso.fun(PathIdTruncIso 1)
             (isContr→isProp c
               ∣ inl flast ∣ ∣ inl fzero ∣)))
  where
  inrT : Fin n → Type
  inrT x with (DiscreteFin (f (x , true)) fzero)
  ... | yes p = ⊥
  ... | no ¬p = Unit

  inlT : Fin (suc (suc m)) → Type
  inlT (zero , p) = ⊥
  inlT (suc x , p) = Unit

  inlrT-pre : (a : _) → inlT (f (a , true)) ≡ inrT a
  inlrT-pre a with ((DiscreteFin (f (a , true)) fzero))
  ... | yes p = cong inlT p
  inlrT-pre s | no ¬p with (f (s , true))
  ... | zero , tt = ⊥.rec (¬p refl)
  ... | suc q , t = refl

  inlrT : (a : _) → inlT (f a) ≡ inrT (fst a)
  inlrT (b , false) = cong inlT (funExt⁻ (q b) false) ∙ inlrT-pre b
  inlrT (b , true) = inlrT-pre b

  T : Pushout f fst → Type
  T (inl x) = inlT x
  T (inr x) = inrT x
  T (push a i) = inlrT a i

{- Technical lemma: given a map f : A × Bool → Unit ⊎ B with B
pointed, this map can be extended to a map F : (Unit ⊎ A) × Bool →
Unit ⊎ B defined by sending

(inl tt , false) ↦ inl tt, and
(inl tt , true) ↦ inr b₀

Consider the pushout
(Unit ⊎ A) × Bool -fst--→ Unit ⊎ A
      |                        ∣
      F                        ∣
      |                        ∣
      ↓                     ⌜  ↓
   Unit ⊎ B ---------------→ P

P is equivalent to the pushout

Consider the pushout
    A × Bool ----fst--------→ A
      |                        |
      f                        |
      ↓                        |
   Unit ⊎ B                   |
      |                        |
 const⋆ ⊎ id                  |
      ↓                     ⌜  ↓
      B --------------------→ Q
-}

module shrinkPushoutLemma (A : Type ℓ) (B : Type ℓ')
  (f : A × Bool → Unit ⊎ B) (b₀ : B) where

  F : (Unit ⊎ A) × Bool → Unit ⊎ B
  F (inl tt , false) = inl tt
  F (inl tt , true) = inr b₀
  F (inr a , x) = f (a , x)

  g : Unit ⊎ B → B
  g (inl x) = b₀
  g (inr x) = x

  Unit⊎A→Pushout-g∘f : (x : Unit ⊎ A) → Pushout (g ∘ f) fst
  Unit⊎A→Pushout-g∘f (inl x) = inl b₀
  Unit⊎A→Pushout-g∘f (inr x) = inr x

  Unit⊎A→Pushout-g∘f-fst : (a : _)
    → inl (g (F a)) ≡ Unit⊎A→Pushout-g∘f (fst a)
  Unit⊎A→Pushout-g∘f-fst (inl x , false) = refl
  Unit⊎A→Pushout-g∘f-fst (inl x , true) = refl
  Unit⊎A→Pushout-g∘f-fst (inr x , false) = push (x , false)
  Unit⊎A→Pushout-g∘f-fst (inr x , true) = push (x , true)

  PushoutF→Pushout-g∘f : Pushout F fst → Pushout (g ∘ f) fst
  PushoutF→Pushout-g∘f (inl x) = inl (g x)
  PushoutF→Pushout-g∘f (inr x) = Unit⊎A→Pushout-g∘f x
  PushoutF→Pushout-g∘f (push a i) = Unit⊎A→Pushout-g∘f-fst a i

  Unit⊎A→Pushout-g∘f-fst₂ : (a : _) (b : _)
    → Path (Pushout F fst)
            (inl (inr (g (f (a , b))))) (inl (f (a , b)))
  Unit⊎A→Pushout-g∘f-fst₂ a b with (f (a , b))
  Unit⊎A→Pushout-g∘f-fst₂ a b | inl x =
    (push (inl tt , true)) ∙ sym (push (inl tt , false))
  ... | inr x = refl

  Pushout-g∘f-fst→Unit⊎A : Pushout (g ∘ f) fst → Pushout F fst
  Pushout-g∘f-fst→Unit⊎A (inl x) = inl (inr x)
  Pushout-g∘f-fst→Unit⊎A (inr x) = inr (inr x)
  Pushout-g∘f-fst→Unit⊎A (push (a , false) i) =
    (Unit⊎A→Pushout-g∘f-fst₂ a false ∙ push (inr a , false)) i
  Pushout-g∘f-fst→Unit⊎A (push (a , true) i) =
    (Unit⊎A→Pushout-g∘f-fst₂ a true ∙ push (inr a , true)) i

  PushoutF→Pushout-g∘f→Unit⊎Aₗ : (x : _)
    → Pushout-g∘f-fst→Unit⊎A (PushoutF→Pushout-g∘f (inl x)) ≡ (inl x)
  PushoutF→Pushout-g∘f→Unit⊎Aₗ (inl x) =
    push (inl tt , true) ∙ sym (push (inl tt , false))
  PushoutF→Pushout-g∘f→Unit⊎Aₗ (inr x) = refl

  PushoutF→Pushout-g∘f→Unit⊎Aᵣ : (x : _)
    → Pushout-g∘f-fst→Unit⊎A (PushoutF→Pushout-g∘f (inr x)) ≡ (inr x)
  PushoutF→Pushout-g∘f→Unit⊎Aᵣ (inl x) = push (inl tt , true)
  PushoutF→Pushout-g∘f→Unit⊎Aᵣ (inr x) = refl

  private
    lem₁ : (x : A) → PushoutF→Pushout-g∘f→Unit⊎Aₗ (f (x , false))
                   ≡ Unit⊎A→Pushout-g∘f-fst₂ x false
    lem₁ x with (f (x , false))
    ... | inl x₁ = refl
    ... | inr x₁ = refl

    lem₂ : (x : A) → PushoutF→Pushout-g∘f→Unit⊎Aₗ (f (x , true))
                   ≡ Unit⊎A→Pushout-g∘f-fst₂ x true
    lem₂ x with (f (x , true))
    ... | inl x₁ = refl
    ... | inr x₁ = refl 

  Pushout-g∘f→PushoutF→Pushout-g∘f : (x : _)
    → Pushout-g∘f-fst→Unit⊎A (PushoutF→Pushout-g∘f x) ≡ x 
  Pushout-g∘f→PushoutF→Pushout-g∘f (inl x) = PushoutF→Pushout-g∘f→Unit⊎Aₗ x
  Pushout-g∘f→PushoutF→Pushout-g∘f (inr x) = PushoutF→Pushout-g∘f→Unit⊎Aᵣ x
  Pushout-g∘f→PushoutF→Pushout-g∘f (push (inl x , false) i) j =
    compPath-filler (push (inl tt , true)) (sym (push (inl tt , false))) (~ i) j
  Pushout-g∘f→PushoutF→Pushout-g∘f (push (inr x , false) i) j =
    (lem₁ x
    ◁ flipSquare
       (symP (compPath-filler'
         (Unit⊎A→Pushout-g∘f-fst₂ x false) (push (inr x , false))))) i j
  Pushout-g∘f→PushoutF→Pushout-g∘f (push (inl x , true) i) j =
    push (inl x , true) (i ∧ j)
  Pushout-g∘f→PushoutF→Pushout-g∘f (push (inr x , true) i) j =
    (lem₂ x
    ◁ flipSquare
       (symP (compPath-filler'
         (Unit⊎A→Pushout-g∘f-fst₂ x true) (push (inr x , true))))) i j

  PushoutF→Pushout-g∘f→Unit⊎A-push : (b : _) (a : _)
    → cong PushoutF→Pushout-g∘f (Unit⊎A→Pushout-g∘f-fst₂ b a) ≡ refl
  PushoutF→Pushout-g∘f→Unit⊎A-push b a with (f (b , a))
  ... | inl x = cong-∙ PushoutF→Pushout-g∘f
                       (push (inl tt , true)) (sym (push (inl tt , false)))
              ∙ sym (rUnit refl)
  ... | inr x = refl

  PushoutF→Pushout-g∘f→PushoutF : (x : _)
    → PushoutF→Pushout-g∘f (Pushout-g∘f-fst→Unit⊎A x) ≡ x
  PushoutF→Pushout-g∘f→PushoutF (inl x) = refl
  PushoutF→Pushout-g∘f→PushoutF (inr x) = refl
  PushoutF→Pushout-g∘f→PushoutF (push (b , false) i) j =
    (cong-∙ PushoutF→Pushout-g∘f
      (Unit⊎A→Pushout-g∘f-fst₂ b false) (push (inr b , false))
    ∙ cong (_∙ push (b , false)) (PushoutF→Pushout-g∘f→Unit⊎A-push b false)
    ∙ sym (lUnit _)) j i
  PushoutF→Pushout-g∘f→PushoutF (push (b , true) i) j =
    (cong-∙ PushoutF→Pushout-g∘f
      (Unit⊎A→Pushout-g∘f-fst₂ b true) (push (inr b , true))
    ∙ cong (_∙ push (b , true)) (PushoutF→Pushout-g∘f→Unit⊎A-push b true)
    ∙ sym (lUnit _)) j i

  Iso-PushoutF-Pushout-g∘f : Iso (Pushout F fst) (Pushout (g ∘ f) fst)
  Iso.fun Iso-PushoutF-Pushout-g∘f = PushoutF→Pushout-g∘f
  Iso.inv Iso-PushoutF-Pushout-g∘f = Pushout-g∘f-fst→Unit⊎A
  Iso.rightInv Iso-PushoutF-Pushout-g∘f = PushoutF→Pushout-g∘f→PushoutF
  Iso.leftInv Iso-PushoutF-Pushout-g∘f = Pushout-g∘f→PushoutF→Pushout-g∘f


module CWLemmas-0Connected where
  -- For any (attaching) map f : Fin (2 + n) × S⁰ → Fin (2 + m) with
  -- f(1 + n, -) non-constant yields has the same pushout as some f' : Fin
  -- k × S⁰ → Fin (1 + n).
  shrinkImageAttachingMapLem : (n m : ℕ)
       (f : Fin (suc (suc n)) × S₊ 0 → Fin (suc (suc m)))
    → f (flast , false) ≡ flast
    → (t : f (flast , true) .fst <ᵗ suc m)
    → Σ[ k ∈ ℕ ] Σ[ f' ∈ (Fin k × S₊ 0 → Fin (suc m)) ]
         Iso (Pushout f fst)
             (Pushout f' fst)
  shrinkImageAttachingMapLem n m f p q = (suc n)
    , _
    , compIso (invIso (pushoutIso _ _ _ _
                (isoToEquiv (Σ-cong-iso-fst (invIso Iso-Fin-Unit⊎Fin)))
                (isoToEquiv (invIso Iso-Fin-Unit⊎Fin))
                (isoToEquiv (invIso Iso-Fin-Unit⊎Fin))
                (funExt (uncurry help))
                (funExt λ x → refl)))
       (Iso-PushoutF-Pushout-g∘f
                 (λ x → Fin→Unit⊎Fin (f ((injectSuc (fst x)) , (snd x))))
                 (f (flast , true) .fst , q))
    where
    open shrinkPushoutLemma (Fin (suc n)) (Fin (suc m))

    help : (y : Unit ⊎ Fin (suc n)) (x : Bool)
      → Unit⊎Fin→Fin
          (F (λ x₁ → Ind.elimFin (inl tt) inr (f (injectSuc (fst x₁) , snd x₁)))
          (f (flast , true) .fst , q) (y , x))
       ≡ f (Unit⊎Fin→Fin y , x)
    help (inl a) false = sym p
    help (inl b) true = Σ≡Prop (λ _ → isProp<ᵗ) refl
    help (inr a) false = Iso.leftInv Iso-Fin-Unit⊎Fin _
    help (inr a) true = Iso.leftInv Iso-Fin-Unit⊎Fin _

  -- If the domain of f is instead Fin 1 × S⁰, this must also be the
  -- codomain of f.
  Fin1×Bool≅ImageAttachingMap : (m : ℕ)
    (f : Fin 1 × S₊ 0 → Fin (suc (suc m)))
    → isConnected 2 (Pushout f fst)
    → Iso (Fin 1 × S₊ 0) (Fin (suc (suc m)))
  Fin1×Bool≅ImageAttachingMap m f c = mainIso
    where
    f' : Bool → Fin (suc (suc m))
    f' = f ∘ (fzero ,_)

    f'-surj : (x : _) → Σ[ t ∈ Bool ] (f' t ≡ x)
    f'-surj x =
      isSurj-α₀ (suc zero) m f c x .fst .snd
      , cong f (ΣPathP (isPropFin1 _ _ , refl))
      ∙ isSurj-α₀ (suc zero) m f c x .snd
    f-true≠f-false : (x : _) → f' true ≡ x →  ¬ f' true ≡ f' false
    f-true≠f-false (zero , q) p r = lem (f'-surj fone)
      where
      lem : Σ[ t ∈ Bool ] (f' t ≡ fone) → ⊥
      lem (false , s) = snotz (cong fst (sym s ∙ sym r ∙ p))
      lem (true , s) = snotz (cong fst (sym s ∙ p))
    f-true≠f-false (suc x , q) p r = lem (f'-surj fzero)
      where
      lem : Σ[ t ∈ Bool ] (f' t ≡ fzero) → ⊥
      lem (false , s) = snotz (cong fst (sym p ∙ r ∙ s))
      lem (true , s) = snotz (cong fst (sym p ∙ s))

    f-inj : (x y : _) → f x ≡ f y → x ≡ y
    f-inj ((zero , tt) , false) ((zero , tt) , false) p = refl
    f-inj ((zero , tt) , false) ((zero , tt) , true) p =
      ⊥.rec (f-true≠f-false _ refl (sym p))
    f-inj ((zero , tt) , true) ((zero , tt) , false) p =
      ⊥.rec (f-true≠f-false _ refl p)
    f-inj ((zero , tt) , true) ((zero , tt) , true) p = refl

    mainIso : Iso (Fin 1 × S₊ 0) (Fin (suc (suc m)))
    Iso.fun mainIso = f
    Iso.inv mainIso x = isSurj-α₀ (suc zero) m f c x .fst
    Iso.rightInv mainIso x = isSurj-α₀ 1 m f c x .snd
    Iso.leftInv mainIso ((zero , tt) , x) =
     (f-inj _ _ (isSurj-α₀ 1 m f c (f (fzero , x)) .snd))

  -- Strengthening of shrinkImageAttachingMapLem for domain of f of
  -- arbitrary cardinality.
  shrinkImageAttachingMap : (n m : ℕ) (f : Fin n × S₊ 0 → Fin (suc (suc m)))
    → isConnected 2 (Pushout f fst)
    → Σ[ k ∈ ℕ ] Σ[ f' ∈ (Fin k × S₊ 0 → Fin (suc m)) ]
         Iso (Pushout f fst)
             (Pushout f' fst)
  shrinkImageAttachingMap zero m f c =
    ⊥.rec (snd (notAllLoops-α₀ zero m f c .fst))
  shrinkImageAttachingMap (suc zero) zero f c =
    0 , ((λ ()) , compIso isoₗ (PushoutEmptyFam (snd ∘ fst) snd))
    where
    isoₗ : Iso (Pushout f fst) (Fin 1)
    isoₗ = PushoutAlongEquiv
           (isoToEquiv (Fin1×Bool≅ImageAttachingMap zero f c)) fst
  shrinkImageAttachingMap (suc zero) (suc m) f c =
    ⊥.rec (Fin≠Fin (snotz ∘ sym ∘ cong (predℕ ∘ predℕ))
          mainIso)
    where
    mainIso : Iso (Fin 2) (Fin (3 +ℕ m))
    mainIso =
      compIso
        (compIso
          (invIso rUnit×Iso)
          (compIso
            (Σ-cong-iso
              (invIso Iso-Bool-Fin2)
              (λ _ → isContr→Iso (tt , (λ _ → refl))
                        (inhProp→isContr fzero isPropFin1)))
              Σ-swap-Iso))
        (Fin1×Bool≅ImageAttachingMap (suc m) f c)
  shrinkImageAttachingMap (suc (suc n)) m f c =
      main .fst , main .snd .fst
    , compIso correctIso (main .snd .snd)
    where
    t = notAllLoops-α₀ (suc (suc n)) m f c

    abstract
      x₀ : Fin (suc (suc n))
      x₀ = fst t

      xpath : ¬ (f (x₀ , true) ≡ f (x₀ , false))
      xpath = snd t

    Fin×S⁰-swapIso : Iso (Fin (suc (suc n)) × S₊ 0) (Fin (suc (suc n)) × S₊ 0)
    Fin×S⁰-swapIso = Σ-cong-iso-fst (swapFinIso flast x₀)

    FinIso2 : Iso (Fin (suc (suc m))) (Fin (suc (suc m)))
    FinIso2 = swapFinIso (f (x₀ , false)) flast

    f' : Fin (suc (suc n)) × S₊ 0 → Fin (suc (suc m))
    f' = Iso.fun FinIso2 ∘ f ∘ Iso.fun Fin×S⁰-swapIso

    f'≡flast : f' (flast , false) ≡ flast
    f'≡flast = cong (Iso.fun FinIso2 ∘ f)
            (cong (_, false) (swapFinβₗ flast x₀))
        ∙ swapFinβₗ (f (x₀ , false)) flast

    ¬f'≡flast : ¬ (f' (flast , true) ≡ flast)
    ¬f'≡flast p = xpath (cong f (ΣPathP (sym (swapFinβₗ flast x₀) , refl))
                  ∙ sym (Iso.rightInv FinIso2 _)
                  ∙ cong (Iso.inv FinIso2) (p ∙ sym f'≡flast)
                  ∙ Iso.rightInv FinIso2 _
                  ∙ cong f (ΣPathP (swapFinβₗ flast x₀ , refl)))

    f'-bound : fst (f' (flast , true)) <ᵗ suc m
    f'-bound = ≠flast→<ᵗflast _ ¬f'≡flast

    main = shrinkImageAttachingMapLem _ _ f' f'≡flast f'-bound

    correctIso : Iso (Pushout f fst) (Pushout f' fst)
    correctIso = pushoutIso _ _ _ _
      (isoToEquiv Fin×S⁰-swapIso)
      (isoToEquiv FinIso2)
      (isoToEquiv (swapFinIso flast x₀))
      (funExt (λ x → cong (FinIso2 .Iso.fun ∘ f)
                      (sym (Iso.rightInv Fin×S⁰-swapIso x))))
      refl

  -- the main lemma: a pushout of f : Fin n × S⁰ → Fin m is equivalent
  -- to one of the constant funktion Fin k × S⁰ → Fin 1 for some k.

  Contract1Skel : (n m : ℕ) (f : Fin n × S₊ 0 → Fin m)
    → isConnected 2 (Pushout f fst)
    → Σ[ k ∈ ℕ ]
         Iso (Pushout f fst)
             (Pushout {A = Fin k × S₊ 0} {B = Fin 1} (λ _ → fzero) fst)
  Contract1Skel zero zero f c = ⊥.rec (TR.rec (λ()) help (fst c))
    where
    help : ¬ Pushout f fst
    help = elimProp _ (λ _ → λ ()) snd snd
  Contract1Skel (suc n) zero f c = ⊥.rec (f (fzero , true) .snd)
  Contract1Skel n (suc zero) f c = n
    , pushoutIso _ _ _ _ (idEquiv _) (idEquiv _) (idEquiv _)
      (funExt (λ x → isPropFin1 _ _)) refl
  Contract1Skel zero (suc (suc m)) f c =
    ⊥.rec (TR.rec (λ()) (snotz ∘ sym ∘ cong fst)
            (Iso.fun (PathIdTruncIso _)
              (isContr→isProp (subst (isConnected 2) (isoToPath help) c)
                ∣ fzero ∣ ∣ fone ∣)))
    where
    help : Iso (Pushout f fst) (Fin (suc (suc m)))
    help = invIso (PushoutEmptyFam (λ()) λ())
  Contract1Skel (suc n) (suc (suc m)) f c
    with (Contract1Skel _ (suc m) (shrinkImageAttachingMap (suc n) m f c .snd .fst)
         (subst (isConnected 2)
           (isoToPath (shrinkImageAttachingMap (suc n) m f c .snd .snd)) c))
  ... | (k , e) = k , compIso (shrinkImageAttachingMap (suc n) m f c .snd .snd) e

-- Uning this, we can show that a 0-connected CW complex can be
-- approximated by one with trivial 1-skeleton.
module _ (A : ℕ → Type ℓ) (sk+c : yieldsConnectedCWskel' A 0) where
  private
    open CWLemmas-0Connected
    c = snd sk+c
    sk = fst sk+c
    c' = isConnectedColim→isConnectedSkel (_ , sk) 2 c

    module AC = CWskel-fields (_ , sk)

    e₁ : Iso (Pushout (fst (CW₁-discrete (_ , sk)) ∘ AC.α 1) fst) (A 2)
    e₁ = compIso (PushoutCompEquivIso (idEquiv _) (CW₁-discrete (A , sk)) (AC.α 1) fst)
                 (equivToIso (invEquiv (AC.e 1)))

    liftStr = Contract1Skel _ _ (fst (CW₁-discrete (_ , sk)) ∘ AC.α 1)
                (isConnectedRetractFromIso 2 e₁ c')

  collapse₁card : ℕ → ℕ
  collapse₁card zero = 1
  collapse₁card (suc zero) = fst liftStr
  collapse₁card (suc (suc x)) = AC.card (suc (suc x))

  collapse₁CWskel : ℕ → Type _
  collapse₁CWskel zero = Lift ⊥
  collapse₁CWskel (suc zero) = Lift (Fin 1)
  collapse₁CWskel (suc (suc n)) = A (suc (suc n))

  collapse₁α : (n : ℕ)
    → Fin (collapse₁card n) × S⁻ n → collapse₁CWskel n
  collapse₁α (suc zero) (x , p) = lift fzero
  collapse₁α (suc (suc n)) = AC.α (2 +ℕ n)

  connectedCWskel→ : yieldsConnectedCWskel collapse₁CWskel 0
  fst (fst connectedCWskel→) = collapse₁card
  fst (snd (fst connectedCWskel→)) = collapse₁α
  fst (snd (snd (fst connectedCWskel→))) = λ()
  snd (snd (snd (fst connectedCWskel→))) zero =
    isContr→Equiv (isOfHLevelLift 0 (inhProp→isContr fzero isPropFin1))
                       ((inr fzero)
                 , (λ { (inr x) j → inr (isPropFin1 fzero x j) }))
  snd (snd (snd (fst connectedCWskel→))) (suc zero) =
    compEquiv (invEquiv (isoToEquiv e₁))
      (compEquiv (isoToEquiv (snd liftStr))
      (isoToEquiv (pushoutIso _ _ _ _
        (idEquiv _) LiftEquiv (idEquiv _)
        (funExt cohₗ) (funExt cohᵣ))))
    where
    -- Agda complains if these proofs are inlined...
    cohₗ : (x : _) → collapse₁α 1 x ≡ collapse₁α 1 x
    cohₗ (x , p) = refl

    cohᵣ : (x : Fin (fst liftStr) × Bool) → fst x ≡ fst x
    cohᵣ x = refl
  snd (snd (snd (fst connectedCWskel→))) (suc (suc n)) = AC.e (suc (suc n))
  snd connectedCWskel→ = refl , (λ _ → λ ())

  collapse₁Equiv : (n : ℕ)
    → realise (_ , sk) ≃ realise (_ , connectedCWskel→ .fst)
  collapse₁Equiv n =
    compEquiv
      (isoToEquiv (Iso-SeqColim→SeqColimShift _ 3))
      (compEquiv (pathToEquiv (cong SeqColim
        (cong₂ sequence (λ _ m → A (3 +ℕ m))
                        λ _ {z} → CW↪ (A , sk) (suc (suc (suc z))))))
        (invEquiv (isoToEquiv (Iso-SeqColim→SeqColimShift _ 3))))

isConnectedCW→Contr : ∀ {ℓ} (n : ℕ)
  (sk : connectedCWskel ℓ n) (m : Fin (suc n))
  → isContr (fst sk (suc (fst m)))
isConnectedCW→Contr zero sk (zero , p) =
  isOfHLevelRetractFromIso 0 (equivToIso (CW₁-discrete (_ , snd sk .fst)))
    (subst isContr (cong Fin (sym (snd sk .snd .fst)))
      (flast , isPropFin1 _))
isConnectedCW→Contr (suc n) sk (zero , p) =
  subst isContr (ua (symPushout _ _)
               ∙ ua (invEquiv (sk .snd .fst .snd .snd .snd 0)))
        (isOfHLevelRetractFromIso 0
          (invIso (PushoutEmptyFam (λ()) (snd sk .fst .snd .snd .fst)))
            (subst (isContr ∘ Fin) (sym (snd sk .snd .fst))
              (flast , isPropFin1 _)))
isConnectedCW→Contr (suc n) sk (suc x , p)
  with (isConnectedCW→Contr n
        (fst sk , (snd sk .fst) , ((snd sk .snd .fst)
                , (λ p w → snd sk .snd .snd p (<ᵗ-trans w <ᵗsucm))))
                             (x , p))
... | ind = subst isContr
               (ua (invEquiv (sk .snd .fst .snd .snd .snd (suc x))))
               (isOfHLevelRetractFromIso 0
                 (invIso
                   (PushoutEmptyFam
                  (λ p' → ¬Fin0 (subst Fin
                     (snd sk .snd .snd x p) (fst p')))
                   λ p' → ¬Fin0 (subst Fin
                     (snd sk .snd .snd x p) p')))
                 ind)

makeConnectedCW : ∀ {ℓ} (n : ℕ) {C : Type ℓ}
  → isCW C
  → isConnected (suc (suc n)) C
  → ∥ isConnectedCW n C ∥₁
makeConnectedCW zero {C = C} (cwsk , e) cA =
  ∣ (_ , (M .fst , refl , λ p → λ()))
  , compEquiv (invEquiv (collapse₁Equiv _ _ 0)) (invEquiv e) ∣₁
  where
  M = connectedCWskel→ (cwsk .fst) (snd cwsk , subst (isConnected 2) (ua e) cA)
makeConnectedCW {ℓ = ℓ} (suc n) {C = C} (cwsk , eqv) cA with
  (makeConnectedCW n (cwsk , eqv) (isConnectedSubtr (suc (suc n)) 1 cA))
... | s = PT.rec squash₁
  (λ s → PT.rec squash₁
    (λ α-pt* → PT.rec squash₁
      (λ α-pt2*
        → PT.rec squash₁
          (λ vanish*
            → PT.map (uncurry (buildCW s α-pt* α-pt2* vanish*))
          (mainF s α-pt* α-pt2* vanish*))
          (sphereBouquetVanish s α-pt* α-pt2*
            (const* s α-pt* α-pt2*)))
              (α-pt∙₂ s α-pt*)) (α'2+n∙ s)) s
  where
  module _ (ind : isConnectedCW n C) where
    open CWskel-fields (_ , ind .fst .snd .fst)
    -- By the induction hypothesis we get a CW structure on C with C (suc n) trivial

    -- some basic abbreviations and lemmas
    module _ where
      C* = ind .fst .fst

      C1+n = C* (suc n)
      C2+n = C* (suc (suc n))
      C3+n = C* (suc (suc (suc n))) 
      C4+n = C* (suc (suc (suc (suc n))))

      α2+n = α (suc (suc n))

      isConnectedC4+n : isConnected (3 +ℕ n) C4+n
      isConnectedC4+n = isConnectedCW→isConnectedSkel
                 (_ , ind .fst .snd .fst) (suc (suc (suc (suc n))))
                   (suc (suc (suc n)) , <ᵗ-trans <ᵗsucm <ᵗsucm)
                   (subst (isConnected (3 +ℕ n)) (ua (invEquiv (ind .snd)))
                   cA)

      isConnected3+n : isConnected (2 +ℕ n) C3+n
      isConnected3+n = isConnectedCW→isConnectedSkel
                 (_ , ind .fst .snd .fst) (suc (suc (suc n)))
                   (suc (suc n) , <ᵗ-trans <ᵗsucm <ᵗsucm)
                   (subst (isConnected (2 +ℕ n)) (ua (invEquiv (ind .snd)))
                   (isConnectedSubtr (suc (suc n)) 1 cA))

    -- C₁₊ₙ is trivial
    Iso-C1+n-Fin1 : Iso C1+n (Fin 1)
    Iso-C1+n-Fin1 =
      isContr→Iso (isConnectedCW→Contr n (ind .fst) (n , <ᵗsucm))
                   (flast , isPropFin1 _)

    -- C₂₊ₙ is a bouquet of spheres 
    Iso-C2+n-SphereBouquet : Iso C2+n (SphereBouquet (suc n) (A (suc n)))
    Iso-C2+n-SphereBouquet = compIso (equivToIso
             (ind .fst .snd .fst .snd .snd .snd (suc n)))
             (compIso
               (compIso
                 (compIso
                   (pushoutIso _ _ _ _ (idEquiv _)
                     (isoToEquiv (compIso Iso-C1+n-Fin1
                       (isContr→Iso (flast , isPropFin1 _)
                         (tt , λ _ → refl))))
                     (idEquiv _)
                     refl
                     refl)
                   (⋁-cofib-Iso _ (const∙ _ _)))
                 PushoutSuspIsoSusp )
               sphereBouquetSuspIso)

    -- We rewrite α along this iso.
    α'2+n : A (suc (suc n)) × S₊ (suc n) → SphereBouquet (suc n) (A (suc n))
    α'2+n = Iso.fun Iso-C2+n-SphereBouquet ∘ α (suc (suc n))

    opaque
      Iso-C3+n-Pushoutα'2+n : Iso (C* (suc (suc (suc n))))
                 (Pushout α'2+n fst)
      Iso-C3+n-Pushoutα'2+n = compIso (equivToIso (e (suc (suc n))))
                        (pushoutIso _ _ _ _ (idEquiv _)
                          (isoToEquiv Iso-C2+n-SphereBouquet)
                          (idEquiv _)
                          refl
                          refl)

    -- α is merely pointed
    α'2+n∙ : ∥ ((x : _) → α'2+n (x , ptSn (suc n)) ≡ inl tt) ∥₁
    α'2+n∙ = invEq propTrunc≃Trunc1 (invEq (_ , InductiveFinSatAC _ _ _)
             λ a → isConnectedPath 1
               (isConnectedSubtr' n 2
                 (isConnectedSphereBouquet' {n = n})) _ _ .fst)

    -- Let us assume it is pointed (we are proving a proposition in the end)...
    module _ (α-pt∙ : (x : _) → α'2+n (x , ptSn (suc n)) ≡ inl tt) where

      -- Doing so allows us to lift it to a map of sphere bouquets
      α∙ : SphereBouquet∙ (suc n) (A (suc (suc n)))
        →∙ SphereBouquet∙ (suc n) (A (suc n))
      fst α∙ (inl x) = inl tt
      fst α∙ (inr x) = α'2+n x
      fst α∙ (push a i) = α-pt∙ a (~ i)
      snd α∙ = refl

      -- The cofibre of α∙ is C₃₊ₙ
      opaque
        Iso-C3+n-cofibα : Iso C3+n
                   (cofib (fst α∙))
        Iso-C3+n-cofibα = compIso Iso-C3+n-Pushoutα'2+n (⋁-cofib-Iso _ α∙)

      -- This iso is also merely pointed:
      α-pt∙₂ : ∥ ((x : A (3 +ℕ n))
               → Iso.fun Iso-C3+n-cofibα (α (3 +ℕ n) (x , north)) ≡ inl tt) ∥₁
      α-pt∙₂ = invEq propTrunc≃Trunc1 (invEq (_ , InductiveFinSatAC _ _ _)
             λ a → isConnectedPath 1
                     (isConnectedRetractFromIso 2 (invIso Iso-C3+n-cofibα)
                     (isConnectedSubtr' n 2 isConnected3+n) ) _ _ .fst)

      -- But again, let us assume it is...
      module _ (α-pt∙₂ : (x : A (3 +ℕ n))
             → Iso.fun Iso-C3+n-cofibα (α (3 +ℕ n) (x , north)) ≡ inl tt) where

        -- Doing so, we can lift α yet again this time to a map
        -- α↑ : ⋁S²⁺ⁿ → cofib α
        α↑ : SphereBouquet∙ (suc (suc n)) (A (suc (suc (suc n))))
         →∙ (cofib (fst α∙) , inl tt)
        fst α↑ (inl x) = inl tt
        fst α↑ (inr x) = Iso.fun Iso-C3+n-cofibα (α (3 +ℕ n) x)
        fst α↑ (push a i) = α-pt∙₂ a (~ i)
        snd α↑ = refl

        -- The cofibre of this map is C₄₊ₙ
        Iso-C4+n-cofibα↑ : Iso (C* (4 +ℕ n)) (cofib (fst α↑))
        Iso-C4+n-cofibα↑ = compIso (equivToIso (e (3 +ℕ n)))
                (compIso
                  (pushoutIso _ _ _ _
                    (idEquiv _)
                    (isoToEquiv Iso-C3+n-cofibα)
                    (idEquiv _) refl refl)
                  (⋁-cofib-Iso _ α↑))


        opaque
          Iso-cofibαinr-SphereBouquet :
            Iso (Pushout {B = cofib (fst α∙)} inr (λ _ → tt))
                (SphereBouquet (suc (suc n)) (A (suc (suc n))))
          Iso-cofibαinr-SphereBouquet = compIso (equivToIso (symPushout _ _))
                    (compIso (Iso-cofibInr-Susp α∙)
                      sphereBouquetSuspIso)

          Iso-cofibαinr-SphereBouquet∙ :
            Iso.fun Iso-cofibαinr-SphereBouquet (inl (inl tt)) ≡ inl tt
          Iso-cofibαinr-SphereBouquet∙ = refl

        open commSquare
        open 3-span

        PT : commSquare
        A0 (sp PT) = cofib (fst α∙)
        A2 (sp PT) = SphereBouquet (suc (suc n)) (A (suc (suc (suc n))))
        A4 (sp PT) = Unit
        f1 (sp PT) = fst α↑
        f3 (sp PT) = λ _ → tt
        P PT = cofib (fst α↑)
        inlP PT = inr
        inrP PT = inl
        comm PT = funExt λ x → sym (push x)

        PTPush : PushoutSquare
        fst PTPush = PT
        snd PTPush =
          subst isEquiv (funExt
            (λ { (inl x) → refl
               ; (inr x) → refl
               ; (push a i) → refl}))
            (symPushout _ _ .snd)


        PL : commSquare
        A0 (sp PL) = cofib (fst α∙)
        A2 (sp PL) = SphereBouquet (suc n) (A (suc n))
        A4 (sp PL) = Unit
        f1 (sp PL) = inr
        f3 (sp PL) = _
        P PL = SphereBouquet (suc (suc n)) (A (suc (suc n)))
        inlP PL x = Iso.fun Iso-cofibαinr-SphereBouquet (inl x)
        inrP PL _ = Iso.fun Iso-cofibαinr-SphereBouquet (inr tt)
        comm PL =
          funExt λ x → cong (Iso.fun Iso-cofibαinr-SphereBouquet) (push x)

        PLPush : PushoutSquare
        fst PLPush = PL
        snd PLPush =
          subst isEquiv (funExt coh)
            (isoToIsEquiv Iso-cofibαinr-SphereBouquet)
          where
          coh : (x : _) → Iso.fun Iso-cofibαinr-SphereBouquet x
                         ≡ Pushout→commSquare PL x
          coh (inl x) = refl
          coh (inr x) = refl
          coh (push x i₁) = refl

        C∨PlaceHolder =
          Pushout (Iso.inv Iso-C4+n-cofibα↑ ∘ inr)
                  (λ x → Iso.fun Iso-cofibαinr-SphereBouquet (inl x))

        C∨ = (C4+n , Iso.inv Iso-C4+n-cofibα↑ (inl tt))
           ⋁ SphereBouquet∙ (suc (suc n)) (A (suc (suc n)))

        module L→R = PushoutPasteDown PLPush {B = C∨PlaceHolder}
                       (Iso.inv Iso-C4+n-cofibα↑ ∘ inr) inl inr (funExt push)

        isPushoutTot =
          L→R.isPushoutBottomSquare→isPushoutTotSquare
            (subst isEquiv (funExt (λ { (inl x) → refl
                                      ; (inr x) → refl
                                      ; (push a i) → refl}))
            (idIsEquiv _))

        const* : SphereBouquet (suc n) (A (suc n)) → C4+n
        const* = λ x → Iso.inv Iso-C4+n-cofibα↑ (inr (inr x))

        C⋆ = Iso-C4+n-cofibα↑ .Iso.inv (inl tt)

        sphereVanish : (f : S₊ (suc n) → C4+n)
                     → ∥ ((x : S₊ (suc n)) → f x ≡ C⋆) ∥₁
        sphereVanish f = sphereToTrunc (suc n)
          λ x → isConnectedPath (suc (suc n)) isConnectedC4+n _ _ .fst

        sphereBouquetVanish : ∀ {k : ℕ} (f : SphereBouquet (suc n) (Fin k) → C4+n)
          → ∥ f ≡ (λ _ → C⋆) ∥₁
        sphereBouquetVanish {k = k} f =
          TR.rec (isProp→isOfHLevelSuc (suc n) squash₁)
            (λ p → PT.rec squash₁
            (λ q → ∣ funExt
              (λ { (inl x) → p
                 ; (inr (x , y)) → (q x y ∙ sym (q x (ptSn (suc n))))
                                  ∙ cong f (sym (push x)) ∙ p
                 ; (push a i) j → (cong (_∙ cong f (sym (push a)) ∙ p)
                                         (rCancel (q a (ptSn (suc n))))
                                  ∙ sym (lUnit _)
                                  ◁ (symP (compPath-filler'
                                      (cong f (sym (push a))) p))) (~ i) j}) ∣₁)
            help)
            isPted
          where
          isPted = Iso.fun (PathIdTruncIso (suc (suc n)))
                           (isContr→isProp isConnectedC4+n  ∣ f (inl tt) ∣ₕ ∣ C⋆ ∣ₕ)

          help : ∥ ((x : Fin k) → (y :  _) → f (inr (x , y)) ≡ C⋆) ∥₁
          help = invEq propTrunc≃Trunc1
            (invEq (_ , InductiveFinSatAC _ _ _)
              λ x → PT.rec (isOfHLevelTrunc 1)
                ∣_∣ₕ
                (sphereVanish λ y → f (inr (x , y))))

        pushoutTotAlt : C∨PlaceHolder ≃ cofib const*
        pushoutTotAlt =
          compEquiv
           (invEquiv (_ , isPushoutTot))
           (symPushout _ _)

        β : SphereBouquet (suc (suc n)) (A (suc (suc (suc n))))
          → SphereBouquet (suc (suc n)) (A (suc (suc n)))
        β = (Iso.fun Iso-cofibαinr-SphereBouquet ∘ inl) ∘ fst α↑

        β∙ : SphereBouquet∙ (suc (suc n)) (A (suc (suc (suc n))))
          →∙ SphereBouquet∙ (suc (suc n)) (A (suc (suc n)))
        fst β∙ = β
        snd β∙ = Iso-cofibαinr-SphereBouquet∙

        module _ (vanish : const* ≡ λ _ → C⋆) where
          S∨C = SphereBouquet∙ (suc (suc n)) (A (suc n)) ⋁ (C4+n , C⋆)

          connS∨C : isConnected (suc (suc (suc n))) S∨C
          fst connS∨C = ∣ inl (inl tt) ∣ₕ
          snd connS∨C =
            TR.elim (λ _ → isOfHLevelPath (suc (suc (suc n)))
                            (isOfHLevelTrunc (suc (suc (suc n)))) _ _)
              λ { (inl x) → inlEq x
                ; (inr x) → SP ∙ inrEq x
                ; (push tt i) j →
                  (compPath-filler (inlEq (inl tt)) (cong ∣_∣ₕ (push tt))
                ▷ (rUnit SP ∙ cong (SP ∙_) (sym inrEq∙))) i j}
            where
            inlEq : (x : _)
              → Path (hLevelTrunc (suc (suc (suc n))) S∨C)
                ∣ inl (inl tt) ∣ ∣ inl x ∣
            inlEq x = TR.rec (isOfHLevelTrunc (3 +ℕ n) _ _)
              (λ p i → ∣ inl (p i) ∣ₕ)
              (Iso.fun (PathIdTruncIso _)
                (isContr→isProp
                  (isConnectedSphereBouquet' {n = suc n})
                    ∣ inl tt ∣ ∣ x ∣))

            G :  (x : C4+n) → ∥ C⋆ ≡ x ∥ suc (suc n)
            G x = Iso.fun (PathIdTruncIso _)
                    (isContr→isProp isConnectedC4+n ∣ C⋆ ∣ₕ ∣ x ∣ₕ)

            G∙ : G C⋆ ≡ ∣ refl ∣ₕ
            G∙ = cong (Iso.fun (PathIdTruncIso _))
                  (isProp→isSet (isContr→isProp isConnectedC4+n) _ _
                    (isContr→isProp isConnectedC4+n ∣ C⋆ ∣ₕ ∣ C⋆ ∣ₕ) refl)
               ∙ cong ∣_∣ₕ (transportRefl refl)

            inrEq : (x : C4+n)
              → Path (hLevelTrunc (suc (suc (suc n))) S∨C)
                      ∣ inr C⋆ ∣ₕ ∣ inr x ∣ₕ
            inrEq x = TR.rec (isOfHLevelTrunc (suc (suc (suc n))) _ _)
                             (λ p i → ∣ inr (p i) ∣ₕ) (G x)

            inrEq∙ : inrEq C⋆ ≡ refl
            inrEq∙ = cong (TR.rec (isOfHLevelTrunc (suc (suc (suc n))) _ _)
                             (λ p i → ∣ inr (p i) ∣ₕ)) G∙

            SP = inlEq (inl tt) ∙ cong ∣_∣ₕ (push tt)

          Iso-C∨PlaceHolder-Wedge :
            C∨PlaceHolder ≃ (SphereBouquet∙ (suc (suc n)) (A (suc n)) ⋁ (C4+n , C⋆))
          Iso-C∨PlaceHolder-Wedge =
            compEquiv pushoutTotAlt
              (isoToEquiv (compIso (cofibConst-⋁-Iso' {A = _ , inl tt} {B = _ , C⋆}
                                     (const* , funExt⁻ vanish _)
                                     (funExt⁻ vanish))
                          (pushoutIso _ _ _ _
                            (idEquiv _)
                            (isoToEquiv sphereBouquetSuspIso)
                            (idEquiv _)
                            refl
                            refl)))

          module T→B = PushoutPasteDown PTPush {B = C∨PlaceHolder}
            (λ x → Iso.fun Iso-cofibαinr-SphereBouquet (inl x)) inr
            (λ x → inl (Iso.inv Iso-C4+n-cofibα↑ x))
            (sym (funExt push))

          helpIso : Iso (spanPushout (sp T→B.bottomSquare)) (P T→B.bottomSquare)
          helpIso = compIso (equivToIso (symPushout _ _))
                            (pushoutIso _ _ _ _ (idEquiv _)
                              (invEquiv (isoToEquiv Iso-C4+n-cofibα↑))
                              (idEquiv _) refl refl)

          helpIsoCoh : (x : _) → Iso.fun helpIso x
                                ≡ Pushout→commSquare T→B.bottomSquare x
          helpIsoCoh (inl x) = refl
          helpIsoCoh (inr x) = refl
          helpIsoCoh (push a i) j = sym (rUnit (sym (push a))) j i

          ⋁-as-cofib : cofib β ≃ S∨C
          ⋁-as-cofib =
            compEquiv (compEquiv (symPushout _ _)
              (_ , T→B.isPushoutBottomSquare→isPushoutTotSquare
                (subst isEquiv (funExt helpIsoCoh) (isoToIsEquiv helpIso))))
              Iso-C∨PlaceHolder-Wedge

          open import Cubical.Data.Unit
          testβ : isConnectedFun (suc (suc (suc n))) {B = cofib β} inr
          testβ = inrConnected (3 +ℕ n) _ _
                    λ b → isOfHLevelRetractFromIso 0 (mapCompIso fiberUnitIso)
                            isConnectedSphereBouquet'

          testβ3 : isConnectedFun (suc (suc (suc n))) {B = S∨C} (⋁-as-cofib .fst ∘ inr)
          testβ3 = isConnectedComp (⋁-as-cofib .fst) inr (3 +ℕ n)
                     (isEquiv→isConnected _ (⋁-as-cofib .snd) (3 +ℕ n)) testβ

          main-inr : ∥ ((x : A (suc n)) (y : S₊ (suc (suc n)))
            → Σ[ t ∈ SphereBouquet (suc (suc n)) (A (suc (suc n))) ]
                  (⋁-as-cofib .fst (inr t) ≡ inl (inr (x , y)))) ∥₁
          main-inr =
            invEq propTrunc≃Trunc1
              (invEq (_ , InductiveFinSatAC _ _ _)
                λ x → fst propTrunc≃Trunc1
                  (sphereToTrunc (suc (suc n))
                    λ y → testβ3 (inl (inr (x , y))) .fst))

          mainF : ∃[ F ∈ (SphereBouquet∙ (suc (suc n)) (A (suc n))
                       →∙ SphereBouquet∙ (suc (suc n)) (A (suc (suc n)))) ]
                   ((x : _) → Path S∨C (⋁-as-cofib .fst (inr (fst F x))) (inl x))
          mainF = TR.rec (isProp→isOfHLevelSuc (suc n) squash₁)
            (λ coh₁ → PT.rec squash₁ (λ F → TR.rec squash₁
            (λ h → TR.rec squash₁ (λ q → ∣ (F* F coh₁ h , refl) ,
                                            (coh F coh₁ h q) ∣₁)
            (makeCoh F coh₁ h))
            (F∙ F coh₁))
            main-inr)
              (isConnectedPath _ connS∨C
                (⋁-as-cofib .fst (inr (inl tt))) (inl (inl tt)) .fst)
            where
            CON = (subst (λ x → isConnected x (SphereBouquet (suc (suc n))
                         (A (suc (suc n)))))
                         (cong suc (+-comm 2 n))
                         isConnectedSphereBouquet')
            module _ (F : ((x : A (suc n)) (y : S₊ (suc (suc n)))
               → Σ[ t ∈ SphereBouquet (suc (suc n)) (A (suc (suc n))) ]
                     (⋁-as-cofib .fst (inr t) ≡ inl (inr (x , y)))))
                     (coh₁ : Path S∨C (⋁-as-cofib .fst (inr (inl tt)))
                                        (inl (inl tt))) where
              F∙ : hLevelTrunc 1 ((x : Fin _) → F x north .fst ≡ inl tt)
              F∙ =
                invEq (_ , InductiveFinSatAC _ _ _)
                  λ a → isConnectedPath 1 (isConnectedSubtr 2 (suc n) CON) _ _ .fst

              module _ (h  : (x : Fin _) → F x north .fst ≡ inl tt) where
                F* : (SphereBouquet (suc (suc n)) (A (suc n))
                    → SphereBouquet (suc (suc n)) (A (suc (suc n))))
                F* (inl x) = inl tt
                F* (inr (x , y)) = F x y .fst
                F* (push a i) = h  a (~ i)

                cohTy : Type _
                cohTy = (a : A (suc n))
                  → Square (λ i → ⋁-as-cofib .fst (inr (h a (~ i))))
                            (λ i → inl (push a i))
                            coh₁ (F a north .snd)

                makeCoh : hLevelTrunc 1 cohTy
                makeCoh = invEq (_ , InductiveFinSatAC _ _ _)
                  λ a → isConnectedPathP 1
                    (isConnectedSubtr' n 2 (isConnectedPath _ connS∨C _ _)) _ _ .fst

                module _ (coh₂ : cohTy) where
                  coh : (x : _) → Path S∨C (⋁-as-cofib .fst (inr (F* x))) (inl x)
                  coh (inl x) = coh₁
                  coh (inr (x , y)) = F x y .snd
                  coh (push a i) j = coh₂ a j i
          module _ (F : (SphereBouquet∙ (suc (suc n)) (A (suc n))
                       →∙ SphereBouquet∙ (suc (suc n)) (A (suc (suc n)))))
                   (h : (x : _) → Path S∨C (⋁-as-cofib .fst (inr (fst F x))) (inl x))
            where
            h' : (x : _) → inr (fst F x) ≡ invEq ⋁-as-cofib (inl x)
            h' x = sym (retEq ⋁-as-cofib (inr (fst F x)))
                 ∙ cong (invEq ⋁-as-cofib) (h x)

            open import Cubical.Foundations.Transport

            N = card (suc n) +ℕ card (suc (suc (suc n)))

            iso7 : Iso (SphereBouquet (suc (suc n)) (Fin N))
                       (SphereBouquet∙ (suc (suc n)) (A (suc n))
                      ⋁ SphereBouquet∙ (suc (suc n)) (A (suc (suc (suc n)))))
            iso7 = compIso
              (pathToIso
                ((λ i → ⋁gen (isoToPath
                  (Iso-Fin⊎Fin-Fin+ {n = card (suc n)} {m = card (suc (suc (suc n)))}) (~ i))
                    (λ _ → S₊∙ (suc (suc n))))
                  ∙ cong (⋁gen (A (suc n) ⊎ A (suc (suc (suc n)))))
                         (funExt (⊎.elim (λ _ → refl) (λ _ → refl)))))
                (invIso ⋁gen⊎Iso)

            T : Iso (cofib (F ∨→ β∙)) C4+n
            T = compIso (cofib∨→compIsoᵣ  F β∙)
                 (compIso
                   (pathToIso (cong cofib (funExt h')))
                   (compIso
                     (equivToIso (symPushout _ _))
                     (compIso
                       (PushoutCompEquivIso
                         (idEquiv (SphereBouquet (suc (suc n)) (A (suc n))))
                         (invEquiv ⋁-as-cofib) inl (λ _ → tt))
                       (compIso (equivToIso (symPushout _ _)) cofibInl-⋁))))
                       

            T∙ : Σ[ c ∈ ℕ ] Σ[ α ∈ (SphereBouquet (suc (suc n)) (Fin c)
                                  → SphereBouquet (suc (suc n)) (A (suc (suc n)))) ]
                 Iso (Pushout (α ∘ inr) fst) C4+n
            fst T∙ = N
            fst (snd T∙) = F ∨→ β∙ ∘ Iso.fun iso7
            snd (snd T∙) =
              compIso
                (compIso (⋁-cofib-Iso (_ , fst F (inl tt)) ((F ∨→ β∙ ∘ Iso.fun iso7) , refl))
                         (invIso (PushoutCompEquivIso
                           (invEquiv (isoToEquiv iso7))
                             (idEquiv Unit) _ _))) T

            tyFamParam : (m : ℕ) → Trichotomyᵗ m (suc (suc (suc n))) → Type ℓ
            tyFamParam zero (lt x) = ⊥*
            tyFamParam (suc m) (lt x) = Unit*
            tyFamParam m (eq x) = Lift (SphereBouquet (suc (suc n)) (A (suc (suc n))))
            tyFamParam m (gt x) = C* m

            cardParam : (m : ℕ) → Trichotomyᵗ m (suc (suc n)) → Trichotomyᵗ m (suc (suc (suc n))) → ℕ
            cardParam zero (lt x) q = 1
            cardParam (suc m) (lt x) q = 0
            cardParam m (eq x) q = card (suc (suc n))
            cardParam m (gt x) (lt x₁) = 0
            cardParam m (gt x) (eq x₁) = N
            cardParam m (gt x) (gt x₁) = card m


            tyFamParam∙ : (m : ℕ) (q : _) → tyFamParam (suc m) q
            tyFamParam∙ m (lt x) = tt*
            tyFamParam∙ m (eq x) = lift (inl tt)
            tyFamParam∙ m (gt x) = subst C* (+-comm m 1)
              (CW↪Iterate (_ , ind .fst .snd .fst) 1 m
                (invEq (CW₁-discrete (_ , ind .fst .snd .fst))
                  (subst Fin (sym (ind .fst .snd .snd .fst)) flast)))

            carParamConn : (n₁ : ℕ) → n₁ <ᵗ suc n → (p : _) (q : _) → cardParam (suc n₁) p q ≡ 0
            carParamConn m ineq (lt x) q = refl
            carParamConn m ineq (eq x) q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) x ineq))
            carParamConn m ineq (gt x) q = ⊥.rec (¬m<ᵗm (<ᵗ-trans ineq x))

            newα : (m : ℕ) (p : _) (q : _) → Fin (cardParam m p q) × S⁻ m → tyFamParam m q
            newα (suc m) (lt x) q ()
            newα (suc m) (eq x) (lt x₁) _ = tt*
            newα (suc m) (eq x) (eq x₁) _ = tyFamParam∙ m (eq x₁)
            newα (suc m) (eq x) (gt x₁) _ = tyFamParam∙ m (gt x₁)
            newα (suc m) (gt x) (lt x₁) _ = tyFamParam∙ m (lt x₁)
            newα (suc m) (gt x) (eq x₁) (a , p) = lift (snd T∙ .fst (inr (a , subst S₊ (cong predℕ x₁) p)))
            newα (suc m) (gt x) (gt x₁) = α (suc m)

            tyFamParamContr : (m : _) (t : m <ᵗ suc n) (q : _) → isContr (tyFamParam (suc m) q)
            tyFamParamContr m t (lt x) = tt* , λ {tt* → refl}
            tyFamParamContr m t (eq x) =
              ⊥.rec (¬m<ᵗm (<ᵗ-trans (subst (_<ᵗ suc n) (cong predℕ x) t) <ᵗsucm))
            tyFamParamContr m t (gt x) =
              ⊥.rec (¬m<ᵗm (<ᵗ-trans (<ᵗ-trans x t) <ᵗsucm))

            newEq : (n₁ : ℕ) (p : _) (q : _)
              → tyFamParam (suc n₁) (Trichotomyᵗ-suc p)
                ≃ Pushout (newα n₁ p q) fst
            newEq zero (lt s) (lt t) =
              isoToEquiv (isContr→Iso (tt* , (λ {tt* → refl}))
                         ((inr flast) , λ {(inr (zero , tt)) → refl}))
            newEq zero (lt x) (eq p) = ⊥.rec (snotz (sym p))
            newEq zero (eq x) q = ⊥.rec (snotz (sym x))
            newEq (suc m) (lt x) q =
              isoToEquiv (isContr→Iso (tt* , (λ {tt* → refl}))
                         ((inl (tyFamParamContr m x q .fst))
                        , (λ { (inl t) → λ i
                          → inl (tyFamParamContr m x q .snd t i)})))
            newEq (suc m) (eq x) (lt x₁) =
              invEquiv (isoToEquiv
                (compIso (⋁-cofib-Iso {B = λ _ → _ , ptSn m} (_ , tt*) (_ , refl))
                  (compIso (cofibConst-⋁-Iso {A = SphereBouquet∙ m _})
                    (compIso ⋁-rUnitIso
                      (compIso sphereBouquetSuspIso
                        (compIso
                          (pathToIso (λ i → SphereBouquet (x i) (A (suc (suc n)))))
                          LiftIso))))))
            newEq (suc m) (eq x) (eq x₁) =
              ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n)
                      (cong (predℕ ∘ predℕ) (sym x ∙ x₁)) <ᵗsucm))
            newEq (suc m) (eq x) (gt y) =
              ⊥.rec (¬m<ᵗm (<ᵗ-trans (subst (suc (suc n) <ᵗ_)
                                   (cong predℕ x) y) <ᵗsucm))
            newEq (suc m) (gt x) (lt x₁) = ⊥.rec (¬squeeze (x , x₁))
            newEq (suc m) (gt x) (eq x₁) =
              isoToEquiv (compIso (compIso
                (pathToIso (λ i → C* (suc (x₁ i))))
                (invIso (T∙ .snd .snd)))
                (invIso (pushoutIso _ _ _ _
                  (Σ-cong-equiv-snd
                    (λ _ → pathToEquiv (cong S₊ (cong predℕ x₁))))
                    (invEquiv LiftEquiv) (idEquiv _) refl refl)))
            newEq (suc m) (gt x) (gt x₁) = e (suc m)

            buildCW* : connectedCWskel ℓ (suc n)
            fst buildCW* m = tyFamParam m (m ≟ᵗ (3 +ℕ n))
            fst (fst (snd buildCW*)) m = cardParam m (m ≟ᵗ (2 +ℕ n)) (m ≟ᵗ (3 +ℕ n))
            fst (snd (fst (snd buildCW*))) m = newα m _ _ 
            fst (snd (snd (fst (snd buildCW*)))) ()
            snd (snd (snd (fst (snd buildCW*)))) m = newEq m _ _
            fst (snd (snd buildCW*)) = refl
            snd (snd (snd buildCW*)) m ineq = carParamConn m ineq _ _

            3+n = suc (suc (suc n))
            4+n = suc 3+n

            buildCW-realise : (n₁ : ℕ) (q : _)
              → Iso (tyFamParam (n₁ +ℕ 4+n) q)
                     (C* (n₁ +ℕ 4+n))
            buildCW-realise m (lt x) = ⊥.rec (¬m<m (<-trans (<ᵗ→< x) (m , refl)))
            buildCW-realise m (eq x) = ⊥.rec (¬m<m (m , x))
            buildCW-realise zero (gt x) = idIso
            buildCW-realise (suc m) (gt x) = idIso

            buildCW-realise→help : (n₁ : ℕ) (q : _) (r : _)
                (a : tyFamParam (n₁ +ℕ 4+n) q)
                → CW↪ (fst (fst ind) , snd (fst ind) .fst) (n₁ +ℕ 4+n)
                      (Iso.fun (buildCW-realise n₁ q) a)
                ≡ Iso.fun (buildCW-realise (suc n₁) _)
                    (invEq (newEq (n₁ +ℕ 4+n) r q) (inl a))
            buildCW-realise→help m (lt x) r a = ⊥.rec (¬m<m (<-trans (<ᵗ→< x) (m , refl)))
            buildCW-realise→help m (eq x) r a = ⊥.rec (¬m<m (m , x))
            buildCW-realise→help m (gt x) (lt x₁) a =
              ⊥.rec (¬m<ᵗm (<ᵗ-trans (<ᵗ-trans x x₁) <ᵗsucm))
            buildCW-realise→help m (gt x) (eq x₁) a =
              ⊥.rec (¬m<ᵗm (<ᵗ-trans ((subst (_<ᵗ (m +ℕ 4+n)) (cong suc (sym x₁)) x)) <ᵗsucm))
            buildCW-realise→help zero (gt x) (gt x₁) a = refl
            buildCW-realise→help (suc m) (gt x) (gt x₁) a = refl

            buildCW-realise→ : (n₁ : ℕ)
                (a : tyFamParam (n₁ +ℕ 4+n) _)
                → CW↪ (fst (fst ind) , snd (fst ind) .fst) (n₁ +ℕ 4+n)
                      (Iso.fun (buildCW-realise n₁ _) a)
                ≡ Iso.fun (buildCW-realise (suc n₁) _)
                    (CW↪ ((λ m → tyFamParam m (m ≟ᵗ 3+n)) , snd buildCW* .fst)
                     (n₁ +ℕ 4+n) a)
            buildCW-realise→ n a = buildCW-realise→help n _ _ a

            buildCW : isConnectedCW (suc n) C
            fst buildCW = buildCW*
            snd buildCW =
              compEquiv (isoToEquiv
                (compIso (SeqColimIso _ (4 +ℕ n))
                  (compIso (sequenceIso→ColimIso
                    ((λ m → buildCW-realise m ((m +ℕ 4+n) ≟ᵗ 3+n))
                    , buildCW-realise→))
                    (invIso (SeqColimIso _ (4 +ℕ n)))))) (ind .snd)


-- isConnCW : (n : ℕ) → Type ℓ → Type (ℓ-suc ℓ)
-- isConnCW n A = isCW A × isConnected n A

-- connectedCWskel'→connectedCWskel : ∀ {ℓ}
--   → Σ[ t ∈ connectedCWskel' ℓ 0 ]
--        (Σ[ dim ∈ ℕ ]
--          ((k : ℕ) → isEquiv (CW↪ (_ , snd t .fst) (k +ℕ dim))))
--    → Σ[ t ∈ connectedCWskel ℓ 0 ]
--         Σ[ dim ∈ ℕ ]
--          ((k : ℕ) → isEquiv (CW↪ (_ , snd t .fst) (k +ℕ dim)))
-- fst (connectedCWskel'→connectedCWskel ((A , sk) , conv)) =
--   _ , connectedCWskel→ A ((sk .fst) , (sk .snd)) .fst , refl , (λ _ → λ())
-- fst (snd (connectedCWskel'→connectedCWskel ((A , sk) , conv))) = suc (fst conv)
-- snd (snd (connectedCWskel'→connectedCWskel ((A , sk) , zero , T))) k =
--   ⊥.rec (TR.rec (λ())
--     (λ a → TR.rec (λ())
--       (λ t → CW₀-empty (_ , fst sk) (invEq (_ , T 0) (t .fst)))
--       (isConnected-CW↪∞ 1 (_ , fst sk) a .fst)) (sk .snd .fst))
-- snd (snd (connectedCWskel'→connectedCWskel ((A , sk) , (suc dim) , T))) k =
--   transport (λ i → isEquiv (CW↪ (collapse₁CWskel A sk , connectedCWskel→ A sk .fst)
--             (h i)))
--             (transport (λ i → isEquiv (CW↪ (A , sk .fst) (suc (+-suc k dim i))))
--             (T (suc k)))
--   where
--   h = cong suc (sym (+-suc k dim)) ∙ sym (+-suc k (suc dim))


-- 
-- yieldsGoodCWskel : {ℓ : Level} (A₊₂ : ℕ → Pointed ℓ) → Type _
-- yieldsGoodCWskel {ℓ = ℓ} A  =
--   Σ[ f₊₁ ∈ (ℕ → ℕ) ]
--    Σ[ fin ∈ (A 0) .fst ≃ Fin 1 ] 
--     Σ[ α ∈ ((n : ℕ) → SphereBouquet∙ n (Fin (f₊₁ n)) →∙ A n) ]
--            ((n : ℕ) → cofib (α n .fst) , inl tt ≃∙ A (suc n))

-- GoodCWskelSeq : {ℓ : Level} {A : ℕ → Pointed ℓ} → yieldsGoodCWskel A → Sequence ℓ
-- obj (GoodCWskelSeq {A = A} (f , fin , α , sq)) zero = Lift ⊥
-- obj (GoodCWskelSeq {A = A} (f , fin , α , sq)) (suc n) = fst (A n)
-- Sequence.map (GoodCWskelSeq {A = A} (f , fin , α , sq)) {n = suc n} x = fst (fst (sq n)) (inr x)

-- realiseGood∙ : {ℓ : Level} {A : ℕ → Pointed ℓ} → yieldsGoodCWskel A → Pointed ℓ
-- realiseGood∙ {A = A} S = SeqColim (GoodCWskelSeq S) , incl {n = 1} (snd (A 0))

-- yieldsFinGoodCWskel : {ℓ : Level} (dim : ℕ) (A₊₂ : ℕ → Pointed ℓ) → Type _
-- yieldsFinGoodCWskel {ℓ = ℓ} dim A  =
--   Σ[ A ∈ yieldsGoodCWskel A ] converges (GoodCWskelSeq A) dim

-- GoodCWskel : (ℓ : Level) → Type (ℓ-suc ℓ)
-- GoodCWskel ℓ = Σ[ A ∈ (ℕ → Pointed ℓ) ] yieldsGoodCWskel A

-- FinGoodCWskel : (ℓ : Level) (dim : ℕ) → Type (ℓ-suc ℓ)
-- FinGoodCWskel ℓ dim = Σ[ A ∈ (ℕ → Pointed ℓ) ] yieldsFinGoodCWskel dim A

-- isGoodCWExpl : {ℓ : Level} (A : Pointed ℓ) → Type (ℓ-suc ℓ)
-- isGoodCWExpl {ℓ} A = Σ[ sk ∈ GoodCWskel ℓ ] realiseGood∙ (snd sk) ≃∙ A

-- isFinGoodCWExpl : {ℓ : Level} (A : Pointed ℓ) → Type (ℓ-suc ℓ)
-- isFinGoodCWExpl {ℓ} A =
--   Σ[ dim ∈ ℕ ] Σ[ sk ∈ FinGoodCWskel ℓ dim ] realiseGood∙ (fst (snd sk)) ≃∙ A

-- isGoodCW : {ℓ : Level} (A : Pointed ℓ) → Type (ℓ-suc ℓ)
-- isGoodCW {ℓ} A = ∃[ sk ∈ GoodCWskel ℓ ] realiseGood∙ (snd sk) ≃∙ A

-- isFinGoodCW : {ℓ : Level} (A : Pointed ℓ) → Type (ℓ-suc ℓ)
-- isFinGoodCW {ℓ} A =
--   ∃[ dim ∈ ℕ ] Σ[ sk ∈ FinGoodCWskel ℓ dim ] (realiseGood∙ (fst (snd sk)) ≃∙ A)

-- finGoodCW : (ℓ : Level) → Type (ℓ-suc ℓ)
-- finGoodCW ℓ = Σ[ A ∈ Pointed ℓ ] isFinGoodCW A 

-- ptCW : {ℓ : Level} {A : ℕ → Type ℓ} → yieldsCWskel A → A 1
--   → (n : ℕ) → A (suc n)
-- ptCW sk a zero = a
-- ptCW sk a (suc n) = CW↪ (_ , sk) (suc n) (ptCW sk a n)

-- -- module TWOO {ℓ : Level} (A' : ℕ → Type ℓ) (pt0 : A' 1)
-- --   (dim : ℕ) (con : isConnected 2 (A' 2))
-- --   (C : yieldsFinCWskel dim A')
-- --   where

-- --   open CWskel-fields (_ , fst C)
-- --   e₀ : A' 1 ≃ Fin (card 0)
-- --   e₀ = CW₁-discrete (_ , fst C)

-- --   ptA : (n : ℕ) → A' (suc n)
-- --   ptA = ptCW (fst C) pt0

-- --   conA : (n : ℕ) → isConnected 2 (A' (suc n))
-- --   conA zero = isConnectedRetractFromIso 2 (equivToIso e₀)
-- --                 (subst (isConnected 2) (sym (cong Fin cA))
-- --                   (∣ flast ∣
-- --                   , TR.elim (λ _ → isOfHLevelPath 2
-- --                             (isOfHLevelTrunc 2) _ _)
-- --                       λ {(zero , tt) → refl}))
-- --   conA (suc n) =
-- --     isConnectedRetractFromIso 2
-- --       (equivToIso (e (suc n)))
-- --       (∣ inl (ptA n) ∣ₕ
-- --       , TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
-- --           (elimProp _ (λ _ → isOfHLevelTrunc 2 _ _)
-- --             (conA' (conA n))
-- --             λ c → conA' (conA n) _
-- --                  ∙ cong ∣_∣ₕ (push (c , ptSn n))))
-- --     where
-- --     conA' : (conA : isConnected 2 (A' (suc n))) (c : A' (suc n))
-- --       → Path (hLevelTrunc 2 (Pushout (α (suc n)) fst))
-- --               ∣ inl (ptA n) ∣ₕ ∣ inl c ∣ₕ
-- --     conA' conA c =
-- --       TR.rec (isOfHLevelTrunc 2 _ _)
-- --         (λ p i → ∣ inl (p i) ∣)
-- --         (Iso.fun (PathIdTruncIso _)
-- --           (isContr→isProp conA ∣ ptA n ∣ₕ ∣ c ∣ₕ))


-- --   private
-- --     funType = ((n : Fin (suc dim))
-- --                 → Σ[ h ∈ (SphereBouquet∙ (fst n) (Fin (card (suc (fst n))))
-- --                 →∙ (A' (suc (fst n)) , ptA (fst n))) ]
-- --                    ((x : _) → fst h (inr x) ≡ α (suc (fst n)) x))

-- --   mapMakerNil : ∥ funType ∥₁
-- --   mapMakerNil =
-- --     invEq propTrunc≃Trunc1 (invEq (_ , InductiveFinSatAC _ _ _)
-- --       λ n → TR.map
-- --         (λ pted → ((λ { (inl x) → ptA (fst n)
-- --                        ; (inr x) → α _ x
-- --                        ; (push a i) → pted a i})
-- --                   , refl)
-- --           , λ _ → refl) (help n))
-- --     where
-- --     help : (n : Fin (suc dim))
-- --       → hLevelTrunc 1 ((x : Fin (card (suc (fst n))))
-- --                      → (ptA (fst n) ≡ α (suc (fst n)) (x , ptSn (fst n))))
-- --     help n = invEq (_ , InductiveFinSatAC _ _ _)
-- --       λ m → Iso.fun (PathIdTruncIso _)
-- --               (isContr→isProp
-- --                 (conA (fst n)) ∣ (ptA (fst n)) ∣ₕ
-- --                                ∣ α (suc (fst n)) (m , ptSn (fst n)) ∣ₕ)
-- --   module _ (F : funType) where
-- --     funs : (n : ℕ) → SphereBouquet∙ n (Fin (card (suc n)))
-- --                    →∙ (A' (suc n) , ptA n)
-- --     funs n with (n ≟ᵗ dim)
-- --     ... | lt x = F (n , <ᵗ-trans-suc x) .fst
-- --     ... | eq x = F (n , subst (_<ᵗ suc dim) (sym x) <ᵗsucm) .fst
-- --     ... | gt x = const∙ _ _

-- --     funEqP1 : (n : ℕ) → (cofib (funs n .fst) , inl tt)
-- --                       ≃∙ Pushout (funs n .fst ∘ inr) (λ r → fst r) , inl (ptA n)
-- --     funEqP1 n = invEquiv (isoToEquiv (⋁-cofib-Iso _ (funs n))) , refl

-- --     funEq : (n : ℕ) → Pushout (funs n .fst ∘ inr) fst , inl (ptA n)
-- --                      ≃∙ Pushout (fst (C .snd) (suc n)) fst , inl (ptA n)
-- --     funEq n = isoToEquiv (pushoutIso _ _ _ _
-- --                   (idEquiv _)
-- --                   (idEquiv _)
-- --                   (idEquiv _)
-- --                   (funExt (uncurry (main n)))
-- --                   (λ i x → fst x))
-- --                 , λ _ → inl (ptA n)
-- --       where
-- --       main : (n : ℕ) (x : Fin (card (suc n))) (y : S₊ n)
-- --         → funs n .fst (inr (x , y)) ≡ fst (C .snd) (suc n) (x , y)
-- --       main n with (n ≟ᵗ dim)
-- --       ... | lt p = λ x y
-- --         → F (n , <ᵗ-trans-suc p) .snd (x , y)
-- --       ... | eq p = λ x y
-- --         → F (n , subst (_<ᵗ suc dim) (λ i → p (~ i)) <ᵗsucm) .snd (x , y)
-- --       ... | gt p = λ x
-- --         → ⊥.rec (¬Fin0 (subst Fin (ind (suc n) (<ᵗ-trans p <ᵗsucm)) x))

-- --   getGoodCWskelAux : ∥ yieldsGoodCWskel (λ n → A' (suc n) , ptA n) ∥₁
-- --   getGoodCWskelAux = PT.map help mapMakerNil
-- --     where
-- --     help : funType → yieldsGoodCWskel (λ n → A' (suc n) , ptA n)
-- --     fst (help F) = card ∘ suc
-- --     fst (snd (help F)) = compEquiv e₀ (pathToEquiv (cong Fin cA))
-- --     fst (snd (snd (help F))) n = funs F n
-- --     snd (snd (snd (help F))) n =
-- --       compEquiv∙ (compEquiv∙ (funEqP1 F n) (funEq F n))
-- --                  (invEquiv (e (suc n)) , refl)


-- module BS {ℓ : Level} (A' : ℕ → Type ℓ)
--   (dim : ℕ)
--   (C+eq : yieldsFinCWskel dim A')
--   (cA : fst (fst C+eq) 0 ≡ 1)
--   where
--   C = fst C+eq
--   ind = snd C+eq

--   open CWskel-fields (_ , C)
--   e₀ : A' 1 ≃ Fin (card 0)
--   e₀ = CW₁-discrete (_ , C)


--   ¬dim≡0 : ¬ (dim ≡ 0)
--   ¬dim≡0 p = CW₀-empty (_ , C) (subst A' p
--           (invEq (_ , ind 0) (subst A' (cong suc (sym p))
--             (invEq e₀ (subst Fin (sym cA) fzero)))))

--   pt0 : A' 1
--   pt0 = invEq e₀ (subst Fin (sym cA) flast)

--   ptA : (n : ℕ) → A' (suc n)
--   ptA = ptCW C pt0

--   conA : (n : ℕ) → isConnected 2 (A' (suc n))
--   conA zero = isConnectedRetractFromIso 2 (equivToIso e₀)
--                 (subst (isConnected 2) (sym (cong Fin cA))
--                   (∣ flast ∣
--                   , TR.elim (λ _ → isOfHLevelPath 2
--                             (isOfHLevelTrunc 2) _ _)
--                       λ {(zero , tt) → refl}))
--   conA (suc n) =
--     isConnectedRetractFromIso 2
--       (equivToIso (e (suc n)))
--       (∣ inl (ptA n) ∣ₕ
--       , TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
--           (elimProp _ (λ _ → isOfHLevelTrunc 2 _ _)
--             (conA' (conA n))
--             λ c → conA' (conA n) _
--                  ∙ cong ∣_∣ₕ (push (c , ptSn n))))
--     where
--     conA' : (conA : isConnected 2 (A' (suc n))) (c : A' (suc n))
--       → Path (hLevelTrunc 2 (Pushout (α (suc n)) fst))
--               ∣ inl (ptA n) ∣ₕ ∣ inl c ∣ₕ
--     conA' conA c =
--       TR.rec (isOfHLevelTrunc 2 _ _)
--         (λ p i → ∣ inl (p i) ∣)
--         (Iso.fun (PathIdTruncIso _)
--           (isContr→isProp conA ∣ ptA n ∣ₕ ∣ c ∣ₕ))

--   private
--     funType = ((n : Fin dim)
--                 → Σ[ h ∈ (SphereBouquet∙ (fst n) (Fin (card (suc (fst n))))
--                 →∙ (A' (suc (fst n)) , ptA (fst n))) ]
--                    ((x : _) → fst h (inr x) ≡ α (suc (fst n)) x))

--   mapMakerNil : ∥ funType ∥₁
--   mapMakerNil =
--     invEq propTrunc≃Trunc1 (invEq (_ , InductiveFinSatAC _ _ _)
--       λ n → TR.map
--         (λ pted → ((λ { (inl x) → ptA (fst n)
--                        ; (inr x) → α _ x
--                        ; (push a i) → pted a i})
--                   , refl)
--           , λ _ → refl) (help n))
--     where
--     help : (n : Fin dim)
--       → hLevelTrunc 1 ((x : Fin (card (suc (fst n))))
--                      → (ptA (fst n) ≡ α (suc (fst n)) (x , ptSn (fst n))))
--     help n = invEq (_ , InductiveFinSatAC _ _ _)
--       λ m → Iso.fun (PathIdTruncIso _)
--               (isContr→isProp
--                 (conA (fst n)) ∣ (ptA (fst n)) ∣ₕ  ∣ α (suc (fst n)) (m , ptSn (fst n)) ∣ₕ)

--   module _ (F : funType) where
--     card' : ℕ → ℕ
--     card' n with (n ≟ᵗ dim)
--     ... | lt x = card (suc n)
--     ... | eq x = 0
--     ... | gt x = 0

--     funs : (n : ℕ) → SphereBouquet∙ n (Fin (card' n))
--                    →∙ (A' (suc n) , ptA n)
--     funs n with (n ≟ᵗ dim)
--     ... | lt x = F (n , x) .fst
--     ... | eq x = const∙ _ _
--     ... | gt x = const∙ _ _

--     funEqP1 : (n : ℕ) → (cofib (funs n .fst) , inl tt)
--                       ≃∙ Pushout (funs n .fst ∘ inr) (λ r → fst r) , inl (ptA n)
--     funEqP1 n = invEquiv (isoToEquiv (⋁-cofib-Iso _ (funs n))) , refl

--     funEq : (n : ℕ) → Pushout (funs n .fst ∘ inr) fst , inl (ptA n)
--                      ≃∙ Pushout (fst (C .snd) (suc n)) fst , inl (ptA n)
--     funEq n with (n ≟ᵗ dim)
--     ... | lt x = isoToEquiv (pushoutIso _ _ _ _
--                   (idEquiv _)
--                   (idEquiv _)
--                   (idEquiv _)
--                   (funExt (uncurry λ x y → F (n , _) .snd (x , y)))
--                   (λ i x → fst x))
--                 , λ _ → inl (ptA n)
--     ... | eq x = (compEquiv (isoToEquiv (invIso (PushoutEmptyFam (λ()) λ())))
--                    (compEquiv ((CW↪ (_ , C) (suc n))
--                               , transport (λ i → isEquiv (CW↪ (A' , C)
--                                     (suc (x (~ i)))))
--                                       (ind 1)
--                                       )
--                               (e (suc n)))) , secEq (e (suc n)) _
--     ... | gt x = (compEquiv (isoToEquiv (invIso (PushoutEmptyFam (λ()) λ())))
--                    (compEquiv ((CW↪ (_ , C) (suc n))
--                                 , (transport (λ i → isEquiv (CW↪ (A' , C)
--                                     (suc ((sym (+-suc (fst (<ᵗ→< x)) dim)
--                                         ∙ (<ᵗ→< x .snd)) i))))
--                                       (ind (suc (suc (fst (<ᵗ→< x)))))))
--                               (e (suc n)))) , secEq (e (suc n)) _

--     goodCWmk : yieldsGoodCWskel (λ n → A' (suc n) , ptA n)
--     fst goodCWmk = card'
--     fst (snd goodCWmk) = compEquiv e₀ (pathToEquiv (cong Fin cA))
--     fst (snd (snd goodCWmk)) = funs
--     snd (snd (snd goodCWmk)) n =
--       compEquiv∙ (compEquiv∙ (funEqP1 n) (funEq n))
--                   (invEquiv (e (suc n)) , refl)

--     goodCWmk-converges : converges
--       (sequence (obj (GoodCWskelSeq goodCWmk))
--                 (Sequence.map (GoodCWskelSeq goodCWmk)))
--       dim
--     goodCWmk-converges zero = help dim refl
--       where
--       help : (x : _) (p : dim ≡ x) → isEquiv (Sequence.map (GoodCWskelSeq goodCWmk) {x})
--       help zero p = ⊥.rec (¬dim≡0 p)
--       help (suc x) p with (x ≟ᵗ dim)
--       ... | lt x₁ = transport (λ i → isEquiv λ z → CW↪ (A' , C) (p i) z) (ind zero)
--       ... | eq x₁ = ⊥.rec (¬m<m (0 , sym (x₁ ∙ p)))
--       ... | gt x₁ = ⊥.rec (¬m<ᵗm (subst (dim <ᵗ_) (sym p) (<ᵗ-trans x₁ <ᵗsucm)))
--     goodCWmk-converges (suc k) with ((k +ℕ dim) ≟ᵗ dim)
--     ... | lt x = ⊥.rec (¬squeeze (x , (<→<ᵗ (k , +-suc k dim))))
--     ... | eq x = compEquiv (_ , ind _)
--                   (compEquiv (e (suc (k +ℕ dim)))
--                    (invEquiv (_ , snd (fst C+eq .snd .snd .snd (suc (k +ℕ dim)))))) .snd
--     ... | gt x = compEquiv (_ , ind _)
--                   (compEquiv (e (suc (k +ℕ dim)))
--                    (invEquiv (_ , snd (fst C+eq .snd .snd .snd (suc (k +ℕ dim)))))) .snd
 
--     funType→ : realiseGood∙ goodCWmk .fst ≃ A' (suc dim)
--     funType→ = compEquiv (isoToEquiv (invIso
--         (converges→ColimIso dim goodCWmk-converges)))
--           (help dim refl)
--       where
--       help : (x : _) (p : dim ≡ x) → obj (GoodCWskelSeq goodCWmk) x ≃ A' (suc x)
--       help zero p = ⊥.rec (¬dim≡0 p)
--       help (suc x) p = subst (λ x → A' x ≃ A' (suc x)) p (_ , ind 0)

--     merelyPointed : ∥ realiseGood∙ goodCWmk ≃∙ A' (suc dim) , ptA dim ∥₁
--     merelyPointed = PT.map (λ idp → funType→ , idp) (help dim refl)
--       where
--       help : (x : ℕ) (p : dim ≡ x)
--         → ∥ funType→ .fst (realiseGood∙ goodCWmk .snd) ≡ ptA dim ∥₁
--       help zero p = ⊥.rec (¬dim≡0 p)
--       help (suc x) p = invEq propTrunc≃Trunc1 (PathIdTruncIso 1 .Iso.fun
--                         (isContr→isProp
--                           (subst (isConnected 2 ∘ A') (sym (cong suc p))
--                             (conA (suc x)))
--                             ∣ (funType→ .fst (realiseGood∙ goodCWmk .snd)) ∣ₕ
--                             ∣ ptA dim ∣ₕ))

--   getGoodCWskel : ∃[ skel ∈ yieldsGoodCWskel (λ n → A' (suc n) , ptA n) ]
--                      converges (GoodCWskelSeq skel) dim
--   getGoodCWskel = PT.map (λ F → (goodCWmk F)
--                        , (goodCWmk-converges F)) mapMakerNil


-- isFinConnCW : (n : ℕ) → Type ℓ → Type (ℓ-suc ℓ)
-- isFinConnCW n A = isFinCW A × isConnected n A

-- finConnCW∙ :  (n : ℕ)  (ℓ : Level)→ Type (ℓ-suc ℓ)
-- finConnCW∙ n ℓ = Σ[ A ∈ Pointed ℓ ] ∥ isFinConnCW n (fst A) ∥₁

-- open import Cubical.CW.Subcomplex
-- finCW→GoodCW : ∀ {ℓ}
--   → finConnCW∙ 2 ℓ
--   → finGoodCW ℓ
-- fst (finCW→GoodCW A) = fst A
-- snd (finCW→GoodCW ((A , a₀) , cwA+cA)) =
--   PT.rec squash₁ (λ{(cw , cA)
--     → PT.rec squash₁
--         (λ {(sk , T)
--           → TR.rec squash₁
--               (λ p → ∣ (suc (fst cw))
--              , ((_ , sk , T) , (mainEq (cw , cA) sk T , p)) ∣₁)
--               (mainEqId (cw , cA) sk T)})
--       (main (cw , cA))})
--     cwA+cA
--   where
--   module _ (cw+cA : isFinConnCW 2 A) where
--     cA = snd cw+cA
--     cw = fst cw+cA

--     makeNice' = makeNiceFinCWskel {A = A} cw

--     inst = connectedCWskel'→connectedCWskel
--              (((snd makeNice' .fst .fst)
--             , (snd makeNice' .fst .snd .fst
--             , isConnectedRetractFromIso 2
--                  (equivToIso (invEquiv (snd makeNice' .snd))) cA))
--             , _ , snd makeNice' .fst .snd .snd)

--     open BS (inst .fst .fst)
--             (suc (fst cw))
--             ((snd (inst .fst) .fst) , inst .snd .snd)
--             refl

--     main = BS.getGoodCWskel
--               (inst .fst .fst)
--               (suc (fst cw))
--               ((snd (inst .fst) .fst) , inst .snd .snd)
--               refl

--     open import Cubical.Foundations.Transport
--     eqv : (x : _) (p : fst cw ≡ x)
--       → Iso (inst .fst .fst (suc x))
--              (fst (finCWskel→CWskel (fst cw) (fst (cw .snd))) x)
--     eqv zero p = ⊥.rec (TR.rec (λ()) (λ s →
--       (CW₀-empty (_ , snd cw .fst .snd .fst)
--         (invEq (_ , transport (λ i → isEquiv
--                           (CW↪ (fst (snd cw .fst)
--                                , fst (snd cw .fst .snd)) (p i)))
--                  (snd cw .fst .snd .snd 0))
--           (s .fst))))
--             (isConnected-CW↪∞ 1
--               (_ , snd cw .fst .snd .fst)
--                 (fst (snd cw .snd) a₀) .fst))
--     eqv (suc x) p with (suc (suc x) ≟ᵗ fst cw)
--     ... | lt x₁ = ⊥.rec (¬m<ᵗm (<ᵗ-trans (subst (suc (suc x) <ᵗ_) p x₁) <ᵗsucm))
--     ... | eq x₁ = ⊥.rec (¬m<ᵗm (subst (suc x <ᵗ_) (x₁ ∙ p) <ᵗsucm))
--     ... | gt x₁ = pathToIso (cong (fst (snd cw) .fst) p)

--     mainEq : (sk : _) (T : converges (GoodCWskelSeq sk) (suc (fst cw))) → _
--     mainEq sk T = compEquiv
--          (isoToEquiv
--            (compIso (invIso (converges→ColimIso _ T))
--            (compIso (eqv _ refl)
--              (converges→ColimIso _ (cw .snd .fst .snd .snd)))))
--          (invEquiv (cw .snd .snd))


--     mainEqId : (sk : _) (T : _)
--       → hLevelTrunc 1  (mainEq sk T .fst (pt (realiseGood∙ sk)) ≡ a₀)
--     mainEqId sk T = Iso.fun (PathIdTruncIso 1) (isContr→isProp cA _ _)

-- module GoodCW→finCWExpl {ℓ : Level} (A : Pointed ℓ)
--   (dim : ℕ) (sk : FinGoodCWskel ℓ dim)
--   (eq : realiseGood∙ (fst (snd sk)) ≃∙ A)
--   where

--   Fam : ℕ → Type ℓ
--   Fam zero = Lift ⊥
--   Fam (suc n) = fst sk n .fst

--   card : ℕ → ℕ
--   card zero = 1
--   card (suc n) = snd sk .fst .fst n

--   α : (n : ℕ) → Fin (card n) × S⁻ n → Fam n
--   α (suc n) (a , b) = snd sk .fst .snd .snd .fst n .fst (inr (a , b))

--   e : (n : ℕ) → Iso (fst sk n .fst)
--                       (Pushout (α n) fst)
--   e zero = compIso (equivToIso (snd sk .fst .snd .fst))
--                    (compIso (PushoutEmptyFam (λ()) (λ()))
--                    (equivToIso (symPushout _ _)))
--   e (suc n) = compIso (equivToIso (invEquiv (snd sk .fst .snd .snd .snd n .fst)))
--                       (invIso (⋁-cofib-Iso (fst sk n)
--                                             (fst (snd sk .fst .snd .snd) n)))

--   yieldsFinCWskelFam : yieldsFinCWskel dim Fam
--   fst (fst yieldsFinCWskelFam) = card
--   fst (snd (fst yieldsFinCWskelFam)) = α
--   fst (snd (snd (fst yieldsFinCWskelFam))) ()
--   snd (snd (snd (fst yieldsFinCWskelFam))) n = isoToEquiv (e n)
--   snd yieldsFinCWskelFam zero = help dim refl
--     where
--     help : (x : ℕ) (p : x ≡ dim)
--       → isEquiv (CW↪ (Fam , card , (α , (λ()) , (λ n → isoToEquiv (e n)))) x)
--     help zero p with
--       (invEq (_ , transport (λ i → isEquiv (Sequence.map (GoodCWskelSeq (fst (snd sk)))
--                             {n = p (~ i)}))
--              (sk .snd .snd 0)) (fst sk 0 .snd))
--     ... | ()
 
--     help (suc x) p =
--       transport (λ i → isEquiv (Sequence.map (GoodCWskelSeq (fst (snd sk))) {n = p (~ i)}))
--                 (sk .snd .snd 0)
--   snd yieldsFinCWskelFam (suc k) = snd sk .snd (suc k)

--   Skel : finCWskel ℓ dim
--   fst Skel = Fam
--   snd Skel = yieldsFinCWskelFam

--   SkelEq : fst A ≃ realise (finCWskel→CWskel dim Skel)
--   SkelEq = compEquiv (invEquiv (eq .fst))
--                      (isoToEquiv
--                        (compIso (Iso-SeqColim→SeqColimShift _ 2)
--                          (compIso (sequenceIso→ColimIso
--                            ((λ n → idIso {A = (fst (fst sk (suc n)))})
--                            , λ _ _ → refl))
--                          (invIso (Iso-SeqColim→SeqColimShift _ 2)))))

--   conn : isConnected 2 (fst A)
--   conn = isConnectedRetractFromIso 2 (equivToIso SkelEq)
--            (isOfHLevelRetractFromIso 0
--              (compIso
--                (invIso (connectedTruncIso 2 _
--                (isConnected-CW↪∞ 2 (finCWskel→CWskel dim Skel))))
--                (mapCompIso (equivToIso
--                  (snd (finCWskel→CWskel dim Skel) .snd .snd .snd 1) )))
--                  (∣ inl (fst sk 0 .snd) ∣ₕ
--                  , (TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
--                    (elimProp _ (λ _ → isOfHLevelTrunc 2 _ _)
--                      (λ b i → ∣ inl (isProp0 (fst sk 0 .snd) b i) ∣ₕ)
--                      (uncurry λ x y → (λ i → ∣ inl (isProp0 (fst sk 0 .snd)
--                                                     (α 1 ((x , y) , true)) i) ∣ₕ)
--                              ∙ cong ∣_∣ₕ (push ((x , y) , true)))))))
--     where
--     isProp0 : isProp (fst sk 0 .fst)
--     isProp0 = isOfHLevelRetractFromIso 1
--                 (equivToIso(sk .snd .fst .snd .fst))
--                 isPropFin1


-- GoodCW→finCW : ∀ {ℓ}
--   → finGoodCW ℓ → finConnCW∙ 2 ℓ
-- fst (GoodCW→finCW (A , str)) = A
-- snd (GoodCW→finCW (A , str)) =
--   PT.rec squash₁
--     (λ {(dim , sk , e)
--      →  ∣ (dim
--        , (GoodCW→finCWExpl.Skel A dim sk e
--         , GoodCW→finCWExpl.SkelEq A dim sk e))
--        , (GoodCW→finCWExpl.conn A dim sk e) ∣₁})
--         str

-- finGoodCW≅finConnCW∙ : ∀ {ℓ} → Iso (finGoodCW ℓ) (finConnCW∙ 2 ℓ)
-- Iso.fun finGoodCW≅finConnCW∙ = GoodCW→finCW
-- Iso.inv finGoodCW≅finConnCW∙ = finCW→GoodCW
-- Iso.rightInv finGoodCW≅finConnCW∙ A = Σ≡Prop (λ _ → squash₁) refl
-- Iso.leftInv finGoodCW≅finConnCW∙ A = Σ≡Prop (λ _ → squash₁) refl

-- finGoodCW≡finConnCW∙ : ∀ {ℓ} → finGoodCW ℓ ≡ finConnCW∙ 2 ℓ
-- finGoodCW≡finConnCW∙ = isoToPath finGoodCW≅finConnCW∙

-- elimFinConnCW∙ : ∀ {ℓ ℓ'} {P : finConnCW∙ 2 ℓ → Type ℓ'}
--   → ((c : finGoodCW ℓ) → P (GoodCW→finCW c))
--   → (x : _) → P x
-- elimFinConnCW∙ {P = P} ind x =
--   subst P (Iso.rightInv finGoodCW≅finConnCW∙ x) (ind _)
