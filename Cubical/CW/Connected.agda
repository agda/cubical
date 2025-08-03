{-# OPTIONS --lossy-unification #-}

{-
This file contains the definition of an n-connected CW complex. This
is defined by saying that it has non-trivial cells only in dimension
≥n.

The main result is packaged up in makeConnectedCW. This says that the
usual notion of connectedness in terms of truncations (merely)
coincides with the above definition for CW complexes.

It also contains a proof that of πₙ₊₂X is finitely presented for X an
(n+1)-connected CW complex
-}

module Cubical.CW.Connected where

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.Instances.SphereBouquetMap
open import Cubical.CW.Subcomplex

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties as Ind
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Wedge

open import Cubical.Axiom.Choice
open import Cubical.Relation.Nullary

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Properties
open import Cubical.Homotopy.Group.PiCofibFinSphereBouquetMap

open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.FinitePresentation

open Sequence

private
  variable
    ℓ ℓ' ℓ'' : Level

------ Definitions ------

-- An n-connected CW complex has one 0-cell and no m<n-cells.
yieldsConnectedCWskel : (A : ℕ → Type ℓ) (n : ℕ) → Type _
yieldsConnectedCWskel A k =
  Σ[ sk ∈ yieldsCWskel A ] ((sk .fst 0 ≡ 1) × ((n : ℕ) → n <ᵗ k → sk .fst (suc n) ≡ 0))

-- Alternatively, we may say that its colimit is n-connected
yieldsCombinatorialConnectedCWskel : (A : ℕ → Type ℓ) (n : ℕ) → Type _
yieldsCombinatorialConnectedCWskel A n =
  Σ[ sk ∈ yieldsCWskel A ] isConnected (2 +ℕ n) (realise (_ , sk))

connectedCWskel : (ℓ : Level) (n : ℕ) → Type (ℓ-suc ℓ)
connectedCWskel ℓ n = Σ[ X ∈ (ℕ → Type ℓ) ] (yieldsConnectedCWskel X n)

connectedCWskel→CWskel : ∀ {ℓ} {n : ℕ}
  → connectedCWskel ℓ n → CWskel ℓ
fst (connectedCWskel→CWskel sk) = fst sk
snd (connectedCWskel→CWskel sk) = fst (snd sk)

combinatorialConnectedCWskel : (ℓ : Level) (n : ℕ) → Type (ℓ-suc ℓ)
combinatorialConnectedCWskel ℓ n =
  Σ[ X ∈ (ℕ → Type ℓ) ] (yieldsCombinatorialConnectedCWskel X n)

combinatorialConnectedCWskel→CWskel : ∀ {ℓ} {n : ℕ}
  → combinatorialConnectedCWskel ℓ n → CWskel ℓ
fst (combinatorialConnectedCWskel→CWskel sk) = fst sk
snd (combinatorialConnectedCWskel→CWskel sk) = fst (snd sk)

isConnectedCW : ∀ {ℓ} (n : ℕ) → Type ℓ → Type (ℓ-suc ℓ)
isConnectedCW {ℓ = ℓ} n A =
  Σ[ sk ∈ connectedCWskel ℓ n ] realise (_ , (snd sk .fst)) ≃ A

isConnectedCW' : ∀ {ℓ} (n : ℕ) → Type ℓ → Type (ℓ-suc ℓ)
isConnectedCW' {ℓ = ℓ} n A =
  Σ[ sk ∈ combinatorialConnectedCWskel ℓ n ] realise (_ , (snd sk .fst)) ≃ A

ConnectedCW : (ℓ : Level) (n : ℕ) → Type (ℓ-suc ℓ)
ConnectedCW ℓ n = Σ[ X ∈ Type ℓ ] isConnectedCW n X

ConnectedCW→CWexplicit : ∀ {ℓ} {n : ℕ} → ConnectedCW ℓ n → CWexplicit ℓ
fst (ConnectedCW→CWexplicit (X , p , con)) = X
fst (fst (snd (ConnectedCW→CWexplicit (X , (Xsk , _ , _) , con)))) = Xsk
snd (fst (snd (ConnectedCW→CWexplicit (X , (Xsk , p , _) , con)))) = p
snd (snd (ConnectedCW→CWexplicit (X , (Xsk , _ , _) , con))) = invEquiv con

ConnectedCW→CW : ∀ {ℓ} {n : ℕ} → ConnectedCW ℓ n → CW ℓ
ConnectedCW→CW X = CWexplicit→CW (ConnectedCW→CWexplicit X)

--- Goal: show that these two definitions coincide (note that indexing is off by 2) ---
-- For the base case, we need to analyse α₀ : Fin n × S⁰ → X₁ (recall,
-- indexing of skeleta is shifted by 1). In partiuclar, we will need
-- to show that if X is connected, then either X₁ is contractible or
-- there is some a ∈ Fin n s.t. α₀(a,-) is injective. This will allow
-- us to iteratively shrink X₁ by contracting the image of α₀(a,-).

-- Decision producedures
inhabitedFibres?-Fin×S⁰ : {A : Type ℓ}
  (da : Discrete A) (n : ℕ) (f : Fin n × S₊ 0 → A)
  → inhabitedFibres? f
inhabitedFibres?-Fin×S⁰ {A = A} da n =
  subst (λ C → (f : C → A) → inhabitedFibres? f)
        (isoToPath (invIso Iso-Fin×Bool-Fin))
        (inhabitedFibres?Fin da _)

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

-- α₀ must have a section
isSurj-α₀ : (n m : ℕ) (f : Fin n × S₊ 0 → Fin (suc (suc m)))
  → isConnected 2 (Pushout f fst)
  → (y : _) → Σ[ x ∈ _ ] f x ≡ y
isSurj-α₀ n m f c y with (inhabitedFibres?-Fin×S⁰ DiscreteFin n f y)
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
    with (Contract1Skel _ (suc m)
          (shrinkImageAttachingMap (suc n) m f c .snd .fst)
         (subst (isConnected 2)
           (isoToPath
             (shrinkImageAttachingMap (suc n) m f c .snd .snd)) c))
  ... | (k , e) = k
    , compIso (shrinkImageAttachingMap (suc n) m f c .snd .snd) e

-- Uning this, we can show that a 0-connected CW complex can be
-- approximated by one with trivial 1-skeleton.
module _ (A : ℕ → Type ℓ) (sk+c : yieldsCombinatorialConnectedCWskel A 0) where
  private
    open CWLemmas-0Connected
    c = snd sk+c
    sk = fst sk+c
    c' = isConnectedColim→isConnectedSkel (_ , sk) 2 c

    module AC = CWskel-fields (_ , sk)

    e₁ : Iso (Pushout (fst (CW₁-discrete (_ , sk)) ∘ AC.α 1) fst) (A 2)
    e₁ = compIso (PushoutCompEquivIso (idEquiv _)
                   (CW₁-discrete (A , sk)) (AC.α 1) fst)
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
  → hasCWskel C
  → isConnected (suc (suc n)) C
  → ∥ isConnectedCW n C ∥₁
makeConnectedCW zero {C = C} (cwsk , e) cA =
  ∣ (_ , (M .fst , refl , λ p → λ()))
  , compEquiv (invEquiv (collapse₁Equiv _ _ 0)) (invEquiv e) ∣₁
  where
  M = connectedCWskel→ (cwsk .fst)
       (snd cwsk , subst (isConnected 2) (ua e) cA)
makeConnectedCW {ℓ = ℓ} (suc n) {C = C} (cwsk , eqv) cA with
  (makeConnectedCW n (cwsk , eqv) (isConnectedSubtr (suc (suc n)) 1 cA))
... | s = PT.rec squash₁
  (λ s → PT.rec squash₁
    (λ α-pt* → PT.rec squash₁
      (λ α-pt2*
        → PT.rec squash₁
          (λ vanish*
            → PT.map (uncurry (isConnectedCW-C' s α-pt* α-pt2* vanish*))
          (∃Improvedβ s α-pt* α-pt2* vanish*))
          (sphereBouquetVanish s α-pt* α-pt2*
            (const→C4+n s α-pt* α-pt2*)))
              (α-pt∙₂ s α-pt*)) (α'2+n∙ s)) s
  where
  module _ (ind : isConnectedCW n C) where
    open CWskel-fields (_ , ind .fst .snd .fst)
    -- By the induction hypothesis we get a CW structure on C with C (suc n) trivial

    -- some basic abbreviations and lemmas
    module _ where
      C* = ind .fst .fst

      2+n = suc (suc n)
      3+n = suc 2+n
      4+n = suc 3+n

      C1+n = C* (suc n)
      C2+n = C* 2+n
      C3+n = C* 3+n
      C4+n = C* 4+n

      α2+n = α 2+n

      isConnectedC4+n : isConnected 3+n C4+n
      isConnectedC4+n = isConnectedCW→isConnectedSkel
                 (_ , ind .fst .snd .fst) 4+n
                   (3+n , <ᵗ-trans <ᵗsucm <ᵗsucm)
                   (subst (isConnected 3+n) (ua (invEquiv (ind .snd)))
                   cA)

      isConnected3+n : isConnected 2+n C3+n
      isConnected3+n = isConnectedCW→isConnectedSkel
                 (_ , ind .fst .snd .fst) 3+n
                   (2+n , <ᵗ-trans <ᵗsucm <ᵗsucm)
                   (subst (isConnected 2+n) (ua (invEquiv (ind .snd)))
                   (isConnectedSubtr 2+n 1 cA))

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
    α'2+n : A 2+n × S₊ (suc n) → SphereBouquet (suc n) (A (suc n))
    α'2+n = Iso.fun Iso-C2+n-SphereBouquet ∘ α 2+n

    opaque
      Iso-C3+n-Pushoutα'2+n : Iso (C* 3+n)
                 (Pushout α'2+n fst)
      Iso-C3+n-Pushoutα'2+n = compIso (equivToIso (e 2+n))
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
      α∙ : SphereBouquet∙ (suc n) (A 2+n)
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
      α-pt∙₂ : ∥ ((x : A 3+n)
               → Iso.fun Iso-C3+n-cofibα (α 3+n (x , north)) ≡ inl tt) ∥₁
      α-pt∙₂ = invEq propTrunc≃Trunc1 (invEq (_ , InductiveFinSatAC _ _ _)
             λ a → isConnectedPath 1
                     (isConnectedRetractFromIso 2 (invIso Iso-C3+n-cofibα)
                     (isConnectedSubtr' n 2 isConnected3+n) ) _ _ .fst)

      -- But again, let us assume it is...
      module _ (α-pt∙₂ : (x : A 3+n)
             → Iso.fun Iso-C3+n-cofibα (α 3+n (x , north)) ≡ inl tt) where

        -- Doing so, we can lift α yet again this time to a map
        -- α↑ : ⋁S²⁺ⁿ → cofib α
        α↑ : SphereBouquet∙ 2+n (A 3+n)
         →∙ (cofib (fst α∙) , inl tt)
        fst α↑ (inl x) = inl tt
        fst α↑ (inr x) = Iso.fun Iso-C3+n-cofibα (α 3+n x)
        fst α↑ (push a i) = α-pt∙₂ a (~ i)
        snd α↑ = refl

        -- The cofibre of this map is C₄₊ₙ
        Iso-C4+n-cofibα↑ : Iso (C* (4 +ℕ n)) (cofib (fst α↑))
        Iso-C4+n-cofibα↑ = compIso (equivToIso (e 3+n))
                (compIso
                  (pushoutIso _ _ _ _
                    (idEquiv _)
                    (isoToEquiv Iso-C3+n-cofibα)
                    (idEquiv _) refl refl)
                  (⋁-cofib-Iso _ α↑))



        opaque
          Iso-cofibαinr-SphereBouquet :
            Iso (Pushout {B = cofib (fst α∙)} inr (λ _ → tt))
                (SphereBouquet 2+n (A 2+n))
          Iso-cofibαinr-SphereBouquet = compIso (equivToIso (symPushout _ _))
                    (compIso (Iso-cofibInr-Susp α∙)
                      sphereBouquetSuspIso)

          Iso-cofibαinr-SphereBouquet∙ :
            Iso.fun Iso-cofibαinr-SphereBouquet (inl (inl tt)) ≡ inl tt
          Iso-cofibαinr-SphereBouquet∙ = refl

        -- composing the above iso with α↑ lets us define a map of sphere bouquets:
        β : SphereBouquet 2+n (A 3+n)
         → SphereBouquet 2+n (A 2+n)
        β = (Iso.fun Iso-cofibαinr-SphereBouquet ∘ inl) ∘ fst α↑

        β∙ : SphereBouquet∙ 2+n (A 3+n)
          →∙ SphereBouquet∙ 2+n (A 2+n)
        fst β∙ = β
        snd β∙ = Iso-cofibαinr-SphereBouquet∙

        -- The goal now: show that the cofibre of β is C₄₊ₙ ⋁ S²⁺ⁿ
        C⋆ = Iso-C4+n-cofibα↑ .Iso.inv (inl tt)

        -- Abbreviation of C₄₊ₙ ⋁ S²⁺ⁿ:
        C₄₊ₙ⋁SphereBouquet = (C4+n , C⋆)
           ⋁ SphereBouquet∙ 2+n (A 2+n)


        -- Intermediate alternative definition of C₄₊ₙ ⋁ S²⁺ⁿ:
        C₄₊ₙ⋁SphereBouquetAsPushout =
          Pushout (Iso.inv Iso-C4+n-cofibα↑ ∘ inr)
                  (λ x → Iso.fun Iso-cofibαinr-SphereBouquet (inl x))

        -- We geta a map ⋁Sⁿ⁺¹ → C4+n. It is merely constant for
        -- connectedness reasons and its cofibre is
        -- C₄₊ₙ⋁SphereBouquetAsPushout by a simple pasting argument.
        const→C4+n : SphereBouquet (suc n) (A (suc n)) → C4+n
        const→C4+n x = Iso.inv Iso-C4+n-cofibα↑ (inr (inr x))

        -- Settting up the pushout-pastings:
        open commSquare
        open 3-span

        commSquare₁ : commSquare
        A0 (sp commSquare₁) = cofib (fst α∙)
        A2 (sp commSquare₁) = SphereBouquet 2+n (A 3+n)
        A4 (sp commSquare₁) = Unit
        f1 (sp commSquare₁) = fst α↑
        f3 (sp commSquare₁) = λ _ → tt
        P commSquare₁ = cofib (fst α↑)
        inlP commSquare₁ = inr
        inrP commSquare₁ = inl
        comm commSquare₁ = funExt λ x → sym (push x)

        pushoutSquare₁ : PushoutSquare
        fst pushoutSquare₁ = commSquare₁
        snd pushoutSquare₁ =
          subst isEquiv (funExt
            (λ { (inl x) → refl
               ; (inr x) → refl
               ; (push a i) → refl}))
            (symPushout _ _ .snd)

        commSquare₂ : commSquare
        A0 (sp commSquare₂) = cofib (fst α∙)
        A2 (sp commSquare₂) = SphereBouquet (suc n) (A (suc n))
        A4 (sp commSquare₂) = Unit
        f1 (sp commSquare₂) = inr
        f3 (sp commSquare₂) = _
        P commSquare₂ = SphereBouquet 2+n (A 2+n)
        inlP commSquare₂ x = Iso.fun Iso-cofibαinr-SphereBouquet (inl x)
        inrP commSquare₂ _ = Iso.fun Iso-cofibαinr-SphereBouquet (inr tt)
        comm commSquare₂ =
          funExt λ x → cong (Iso.fun Iso-cofibαinr-SphereBouquet) (push x)

        pushoutSquare₂ : PushoutSquare
        fst pushoutSquare₂ = commSquare₂
        snd pushoutSquare₂ =
          subst isEquiv (funExt coh)
            (isoToIsEquiv Iso-cofibαinr-SphereBouquet)
          where
          coh : (x : _) → Iso.fun Iso-cofibαinr-SphereBouquet x
                         ≡ Pushout→commSquare commSquare₂ x
          coh (inl x) = refl
          coh (inr x) = refl
          coh (push x i₁) = refl

        module L→R =
          PushoutPasteDown pushoutSquare₂ {B = C₄₊ₙ⋁SphereBouquetAsPushout}
               (Iso.inv Iso-C4+n-cofibα↑ ∘ inr) inl inr (funExt push)

        -- First equivalence
        C₄₊ₙ⋁SphereBouquetAsPushout≃cofib-const :
          C₄₊ₙ⋁SphereBouquetAsPushout ≃ cofib const→C4+n
        C₄₊ₙ⋁SphereBouquetAsPushout≃cofib-const =
          compEquiv
           (invEquiv (_ , isPushoutTot))
           (symPushout _ _)
           where
          isPushoutTot =
            L→R.isPushoutBottomSquare→isPushoutTotSquare
              (subst isEquiv (funExt (λ { (inl x) → refl
                                        ; (inr x) → refl
                                        ; (push a i) → refl}))
              (idIsEquiv _))

        -- The map we have called constant is actually (merely constant):
        sphereBouquetVanish : ∀ {k : ℕ}
          (f : SphereBouquet (suc n) (Fin k) → C4+n)
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
            lem)
            pted
          where
          sphereVanish : (f : S₊ (suc n) → C4+n)
                      → ∥ ((x : S₊ (suc n)) → f x ≡ C⋆) ∥₁
          sphereVanish f =
            sphereToTrunc (suc (suc n))
              λ x → isConnectedPath 2+n isConnectedC4+n _ _ .fst

          pted = Iso.fun (PathIdTruncIso 2+n)
                           (isContr→isProp isConnectedC4+n  ∣ f (inl tt) ∣ₕ ∣ C⋆ ∣ₕ)

          lem : ∥ ((x : Fin k) → (y :  _) → f (inr (x , y)) ≡ C⋆) ∥₁
          lem = invEq propTrunc≃Trunc1
            (invEq (_ , InductiveFinSatAC _ _ _)
              λ x → PT.rec (isOfHLevelTrunc 1)
                ∣_∣ₕ
                (sphereVanish λ y → f (inr (x , y))))

        -- For now, we asssume it's constant
        module _ (vanish : const→C4+n ≡ λ _ → C⋆) where

          -- Abbreviation: (⋁S⁴⁺ⁿ) ∨ C₄₊ₙ
          SphereBouquet⋁C₄₊ₙ =
            SphereBouquet∙ 2+n (A (suc n)) ⋁ (C4+n , C⋆)

          -- Connectedness of this space
          isConnectedSphereBouquet⋁C₄₊ₙ :
            isConnected 3+n SphereBouquet⋁C₄₊ₙ
          fst isConnectedSphereBouquet⋁C₄₊ₙ = ∣ inl (inl tt) ∣ₕ
          snd isConnectedSphereBouquet⋁C₄₊ₙ =
            TR.elim (λ _ → isOfHLevelPath 3+n
                            (isOfHLevelTrunc 3+n) _ _)
              λ { (inl x) → inlEq x
                ; (inr x) → SP ∙ inrEq x
                ; (push tt i) j →
                  (compPath-filler (inlEq (inl tt)) (cong ∣_∣ₕ (push tt))
                ▷ (rUnit SP ∙ cong (SP ∙_) (sym inrEq∙))) i j}
            where
            inlEq : (x : _)
              → Path (hLevelTrunc 3+n SphereBouquet⋁C₄₊ₙ)
                ∣ inl (inl tt) ∣ ∣ inl x ∣
            inlEq x = TR.rec (isOfHLevelTrunc 3+n _ _)
              (λ p i → ∣ inl (p i) ∣ₕ)
              (Iso.fun (PathIdTruncIso _)
                (isContr→isProp
                  (isConnectedSphereBouquet' {n = suc n})
                    ∣ inl tt ∣ ∣ x ∣))

            G :  (x : C4+n) → ∥ C⋆ ≡ x ∥ 2+n
            G x = Iso.fun (PathIdTruncIso _)
                    (isContr→isProp isConnectedC4+n ∣ C⋆ ∣ₕ ∣ x ∣ₕ)

            G∙ : G C⋆ ≡ ∣ refl ∣ₕ
            G∙ = cong (Iso.fun (PathIdTruncIso _))
                  (isProp→isSet (isContr→isProp isConnectedC4+n) _ _
                    (isContr→isProp isConnectedC4+n ∣ C⋆ ∣ₕ ∣ C⋆ ∣ₕ) refl)
               ∙ cong ∣_∣ₕ (transportRefl refl)

            inrEq : (x : C4+n)
              → Path (hLevelTrunc 3+n SphereBouquet⋁C₄₊ₙ)
                      ∣ inr C⋆ ∣ₕ ∣ inr x ∣ₕ
            inrEq x = TR.rec (isOfHLevelTrunc 3+n _ _)
                             (λ p i → ∣ inr (p i) ∣ₕ) (G x)

            inrEq∙ : inrEq C⋆ ≡ refl
            inrEq∙ = cong (TR.rec (isOfHLevelTrunc 3+n _ _)
                             (λ p i → ∣ inr (p i) ∣ₕ)) G∙

            SP = inlEq (inl tt) ∙ cong ∣_∣ₕ (push tt)


          -- Equivalence of our C₄₊ₙ⋁SphereBouquet and SphereBouquet⋁C₄₊ₙ
          C₄₊ₙ⋁SphereBouquetAsPushout≃SphereBouquet⋁C₄₊ₙ :
              C₄₊ₙ⋁SphereBouquetAsPushout ≃ SphereBouquet⋁C₄₊ₙ
          C₄₊ₙ⋁SphereBouquetAsPushout≃SphereBouquet⋁C₄₊ₙ =
            compEquiv C₄₊ₙ⋁SphereBouquetAsPushout≃cofib-const
              (isoToEquiv
                (compIso (cofibConst-⋁-Iso' {A = _ , inl tt} {B = _ , C⋆}
                           (const→C4+n , funExt⁻ vanish _)
                           (funExt⁻ vanish))
                (pushoutIso _ _ _ _
                  (idEquiv _)
                  (isoToEquiv sphereBouquetSuspIso)
                  (idEquiv _)
                  refl
                  refl)))

          module T→B = PushoutPasteDown pushoutSquare₁
            {B = C₄₊ₙ⋁SphereBouquetAsPushout}
            (λ x → Iso.fun Iso-cofibαinr-SphereBouquet (inl x)) inr
            (λ x → inl (Iso.inv Iso-C4+n-cofibα↑ x))
            (sym (funExt push))

          -- Finally, the first main lemma: the cofibre of β is S¹⁺ⁿ ∨ C₄₊ₙ
          cofibβ≃SphereBouquet⋁C₄₊ₙ : cofib β ≃ SphereBouquet⋁C₄₊ₙ
          cofibβ≃SphereBouquet⋁C₄₊ₙ =
            compEquiv (compEquiv (symPushout _ _)
              (_ , T→B.isPushoutBottomSquare→isPushoutTotSquare
                (subst isEquiv (funExt helpIsoCoh) (isoToIsEquiv helpIso))))
              C₄₊ₙ⋁SphereBouquetAsPushout≃SphereBouquet⋁C₄₊ₙ
            where
            helpIso : Iso (spanPushout (sp T→B.bottomSquare))
                                       (P T→B.bottomSquare)
            helpIso = compIso (equivToIso (symPushout _ _))
                              (pushoutIso _ _ _ _ (idEquiv _)
                                (invEquiv (isoToEquiv Iso-C4+n-cofibα↑))
                                (idEquiv _) refl refl)

            helpIsoCoh : (x : _) → Iso.fun helpIso x
                                  ≡ Pushout→commSquare T→B.bottomSquare x
            helpIsoCoh (inl x) = refl
            helpIsoCoh (inr x) = refl
            helpIsoCoh (push a i) j = sym (rUnit (sym (push a))) j i

          -- If we could adjust β somewhat, killing off S¹⁺ⁿ in S¹⁺ⁿ ∨
          -- C₄₊ₙ, we would be done.


          -- We prove the mere existence of such an `improved β':
          ∃Improvedβ : ∃[ F ∈ (SphereBouquet∙ 2+n (A (suc n))
                          →∙ SphereBouquet∙ 2+n (A 2+n)) ]
                   ((x : _) → Path SphereBouquet⋁C₄₊ₙ
                                (cofibβ≃SphereBouquet⋁C₄₊ₙ .fst
                                  (inr (fst F x))) (inl x))
          ∃Improvedβ = TR.rec (isProp→isOfHLevelSuc (suc n) squash₁)
            (λ coh₁ → PT.rec squash₁ (λ F → TR.rec squash₁
            (λ h → TR.rec squash₁ (λ q → ∣ (Improvedβ F coh₁ h , refl) ,
                                            (coh F coh₁ h q) ∣₁)
            (makeCoh F coh₁ h))
            (F∙ F coh₁))
            ∃Improvedβ-inr)
              (isConnectedPath _ isConnectedSphereBouquet⋁C₄₊ₙ
                (cofibβ≃SphereBouquet⋁C₄₊ₙ .fst
                  (inr (inl tt))) (inl (inl tt)) .fst)
            where
            ∃Improvedβ-inr : ∥ ((x : A (suc n)) (y : S₊ 2+n)
              → Σ[ t ∈ SphereBouquet 2+n (A 2+n) ]
                    (cofibβ≃SphereBouquet⋁C₄₊ₙ .fst (inr t)
                   ≡ inl (inr (x , y)))) ∥₁
            ∃Improvedβ-inr =
              invEq propTrunc≃Trunc1
                (invEq (_ , InductiveFinSatAC _ _ _)
                  λ x → fst propTrunc≃Trunc1
                    (sphereToTrunc (suc 2+n)
                      λ y → isConnectedInr-cofib∘inr (inl (inr (x , y))) .fst))
              where
              isConnectedInr-cofibβ :
                isConnectedFun 3+n {B = cofib β} inr
              isConnectedInr-cofibβ = inrConnected 3+n _ _
                λ b → isOfHLevelRetractFromIso 0 (mapCompIso fiberUnitIso)
                        isConnectedSphereBouquet'

              isConnectedInr-cofib∘inr : isConnectedFun 3+n
                {B = SphereBouquet⋁C₄₊ₙ}
                (cofibβ≃SphereBouquet⋁C₄₊ₙ .fst ∘ inr)
              isConnectedInr-cofib∘inr =
                isConnectedComp
                  (cofibβ≃SphereBouquet⋁C₄₊ₙ .fst) inr 3+n
                  (isEquiv→isConnected _
                    (cofibβ≃SphereBouquet⋁C₄₊ₙ .snd) 3+n)
                    isConnectedInr-cofibβ

            -- We asumme the full existence of such an improved β (F below)
            module _
              (F : ((x : A (suc n)) (y : S₊ 2+n)
               → Σ[ t ∈ SphereBouquet 2+n (A 2+n) ]
                     (cofibβ≃SphereBouquet⋁C₄₊ₙ .fst (inr t)
                   ≡ inl (inr (x , y)))))
              (coh₁ : Path SphereBouquet⋁C₄₊ₙ
                           (cofibβ≃SphereBouquet⋁C₄₊ₙ .fst (inr (inl tt)))
                           (inl (inl tt)))
              where
              -- mere pointedness
              F∙ : hLevelTrunc 1 ((x : Fin _) → F x north .fst ≡ inl tt)
              F∙ =
                invEq (_ , InductiveFinSatAC _ _ _)
                  λ a → isConnectedPath 1 (isConnectedSubtr 2 (suc n)
                    (subst (λ x → isConnected x (SphereBouquet 2+n
                                    (A 2+n)))
                                    (cong suc (+-comm 2 n))
                                    isConnectedSphereBouquet')) _ _ .fst

              -- ... which we assume, as usual.
              module _ (h  : (x : Fin _) → F x north .fst ≡ inl tt) where
                Improvedβ : (SphereBouquet 2+n (A (suc n))
                   → SphereBouquet 2+n (A 2+n))
                Improvedβ (inl x) = inl tt
                Improvedβ (inr (x , y)) = F x y .fst
                Improvedβ (push a i) = h  a (~ i)

                -- We also want the following coherencet to be satisfied
                cohTy : Type _
                cohTy = (a : A (suc n))
                  → Square (λ i → cofibβ≃SphereBouquet⋁C₄₊ₙ .fst
                                    (inr (h a (~ i))))
                            (λ i → inl (push a i))
                            coh₁ (F a north .snd)

                -- It merely is...
                makeCoh : hLevelTrunc 1 cohTy
                makeCoh = invEq (_ , InductiveFinSatAC _ _ _)
                  λ a → isConnectedPathP 1
                    (isConnectedSubtr' n 2
                      (isConnectedPath _
                        isConnectedSphereBouquet⋁C₄₊ₙ _ _)) _ _ .fst

                -- so we assume it, giving us the main coherence we need
                module _ (coh₂ : cohTy) where
                  coh : (x : _) → Path SphereBouquet⋁C₄₊ₙ
                                    (cofibβ≃SphereBouquet⋁C₄₊ₙ .fst
                                      (inr (Improvedβ x)))
                                    (inl x)
                  coh (inl x) = coh₁
                  coh (inr (x , y)) = F x y .snd
                  coh (push a i) j = coh₂ a j i

          -- Now, assuming the exisetence of Imrpovedβ and the coherence above,
          -- we can finally endow C₄₊ₙ with the appropriate cell structure
          module _ (F : (SphereBouquet∙ 2+n (A (suc n))
                     →∙ SphereBouquet∙ 2+n (A 2+n)))
                   (h : (x : _) → Path SphereBouquet⋁C₄₊ₙ
                                    (cofibβ≃SphereBouquet⋁C₄₊ₙ .fst
                                      (inr (fst F x)))
                                    (inl x))
            where
            -- The cardinality of the ₄₊ₙ-cells
            N = card (suc n) +ℕ card 3+n

            -- Techincal ⋁-distributivity lemma
            Iso-SphereBouquetN : Iso (SphereBouquet 2+n (Fin N))
                       (SphereBouquet∙ 2+n (A (suc n))
                     ⋁ SphereBouquet∙ 2+n (A 3+n))
            Iso-SphereBouquetN = compIso
              (pathToIso
                ((λ i → ⋁gen (isoToPath
                  (Iso-Fin⊎Fin-Fin+
                    {n = card (suc n)}
                    {m = card 3+n}) (~ i))
                    (λ _ → S₊∙ 2+n))
                  ∙ cong (⋁gen (A (suc n) ⊎ A 3+n))
                         (funExt (⊎.elim (λ _ → refl) (λ _ → refl)))))
                (invIso ⋁gen⊎Iso)

            -- Finally, we have shown that C₄₊ₙ is the cofibre of F ∨→
            -- β → C4+n
            Iso-cofib-C₄₊ₙ : Iso (cofib (F ∨→ β∙)) C4+n
            Iso-cofib-C₄₊ₙ = compIso (cofib∨→compIsoᵣ  F β∙)
                 (compIso
                   (pathToIso (cong cofib (funExt lem)))
                   (compIso
                     (equivToIso (symPushout _ _))
                     (compIso
                       (PushoutCompEquivIso
                         (idEquiv (SphereBouquet 2+n (A (suc n))))
                         (invEquiv cofibβ≃SphereBouquet⋁C₄₊ₙ) inl (λ _ → tt))
                       (compIso (equivToIso (symPushout _ _)) cofibInl-⋁))))
              where
              lem : (x : _) → inr (fst F x) ≡ invEq cofibβ≃SphereBouquet⋁C₄₊ₙ (inl x)
              lem x = sym (retEq cofibβ≃SphereBouquet⋁C₄₊ₙ (inr (fst F x)))
                   ∙ cong (invEq cofibβ≃SphereBouquet⋁C₄₊ₙ) (h x)

            -- Let us summarise the main data: we have shown that
            -- there is some k and a map α : ⋁ₖ Sⁿ⁺² → ⋁ Sⁿ⁺² s.t. α
            -- defines an attaching map for C₄₊ₙ.
            mainData : Σ[ k ∈ ℕ ] Σ[ α ∈ (SphereBouquet 2+n (Fin k)
                                  → SphereBouquet 2+n (A 2+n)) ]
                 (Iso (Pushout (α ∘ inr) fst) C4+n)
            fst mainData = N
            fst (snd mainData) = F ∨→ β∙ ∘ Iso.fun Iso-SphereBouquetN
            snd (snd mainData) =
              compIso
                (compIso (⋁-cofib-Iso (_ , fst F (inl tt))
                          ((F ∨→ β∙ ∘ Iso.fun Iso-SphereBouquetN) , refl))
                         (invIso (PushoutCompEquivIso
                           (invEquiv (isoToEquiv Iso-SphereBouquetN))
                             (idEquiv Unit) _ _))) Iso-cofib-C₄₊ₙ

            -- Using this, we can finally define a CW structure on C with the
            -- desired properties

            -- We parametrise with Trichotomyᵗ as it makes removes some bureaucracy later

            -- The type family
            C' : (m : ℕ)
              → Trichotomyᵗ m 3+n → Type ℓ
            C' zero (lt x) = ⊥*
            C' (suc m) (lt x) = Unit*
            C' m (eq x) =
              Lift (SphereBouquet 2+n (A 2+n))
            C' m (gt x) = C* m

            -- Basepoints (not needed, but useful)
            C'∙ : (m : ℕ) (q : _) → C' (suc m) q
            C'∙ m (lt x) = tt*
            C'∙ m (eq x) = lift (inl tt)
            C'∙ m (gt x) = subst C* (+-comm m 1)
              (CW↪Iterate (_ , ind .fst .snd .fst) 1 m
                (invEq (CW₁-discrete (_ , ind .fst .snd .fst))
                  (subst Fin (sym (ind .fst .snd .snd .fst)) flast)))

            -- Cardinality of cells
            card' : (m : ℕ) → Trichotomyᵗ m 2+n
              → Trichotomyᵗ m 3+n → ℕ
            card' zero (lt x) q = 1
            card' (suc m) (lt x) q = 0
            card' m (eq x) q = card 2+n
            card' m (gt x) (lt x₁) = 0
            card' m (gt x) (eq x₁) = N
            card' m (gt x) (gt x₁) = card m

            -- Connectedness
            C'-connected : (n₁ : ℕ) → n₁ <ᵗ suc n
              → (p : _) (q : _) → card' (suc n₁) p q ≡ 0
            C'-connected m ineq (lt x) q = refl
            C'-connected m ineq (eq x) q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ 2+n) x ineq))
            C'-connected m ineq (gt x) q = ⊥.rec (¬m<ᵗm (<ᵗ-trans ineq x))

            -- Attaching maps
            α' : (m : ℕ) (p : _) (q : _) → Fin (card' m p q) × S⁻ m → C' m q
            α' (suc m) (lt x) q ()
            α' (suc m) (eq x) (lt x₁) _ = tt*
            α' (suc m) (eq x) (eq x₁) _ = C'∙ m (eq x₁)
            α' (suc m) (eq x) (gt x₁) _ = C'∙ m (gt x₁)
            α' (suc m) (gt x) (lt x₁) _ = C'∙ m (lt x₁)
            α' (suc m) (gt x) (eq x₁) (a , p) =
              lift (snd mainData .fst (inr (a , subst S₊ (cong predℕ x₁) p)))
            α' (suc m) (gt x) (gt x₁) = α (suc m)

            -- Equivalences
            e' : (n₁ : ℕ) (p : _) (q : _)
              → C' (suc n₁) (Trichotomyᵗ-suc p)
                ≃ Pushout (α' n₁ p q) fst
            e' zero (lt s) (lt t) =
              isoToEquiv (isContr→Iso (tt* , (λ {tt* → refl}))
                         ((inr flast) , λ {(inr (zero , tt)) → refl}))
            e' zero (lt x) (eq p) = ⊥.rec (snotz (sym p))
            e' zero (eq x) q = ⊥.rec (snotz (sym x))
            e' (suc m) (lt x) q =
              isoToEquiv (isContr→Iso (tt* , (λ {tt* → refl}))
                         ((inl (C'Contr m x q .fst))
                        , (λ { (inl t) → λ i
                          → inl (C'Contr m x q .snd t i)})))
              where
              C'Contr : (m : _) (t : m <ᵗ suc n) (q : _)
                → isContr (C' (suc m) q)
              C'Contr m t (lt x) = tt* , λ {tt* → refl}
              C'Contr m t (eq x) =
                ⊥.rec (¬m<ᵗm (<ᵗ-trans (subst (_<ᵗ suc n)
                                        (cong predℕ x) t) <ᵗsucm))
              C'Contr m t (gt x) =
                ⊥.rec (¬m<ᵗm (<ᵗ-trans (<ᵗ-trans x t) <ᵗsucm))
            e' (suc m) (eq x) (lt x₁) =
              invEquiv (isoToEquiv
                (compIso (⋁-cofib-Iso
                          {B = λ _ → _ , ptSn m} (_ , tt*) (_ , refl))
                  (compIso (cofibConst-⋁-Iso {A = SphereBouquet∙ m _})
                    (compIso ⋁-rUnitIso
                      (compIso sphereBouquetSuspIso
                        (compIso
                          (pathToIso
                            (λ i → SphereBouquet (x i) (A 2+n)))
                          LiftIso))))))
            e' (suc m) (eq x) (eq x₁) =
              ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n)
                      (cong (predℕ ∘ predℕ) (sym x ∙ x₁)) <ᵗsucm))
            e' (suc m) (eq x) (gt y) =
              ⊥.rec (¬m<ᵗm (<ᵗ-trans (subst (2+n <ᵗ_)
                                   (cong predℕ x) y) <ᵗsucm))
            e' (suc m) (gt x) (lt x₁) = ⊥.rec (¬squeeze (x , x₁))
            e' (suc m) (gt x) (eq x₁) =
              isoToEquiv (compIso (compIso
                (pathToIso (λ i → C* (suc (x₁ i))))
                (invIso (mainData .snd .snd)))
                (invIso (pushoutIso _ _ _ _
                  (Σ-cong-equiv-snd
                    (λ _ → pathToEquiv (cong S₊ (cong predℕ x₁))))
                    (invEquiv LiftEquiv) (idEquiv _) refl refl)))
            e' (suc m) (gt x) (gt x₁) = e (suc m)

            -- packaging it up into a connectedCWskel
            C'-connectedCWskel : connectedCWskel ℓ (suc n)
            fst C'-connectedCWskel m = C' m (m ≟ᵗ 3+n)
            fst (fst (snd C'-connectedCWskel)) m =
              card' m (m ≟ᵗ 2+n) (m ≟ᵗ 3+n)
            fst (snd (fst (snd C'-connectedCWskel))) m = α' m _ _
            fst (snd (snd (fst (snd C'-connectedCWskel)))) ()
            snd (snd (snd (fst (snd C'-connectedCWskel)))) m = e' m _ _
            fst (snd (snd C'-connectedCWskel)) = refl
            snd (snd (snd C'-connectedCWskel)) m ineq = C'-connected m ineq _ _

            C'-realise : (n₁ : ℕ) (q : _)
              → Iso (C' (n₁ +ℕ 4+n) q)
                     (C* (n₁ +ℕ 4+n))
            C'-realise m (lt x) = ⊥.rec (¬m<m (<-trans (<ᵗ→< x) (m , refl)))
            C'-realise m (eq x) = ⊥.rec (¬m<m (m , x))
            C'-realise zero (gt x) = idIso
            C'-realise (suc m) (gt x) = idIso

            C'-realise-coh : (n₁ : ℕ) (q : _) (r : _)
                (a : C' (n₁ +ℕ 4+n) q)
                → CW↪ (fst (fst ind) , snd (fst ind) .fst) (n₁ +ℕ 4+n)
                      (Iso.fun (C'-realise n₁ q) a)
                ≡ Iso.fun (C'-realise (suc n₁) _)
                    (invEq (e' (n₁ +ℕ 4+n) r q) (inl a))
            C'-realise-coh m (lt x) r a = ⊥.rec (¬m<m (<-trans (<ᵗ→< x) (m , refl)))
            C'-realise-coh m (eq x) r a = ⊥.rec (¬m<m (m , x))
            C'-realise-coh m (gt x) (lt x₁) a =
              ⊥.rec (¬m<ᵗm (<ᵗ-trans (<ᵗ-trans x x₁) <ᵗsucm))
            C'-realise-coh m (gt x) (eq x₁) a =
              ⊥.rec (¬m<ᵗm (<ᵗ-trans ((subst (_<ᵗ (m +ℕ 4+n)) (cong suc (sym x₁)) x)) <ᵗsucm))
            C'-realise-coh zero (gt x) (gt x₁) a = refl
            C'-realise-coh (suc m) (gt x) (gt x₁) a = refl

            -- finally, we're done
            isConnectedCW-C' : isConnectedCW (suc n) C
            fst isConnectedCW-C' = C'-connectedCWskel
            snd isConnectedCW-C' =
              compEquiv (isoToEquiv
                (compIso (SeqColimIso _ (4 +ℕ n))
                  (compIso (sequenceIso→ColimIso
                    ((λ m → C'-realise m ((m +ℕ 4+n) ≟ᵗ 3+n))
                    , (λ n → C'-realise-coh n _ _)))
                    (invIso (SeqColimIso _ (4 +ℕ n)))))) (ind .snd)

-- As a consequence, we can compute Xₘ for m small enough when X is an
-- n-connected CW complex.  This is done in the following three theorems
open CWskel-fields
connectedCWContr : {ℓ : Level} (n m : ℕ) (l : m <ᵗ suc n) (X : Type ℓ)
  (cwX : isConnectedCW n X) → isContr (fst (fst cwX) (suc m))
connectedCWContr n zero l X cwX =
  subst isContr
     (cong (Lift ∘ Fin) (sym ((snd (fst cwX)) .snd .fst))
    ∙ sym (ua (compEquiv (CW₁-discrete (connectedCWskel→CWskel (fst cwX)))
                         LiftEquiv)))
     (isOfHLevelLift 0 (inhProp→isContr fzero isPropFin1))
connectedCWContr n (suc m) l X cwX =
  subst isContr
    (ua (compEquiv (isoToEquiv (PushoutEmptyFam
      (¬Fin0 ∘ subst Fin cardₘ₊₁≡0 ∘ fst)
      (¬Fin0 ∘ subst Fin cardₘ₊₁≡0)))
      (invEquiv (e (connectedCWskel→CWskel (fst cwX)) (suc m)))
      ))
    (connectedCWContr n m (<ᵗ-trans l <ᵗsucm) X cwX)
  where
  cardₘ₊₁≡0 = snd (snd (snd (fst cwX))) m l

connectedCW≃SphereBouquet : {ℓ : Level} (n : ℕ) (X : Type ℓ) (cwX : isConnectedCW n X)
  → fst (fst cwX) (suc (suc n))
  ≃ SphereBouquet (suc n) (Fin (card (connectedCWskel→CWskel (fst cwX)) (suc n)))
connectedCW≃SphereBouquet n X cwX =
  compEquiv
    (e (connectedCWskel→CWskel (fst cwX)) (suc n))
    (compEquiv
     (pushoutEquiv _ _ _ fst
       (idEquiv _)
       (isContr→≃Unit (connectedCWContr n n <ᵗsucm X cwX))
       (idEquiv _)
       (λ _ _ → tt)
       (λ i x → fst x))
     (compEquiv (isoToEquiv (Iso-cofibFst-⋁ (λ A → S₊∙ n)))
     (pushoutEquiv _ _ _ _ (idEquiv _) (idEquiv _)
       (Σ-cong-equiv-snd (λ _ → isoToEquiv (invIso (IsoSucSphereSusp n))))
       (λ _ _ → tt) (λ i x → x , IsoSucSphereSusp∙ n i))))


open import Cubical.CW.Instances.Lift
module _ {ℓ : Level} (n : ℕ) (X : Type ℓ) (cwX : isConnectedCW n X)
         (str : isCW (fst cwX .fst (suc (suc (suc n))))) where

  private
   X₃₊ₙ = fst (fst cwX) (suc (suc (suc n)))
   X₂₊ₙ = fst (fst cwX) (suc (suc n))
   Xˢᵏᵉˡ = connectedCWskel→CWskel (fst cwX)

   X₃₊ₙᶜʷ : CW ℓ
   X₃₊ₙᶜʷ = X₃₊ₙ , str

  connectedCW≃CofibFinSphereBouquetMap :
     ∃[ α ∈ FinSphereBouquetMap∙
              (card Xˢᵏᵉˡ (suc (suc n))) (card Xˢᵏᵉˡ (suc n)) n ]
      (X₃₊ₙᶜʷ ≡ CWLift ℓ (SphereBouquet/ᶜʷ  (fst α)))
  connectedCW≃CofibFinSphereBouquetMap =
    PT.rec squash₁
      (λ { (x , ptz , t) →
        ∣ (≃∘α' x ptz t)
        , (Σ≡Prop (λ _ → squash₁)
            (isoToPath (compIso
              (connectedCW≅CofibFinSphereBouquetMap x ptz t)
              LiftIso))) ∣₁})
      lem
    where
    isConX₂₊ₙ : isConnected 2 X₂₊ₙ
    isConX₂₊ₙ =
      isConnectedRetractFromIso 2
        (equivToIso (connectedCW≃SphereBouquet n X cwX))
        (isConnectedSubtr' n 2 isConnectedSphereBouquet')

    lem : ∃[ x ∈ X₂₊ₙ ]
          (((a : Fin (card Xˢᵏᵉˡ (suc (suc n))))
         → x ≡ α Xˢᵏᵉˡ (suc (suc n)) (a , ptSn (suc n)))
         × (fst (connectedCW≃SphereBouquet n X cwX) x ≡ inl tt))
    lem = TR.rec (isProp→isSet squash₁)
      (λ x₀ → TR.rec squash₁
        (λ pts → TR.rec squash₁ (λ F → ∣ x₀ , F , pts ∣₁)
          (invEq (_ , InductiveFinSatAC 1 (card Xˢᵏᵉˡ (suc (suc n))) _)
                λ a → isConnectedPath 1 isConX₂₊ₙ _ _ .fst))
        (isConnectedPath 1 (isConnectedSubtr' n 2 isConnectedSphereBouquet')
          (fst (connectedCW≃SphereBouquet n X cwX) x₀) (inl tt) .fst))
      (fst isConX₂₊ₙ)

    module _ (x : X₂₊ₙ)
             (pts : ((a : Fin (card Xˢᵏᵉˡ (suc (suc n))))
                  → x ≡ α Xˢᵏᵉˡ (suc (suc n)) (a , ptSn (suc n))))
             (ptd : fst (connectedCW≃SphereBouquet n X cwX) x ≡ inl tt) where
      α' : SphereBouquet (suc n) (Fin (card Xˢᵏᵉˡ (suc (suc n)))) → X₂₊ₙ
      α' (inl tt) = x
      α' (inr x) = α Xˢᵏᵉˡ (suc (suc n)) x
      α' (push a i) = pts a i

      ≃∘α' : SphereBouquet∙ (suc n) (Fin (card Xˢᵏᵉˡ (suc (suc n))))
       →∙ SphereBouquet∙ (suc n) (Fin (card Xˢᵏᵉˡ (suc n)))
      fst ≃∘α' = fst (connectedCW≃SphereBouquet n X cwX) ∘ α'
      snd ≃∘α' = ptd

      connectedCW≅CofibFinSphereBouquetMap :
        Iso X₃₊ₙ (cofib (fst ≃∘α'))
      connectedCW≅CofibFinSphereBouquetMap =
        compIso (equivToIso (compEquiv
          (e Xˢᵏᵉˡ (suc (suc n)))
          (pushoutEquiv _ _ _ _
            (idEquiv _) (connectedCW≃SphereBouquet n X cwX) (idEquiv _)
            (λ i x → fst ≃∘α' (inr x))
            (λ i x → fst x))))
        (⋁-cofib-Iso (SphereBouquet∙ (suc n) (Fin (card Xˢᵏᵉˡ (suc n)))) ≃∘α')

-- Proof that πₙ₊₂(X) is FP when X is (n+1)-connected
-- first: a proof of the result with some additional explicit assumptions
-- (which we later get for free up to propositional truncation)
module isFinitelyPresented-π'connectedCW-lemmas {ℓ : Level}
  (X : Pointed ℓ) (n : ℕ)
  (X' : isConnectedCW (1 +ℕ n) (typ X))
  (isConX' : isConnected 2 (X' .fst .fst (4 +ℕ n)))
  (x : X' .fst .fst (4 +ℕ n))
  (x≡ : X' .snd .fst (CW↪∞ (connectedCWskel→CWskel (fst X')) (4 +ℕ n) x)
          ≡ snd X)
  where
  private
    Xˢᵏᵉˡ : CWskel _
    Xˢᵏᵉˡ = connectedCWskel→CWskel (fst X')

    e∞ = X' .snd

    X₄₊ₙ∙ : Pointed _
    fst X₄₊ₙ∙ = X' .fst .fst (4 +ℕ n)
    snd X₄₊ₙ∙ = x

  firstEquiv : GroupEquiv (π'Gr (suc n) X₄₊ₙ∙) (π'Gr (suc n) X)
  firstEquiv =
     (connectedFun→π'Equiv (suc n)
       (fst e∞ ∘ CW↪∞ Xˢᵏᵉˡ (4 +ℕ n) , x≡)
       (isConnectedComp (fst e∞) (CW↪∞ Xˢᵏᵉˡ (4 +ℕ n)) _
         (isEquiv→isConnected _ (snd e∞) (4 +ℕ n))
         (isConnected-CW↪∞ (4 +ℕ n) Xˢᵏᵉˡ)))

  isFP-π'X₄₊ₙ : isFinitelyPresented (Group→AbGroup (π'Gr (suc n) X₄₊ₙ∙)
                                    (π'-comm n))
  isFP-π'X₄₊ₙ = PT.rec squash₁
    (λ {(α , e) → PT.map
      (λ pp → subst FinitePresentation
                      (cong (λ X → Group→AbGroup (π'Gr (suc n) X) (π'-comm n))
                     (ΣPathP ((sym (cong fst e)) , pp)))
                     (GrIsoPresFinitePresentation
                       (invGroupIso (π'GrLiftIso ℓ (suc n)))
                       (hasFPπ'CofibFinSphereBouquetMap α)))
      (lem α (cong fst e))})
     (connectedCW≃CofibFinSphereBouquetMap (suc n) (fst X)
        X' (subCW (4 +ℕ n) (fst X , Xˢᵏᵉˡ , invEquiv e∞) .snd))
      where
      ll = π'GrIso
      lem : (α : FinSphereBouquetMap∙
                   (card Xˢᵏᵉˡ (suc (suc (suc n)))) (card Xˢᵏᵉˡ (suc (suc n)))
                   (suc n))
             (e : fst X₄₊ₙ∙ ≡ Lift (cofib (fst α)))
        → ∥ PathP (λ i → e (~ i)) (lift (inl tt)) x ∥₁
      lem α e = TR.rec squash₁ ∣_∣₁ (isConnectedPathP _ isConX' _ _ .fst)

  isFPX : isFinitelyPresented (Group→AbGroup (π'Gr (suc n) X) (π'-comm n))
  isFPX =
    PT.map (λ fp → subst FinitePresentation (AbGroupPath _ _ .fst firstEquiv) fp)
           isFP-π'X₄₊ₙ

-- Main result
isFinitelyPresented-π'connectedCW : ∀ {ℓ} (X : Pointed ℓ)
  (cwX : isCW (fst X)) (n : ℕ) (cX : isConnected (3 +ℕ n) (typ X))
  → isFinitelyPresented (Group→AbGroup (π'Gr (suc n) X) (π'-comm n))
isFinitelyPresented-π'connectedCW X =
  PT.rec (isPropΠ2 (λ _ _ → squash₁)) λ cwX n cX →
  PT.rec squash₁ (λ a →
  PT.rec squash₁ (λ b →
  PT.rec squash₁ (λ c →
  PT.rec squash₁ (isFPX X n a b c)
    (TR.rec (isProp→isOfHLevelSuc (suc n) squash₁) ∣_∣₁
            (isConnectedPath _ cX _ _ .fst)))
    (TR.rec (isOfHLevelSuc 1 squash₁) ∣_∣₁ (b .fst)))
    ∣ connectedFunPresConnected 2
       {f = fst (snd a) ∘ CW↪∞ (connectedCWskel→CWskel (fst a)) (4 +ℕ n)}
         (isConnectedSubtr' (suc n) 2 cX)
         (isConnectedComp (fst (snd a)) _ _
           (isEquiv→isConnected _ (snd (snd a)) 2)
         λ b → isConnectedSubtr' (suc (suc n)) 2
                 ((isConnected-CW↪∞ (4 +ℕ n)
                   (connectedCWskel→CWskel (fst a))) b)) ∣₁)
    (makeConnectedCW (1 +ℕ n) cwX cX)
  where
  open isFinitelyPresented-π'connectedCW-lemmas
