{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude

module Cubical.Data.DescendingList.Strict.Properties
 (A : Type₀)
 (_>_ : A → A → Type₀)
 where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.DescendingList.Strict A _>_
open import Cubical.HITs.ListedFiniteSet as LFSet renaming (_∈_ to _∈ʰ_)

import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.Relation.Nullary using (Dec; Discrete) renaming (¬_ to Type¬_)

unsort : SDL → LFSet A
unsort [] = []
unsort (cons x xs x>xs) = x ∷ unsort xs

module _ where
  open import Cubical.Relation.Nullary
  data Tri (A B C : Type) : Type where
    tri-< : A → ¬ B → ¬ C → Tri A B C
    tri-≡ : ¬ A → B → ¬ C → Tri A B C
    tri-> : ¬ A → ¬ B → C → Tri A B C

module IsoToLFSet
   (A-discrete : Discrete A)
   (>-isProp : ∀ {x y} → isProp (x > y))
   (tri : ∀ x y → Tri (y > x) (x ≡ y) (x > y))
   (>-trans : ∀ {x y z} → x > y → y > z → x > z)
   (>-irreflexive : ∀ {x} → Type¬ x > x)
  where

  Tri' : A → A → Type
  Tri' x y = Tri (y > x) (x ≡ y) (x > y)

  open import Cubical.HITs.PropositionalTruncation as PropTrunc
  open import Cubical.Functions.Logic

  -- Membership is defined via `LFSet`.
  -- This computes just as well as a direct inductive definition,
  -- and additionally lets us use the extra `comm` and `dup` paths to prove
  -- things about membership.
  _∈ˡ_ : A → SDL → hProp ℓ-zero
  a ∈ˡ l = a ∈ʰ unsort l

  Memˡ : SDL → A → hProp ℓ-zero
  Memˡ l a = a ∈ˡ l

  Memʰ : LFSet A → A → hProp ℓ-zero
  Memʰ l a = a ∈ʰ l

  >ᴴ-trans : ∀ x y zs → x > y → y >ᴴ zs → x >ᴴ zs
  >ᴴ-trans x y [] x>y y>zs = >ᴴ[]
  >ᴴ-trans x y (cons z zs _) x>y (>ᴴcons y>z) = >ᴴcons (>-trans x>y y>z)

  ≡ₚ-sym : ∀ {A : Type} {x y : A} → ⟨ x ≡ₚ y ⟩ → ⟨ y ≡ₚ x ⟩
  ≡ₚ-sym p = PropTrunc.rec squash (λ p → ∣ sym p ∣) p

  >-all : ∀ x l → x >ᴴ l → ∀ a → ⟨ a ∈ˡ l ⟩ → x > a
  >-all x (cons y zs y>zs) (>ᴴcons x>y) a a∈l =
     ⊔-elim (a ≡ₚ y) (a ∈ˡ zs) (λ _ → (x > a) , >-isProp {x} {a})
       (λ a≡ₚy → substₚ (λ q → x > q , >-isProp) (≡ₚ-sym a≡ₚy) x>y)
       (λ a∈zs → >-all x zs (>ᴴ-trans x y zs x>y y>zs) a a∈zs)
       a∈l

  >-absent : ∀ x l → x >ᴴ l → ⟨ ¬ (x ∈ˡ l) ⟩
  >-absent x l x>l x∈l = ⊥.rec (>-irreflexive (>-all x l x>l x x∈l))

  >ᴴ-isProp : ∀ x xs → isProp (x >ᴴ xs)
  >ᴴ-isProp x _ >ᴴ[] >ᴴ[] = refl
  >ᴴ-isProp x _ (>ᴴcons p) (>ᴴcons q) = cong >ᴴcons (>-isProp p q)

  SDL-isSet : isSet SDL
  SDL-isSet = isSetDL.isSetDL A _>_ >-isProp A-discrete where
    open import Cubical.Data.DescendingList.Properties

  insert : A → SDL → SDL
  >ᴴinsert : {x y : A} {u : SDL} → y >ᴴ u → (y > x) → y >ᴴ insert x u
  insert x [] = cons x [] >ᴴ[]
  insert x (cons y zs good) with tri x y
  insert x (cons y zs good) | tri-< x<y _ _ = cons y (insert x zs) (>ᴴinsert good x<y)
  insert x (cons y zs good) | tri-≡ _ x≡y _ = cons y zs good
  insert x (cons y zs good) | tri-> _ _ x>y = cons x (cons y zs good) (>ᴴcons x>y)
  >ᴴinsert >ᴴ[] y>x = >ᴴcons y>x
  >ᴴinsert {x} (>ᴴcons {y} y>ys) y>x with tri x y
  >ᴴinsert {x} {y} (>ᴴcons {z} z>zs) y>x | tri-< _ _ e = >ᴴcons z>zs
  >ᴴinsert {x} (>ᴴcons {y} y>ys) y>x | tri-≡ _ _ e = >ᴴcons y>ys
  >ᴴinsert {x} (>ᴴcons {y} y>ys) y>x | tri-> _ _ _ = >ᴴcons y>x

  insert-correct : ∀ x ys → unsort (insert x ys) ≡ (x ∷ unsort ys)
  insert-correct x [] = refl
  insert-correct x (cons y zs y>zs) with tri x y
  ... | tri-< _ _ _ =
    y ∷ unsort (insert x zs) ≡⟨ (λ i → y ∷ (insert-correct x zs i)) ⟩
    y ∷ x ∷ unsort zs ≡⟨ comm _ _ _ ⟩
    x ∷ y ∷ unsort zs ∎
  ... | tri-≡ _ x≡y _ = sym (dup y (unsort zs)) ∙ (λ i → (x≡y (~ i)) ∷ y ∷ unsort zs)
  ... | tri-> _ _ _ = refl

  insert-correct₂ : ∀ x y zs → unsort (insert x (insert y zs)) ≡ (x ∷ y ∷ unsort zs)
  insert-correct₂ x y zs =
    insert-correct x (insert y zs)
    ∙ cong (λ q → x ∷ q) (insert-correct y zs)

  abstract
    -- for some reason, making [exclude] non-abstract makes
    -- typechecking noticeably slower
    exclude : A → (A → hProp ℓ-zero) → (A → hProp ℓ-zero)
    exclude x h a = ¬ a ≡ₚ x ⊓ h a

    >-excluded : ∀ x xs → x >ᴴ xs → exclude x (Memʰ (x ∷ unsort xs)) ≡ Memˡ xs
    >-excluded x xs x>xs = funExt (λ a → ⇔toPath (to a) (from a)) where

     import Cubical.Data.Sigma as D
     import Cubical.Data.Sum   as D

     from : ∀ a → ⟨ a ∈ˡ xs ⟩ → ⟨ ¬ a ≡ₚ x ⊓ (a ≡ₚ x ⊔ a ∈ˡ xs) ⟩
     from a a∈xs = (PropTrunc.rec (snd ⊥) a≢x) D., inr a∈xs where
       a≢x : Type¬ (a ≡ x)
       a≢x = λ a≡x → (>-absent x xs x>xs (transport (λ i → ⟨ a≡x i ∈ˡ xs ⟩) a∈xs ))

     to : ∀ a → ⟨ ¬ a ≡ₚ x ⊓ (a ≡ₚ x ⊔ a ∈ˡ xs) ⟩ → ⟨ a ∈ˡ xs ⟩
     to a (a≢x D., x) = PropTrunc.rec (snd (a ∈ˡ xs)) (λ {
       (D.inl a≡x) → ⊥.rec (a≢x a≡x);
       (D.inr x) → x }) x

  cons-eq : ∀ x xs x>xs y ys y>ys → x ≡ y → xs ≡ ys → cons x xs x>xs ≡ cons y ys y>ys
  cons-eq x xs x>xs y ys y>ys x≡y xs≡ys i = cons (x≡y i) (xs≡ys i)
    (>ᴴ-isProp (x≡y i) (xs≡ys i)
           (transp (λ j → (x≡y (i ∧ j)) >ᴴ (xs≡ys) (i ∧ j)) (~ i) x>xs)
           (transp (λ j → (x≡y (i ∨ ~ j)) >ᴴ (xs≡ys) (i ∨ ~ j)) i y>ys)
           i)

  Memˡ-inj-cons : ∀ x xs x>xs y ys y>ys → x ≡ y → Memˡ (cons x xs x>xs) ≡ Memˡ (cons y ys y>ys) → Memˡ xs ≡ Memˡ ys
  Memˡ-inj-cons x xs x>xs y ys y>ys x≡y e =
         Memˡ xs ≡⟨
           sym (>-excluded x xs x>xs)
         ⟩ exclude x (Memʰ (x ∷ unsort xs)) ≡⟨
           (λ i → exclude (x≡y i) (e i))
         ⟩ exclude y (Memʰ (y ∷ unsort ys)) ≡⟨
           (>-excluded y ys y>ys)
         ⟩ Memˡ ys ∎

  Memˡ-inj : ∀ l₁ l₂ → Memˡ l₁ ≡ Memˡ l₂ → l₁ ≡ l₂
  Memˡ-inj [] [] eq = refl
  Memˡ-inj [] (cons y ys y>ys) eq = ⊥.rec (lower (transport (λ i → ⟨ eq (~ i) y ⟩) (inl ∣ refl ∣)))
  Memˡ-inj (cons y ys y>ys) [] eq = ⊥.rec (lower (transport (λ i → ⟨ eq i y ⟩) (inl ∣ refl ∣)))
  Memˡ-inj (cons x xs x>xs) (cons y ys y>ys) e =
     ⊔-elim (x ≡ₚ y) (x ∈ʰ unsort ys)
       (λ _ → ((cons x xs x>xs) ≡ (cons y ys y>ys)) , SDL-isSet _ _)
       (PropTrunc.rec (SDL-isSet _ _) with-x≡y)
       (⊥.rec ∘ x∉ys)
       (transport (λ i → ⟨ e i x ⟩) (inl ∣ refl ∣)) where

    xxs = cons x xs x>xs

    x∉ys : ⟨ ¬ x ∈ˡ ys ⟩
    x∉ys x∈ys = ⊥.rec (>-irreflexive y>y) where
        y>x : y > x
        y>x = (>-all y ys y>ys x x∈ys)

        y∈xxs : ⟨ y ∈ˡ (cons x xs x>xs) ⟩
        y∈xxs = (transport (λ i → ⟨ e (~ i) y ⟩) (inl ∣ refl ∣))

        y>y : y > y
        y>y = >-all y xxs (>ᴴcons y>x) y y∈xxs

    with-x≡y : x ≡ y → (cons x xs x>xs) ≡ (cons y ys y>ys)
    with-x≡y x≡y = cons-eq x xs x>xs y ys y>ys x≡y r where

      r : xs ≡ ys
      r = Memˡ-inj _ _ (Memˡ-inj-cons x xs x>xs y ys y>ys x≡y e)

  unsort-inj : ∀ x y → unsort x ≡ unsort y → x ≡ y
  unsort-inj x y e = Memˡ-inj x y λ i a → a ∈ʰ (e i)

  insert-swap : (x y : A) (zs : SDL) → insert x (insert y zs) ≡ insert y (insert x zs)
  insert-swap x y zs =
    unsort-inj (insert x (insert y zs)) (insert y (insert x zs))
      (unsort (insert x (insert y zs))
        ≡⟨ (λ i → insert-correct₂ x y zs i) ⟩
      x ∷ y ∷ unsort zs
        ≡⟨ (λ i → comm x y (unsort zs) i) ⟩
      y ∷ x ∷ unsort zs
        ≡⟨ (λ i → insert-correct₂ y x zs (~ i)) ⟩
      unsort (insert y (insert x zs)) ∎)

  insert-dup : (x : A) (ys : SDL) → insert x (insert x ys) ≡ insert x ys
  insert-dup x ys = unsort-inj (insert x (insert x ys)) (insert x ys)
    (
      unsort (insert x (insert x ys))
        ≡⟨ (λ i → insert-correct₂ x x ys i) ⟩
      x ∷ x ∷ unsort ys
        ≡⟨ dup x (unsort ys) ⟩
      x ∷ unsort ys
        ≡⟨ (λ i → insert-correct x ys (~ i)) ⟩
      unsort (insert x ys) ∎
    )

  sort : LFSet A → SDL
  sort = LFSet.Rec.f [] insert insert-swap insert-dup SDL-isSet

  unsort∘sort : ∀ x → unsort (sort x) ≡ x
  unsort∘sort =
     LFSet.PropElim.f
       refl
       (λ x {ys} ys-hyp → insert-correct x (sort ys) ∙ cong (λ q → x ∷ q) ys-hyp)
       (λ xs → trunc (unsort (sort xs)) xs)

  sort∘unsort : ∀ x → sort (unsort x) ≡ x
  sort∘unsort x = unsort-inj (sort (unsort x)) x (unsort∘sort (unsort x))

  SDL-LFSet-iso : Iso SDL (LFSet A)
  SDL-LFSet-iso = (iso unsort sort unsort∘sort sort∘unsort)

  SDL≡LFSet : SDL ≡ LFSet A
  SDL≡LFSet = ua (isoToEquiv SDL-LFSet-iso)
