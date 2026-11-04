module Cubical.Data.Rationals.Positive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.OrderedCommRing hiding (module Positive)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedField
open import Cubical.Algebra.OrderedField.Instances.Rationals

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Base as ℕ using (ℕ ; suc ; zero ; predℕ)
open import Cubical.Data.Nat.Properties as ℕ hiding (max ; min)
open import Cubical.Data.NatPlusOne using (ℕ₊₁ ; 1+_)
open import Cubical.Data.Fast.Int as ℤ using (ℤ ; pos ; negsuc)
import Cubical.Data.Fast.Int.Order as ℤ
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sum

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Rationals

open OrderedFieldReasoning ℚOrderedField
open PseudolatticeTheory ℚ≤Pseudolattice

opaque
  0<+Closed : ∀ x y → 0 < x → 0 < y → 0 < x + y
  0<+Closed = SQ.ElimProp2.go onFrac where
    open ElimProp2
    onFrac : ElimProp2 λ x y → 0 < x → 0 < y → 0 < x + y
    onFrac .fun (pos zero , _)    (pos _ , _) (pos<pos ())
    onFrac .fun (pos (suc n) , _) (pos zero , _) _ (pos<pos ())
    onFrac .fun (pos (suc n) , _) (pos (suc m) , _) _ _ = pos<pos tt
    onFrac .prop _ _ = isProp→ $ isProp→ $ isProp< 0 _

  0<·Closed : ∀ x y → 0 < x → 0 < y → 0 < x · y
  0<·Closed = SQ.ElimProp2.go onFrac where
    open ElimProp2
    onFrac : ElimProp2 λ x y → 0 < x → 0 < y → 0 < x · y
    onFrac .fun (pos zero , _)    (pos _ , _) (pos<pos ())
    onFrac .fun (pos (suc n) , _) (pos zero , _) _ (pos<pos ())
    onFrac .fun (pos (suc n) , _) (pos (suc m) , _) _ _ = pos<pos tt
    onFrac .prop _ _ = isProp→ $ isProp→ $ isProp< 0 _

open Positive ℚOrderedField 0<+Closed 0<·Closed public renaming (
    F₊ to ℚ₊ ; isSetF₊ to isSetℚ₊ ; R₊≡ to ℚ₊≡ ; ≡₊→F₊ to ≡₊→ℚ₊
  ; R₊AdditiveSemigroup to +ℚ₊Semigroup ; R₊MultiplicativeCommMonoid to ·ℚ₊CommMonoid)
open module PositiveHalvesℚ =
  PositiveHalves ℚOrderedCommRing [ 1 / 2 ] (eq/ _ _ refl) 0<+Closed 0<·Closed public

-- Natural number literals for ℚ₊

instance
  fromNatℚ₊ : HasFromNat ℚ₊
  fromNatℚ₊ = record { Constraint = λ { zero → ⊥ ; _ → Unit }
                     ; fromNat = λ { (suc n) .fst → [ pos (suc n) / 1 ]
                                   ; (suc n) .snd → pos<pos tt } }

[_/_]₊ : ℕ₊₁ → ℕ₊₁ → ℚ₊
[ 1+ n / 1+ m ]₊ = [ pos (suc n) / 1+ m ] , pos<pos tt

-- max/min over ℚ₊

max₊ : ℚ₊ → ℚ₊ → ℚ₊
fst (max₊ x y) = max (fst x) (fst y)
snd (max₊ x y) = ElimProp2.go onFrac (fst x) (fst y) (snd x) (snd y) where
  open ElimProp2
  onFrac : ElimProp2 λ a b → 0 < a → 0 < b → 0 < max a b
  onFrac .fun (pos 1+n@(suc n) , 1+ a) (pos 1+m@(suc m) , 1+ b) (pos<pos p) (pos<pos q) =
    inj (ℤ.recompute< $ subst (0 ℤ.<_)
      (sym $ cong (pos ∘ (ℕ._· 1)) $
        ℕ.maxSuc {predℕ (1+n ℕ.· suc b)} {predℕ (1+m ℕ.· suc a)})
      (ℤ.pos<pos tt))
  onFrac .prop _ _ = isProp→ $ isProp→ $ isProp< 0 _

max₊LUB< : ∀ δ η ε → δ <₊ ε → η <₊ ε → max₊ δ η <₊ ε
max₊LUB< δ η ε δ<ε η<ε = PT.rec (isProp< _ _) proof (isTotal≤ ⟨ δ ⟩₊ ⟨ η ⟩₊) where
  proof : (δ ≤₊ η) ⊎ (η ≤₊ δ) → max₊ δ η <₊ ε
  proof (inl δ≤η) = subst<L (sym (≤→∨≡Right δ≤η)) η<ε
  proof (inr η≤δ) = subst<L (sym (≥→∨≡Left  η≤δ)) δ<ε

min₊ : ℚ₊ → ℚ₊ → ℚ₊
fst (min₊ x y) = min (fst x) (fst y)
snd (min₊ x y) = ElimProp2.go onFrac (fst x) (fst y) (snd x) (snd y) where
  open ElimProp2
  onFrac : ElimProp2 λ a b → 0 < a → 0 < b → 0 < min a b
  onFrac .fun (pos 1+n@(suc n) , 1+ a) (pos 1+m@(suc m) , 1+ b) (pos<pos p) (pos<pos q) =
    inj (ℤ.recompute< $ subst (0 ℤ.<_)
      (sym $ cong (pos ∘ (ℕ._· 1)) $
        ℕ.minSuc {predℕ (1+n ℕ.· suc b)} {predℕ (1+m ℕ.· suc a)})
      (ℤ.pos<pos tt))
  onFrac .prop _ _ = isProp→ $ isProp→ $ isProp< 0 _

min₊≤L : ∀ ε δ → min₊ ε δ ≤₊ ε
min₊≤L ε δ = min≤ ⟨ ε ⟩₊ ⟨ δ ⟩₊

min₊≤R : ∀ ε δ → min₊ ε δ ≤₊ δ
min₊≤R ε δ = subst≤L (ℚ.minComm ⟨ δ ⟩₊ ⟨ ε ⟩₊) (min≤ ⟨ δ ⟩₊ ⟨ ε ⟩₊)

min/2₊<L : ∀ ε δ → (min₊ ε δ /2₊) <₊ ε
min/2₊<L ε δ = begin<
  ⟨ min₊ ε δ /2₊ ⟩₊ <⟨ /2₊<id (min₊ ε δ) ⟩
  ⟨ min₊ ε δ ⟩₊     ≤⟨ min₊≤L ε δ ⟩
  ⟨ ε ⟩₊            ◾

min/2₊<R : ∀ ε δ → (min₊ ε δ /2₊) <₊ δ
min/2₊<R ε δ = begin<
  ⟨ min₊ ε δ /2₊ ⟩₊ <⟨ /2₊<id (min₊ ε δ) ⟩
  ⟨ min₊ ε δ ⟩₊     ≤⟨ min₊≤R ε δ ⟩
  ⟨ δ ⟩₊            ◾
