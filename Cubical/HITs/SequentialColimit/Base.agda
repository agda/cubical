{-# OPTIONS --safe --lossy-unification #-}
module Cubical.HITs.SequentialColimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties


private
  variable
    ℓ ℓ' : Level

open Sequence

data SeqColim (X : Sequence ℓ) : Type ℓ where
  incl : {n : ℕ} → X .obj n → SeqColim X
  push : {n : ℕ} (x : X .obj n) → incl x ≡ incl (X .map x)

data FinSeqColim (m : ℕ) (X : Sequence ℓ) : Type ℓ where
  fincl : (n : Fin (suc m)) → X .obj (fst n) → FinSeqColim m X
  fpush : (n : Fin m) (x : X .obj (fst n))
    → fincl (injectSuc n) x ≡ fincl (fsuc n) (X .map x)

FinSeqColim→Colim : (m : ℕ) {X : Sequence ℓ} → FinSeqColim m X → SeqColim X
FinSeqColim→Colim m (fincl n x) = incl x
FinSeqColim→Colim m (fpush n x i) = push x i

realiseSequenceMap : {C : Sequence ℓ} {D : Sequence ℓ'}
  → SequenceMap C D → SeqColim C → SeqColim D
realiseSequenceMap record { map = map ; comm = comm } (incl x) = incl (map _ x)
realiseSequenceMap record { map = map ; comm = comm } (push {n = n} x i) =
  (push (map n x) ∙ λ i → incl (comm n x i)) i



open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence




open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws



open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Sum hiding (map)


-- colim (X₀ → ... → Xₙ) ≃ colim (X₁ → ... → Xₙ)

module _ (X : Sequence ℓ) where
  ShiftSeq : Sequence ℓ
  obj ShiftSeq m = obj X (suc m)
  map ShiftSeq = map X

  Iso-FinSeqColim→FinSeqColim↑ : (m : ℕ)
     → Iso (FinSeqColim (suc m) X) (FinSeqColim m ShiftSeq)
  Iso-FinSeqColim→FinSeqColim↑ m = iso (G m) (F m) (F→G→F m) (G→F→G m)
    where
    F : (m : ℕ) → FinSeqColim m ShiftSeq → FinSeqColim (suc m) X
    F m (fincl n x) = fincl (fsuc n) x
    F (suc m) (fpush (n , p) x i) = fpush (suc n , p) x i

    G : (m : ℕ) → FinSeqColim (suc m) X → FinSeqColim m ShiftSeq
    G m (fincl (zero , p) x) = fincl (zero , p) (map X x)
    G m (fincl (suc n , p) x) = fincl (n , p) x
    G m (fpush (zero , p) x i) = fincl (zero , p) (map X x)
    G (suc m) (fpush (suc n , p) x i) = fpush (n , p) x i

    F→G→F : (m : ℕ) → (x : FinSeqColim m ShiftSeq) → G m (F m x) ≡ x
    F→G→F m (fincl n x) = refl
    F→G→F (suc m) (fpush n x i) = refl

    G→F→G : (m : ℕ) → (x : FinSeqColim (suc m) X) → F m (G m x) ≡ x
    G→F→G m (fincl (zero , p) x) = sym (fpush (zero , p) x)
    G→F→G m (fincl (suc n , p) x) = refl
    G→F→G m (fpush (zero , p) x i) j = fpush (zero , p) x (~ j ∨ i)
    G→F→G (suc m) (fpush (suc n , p) x i) = refl

  Iso-FinSeqColim₀-Top : Iso (FinSeqColim 0 X) (obj X zero)
  Iso.fun Iso-FinSeqColim₀-Top (fincl (zero , p) x) = x
  Iso.inv Iso-FinSeqColim₀-Top a = fincl fzero a
  Iso.rightInv Iso-FinSeqColim₀-Top a = refl
  Iso.leftInv Iso-FinSeqColim₀-Top (fincl (zero , p) x) = refl

pre-Iso-FinSeqColim-Top : (X : Sequence ℓ) (m : ℕ)
  → Iso (FinSeqColim m X) (obj X m)
pre-Iso-FinSeqColim-Top X zero = Iso-FinSeqColim₀-Top X
pre-Iso-FinSeqColim-Top X (suc m) =
  compIso (Iso-FinSeqColim→FinSeqColim↑ X m)
          (pre-Iso-FinSeqColim-Top (ShiftSeq X) m)

characInverse : (X : Sequence ℓ) (m : ℕ) (a : obj X m)
  → Iso.inv (pre-Iso-FinSeqColim-Top X m) a ≡ fincl flast a
characInverse X zero a = refl
characInverse X (suc m) a =
  cong (Iso.inv (Iso-FinSeqColim→FinSeqColim↑ X m)) (characInverse _ m a)

-- main result
Iso-FinSeqColim-Top : (X : Sequence ℓ) (m : ℕ)
  → Iso (FinSeqColim m X) (obj X m)
Iso.fun (Iso-FinSeqColim-Top X m) = Iso.fun (pre-Iso-FinSeqColim-Top X m)
Iso.inv (Iso-FinSeqColim-Top X m) = fincl flast
Iso.rightInv (Iso-FinSeqColim-Top X m) r =
  cong (Iso.fun (pre-Iso-FinSeqColim-Top X m)) (sym (characInverse X m r))
  ∙ Iso.rightInv (pre-Iso-FinSeqColim-Top X m) r
Iso.leftInv (Iso-FinSeqColim-Top X m) r =
    sym (characInverse X m (Iso.fun (pre-Iso-FinSeqColim-Top X m) r))
  ∙ Iso.leftInv (pre-Iso-FinSeqColim-Top X m) r

  -- main corollary : given two maps (f g : SeqColim Xᵢ → B) and a
  -- family of homotopies hᵢ : (x : Xᵢ) → f (incl x) ≡ g (incl x) for
  -- i < n, we can improve hᵢ such that they are compatible with push

→FinSeqColimHomotopy : ∀ {ℓ ℓ'}
  {X : Sequence ℓ} {m : ℕ} {B : FinSeqColim m X → Type ℓ'}
  (f g : (x : FinSeqColim m X) → B x)
  (h : (x : obj X m) → f (fincl flast x)
                      ≡ g (fincl flast x))
  → f ≡ g
→FinSeqColimHomotopy {X = X} {m} f g h = funExt
  (transport (λ i → (x : isoToPath (invIso (Iso-FinSeqColim-Top X m)) i)
    → f (ua-unglue (isoToEquiv (invIso (Iso-FinSeqColim-Top X m))) i x)
     ≡ g (ua-unglue (isoToEquiv (invIso (Iso-FinSeqColim-Top X m))) i x)) h)
