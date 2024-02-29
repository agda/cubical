{-# OPTIONS --safe --lossy-unification #-}
module Cubical.HITs.SequentialColimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence
open import Cubical.Data.Fin


private
  variable
    ℓ ℓ' : Level

open Sequence

data SeqColim (X : Sequence ℓ) : Type ℓ where
  incl : {n : ℕ} → X .obj n → SeqColim X
  push : {n : ℕ} (x : X .obj n) → incl x ≡ incl (X .map x)

data FinSeqColim (m : ℕ) (X : Sequence ℓ) : Type ℓ where
  fincl : {n : Fin (suc m)} → X .obj (fst n) → FinSeqColim m X
  fpush : {n : Fin m} (x : X .obj (fst n))
    → fincl {n = injectSuc n} x ≡ fincl {n = fsuc n} (X .map x)

FinSeqColim→Colim : (m : ℕ) {X : Sequence ℓ} → FinSeqColim m X → SeqColim X
FinSeqColim→Colim m (fincl x) = incl x
FinSeqColim→Colim m (fpush x i) = push x i

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

  -- technical lemmas all concerning the proof irrelevance of the
  -- second field of Fin n.
  private
    ineq-lem₁ : {n m : ℕ} (p : n < m) → suc-≤-suc (snd (injectSuc (n , p)))
                                  ≡ <-trans (snd (fsuc (n , p))) (0 , refl)
    ineq-lem₁ p = isProp≤ _ _

    ineq-lem₂ : {m  : ℕ} (w : zero < suc m)
      → suc-≤-suc zero-≤ ≡ predℕ-≤-predℕ (suc-≤-suc w)
    ineq-lem₂ w = isProp≤ _ _

    ineq-lem₃ : {n m : ℕ} → (w : suc n < suc m)
      → suc-≤-suc (pred-≤-pred w) ≡ pred-≤-pred (suc-≤-suc w)
    ineq-lem₃ p = isProp≤ _ _

    ineq-lem₄ : {n m : ℕ} → (w : suc n < suc m)
      → Path (n < suc m) (pred-≤-pred (<-trans w (0 , refl)))
              (<-trans (pred-≤-pred w) (0 , refl))
    ineq-lem₄ w = Σ≡Prop (λ _ → isSetℕ _ _) refl

    ineq-lem₅ : {n m : ℕ} → (w : n < m) → predℕ-≤-predℕ (suc-≤-suc w) ≡ w
    ineq-lem₅ (w , p) = Σ≡Prop (λ _ → isSetℕ _ _) refl

    ineq-lem₆ : {n : ℕ} (diff : zero < (suc (suc n)))
      → <-trans (snd fzero) (0 , refl) ≡ diff
    ineq-lem₆ diff = isProp≤ _ _

    ineq-lem₇ : {n m : ℕ} (x : suc n < suc m)
      → suc-≤-suc (predℕ-≤-predℕ x) ≡ x
    ineq-lem₇ x = isProp≤ _ _

    -- two highly technical lemmas to deal with problems arising from
    -- the second field of Fin not being a strict prop
    lem₁ : ∀ {ℓ} {A : Type ℓ}
      (n<m : Type) (w₀ : n<m) (isPr : isProp n<m)
      (n'<m' : Type) (dummy : n'<m') (isPr' : isProp n'<m')
      (n''<m'' : Type) (w' : n''<m'') (isPr'' : isProp n''<m'')
      (f1 : n'<m' → A) (f2 : n''<m'' → A)
      (n<m→n'<m' : n<m → n'<m')
      (n<m→n''<m'' : n<m → n''<m'')
      (pash : (s : n<m) → f1 (n<m→n'<m' s) ≡ f2 (n<m→n''<m'' s))
      (w : n<m) (w' : n''<m'') (r : n<m→n''<m'' w₀ ≡ w')
      (t : n<m→n'<m' w₀ ≡ n<m→n'<m' w)
      (s : w' ≡ n<m→n''<m'' w)
       → Square (cong f2 r) (pash w)
                 (sym (pash w₀) ∙ cong f1 t)
                 (cong f2 s)
    lem₁ = JPointedProp (JPointedProp (JPointedProp
      λ f1 f2 n<m→n'<m' n<m→n''<m'' pash w w' r t s
        → flipSquare ((cong (sym (pash tt*) ∙_)
                       (cong (cong f1) (isSetUnit* _ _ t refl))
                     ∙ sym (rUnit _))
                     ◁ (λ i j → pash tt* (i ∨ ~ j))
                     ▷ cong (cong f2) (isSetUnit* _ _ refl s))))

    lem₂ : ∀ {ℓ} {A : Type ℓ}
      (n<m : Type) (w₀ : n<m) (isPr : isProp n<m)
      (n'<m' : Type) (w' : n'<m') (isPr' : isProp n'<m')
      (n''<m'' : Type) (w'' : n''<m'') (isPr'' : isProp n''<m'')
      (f1 : n'<m' → A) (f2 : n''<m'' → A)
      (n<m→n'<m' : n<m → n'<m')
      (n<m→n''<m'' : n<m → n''<m'')
      (pash : (s : n<m) → f1 (n<m→n'<m' s) ≡ f2 (n<m→n''<m'' s))
      (w : n<m) (t : w' ≡ (n<m→n'<m' w))
      (s : w'' ≡ n<m→n''<m'' w) (s' : n<m→n''<m'' w₀ ≡ w'')
      (w''' : n'<m') (ts : w''' ≡ n<m→n'<m' w₀) (t' : w' ≡ w''')
       → Square (cong f1 t' ∙∙ (cong f1 ts ∙ pash w₀) ∙∙ cong f2 s')
                 (pash w)
                 (cong f1 t)
                 (cong f2 s)
    lem₂ =
      JPointedProp (JPointedProp (JPointedProp
       λ f1 f2 n<m→n'<m' n<m→n''<m'' pash w t s t' w''' ts s'
       → (sym (rUnit _) ∙ sym (lUnit _)) ◁ λ i j → pash tt* j))

  -- first direction
  FinSeqColim↑→FinSeqColim : (m : ℕ)
    → FinSeqColim m ShiftSeq → FinSeqColim (suc m) X
  FinSeqColim↑→FinSeqColim m (fincl {n = n} x) = fincl {n = fsuc n} x
  FinSeqColim↑→FinSeqColim m (fpush {n = n} x i) =
     ((λ i → fincl {n = suc (fst n) , ineq-lem₁ (snd n) i} x)
    ∙ fpush {n = fsuc n} x) i

  -- second direction
  FinSeqColim→FinSeqColim↑∘fincl-pre : (m : ℕ) (n : Fin (suc (suc m)))
    → obj X (fst n) → obj X (suc (fst (predFin m n)))
  FinSeqColim→FinSeqColim↑∘fincl-pre m (zero , w) x = map X x
  FinSeqColim→FinSeqColim↑∘fincl-pre m (suc n , w) x = x

  FinSeqColim→FinSeqColim↑∘fincl : (m : ℕ) (n : Fin (suc (suc m)))
    → obj X (fst n) → FinSeqColim m ShiftSeq
  FinSeqColim→FinSeqColim↑∘fincl m n x =
    fincl {n = predFin m n} (FinSeqColim→FinSeqColim↑∘fincl-pre m n x)

  FinSeqColim→FinSeqColim↑≡ : (m : ℕ) (n : Fin (suc m)) (x : X .obj (fst n))
    → Path (FinSeqColim m ShiftSeq)
            (fincl {n = predFin m (injectSuc n)}
              (FinSeqColim→FinSeqColim↑∘fincl-pre m (injectSuc n) x))
            (fincl {n = fst n , predℕ-≤-predℕ (suc-≤-suc (snd n))} (map X x))
  FinSeqColim→FinSeqColim↑≡ m (zero , w) x j =
    fincl {n = zero , ineq-lem₂ w j} (map X x)
  FinSeqColim→FinSeqColim↑≡ m (suc n , w) x =
    (λ i → fincl {n = n , ineq-lem₄ w i} x)
     ∙∙ fpush {n = n , predℕ-≤-predℕ w} x
     ∙∙ λ i → fincl {n = suc n , ineq-lem₃ w i} (map X x)

  FinSeqColim→FinSeqColim↑ : (m : ℕ)
    → FinSeqColim (suc m) X → FinSeqColim m ShiftSeq
  FinSeqColim→FinSeqColim↑ m (fincl {n = n} x) =
    FinSeqColim→FinSeqColim↑∘fincl m n x
  FinSeqColim→FinSeqColim↑ m (fpush {n = n} x i) =
    FinSeqColim→FinSeqColim↑≡ m n x i

  -- cancellations
  -- first direction
  FinSeqColim↑→FinSeqColim→FinSeqColim↑∘fincl :
    (m : ℕ) (n : Fin (suc m)) (x : obj X (suc (fst n)))
    → FinSeqColim→FinSeqColim↑ m (FinSeqColim↑→FinSeqColim m (fincl {n = n} x))
     ≡ fincl {n = n} x
  FinSeqColim↑→FinSeqColim→FinSeqColim↑∘fincl m (n , diff) x i =
    fincl {n = n , ineq-lem₅ diff i} x

  FinSeqColim→FinSeqColim↑→FinSeqColim∘fincl :
    (m : ℕ) (n : Fin (suc (suc m))) (x : obj X (fst n))
    → FinSeqColim↑→FinSeqColim m (FinSeqColim→FinSeqColim↑ m (fincl {n = n} x))
     ≡ fincl {n = n} x
  FinSeqColim→FinSeqColim↑→FinSeqColim∘fincl m (zero , diff) x =
    sym (fpush {n = fzero} x) ∙ λ j → fincl {n = zero , ineq-lem₆ diff j} x
  FinSeqColim→FinSeqColim↑→FinSeqColim∘fincl m (suc n , diff) x j =
    fincl {n = suc n , ineq-lem₇ diff j} x

  FinSeqColim→FinSeqColim↑→FinSeqColim : (m : ℕ) (x : FinSeqColim (suc m) X)
    → FinSeqColim↑→FinSeqColim m (FinSeqColim→FinSeqColim↑ m x) ≡ x
  FinSeqColim→FinSeqColim↑→FinSeqColim m (fincl {n = n} x) = FinSeqColim→FinSeqColim↑→FinSeqColim∘fincl m n x
  FinSeqColim→FinSeqColim↑→FinSeqColim m (fpush {n = zero , w} x i) j = lem j i
    where
    lem : Square {A = FinSeqColim (suc m) X}
                  (λ i → fincl {n = fsuc (zero , ineq-lem₂ w i)} (map X x))
                  (fpush {n = zero , w} x)
                  (sym (fpush {n = fzero} x) ∙ (λ j → fincl {n = zero , ineq-lem₆ (snd (injectSuc (zero , w))) j} x))
                  λ i → fincl {n = 1 , ineq-lem₇ (fsuc (zero , w) .snd) i} (X .map x)
    lem =  lem₁ _ _ isProp≤ _ (injectSuc (zero , w) .snd) isProp≤ _ (fsuc (zero , w) .snd) isProp≤
                   (λ w → fincl {n = zero , w} x)
                   (λ w → fincl {n = suc zero , w} (map X x))
                   (λ w → injectSuc (zero , w) .snd)
                   (λ w → fsuc (zero , w) .snd)
                   (λ w → fpush {n = zero , w} x)
                   w _ _ _ _
  FinSeqColim→FinSeqColim↑→FinSeqColim m (fpush {n = suc n , w} x i) j = lem j i
    where
    lem : Square {A = FinSeqColim (suc m) X}
                  (cong (FinSeqColim↑→FinSeqColim m) ((λ i → fincl {n = n , ineq-lem₄ w i} x)
                                            ∙∙ fpush {n = n , predℕ-≤-predℕ w} x
                                            ∙∙ λ i → fincl {n = suc n , ineq-lem₃ w i} (map X x)))
                  (fpush {n = suc n , w} x)
                  (λ i → fincl {n = suc n , ineq-lem₇ (injectSuc (suc n , w) .snd) i} x)
                  (λ i → fincl {n = suc (suc n) , ineq-lem₇ (fsuc (suc n , w) .snd) i} (X .map x))
    lem =  (cong-∙∙ (FinSeqColim↑→FinSeqColim m)
                    (λ i → fincl {n = n , ineq-lem₄ w i} x)
                    (fpush {n = n , predℕ-≤-predℕ w} x)
                    (λ i → fincl {n = suc n , ineq-lem₃ w i} (map X x)))
          ◁ lem₂ _ _ isProp≤
                    _ _ isProp≤
                    _ _ isProp≤
                    (λ w → fincl {n = suc n , w} x)
                    (λ w → fincl {n = suc (suc n) , w} (map X x))
                    (λ w → (injectSuc (suc n , w)) .snd)
                    (λ w → (fsuc (suc n , w)) .snd)
                    (λ w → fpush {n = suc n , w} x)
                    _ _ _ _ _ _ _

  -- other direction
  FinSeqColim↑→FinSeqColim→FinSeqColim↑ :
    (m : ℕ) (x : FinSeqColim m ShiftSeq)
    → FinSeqColim→FinSeqColim↑ m (FinSeqColim↑→FinSeqColim m x) ≡ x
  FinSeqColim↑→FinSeqColim→FinSeqColim↑ m (fincl x) =
    FinSeqColim↑→FinSeqColim→FinSeqColim↑∘fincl m _ x
  FinSeqColim↑→FinSeqColim→FinSeqColim↑ m (fpush {n = n , w} x i) j = main j i
    where
    sq1 : Square (cong suc-≤-suc (ineq-lem₅ w) ) refl
                 (ineq-lem₃ (suc-≤-suc w))
                 (sym (ineq-lem₅ (suc-≤-suc w)))
    sq1 = isProp→PathP (λ _ → isProp→isSet isProp≤ _ _) _ _

    sq2 : Square (ineq-lem₄ (suc-≤-suc w)) (ineq-lem₅ (<-trans w (0 , refl)))
                 (sym (cong predℕ-≤-predℕ (ineq-lem₁ w)))
                 λ i → <-trans (ineq-lem₅ w i) (0 , (λ _ → suc m))
    sq2 = isProp→PathP (λ _ → isProp→isSet isProp≤ _ _) _ _

    main : Square {A = FinSeqColim m ShiftSeq}
      (cong (FinSeqColim→FinSeqColim↑ m) (((λ i → fincl {n = suc n , ineq-lem₁ w i} x)
                          ∙ fpush {n = fsuc (n , w)} x)))
      (fpush {n = n , w} x)
      (λ j → fincl {n = n , ineq-lem₅ (<-trans w (0 , refl)) j} x)
      λ j → fincl {n = suc n , ineq-lem₅ (suc-≤-suc w) j} (map X x)
    main = (cong-∙ (FinSeqColim→FinSeqColim↑ m)
                   (λ i → fincl {X = X} {n = suc n , ineq-lem₁ w i} x)
                   (fpush {X = X} {n = fsuc (n , w)} x)
         ∙ ((λ s → (λ j → fincl {X = ShiftSeq} {n = n , predℕ-≤-predℕ (ineq-lem₁ w (j ∧ ~ s))} x)
                  ∙ ((λ j → fincl {X = ShiftSeq} {n = n , sq2 s j} x)
                  ∙∙ fpush {X = ShiftSeq} {n = n , ineq-lem₅ {n = n} {m = m} w s} x
                  ∙∙ λ i → fincl {X = ShiftSeq} {n = suc n , sq1 i s} (map X x))))
         ∙ sym (lUnit _))
         ◁ symP (doubleCompPath-filler
             ((λ j → fincl {n = n , ineq-lem₅ (snd (injectSuc (n , w))) j} x))
             (fpush {n = n , w} x)
             (λ j → fincl {n = suc n , ineq-lem₅ (suc-≤-suc w) (~ j)} (map X x)))

  -- main result
  Iso-FinSeqColim→FinSeqColim↑ : (m : ℕ)
    → Iso (FinSeqColim (suc m) X) (FinSeqColim m ShiftSeq)
  Iso.fun (Iso-FinSeqColim→FinSeqColim↑ m) = FinSeqColim→FinSeqColim↑ m
  Iso.inv (Iso-FinSeqColim→FinSeqColim↑ m) = FinSeqColim↑→FinSeqColim m
  Iso.rightInv (Iso-FinSeqColim→FinSeqColim↑ m) =
    FinSeqColim↑→FinSeqColim→FinSeqColim↑ m
  Iso.leftInv (Iso-FinSeqColim→FinSeqColim↑ m) =
    FinSeqColim→FinSeqColim↑→FinSeqColim m

elimFinColim : ∀ {ℓ ℓ'} {X : Sequence ℓ} {m : ℕ} {B : FinSeqColim m X → Type ℓ'}
  → (incl : (n : Fin (suc m)) (x : obj X (fst n)) → B (fincl {n = n} x))
  → ((n : Fin m) (x : obj X (fst n))
        → PathP (λ i → B (fpush {n = n} x i))
                (incl (injectSuc n) x) (incl (fsuc n) (map X x)))
  → (x : _) → B x
elimFinColim incl* push* (fincl x) = incl* _ x
elimFinColim incl* push* (fpush {n = n} x i) = push* n x i

module _ (X : Sequence ℓ) where

  private
    FinSeqColim₀→Top∘ficnl : (n : Fin 1) (x : obj X (fst n)) → obj X zero
    FinSeqColim₀→Top∘ficnl (zero , w) x = x
    FinSeqColim₀→Top∘ficnl (suc n , w) x =
      ⊥.rec (snotz (sym (+-suc (fst w) n)
                  ∙ cong predℕ (sym (+-suc (fst w) (suc n))
                               ∙ snd w)))

  Iso-FinSeqColim₀-Top : Iso (FinSeqColim 0 X) (obj X zero)
  Iso.fun Iso-FinSeqColim₀-Top =
    elimFinColim FinSeqColim₀→Top∘ficnl (λ x → ⊥.rec (¬Fin0 x))
  Iso.inv Iso-FinSeqColim₀-Top a = fincl {n = fzero} a
  Iso.rightInv Iso-FinSeqColim₀-Top a = refl
  Iso.leftInv Iso-FinSeqColim₀-Top =
    elimFinColim
      (λ { (zero , w) x i → fincl {n = zero , isProp≤ (suc-≤-suc zero-≤) w i} x
        ; (suc n , w) → ⊥.rec (snotz (sym (+-suc (fst w) n)
                  ∙ cong predℕ (sym (+-suc (fst w) (suc n))
                               ∙ snd w)))})
        λ x → ⊥.rec (¬Fin0 x)

private
  pre-Iso-FinSeqColim-Top : (X : Sequence ℓ) (m : ℕ)
    → Iso (FinSeqColim m X) (obj X m)
  pre-Iso-FinSeqColim-Top X zero = Iso-FinSeqColim₀-Top X
  pre-Iso-FinSeqColim-Top X (suc m) =
    compIso (Iso-FinSeqColim→FinSeqColim↑ X m)
            (pre-Iso-FinSeqColim-Top (ShiftSeq X) m)

  characInverse : (X : Sequence ℓ) (m : ℕ) (a : obj X m)
    → Iso.inv (pre-Iso-FinSeqColim-Top X m) a ≡ fincl {n = flast} a
  characInverse X zero a = refl
  characInverse X (suc m) a =
    cong (FinSeqColim↑→FinSeqColim X m) (characInverse _ m a)
    ∙ λ i → fincl {n = suc m
                  , isProp≤ (suc-≤-suc (snd flast)) (suc-≤-suc ≤-refl) i} a

  -- main result
  Iso-FinSeqColim-Top : (X : Sequence ℓ) (m : ℕ)
    → Iso (FinSeqColim m X) (obj X m)
  Iso.fun (Iso-FinSeqColim-Top X m) = Iso.fun (pre-Iso-FinSeqColim-Top X m)
  Iso.inv (Iso-FinSeqColim-Top X m) = fincl {n = flast}
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
  (h : (x : obj X m) → f (fincl {n = flast} x)
                      ≡ g (fincl {n = flast} x))
  → f ≡ g
→FinSeqColimHomotopy {X = X} {m} f g h = funExt
  (transport (λ i → (x : isoToPath (invIso (Iso-FinSeqColim-Top X m)) i)
    → f (ua-unglue (isoToEquiv (invIso (Iso-FinSeqColim-Top X m))) i x)
     ≡ g (ua-unglue (isoToEquiv (invIso (Iso-FinSeqColim-Top X m))) i x)) h)
