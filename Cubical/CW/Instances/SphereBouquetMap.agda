{-
File contains : a direct description of cell structure for the
cofibre of a map α : ⋁ₐ Sⁿ → ⋁ₑ Sⁿ (with a and e finite sets)
-}

module Cubical.CW.Instances.SphereBouquetMap where

open import Cubical.CW.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Wedge

open import Cubical.Relation.Nullary

-- Explicit definition of CW structure on the cofibre of a map of
-- (finite) sphere bouquets
module _ (c1 c2 : ℕ) {n : ℕ} where
  SphereBouquet/FamGen : (α : FinSphereBouquetMap c1 c2 n)
    → (m : ℕ) → Trichotomyᵗ m (suc (suc n)) → Type
  SphereBouquet/FamGen a zero p = ⊥
  SphereBouquet/FamGen a (suc m) (lt x) = Unit
  SphereBouquet/FamGen  a (suc m) (eq x) = SphereBouquet (suc n) (Fin c2)
  SphereBouquet/FamGen a (suc m) (gt x) = cofib a

  SphereBouquet/CardGen : (m : ℕ)
    → Trichotomyᵗ m (suc n) → Trichotomyᵗ m (suc (suc n)) → ℕ
  SphereBouquet/CardGen zero p q = 1
  SphereBouquet/CardGen (suc m) (lt x) q = 0
  SphereBouquet/CardGen (suc m) (eq x) q = c2
  SphereBouquet/CardGen (suc m) (gt x) (lt y) = 0
  SphereBouquet/CardGen (suc m) (gt x) (eq y) = c1
  SphereBouquet/CardGen (suc m) (gt x) (gt y) = 0

  SphereBouquet/αGen : (α : FinSphereBouquetMap c1 c2 n) (m : ℕ)
    (p : Trichotomyᵗ m (suc n)) (q : Trichotomyᵗ m (suc (suc n)))
    → Fin (SphereBouquet/CardGen m p q) × S⁻ m → SphereBouquet/FamGen α m q
  SphereBouquet/αGen a (suc m) p (lt y) x = tt
  SphereBouquet/αGen a (suc m) (eq x₂) (eq y) x = inl tt
  SphereBouquet/αGen a (suc m) (gt x₂) (eq y) x =
    a (inr (fst x , subst S₊ (cong predℕ y) (snd x)))
  SphereBouquet/αGen a (suc m) p (gt y) x = inl tt

  SphereBouquet/EqContrGen : (α : FinSphereBouquetMap c1 c2 n)
    (m : ℕ) (m< : m <ᵗ suc n)
    (p : Trichotomyᵗ m (suc n)) (q : Trichotomyᵗ m (suc (suc n)))
    → isContr (Pushout (SphereBouquet/αGen α m p q) fst)
  SphereBouquet/EqContrGen a zero m< (lt x) (lt y) =
    (inr fzero) , λ { (inr (zero , tt)) → refl}
  SphereBouquet/EqContrGen a zero m< (lt x) (eq y) = ⊥.rec (snotz (sym y))
  SphereBouquet/EqContrGen a zero m< (eq x) q = ⊥.rec (snotz (sym x))
  SphereBouquet/EqContrGen a (suc m) m< (lt y) (lt x) =
    (inl tt) , (λ {(inl tt) → refl})
  SphereBouquet/EqContrGen a (suc m) m< (eq y) (lt x) =
    ⊥.rec (¬m<ᵗm {suc n} (subst (_<ᵗ suc n) y m<))
  SphereBouquet/EqContrGen a (suc m) m< (gt y) (lt x) =
    ⊥.rec (¬m<ᵗm {m} (<ᵗ-trans {m} {n} {m} m< y))
  SphereBouquet/EqContrGen a (suc m) m< p (eq x) =
    ⊥.rec (falseDichotomies.lt-eq (m< , (cong predℕ x)))
  SphereBouquet/EqContrGen a (suc m) m< p (gt x) =
    ⊥.rec (¬-suc-n<ᵗn {n} (<ᵗ-trans {suc n} {m} {n} x m<))

  SphereBouquet/EqBottomMainGen : (α : FinSphereBouquetMap c1 c2 n)
    → SphereBouquet (suc n) (Fin c2)
     ≃ cofib {A = Fin c2 × S₊ n} {B = Fin c2} fst
  SphereBouquet/EqBottomMainGen α = isoToEquiv
      (compIso (pushoutIso _ _ _ _ (idEquiv _) (idEquiv Unit)
                  (Σ-cong-equiv-snd (λ a → isoToEquiv (IsoSucSphereSusp n)))
                  refl
                  (funExt (λ a → ΣPathP (refl , IsoSucSphereSusp∙' n))))
               (invIso (Iso-cofibFst-⋁ λ _ → S₊∙ n)))

  SphereBouquet/EqBottomGen : (α : FinSphereBouquetMap c1 c2 n) (m : ℕ)
    (r : m ≡ suc n) (p : Trichotomyᵗ m (suc n)) (q : Trichotomyᵗ m (suc (suc n)))
    → SphereBouquet (suc n) (Fin c2) ≃ Pushout (SphereBouquet/αGen α m p q) fst
  SphereBouquet/EqBottomGen a m m< (lt x) q =
    ⊥.rec (¬m<ᵗm {suc n} (subst (_<ᵗ suc n) m< x))
  SphereBouquet/EqBottomGen a zero m< (eq x) (lt y) = ⊥.rec (snotz (sym x))
  SphereBouquet/EqBottomGen a (suc m) m< (eq x) (lt y) =
    compEquiv (SphereBouquet/EqBottomMainGen a)
              (pathToEquiv λ i → cofib {A = Fin c2 × S₊ (predℕ (m< (~ i)))}
                                        {B = Fin c2} fst)
  SphereBouquet/EqBottomGen a m m< (eq x) (eq y) =
    ⊥.rec (falseDichotomies.eq-eq (x , y))
  SphereBouquet/EqBottomGen a m m< (eq x) (gt y) =
    ⊥.rec (falseDichotomies.eq-gt (x , y))
  SphereBouquet/EqBottomGen a m m< (gt x) q =
    ⊥.rec (¬m<ᵗm {suc n} (subst (suc n <ᵗ_) m< x))

  SphereBouquet/EqTopGen' : (m : ℕ) (α : FinSphereBouquetMap c1 c2 n)
    (p : m ≡ suc n)
    → cofib α ≃ Pushout (α ∘ (λ x → inr (fst x , subst S₊ p (snd x)))) fst
  SphereBouquet/EqTopGen' m a p =
    compEquiv (compEquiv (symPushout _ _)
              (pushoutEquiv _ _ _ _ (idEquiv _) (idEquiv _)
                (invEquiv (isContr→≃Unit (isContrLem c1 n m (sym p))))
                (λ i x → a x)
                λ i x → isContrLem c1 n m (sym p) .snd (inl x) i))
              (invEquiv (isoToEquiv
                (Iso-PushoutComp-IteratedPushout
                (λ x → inr (fst x , subst S₊ p (snd x))) a)))
    where
    isContrLem : (c1 : ℕ) (n m : ℕ) (x : suc n ≡ m)
     → isContr (Pushout {A = Fin c1 × S₊ m} {B = SphereBouquet (suc n) (Fin c1)}
                         (λ x₂ → inr (fst x₂ , subst S₊ (sym x) (snd x₂))) fst)
    isContrLem c1 n =
      J> subst isContr
        (λ i → Pushout {B = SphereBouquet (suc n) (Fin c1)}
                       (λ x₂ → inr (fst x₂ , transportRefl (snd x₂) (~ i))) fst)
         main
       where
       main : isContr (Pushout inr fst)
       fst main = inl (inl tt)
       snd main (inl (inl x)) = refl
       snd main (inl (inr x)) =
         (λ i → inl (push (fst x) i))
          ∙ push (fst x , ptSn (suc n))
          ∙ sym (push x)
       snd main (inl (push a i)) j = lem i j
         where
         lem : Square refl ((λ i₁ → inl (push a i₁))
                          ∙ push (a , ptSn (suc n))
                          ∙ sym (push (a , ptSn (suc n))))
                      refl λ i → inl (push a i)
         lem = (λ i j → inl (push a (i ∧ j)))
            ▷ (rUnit _
             ∙ cong ((λ i₁ → inl (push a i₁)) ∙_)
                    (sym (rCancel (push (a , ptSn (suc n))))))
       snd main (inr x) = (λ i → inl (push x i)) ∙ push (x , ptSn (suc n))
       snd main (push a i) j =
         ((λ i₁ → inl (push (fst a) i₁))
         ∙ compPath-filler (push (fst a , ptSn (suc n))) (sym (push a)) (~ i)) j

  SphereBouquet/EqTopGen : (m : ℕ) (α : FinSphereBouquetMap c1 c2 n)
    → suc n <ᵗ m → (p : Trichotomyᵗ m (suc n)) (q : Trichotomyᵗ m (suc (suc n)))
    → cofib α ≃ Pushout (SphereBouquet/αGen α m p q) fst
  SphereBouquet/EqTopGen (suc m) a m< (lt x) q =
    ⊥.rec (¬m<ᵗm {n} (<ᵗ-trans {n} {m} {n} m< x))
  SphereBouquet/EqTopGen (suc m) a m< (eq x) q =
    ⊥.rec (¬m<ᵗm {suc m} (subst (_<ᵗ suc m) (sym x) m<))
  SphereBouquet/EqTopGen (suc m) a m< (gt x) (lt y) =
    ⊥.rec (¬squeeze {m} {suc n} (y , x))
  SphereBouquet/EqTopGen (suc m) a m< (gt x) (eq y) =
    SphereBouquet/EqTopGen' m a (cong predℕ y)
  SphereBouquet/EqTopGen (suc m) a m< (gt x) (gt y) =
    isoToEquiv (PushoutEmptyFam (λ()) λ())

  SphereBouquet/EqGen : (m : ℕ) (α : FinSphereBouquetMap c1 c2 n)
       (p : Trichotomyᵗ (suc m) (suc (suc n)))
       (q : Trichotomyᵗ m (suc n)) (q' : Trichotomyᵗ m (suc (suc n)))
    → (SphereBouquet/FamGen α (suc m) p)
     ≃ Pushout (SphereBouquet/αGen α m q q') fst
  SphereBouquet/EqGen m a (lt x) q q' =
    invEquiv (isContr→≃Unit (SphereBouquet/EqContrGen a m x q q'))
  SphereBouquet/EqGen m a (eq x) q q' =
    SphereBouquet/EqBottomGen a m (cong predℕ x) q q'
  SphereBouquet/EqGen m a (gt x) q q' = SphereBouquet/EqTopGen m a x q q'

  ¬SphereBouquet/CardGen : (k : ℕ) (ineq : suc (suc n) <ᵗ k) (p : _) (q : _)
    → ¬ (Fin (SphereBouquet/CardGen k p q))
  ¬SphereBouquet/CardGen (suc k) ineq (eq x) q c =
    falseDichotomies.eq-gt (x , ineq)
  ¬SphereBouquet/CardGen (suc k) ineq (gt x) (eq y) c =
    ¬m<ᵗm {suc n} (subst (suc n <ᵗ_) (cong predℕ y) ineq)

  SphereBouquet/ˢᵏᵉˡConverges : (k : ℕ) (α : FinSphereBouquetMap c1 c2 n)
    → suc (suc n) <ᵗ k
    → (p : _) (q : _)
    → isEquiv {B = Pushout (SphereBouquet/αGen α k p q) fst} inl
  SphereBouquet/ˢᵏᵉˡConverges k a ineq p q =
    isoToIsEquiv (PushoutEmptyFam (¬SphereBouquet/CardGen k ineq p q ∘ fst)
                                  (¬SphereBouquet/CardGen k ineq p q))

  SphereBouquet/FamMidElementGen :
    (k : ℕ) (α : FinSphereBouquetMap c1 c2 n)
    → suc (suc n) ≡ k → (p : _)
    → SphereBouquet (suc n) (Fin c2) ≃ (SphereBouquet/FamGen α k p)
  SphereBouquet/FamMidElementGen k q s (lt x) =
    ⊥.rec (¬m<ᵗm {n} (subst (_<ᵗ suc (suc n)) (sym s) x))
  SphereBouquet/FamMidElementGen zero q s (eq x) = ⊥.rec (snotz (sym x))
  SphereBouquet/FamMidElementGen (suc k) q s (eq x) = idEquiv _
  SphereBouquet/FamMidElementGen k q s (gt x) =
    ⊥.rec (¬m<ᵗm {k} (subst (_<ᵗ k) s x))

  SphereBouquet/FamTopElementGen : (k : ℕ) (α : FinSphereBouquetMap c1 c2 n)
    → suc (suc n) <ᵗ k → (p : _)
    → cofib α ≃ (SphereBouquet/FamGen α k p)
  SphereBouquet/FamTopElementGen (suc k) α ineq (lt x) =
    ⊥.rec (¬m<ᵗm {k} (<ᵗ-trans {k} {suc n} {k} x ineq))
  SphereBouquet/FamTopElementGen (suc k) α ineq (eq x) =
    ⊥.rec (¬m<ᵗm {k} (subst (_<ᵗ k) (cong predℕ (sym x)) ineq))
  SphereBouquet/FamTopElementGen (suc k) α ineq (gt x) = idEquiv _

SphereBouquet/EqBottomMainGenLem : {C : Type} {c1 c2 : ℕ} (n : ℕ)
     (α : FinSphereBouquetMap c1 c2 n) {e : C ≃ _}
  → (a : _) → Pushout→Bouquet (suc n) c2 (λ _ → tt) e
                  (fst (SphereBouquet/EqBottomMainGen c1 c2 α) a)
            ≡ a
SphereBouquet/EqBottomMainGenLem n α (inl x) = refl
SphereBouquet/EqBottomMainGenLem zero α (inr (a , base)) = push a
SphereBouquet/EqBottomMainGenLem {c1 = c1} {c2} zero α
  {e = e} (inr (a , loop i)) j = main j i
  where
  main : Square (cong (Pushout→Bouquet 1 c2 (λ _ → tt) e)
                     λ i → fst (SphereBouquet/EqBottomMainGen c1 c2 α)
                                (inr (a , loop i)))
                (λ i → inr (a , loop i))
                (push a) (push a)
  main = (λ j i → Pushout→Bouquet 1 c2 (λ _ → tt) e
                   (⋁→cofibFst {A = Fin c2}  (λ _ → Bool , true)
                    (inr (a , toSusp (Bool , true) false i))))
    ∙ cong-∙ (λ t → Pushout→Bouquet 1 c2 (λ _ → tt) e
                          (⋁→cofibFst (λ _ → Bool , true) (inr (a , t))))
                 (merid false)
                 (sym (merid true))
    ∙ cong₂ _∙_ refl (sym (rUnit (sym (push a))))
    ∙ (λ _ → (push a ∙ (λ i₁ → inr (a , loop i₁))) ∙ (λ i₁ → push a (~ i₁)))
    ∙ sym (assoc (push a) (λ i → inr (a , loop i)) (sym (push a)))
    ∙ sym (doubleCompPath≡compPath
             (push a) (λ i → inr (a , loop i)) (sym (push a)))
    ◁ symP (doubleCompPath-filler
             (push a) (λ i → inr (a , loop i)) (sym (push a)))
SphereBouquet/EqBottomMainGenLem (suc n) α (inr (a , north)) = push a
SphereBouquet/EqBottomMainGenLem (suc n) α (inr (a , south)) =
  λ i → inr (a , merid (ptSn (suc n)) i)
SphereBouquet/EqBottomMainGenLem {c1 = c1} {c2} (suc n) α
  {e = e} (inr (a , merid x i)) j = main j i
  where
  main : Square (cong (Pushout→Bouquet (suc (suc n)) c2 (λ _ → tt) e)
                     λ i → fst (SphereBouquet/EqBottomMainGen c1 c2 α)
                                (inr (a , merid x i)))
                (λ i → inr (a , merid x i))
                (push a) λ i → inr (a , merid (ptSn (suc n)) i)
  main = (cong (push a ∙_)
         (cong-∙ (inr ∘ (a ,_)) (merid x) (sym (merid (ptSn (suc n)))))
        ∙ sym (doubleCompPath≡compPath (push a)
                (λ i → inr (a , merid x i))
                (λ i → inr (a , merid (ptSn (suc n)) (~ i)))))
        ◁ symP (doubleCompPath-filler (push a)
                (λ i → inr (a , merid x i))
                (λ i → inr (a , merid (ptSn (suc n)) (~ i))))
SphereBouquet/EqBottomMainGenLem {c1 = c1} {c2} zero α
  {e = e} (push a i) j = lem j i
  where
  lem : Square (cong (Pushout→Bouquet (suc zero) c2 (λ _ → tt) e)
                 (cong (fst (SphereBouquet/EqBottomMainGen c1 c2 α))
                   (push a)))
               (push a) refl (push a)
  lem = (λ j i → Pushout→Bouquet 1 c2 (λ _ → tt) e
                  (Iso.inv (Iso-cofibFst-⋁ λ _ → S₊∙ zero)
                    (lUnit (push a) (~ j) i)))
      ◁ λ i j → push a (i ∧ j)
SphereBouquet/EqBottomMainGenLem {c1 = c1} {c2} (suc n) α
  {e = e} (push a i) j = lem j i
  where
  lem : Square (cong (Pushout→Bouquet (suc (suc n)) c2 (λ _ → tt) e)
                 (cong (fst (SphereBouquet/EqBottomMainGen c1 c2 α))
                   (push a)))
               (push a) refl (push a)
  lem = (λ j i → Pushout→Bouquet (suc (suc n)) c2 (λ _ → tt) e
                  (Iso.inv (Iso-cofibFst-⋁ λ _ → S₊∙ (suc n))
                    (lUnit (push a) (~ j) i)))
      ◁ λ i j → push a (i ∧ j)

-- Final product
module _ {c1 c2 : ℕ} {n : ℕ} (α : FinSphereBouquetMap c1 c2 n) where
  private
    α∙ : ∥ α (inl tt) ≡ inl tt ∥₁
    α∙ = isConnectedSphereBouquet _

  SphereBouquet/ˢᵏᵉˡ : CWskel ℓ-zero
  fst SphereBouquet/ˢᵏᵉˡ m = SphereBouquet/FamGen c1 c2 α m (m ≟ᵗ (suc (suc n)))
  fst (snd SphereBouquet/ˢᵏᵉˡ) m =
    SphereBouquet/CardGen c1 c2 m (m ≟ᵗ suc n) (m ≟ᵗ suc (suc n))
  fst (snd (snd SphereBouquet/ˢᵏᵉˡ)) m =
    SphereBouquet/αGen c1 c2 α m (m ≟ᵗ suc n) (m ≟ᵗ suc (suc n))
  fst (snd (snd (snd SphereBouquet/ˢᵏᵉˡ))) ()
  snd (snd (snd (snd SphereBouquet/ˢᵏᵉˡ))) m =
    SphereBouquet/EqGen c1 c2 m α
      (suc m ≟ᵗ suc (suc n)) (m ≟ᵗ suc n) (m ≟ᵗ suc (suc n))

  hasCWskelSphereBouquet/ : hasCWskel (cofib α)
  fst hasCWskelSphereBouquet/ = SphereBouquet/ˢᵏᵉˡ
  snd hasCWskelSphereBouquet/ =
    compEquiv (SphereBouquet/FamTopElementGen c1 c2 (suc (suc (suc n))) α
               (<ᵗsucm {n}) (suc (suc (suc n)) ≟ᵗ suc (suc n)))
      (isoToEquiv (converges→ColimIso (suc (suc (suc n)))
      λ k → compEquiv (inl
        , SphereBouquet/ˢᵏᵉˡConverges c1 c2 (k +ℕ suc (suc (suc n))) α
           (<→<ᵗ (k , refl))
           ((k +ℕ suc (suc (suc n))) ≟ᵗ suc n)
           ((k +ℕ suc (suc (suc n))) ≟ᵗ suc (suc n)))
        (invEquiv (SphereBouquet/EqGen c1 c2 (k +ℕ suc (suc (suc n)))
                  α
                  ((suc (k +ℕ suc (suc (suc n)))) ≟ᵗ suc (suc n))
                  ((k +ℕ suc (suc (suc n))) ≟ᵗ suc n) _)) .snd))

  SphereBouquet/ᶜʷ : CW ℓ-zero
  fst SphereBouquet/ᶜʷ = cofib α
  snd SphereBouquet/ᶜʷ = ∣ hasCWskelSphereBouquet/ ∣₁
