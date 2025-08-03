{-# OPTIONS --lossy-unification #-}

{-
This file contains a definition of a notion of (strict)
subcomplexes of a CW complex. Here, a subcomplex of a complex
C = colim ( C₀ → C₁ → ...)
is simply the complex
C⁽ⁿ⁾ := colim (C₀ → ... → Cₙ = Cₙ = ...)

This file contains.
1. Definition of above
2. A `strictification' of finite CW complexes in terms of above
3. An elimination principle for finite CW complexes
4. A proof that C and C⁽ⁿ⁾ has the same homology in appropriate dimensions.
-}

module Cubical.CW.Homology.Groups.Subcomplex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws


open import Cubical.Data.Nat
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.ChainComplex
open import Cubical.CW.Approximation
open import Cubical.CW.Map
open import Cubical.CW.Homology.Base
open import Cubical.CW.Subcomplex

open import Cubical.CW.ChainComplex
open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/s_)
open import Cubical.HITs.SetQuotients.Properties as SQ
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.ChainComplex
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup


private
  variable
    ℓ ℓ' ℓ'' : Level

-- Goal: Show that a cell complex C and its subcomplex C⁽ⁿ⁾ share
-- homology in low enough dimensions
module _ (C : CWskel ℓ) where
  ChainSubComplex : (n : ℕ) → snd C .fst n ≡ snd (subComplex C (suc n)) .fst n
  ChainSubComplex n with (n ≟ᵗ suc n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) (sym x) <ᵗsucm))
  ... | gt x = ⊥.rec (¬-suc-n<ᵗn x)

  ≤ChainSubComplex : (n : ℕ) (m : Fin n)
    → snd C .fst (fst m) ≡ snd (subComplex C n) .fst (fst m)
  ≤ChainSubComplex n (m , p) with (m ≟ᵗ n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x p))
  ... | gt x = ⊥.rec (¬m<ᵗm (<ᵗ-trans x p))

subChainIsoGen : (C : CWskel ℓ) (n : ℕ) (m : Fin n) (p : Trichotomyᵗ (fst m) n)
  → AbGroupIso (CWskel-fields.ℤ[A_] C (fst m))
                ℤ[Fin SubComplexGen.subComplexCard C n (fst m) p ]
subChainIsoGen C n (m , p) (lt x) = idGroupIso
subChainIsoGen C n (m , p) (eq x) = ⊥.rec (¬m<ᵗm (subst (m <ᵗ_) (sym x) p))
subChainIsoGen C n (m , p) (gt x) = ⊥.rec (¬m<ᵗm (<ᵗ-trans x p))

subChainIso : (C : CWskel ℓ) (n : ℕ) (m : Fin n)
  → AbGroupIso (CWskel-fields.ℤ[A_] C (fst m))
                (CWskel-fields.ℤ[A_] (subComplex C n) (fst m))
subChainIso C n (m , p) = subChainIsoGen C n (m , p) _

-- main result
subComplexHomology : (C : CWskel ℓ) (n m : ℕ) (p : suc (suc m) <ᵗ n)
  → GroupIso (H̃ˢᵏᵉˡ C (suc m)) (H̃ˢᵏᵉˡ (subComplex C n) (suc m))
subComplexHomology C n m p =
  homologyIso (suc m) _ _
    (subChainIso C n (suc (suc m) , p))
    (subChainIso C n (suc m , <ᵗ-trans <ᵗsucm p))
    (subChainIso C n (m , <ᵗ-trans <ᵗsucm (<ᵗ-trans <ᵗsucm p)))
    lem₁
    lem₂
  where
  lem₁ : {q : _} {r : _}
    → Iso.fun (subChainIso C n (m , q) .fst) ∘ ∂ C m .fst
    ≡ ∂ (subComplex C n) m .fst
     ∘ Iso.fun (subChainIso C n (suc m , r) .fst)
  lem₁ {q} {r} with (m ≟ᵗ n) | (suc m ≟ᵗ n) | (suc (suc m) ≟ᵗ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x₁ r))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ r))
  ... | eq x | s | t = ⊥.rec (¬-suc-n<ᵗn (subst (suc m <ᵗ_) (sym x) r))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans r x))

  lem₂ : {q : suc m <ᵗ n} {r : (suc (suc m)) <ᵗ n}
    → Iso.fun (subChainIso C n (suc m , q) .fst)
     ∘ ∂ C (suc m) .fst
     ≡ ∂ (subComplex C n) (suc m) .fst
     ∘ Iso.fun (subChainIso C n (suc (suc m) , r) .fst)
  lem₂ {q} with (suc m ≟ᵗ n) | (suc (suc m) ≟ᵗ n) | (suc (suc (suc m)) ≟ᵗ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x₁ p))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ p))
  ... | eq x | s | t = ⊥.rec (¬m<ᵗm (subst (suc m <ᵗ_) (sym x) q))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans p x))


subComplexHomologyEquiv≡ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) (q : suc (suc n) <ᵗ m)
  → Iso.inv (fst (subComplexHomology C m n q))
   ≡ H̃ˢᵏᵉˡ→ (suc n) (incl ∘ Iso.inv (realiseSubComplex m C)) .fst
subComplexHomologyEquiv≡ C m n q =
  funExt (SQ.elimProp (λ _ → squash/ _ _)
    λ a → cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
      (mainGen (suc n ≟ᵗ m) (suc (suc n) ≟ᵗ m) (fst a)
      ∙ (λ i → bouquetDegree ((CTB* ∘ f1/f2≡ i ∘
       BouquetFuns.BTC (suc n)
         (G.subComplexCard C m (suc n) (suc n ≟ᵗ m))
         (G.subComplexα C m (suc n) (suc n ≟ᵗ m))
         (G.subComplexFam≃Pushout C m (suc n) (suc n ≟ᵗ m)
           (suc (suc n) ≟ᵗ m)))) .fst (fst a)))))
    ∙ cong fst (sym (H̃ˢᵏᵉˡ→β (subComplex C m) C (suc n)
                     {f = (incl ∘ Iso.inv (realiseSubComplex m C))}
                 (help q)))
  where
  open CWskel-fields C

  help' : (m : _)  (k : _) (q : _)
    → finCellApprox (subComplex C m) C
        (λ x → incl (Iso.inv (realiseSubComplex m C) x)) k
  fst (help' m k q) = subComplex→ C m k
  snd (help' m k q) = →FinSeqColimHomotopy _ _
    λ x → CW↑Gen≡ C k (suc m) (suc m ≟ᵗ suc k) q _
    ∙ cong (incl {n = suc m})
           (funExt⁻ (CW↑GenComm C k (suc m) m (suc m ≟ᵗ suc k) q) x
      ∙ funExt⁻ (subComplex→map'Charac C m (suc m ≟ᵗ m) (m ≟ᵗ m))
              (CW↑Gen (subComplex C m) k (suc m) (suc m ≟ᵗ suc k) q x)
      ∙ cong (CW↪ C m) (sym (Iso.leftInv ( (realiseSubComplex m C) ) _)
      ∙ cong (Iso.inv (realiseSubComplex m C))
        ((push _ ∙ cong (incl {n = suc m})
           (cong (CW↪ (subComplex C m) m)
             (secEq (complex≃subcomplex' C m m <ᵗsucm (m ≟ᵗ m)) _)
          ∙ CW↪subComplexFam↓ C m (m ≟ᵗ m) (suc m ≟ᵗ m) _))
        ∙ sym (CW↑Gen≡ (subComplex C m) k (suc m) (suc m ≟ᵗ suc k) q x))))
    ∙ sym (push _)

  help : (q : suc (suc n) <ᵗ m)
    → finCellApprox (subComplex C m) C
        (λ x → incl (Iso.inv (realiseSubComplex m C) x))
        (suc (suc (suc (suc n))))
  fst (help q) = subComplex→ C m (suc (suc (suc (suc n))))
  snd (help q) with (suc (suc (suc n)) ≟ᵗ m)
  ... | lt x = help' m (suc (suc (suc (suc n)))) x .snd
  ... | eq x = funExt (subst (λ m → (x : _)
    → FinSeqColim→Colim (suc (suc (suc (suc n))))
         (finCellMap→FinSeqColim (subComplex C m) C
          (subComplex→ C m (suc (suc (suc (suc n))))) x) ≡ incl
         (Iso.inv (realiseSubComplex m C)
          (FinSeqColim→Colim (suc (suc (suc (suc n)))) x))) x
          (funExt⁻ (→FinSeqColimHomotopy _ _ λ w →
           (cong (incl {n = suc (suc (suc (suc n)))})
            (cong (subComplex→map C
                    (suc (suc (suc n))) (suc (suc (suc (suc n)))))
              (sym (secEq (_ , subComplexFin C (suc (suc (suc n)))
                                 (suc (suc (suc n)) , <ᵗsucm)) w)))
    ∙ (cong (incl {n = suc (suc (suc (suc n)))})
         (CW↪Eq (3 + n) ((4 + n) ≟ᵗ (3 + n)) ((3 + n) ≟ᵗ (3 + n))
           (invEq
             (CW↪ (subComplex C (suc (suc (suc n)))) (suc (suc (suc n)))
               , subComplexFin C (suc (suc (suc n))) (suc (suc (suc n))
               , <ᵗsucm)) w))
    ∙ sym (push (FinSequenceMap.fmap
                  (fst (help' (suc (suc (suc n))) (suc (suc (suc n))) <ᵗsucm))
                  (suc (suc (suc n)) , <ᵗsucm)
                  (invEq
                   (CW↪ (subComplex C (suc (suc (suc n)))) (suc (suc (suc n)))
                     , subComplexFin C (suc (suc (suc n))) (suc (suc (suc n))
                     , <ᵗsucm)) w)))
           ∙ funExt⁻ (help' (suc (suc (suc n))) (suc (suc (suc n))) <ᵗsucm .snd)
                     (fincl (suc (suc (suc n)) , <ᵗsucm) _)))
    ∙ cong (incl {n = suc (suc (suc n))})
        (cong (Iso.inv (realiseSubComplex (suc (suc (suc n))) C))
           (push _
           ∙ cong (incl {n = suc (suc (suc (suc n)))})
           (secEq (_ , subComplexFin C (suc (suc (suc n))) (suc (suc (suc n))
                     , <ᵗsucm)) w))))))
    where
    CW↑GenEq : (n : ℕ) (x₂ : _) (x : _)
      → CW↑Gen C n (suc n) (eq (λ _ → suc n)) x₂ x ≡ invEq (e n) (inl x)
    CW↑GenEq zero x₂ x = ⊥.rec (C .snd .snd .snd .fst x)
    CW↑GenEq (suc n) x₂ x = cong (CW↪ C (suc n)) (transportRefl x)

    CW↪Eq : (n : ℕ) (P : _) (Q : _) (x : _)
      → subComplexMapGen.subComplex→map' C n (suc n) P
          (invEq (G.subComplexFam≃Pushout C n n Q P) (inl x))
      ≡ CW↪ C n (subComplexMapGen.subComplex→map' C n n Q x)
    CW↪Eq n P (lt y) x = ⊥.rec (¬m<ᵗm y)
    CW↪Eq n (lt x₂) (eq y) x = ⊥.rec (¬-suc-n<ᵗn x₂)
    CW↪Eq n (eq x₂) (eq y) x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) (sym x₂) <ᵗsucm))
    CW↪Eq n (gt x₂) (eq y) x = ah
      where
      ah :  CW↑Gen C n (suc n) (Trichotomyᵗ-suc (n ≟ᵗ n)) x₂
         (invEq (G.subComplexFam≃Pushout C n n (eq y) (gt x₂)) (inl x))
         ≡ CW↪ C n (idfun (fst C n) x)
      ah with (n ≟ᵗ n)
      ... | lt x = ⊥.rec (¬m<ᵗm x)
      ... | eq q = cong₂ (λ p r → CW↑Gen C n (suc n) (eq p) x₂
                                    (transport refl (subst (fst C) r x)))
                         (isSetℕ _ _ _ refl) (isSetℕ _ _ _ refl)
                 ∙ cong (CW↑Gen C n (suc n) (eq (λ _ → suc n)) x₂)
                   (transportRefl _ ∙ transportRefl x)
                 ∙ CW↑GenEq n x₂ x
      ... | gt x = ⊥.rec (¬m<ᵗm x)
    CW↪Eq n P (gt y) x = ⊥.rec (¬m<ᵗm y)
  ... | gt x = ⊥.rec (¬squeeze (q , x))

  [3+n] : Fin (suc (suc (suc n)))
  fst [3+n] = suc n
  snd [3+n] = <ᵗ-trans {n = suc n} {m = suc (suc n)} {k = suc (suc (suc n))}
                     <ᵗsucm <ᵗsucm

  CTB* = BouquetFuns.CTB (suc n) (card (suc n)) (α (suc n)) (e (suc n))

  f1/f2gen :  (q1 : _) (q2 : _)
    → cofib (invEq (G.subComplexFam≃Pushout C m (suc n) q1 q2) ∘ inl)
    → Pushout (λ _ → tt) (invEq (e (suc n)) ∘ inl)
  f1/f2gen q1 q2 (inl x) = inl x
  f1/f2gen q1 q2 (inr x) =
    inr (subComplexMapGen.subComplex→map' C m (suc (suc n)) q2 x)
  f1/f2gen q1 q2 (push a i) =
      (push (subComplexMapGen.subComplex→map' C m (suc n) q1 a)
    ∙ λ i → inr (subComplex→comm C (suc n) m q1 q2 a i)) i

  f1/f2≡ :  f1/f2gen (suc n ≟ᵗ m) (suc (suc n) ≟ᵗ m)
         ≡ prefunctoriality.fn+1/fn (suc (suc (suc (suc n))))
            (subComplex→ C m (suc (suc (suc (suc n)))))
              ((suc n , <ᵗ-trans-suc (<ᵗ-trans (snd flast) <ᵗsucm)))
  f1/f2≡ = funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) → refl}

  f1/f2genId : (q1 : _) (q2 : _) → f1/f2gen (lt q1) (lt q2) ≡ idfun _
  f1/f2genId q1 q2 =
    funExt λ { (inl x) → refl
             ; (inr x) → refl
             ; (push a i) j
    → ((λ i → push a ∙ (λ j → inr (lem m q1 q2 a i j)))
                      ∙ sym (rUnit (push a))) j i}
    where
    lem : (m : ℕ) (q1 : _) (q2 : _) (a : _)
      → subComplex→comm C (suc n) m (lt q1) (lt q2) a ≡ refl
    lem (suc m) q1 q2 a = refl

  mainGen : (q1 : _) (q2 : _) (a : _)
    → Iso.inv (fst (subChainIsoGen C m (suc n , <ᵗ-trans <ᵗsucm q) q1)) a
    ≡ bouquetDegree
      (CTB* ∘ f1/f2gen q1 q2
      ∘ (BouquetFuns.BTC (suc n)
         (G.subComplexCard C m (suc n) q1)
         (G.subComplexα C m (suc n) q1)
           (G.subComplexFam≃Pushout C m (suc n) q1 q2))) .fst a
  mainGen (lt x) (lt y) a =
    funExt⁻ (sym (cong fst (bouquetDegreeId))) a
    ∙ λ i → bouquetDegree (lem (~ i)) .fst a
    where
    lem : CTB* ∘ f1/f2gen (lt x) (lt y)
          ∘ BouquetFuns.BTC (suc n) (G.subComplexCard C m (suc n) (lt x))
             (G.subComplexα C m (suc n) (lt x))
               (G.subComplexFam≃Pushout C m (suc n) (lt x) (lt y))
             ≡ idfun _
    lem = funExt λ a → cong CTB*
                  (funExt⁻ (f1/f2genId x y) _)
                ∙ CTB-BTC-cancel (suc n) (card (suc n))
                    (α (suc n)) (e (suc n)) .fst _
  mainGen (lt x) (eq y) a = ⊥.rec (¬m<ᵗm (subst (suc (suc n) <ᵗ_) (sym y) q))
  mainGen (lt x) (gt y) a = ⊥.rec (¬squeeze (x , y))
  mainGen (eq x) q2 a =
    ⊥.rec (¬m<ᵗm  (subst (_<ᵗ_ (suc n)) (sym x) (<ᵗ-trans <ᵗsucm q)))
  mainGen (gt x) q2 a =
    ⊥.rec (¬m<ᵗm (<ᵗ-trans x (<ᵗ-trans <ᵗsucm q)))

subComplexHomologyEquiv : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) (m : ℕ)
  (p : suc (suc n) <ᵗ m)
  → GroupEquiv (H̃ˢᵏᵉˡ (subComplex C m) (suc n))
                (H̃ˢᵏᵉˡ C (suc n))
fst (fst (subComplexHomologyEquiv C n m p)) =
  H̃ˢᵏᵉˡ→ (suc n) (incl ∘ Iso.inv (realiseSubComplex m C)) .fst
snd (fst (subComplexHomologyEquiv C n m p)) =
  subst isEquiv (subComplexHomologyEquiv≡ C m n p)
    (isoToIsEquiv (invIso (fst (subComplexHomology C m n p))))
snd (subComplexHomologyEquiv C n m p) =
  H̃ˢᵏᵉˡ→ (suc n) (incl ∘ Iso.inv (realiseSubComplex m C)) .snd

-- H̃ᶜʷₙ Cₘ ≅ H̃ᶜʷₙ C∞ for n sufficiently small
subComplexHomologyᶜʷEquiv : ∀ {ℓ} (C : CWexplicit ℓ) (n : ℕ) (m : ℕ)
  (p : suc (suc n) <ᵗ m)
  → GroupEquiv (H̃ᶜʷ ((fst (fst (snd C))) m
                       , ∣ subComplex (snd C .fst) m
                       , isoToEquiv (realiseSubComplex m (snd C .fst)) ∣₁)
                    (suc n))
                (H̃ᶜʷ (realise (snd C .fst)
                       , ∣ fst (snd C)
                       , idEquiv _ ∣₁)
                    (suc n))
fst (subComplexHomologyᶜʷEquiv C n m p) =
  H̃ᶜʷ→ (suc n) (incl {n = m}) .fst
  , subComplexHomologyEquiv (snd C .fst) n m p .fst .snd
snd (subComplexHomologyᶜʷEquiv C n m p) =
  H̃ᶜʷ→ (suc n) (incl {n = m}) .snd
