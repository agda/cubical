{-# OPTIONS --lossy-unification #-}
{-
This file contains
1. a construction of the Hurewicz map πₙᵃᵇ(X) → H̃ᶜʷₙ(X),
2. a proof that it's a homomorphism, and
3. the fact that it is an equivalence when X in (n-1)-connected
-}
module Cubical.CW.HurewiczTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.Map
open import Cubical.CW.Connected
open import Cubical.CW.Subcomplex
open import Cubical.CW.Approximation
open import Cubical.CW.ChainComplex
open import Cubical.CW.Instances.Sn
open import Cubical.CW.Instances.SphereBouquetMap
open import Cubical.CW.Homology.Base
open import Cubical.CW.Homology.Groups.Sn
open import Cubical.CW.Homology.Groups.CofibFinSphereBouquetMap
open import Cubical.CW.Homology.Groups.Subcomplex
open import Cubical.CW.Instances.Lift

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Fin
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.FinSequence
open import Cubical.Data.Int

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/s_)
open import Cubical.HITs.Wedge

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Properties
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.PiAbCofibFinSphereBouquetMap

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Abelianization.Properties as Abi
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Relation.Nullary

open Iso renaming (inv to inv')
open FinSequenceMap

private
  variable
    ℓ ℓ' : Level

-- Generators of ℤ[k] with locked definitions for faster type checking
private
  module _ {k : ℕ} (w : Fin k) (x : _) where
    ℤFinGenerator* : lockUnit {ℓ} → ℤ
    ℤFinGenerator* unlock = ℤFinGenerator w x

    ℤFinGenerator*₀ : (l : _) → ¬ (fst w ≡ fst x) → ℤFinGenerator* {ℓ} l ≡ pos 0
    ℤFinGenerator*₀ unlock nope with (fst w ≟ᵗ fst x)
    ... | (lt ineq) = refl
    ... | (eq p) = ⊥.rec (nope p)
    ... | (gt ineq) = refl

    ℤFinGenerator*₁ : (l : _) → (fst w ≡ fst x) → ℤFinGenerator* {ℓ} l ≡ pos 1
    ℤFinGenerator*₁ unlock aye with (fst w ≟ᵗ fst x)
    ... | (lt ineq) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst x) aye ineq))
    ... | (eq p) = refl
    ... | (gt ineq) = ⊥.rec (¬m<ᵗm (subst (fst x <ᵗ_) aye ineq))

--- Parts 1 and 2: construction of map and homomorphism proof ---

-- Construction of the Hurewicz map πₙ(X) → H̃ᶜʷₙ(X)
module _ where
  -- variations of the map
  preHurewiczMap : {n : ℕ} (X : CW ℓ) (x : fst X)
    (f : S₊∙ (suc n) →∙ (fst X , x))
    → GroupHom (H̃ᶜʷ (Sᶜʷ (suc n)) (suc n)) (H̃ᶜʷ X (suc n))
  preHurewiczMap {n = n} X x f = H̃ᶜʷ→ {C = Sᶜʷ (suc n)} {D = X} (suc n) (fst f)

  HurewiczMapUntrunc :  {n : ℕ} (X : CW ℓ) (x : fst X)
    (f : S₊∙ (suc n) →∙ (fst X , x)) → H̃ᶜʷ X (suc n) .fst
  HurewiczMapUntrunc {n = n} X x f = preHurewiczMap X x f .fst (genHₙSⁿ n)

  HurewiczMap : {n : ℕ} (X : CW ℓ) (x : fst X)
    → π' (suc n) (fst X , x)
    → fst (H̃ᶜʷ X (suc n))
  HurewiczMap X x =
    ST.rec (GroupStr.is-set (snd (H̃ᶜʷ X _))) (HurewiczMapUntrunc X x)

  -- proof that it is a homomorphism
  HurewiczMapHom :  {n : ℕ} (X : CW ℓ) (x : fst X)
    (f g : π' (suc n) (fst X , x)) → isConnected 2 (fst X)
     → HurewiczMap X x (·π' n f g)
      ≡ GroupStr._·_ (snd (H̃ᶜʷ X (suc n)))
          (HurewiczMap X x f) (HurewiczMap X x g)
  HurewiczMapHom {n = n} = uncurry λ X → PT.elim
    (λ x → isPropΠ4 λ _ _ _ _
           → GroupStr.is-set (snd (H̃ᶜʷ (X , x) (suc n))) _ _)
    (uncurry λ Xsk → EquivJ (λ X y → (x : X)
      (f g : π' (suc n) (X , x)) → isConnected 2 X
     → HurewiczMap (X , ∣ Xsk , y ∣₁) x (·π' n f g)
     ≡ GroupStr._·_ (snd (H̃ᶜʷ (X , ∣ Xsk , y ∣₁) (suc n)))
           (HurewiczMap (X , ∣ Xsk , y ∣₁) x f)
           (HurewiczMap (X , ∣ Xsk , y ∣₁) x g))
      (λ x → TR.rec (isPropΠ3 (λ _ _ _ → squash/ _ _))
        (uncurry λ x₀ → main Xsk x x₀ x)
        (isConnected-CW↪∞ 1 Xsk x .fst)))
    where
    module _ (Xsk : CWskel ℓ) (x : realise Xsk) where
     ∥x₀∥ : hLevelTrunc 1 (Xsk .fst 1)
     ∥x₀∥ = TR.map fst (isConnected-CW↪∞ 1 Xsk x .fst)

     X' : CW ℓ
     X' = realise Xsk , ∣ Xsk , idEquiv (realise Xsk) ∣₁

     main : (x₁ : fst Xsk 1) (x : realise Xsk) (y : CW↪∞ Xsk 1 x₁ ≡ x)
       (f g : π' (suc n) (realise Xsk , x))
       → isConnected 2 (realise Xsk)
       → HurewiczMap X' x (·π' n f g)
       ≡ GroupStr._·_ (snd (H̃ᶜʷ X' (suc n)))
          (HurewiczMap X' x f) (HurewiczMap X' x g)
     main x₀ = J> ST.elim2 (λ _ _ → isSetΠ λ _ → isProp→isSet (squash/ _ _))
       λ f g t → PT.rec2 (squash/ _ _)
         (λ {(f' , fp) (g' , gp) → goal f' g' f fp g gp})
         (approxSphereMap∙ Xsk x₀ n f)
         (approxSphereMap∙ Xsk x₀ n g)
      where
      X∙ : Pointed _
      X∙ = fst Xsk (suc (suc n)) , CW↪ Xsk (suc n) (CWskel∙ Xsk x₀ n)

      X* : (n : ℕ) → Pointed _
      X* n = fst Xsk (suc (suc n)) , CW↪ Xsk (suc n) (CWskel∙ Xsk x₀ n)

      goalTy : (f g : S₊∙ (suc n) →∙ (realise Xsk , CW↪∞ Xsk 1 x₀)) → Type _
      goalTy f g =
        HurewiczMap X' (CW↪∞ Xsk 1 x₀) (·π' n ∣ f ∣₂ ∣ g ∣₂)
            ≡ GroupStr._·_ (snd (H̃ᶜʷ X' (suc n)))
              (HurewiczMap X' (CW↪∞ Xsk 1 x₀) ∣ f ∣₂)
              (HurewiczMap X' (CW↪∞ Xsk 1 x₀) ∣ g ∣₂)

      module _ (f' g' : S₊∙ (suc n) →∙ X∙) where
       open CWskel-fields Xsk
       finCellApprox∙Π : finCellApprox (Sˢᵏᵉˡ (suc n)) Xsk
         (fst (∙Π (incl∙ Xsk x₀ ∘∙ f') (incl∙ Xsk x₀ ∘∙ g')) ∘
           invEq (hasCWskelSphere (suc n) .snd)) (suc (suc (suc (suc n))))
       finCellApprox∙Π =
         finCellApproxSˢᵏᵉˡImproved Xsk (suc n) x₀
          (∙Π f' g') (∙Π (incl∙ Xsk x₀ ∘∙ f') (incl∙ Xsk x₀ ∘∙ g'))
          (λ x → funExt⁻ (cong fst (∙Π∘∙ n f' g' (incl∙ Xsk x₀))) x ∙ refl)
          (suc (suc (suc (suc n))))

       CTB→ : (n : ℕ) → _
       CTB→ n = BouquetFuns.CTB (suc n)
                 (card (suc n)) (α (suc n)) (e (suc n))

       cofib→cofibCW : (n : ℕ) (f : S₊∙ (suc n) →∙ X* n) (p : _) (q : _) →
         cofib (invEq (SαEqGen (suc n) (suc n) p q) ∘ inl) → cofibCW (suc n) Xsk
       cofib→cofibCW n f p q (inl x) = inl x
       cofib→cofibCW n f (lt _) q (inr x) = inl tt
       cofib→cofibCW n f (eq _) p (inr x) = inr (f .fst x)
       cofib→cofibCW n f (gt _) q (inr x) = inl tt
       cofib→cofibCW n f (lt x) q (push a i) = inl tt
       cofib→cofibCW n f (eq x) q (push a i) =
         (push (CWskel∙ Xsk x₀ n) ∙ λ i → inr (f'∘SαEqGen⁻¹≡ q x a (~ i))) i
         where
         f'∘SαEqGen⁻¹≡ : (q : _) (x : _) (a : _)
           → f .fst ((invEq (SαEqGen (suc n) (suc n) (eq x) q) ∘ inl) a)
            ≡ CWskel∙ Xsk x₀ (suc n)
         f'∘SαEqGen⁻¹≡ (lt _) x a = snd f
         f'∘SαEqGen⁻¹≡ (eq p) x a =
           ⊥.rec (¬m<ᵗm (subst (_<ᵗ_ (suc n)) ((sym p) ∙ cong predℕ x) <ᵗsucm))
         f'∘SαEqGen⁻¹≡ (gt p) x a =
           ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ_ (suc (suc n))) (λ i → predℕ (x i)) p))

       cofib→cofibCW n f (gt x) q (push a i) = inl tt

       CTB∘cofib→cofibCW∘BTC : (n : ℕ) (f : S₊∙ (suc n) →∙ X* n)
         (p : _) (q : _) (x : _) → _
       CTB∘cofib→cofibCW∘BTC n f' p q x =
         CTB→ n (cofib→cofibCW n f' p q (BouquetFuns.BTC (suc n)
                 (ScardGen (suc n) (suc n) p)
                 (SαGen (suc n) (suc n) p q)
                 (SαEqGen (suc n) (suc n) p q) x))

       module _ (f' : S₊∙ (suc n) →∙ X∙) (Q : _) where
         private
           f = finCellApproxSˢᵏᵉˡImproved Xsk (suc n) x₀ f'
                   (incl∙ Xsk x₀ ∘∙ f') Q (suc (suc (suc (suc n))))

         cofib→cofibCW≡inr : (x : _)
           → prefunctoriality.fn+1/fn (suc (suc (suc (suc n)))) (f .fst)
               (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) (inr x)
           ≡ cofib→cofibCW n f' (suc (suc n) ≟ᵗ suc (suc n))
                                 (suc n ≟ᵗ suc (suc n)) (inr x)
         cofib→cofibCW≡inr x with (n ≟ᵗ n)
         ... | lt p = ⊥.rec (¬m<ᵗm p)
         ... | eq q = λ i → inr ((cong (λ p → subst (fst Xsk) p (fst f' x))
           (cong sym (isSetℕ _ _ (cong suc (cong suc q)) refl))
           ∙ transportRefl (fst f' x)) i)
         ... | gt p = ⊥.rec (¬m<ᵗm p)

         cofib→cofibCW≡push : (a : _)
           → Square refl (cofib→cofibCW≡inr (CW↪ (Sˢᵏᵉˡ (suc n)) (suc n) a))
               (push (cellMapSˢᵏᵉˡFunGenGen Xsk (suc n) x₀
                     (fst f') (snd f') (suc n) (suc n ≟ᵗ suc (suc n)) a)
               ∙ (λ i → inr (cellMapSˢᵏᵉˡFunGenComm Xsk (suc n) x₀
                             (fst f') (snd f') (suc n)
                             (suc (suc n) ≟ᵗ suc (suc n))
                             (suc n ≟ᵗ suc (suc n)) a (~ i))))
               (cong (cofib→cofibCW n f'
                      (suc (suc n) ≟ᵗ suc (suc n)) (suc n ≟ᵗ suc (suc n))) (push a))
         cofib→cofibCW≡push a with (n ≟ᵗ n)
         ... | lt x = ⊥.rec (¬m<ᵗm x)
         ... | eq x =
           flipSquare (help (cong suc (cong suc x)) (sym (isSetℕ _ _ _ _)))
           where
           cool : cellMapSˢᵏᵉˡFunGenGen∙ Xsk _ x₀
                   (fst f') (snd f') (suc n) (eq refl)
                ≡ transportRefl _ ∙ snd f'
           cool =
             cong₂ _∙_
               (λ j i → subst (fst Xsk)
                               (isSet→isGroupoid isSetℕ _ _ _ _
                                 (isSetℕ (suc (suc n)) _ refl refl) refl j i)
                               (snd f' i))
               (transportRefl _)
            ∙ λ i → (λ j → transportRefl (snd f' (j ∧ ~ i)) (j ∧ i))
                   ∙ λ j → transportRefl (snd f' (~ i ∨ j)) (i ∨ j)

           help : (w : suc (suc n) ≡ suc (suc n)) (t : refl ≡ w)
             → Square
               ((push (cellMapSˢᵏᵉˡFunGenGen Xsk (suc n) x₀ (fst f')
                       (snd f') (suc n) (suc n ≟ᵗ suc (suc n)) a)
               ∙ (λ i → inr (cellMapSˢᵏᵉˡFunGenComm Xsk (suc n) x₀
                               (fst f') (snd f') (suc n)
                               (eq w) (suc n ≟ᵗ suc (suc n)) a (~ i)))))
                (λ i → cofib→cofibCW n f' (eq w) (suc n ≟ᵗ suc (suc n))
                         (push a i))
                (λ _ → inl tt)
                (λ i → inr ((cong (λ p → subst (fst Xsk) p
                                 (fst f' (invEq (SαEqGen (suc n) (suc n) (eq w)
                                 (suc n ≟ᵗ suc (suc n))) (inl a))))
                           (sym (cong sym t)) ∙ transportRefl _) i))
           help with (n ≟ᵗ suc n)
           ... | lt w =
             J> (cong₂ _∙_
                   refl
                   ((λ j i → inr ((lUnit (cool j) (~ j)) (~ i)))
                   ∙ cong sym (cong-∙ inr (transportRefl _)
                              (snd f'))
                   ∙ symDistr _ _)
               ∙ GL.assoc _ _ _)
               ◁ flipSquare (flipSquare (symP (compPath-filler
                            (push (CWskel∙ Xsk x₀ n)
                            ∙ (λ i₁ → inr (snd f' (~ i₁))))
                            (sym (transportRefl (inr (f' .snd i0))))))
               ▷ λ j i → inr (lUnit (transportRefl (fst f' (ptSn (suc n)))) j i))
           ... | eq x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) x <ᵗsucm))
           ... | gt x = ⊥.rec (¬-suc-n<ᵗn x)
         ... | gt x = ⊥.rec (¬m<ᵗm x)

         cofib→cofibCW≡ : (x : _)
           → prefunctoriality.fn+1/fn (suc (suc (suc (suc n)))) (f .fst)
               (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) x
            ≡ cofib→cofibCW n f'
               (suc (suc n) ≟ᵗ suc (suc n)) (suc n ≟ᵗ suc (suc n)) x
         cofib→cofibCW≡ (inl x) = refl
         cofib→cofibCW≡ (inr x) = cofib→cofibCW≡inr x
         cofib→cofibCW≡ (push a i) = cofib→cofibCW≡push a i

         bouquetFunct≡ :
            prefunctoriality.bouquetFunct (suc (suc (suc (suc n))))
              (f .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm))
           ≡ CTB∘cofib→cofibCW∘BTC n f'
              (suc (suc n) ≟ᵗ suc (suc n)) (suc n ≟ᵗ suc (suc n))
         bouquetFunct≡ = funExt (λ x → cong (CTB→ n) (cofib→cofibCW≡ _))

       f = finCellApproxSˢᵏᵉˡImproved Xsk (suc n) x₀ f'
            (incl∙ Xsk x₀ ∘∙ f') (λ _ → refl) (suc (suc (suc (suc n))))
       g = finCellApproxSˢᵏᵉˡImproved Xsk (suc n) x₀ g'
            (incl∙ Xsk x₀ ∘∙ g') (λ _ → refl) (suc (suc (suc (suc n))))

       wraplem : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) (l1 l2 : y ≡ y)
         → p ∙∙ (l1 ∙ l2) ∙∙ sym p
         ≡ (p ∙∙ l1 ∙∙ sym p) ∙ (p ∙∙ l2 ∙∙ sym p)
       wraplem = J> λ l1 l2 → sym (rUnit _) ∙ cong₂ _∙_ (rUnit l1) (rUnit l2)

       CTB∘cofib→cofibCW∘BTC-Hom : (n : ℕ) (f' g' : _) (p : _) (q : _) (x : _)
         → CTB∘cofib→cofibCW∘BTC n (∙Π f' g') p q x
         ≡ SphereBouquet∙Π (CTB∘cofib→cofibCW∘BTC n f' p q , refl)
                           (CTB∘cofib→cofibCW∘BTC n g' p q , refl) .fst x
       CTB∘cofib→cofibCW∘BTC-Hom n f' g' (lt s) q x = ⊥.rec (¬m<ᵗm s)
       CTB∘cofib→cofibCW∘BTC-Hom n f' g' (eq _) (lt _) (inl _) = refl
       CTB∘cofib→cofibCW∘BTC-Hom zero f' g' (eq s) (lt d)
         (inr (t , base)) = refl
       CTB∘cofib→cofibCW∘BTC-Hom zero f' g' (eq s) (lt d)
         (inr ((zero , tt) , loop i)) j = CTB∘cofib→cofibCW∘BTC-Hom₀loop j i
         where
         p : I → _
         p i = subst S₊ (isSetℕ _ _ (cong (predℕ ∘ predℕ) s) refl i)

         q = cong (CTB∘cofib→cofibCW∘BTC zero f' (eq s) (lt d))
                  (sym (push fzero)) ∙ refl

         lem : (h : S₊∙ 1 →∙ X* zero)
           → cong (cofib→cofibCW zero h (eq s) (lt d)
                   ∘ inr ∘ invEq (SαEqGen 1 1 (eq s) (lt d)))
                   (push (fzero , false) ∙ sym (push (fzero , true)))
           ≡ (λ i → inr (fst h (loop i)))
         lem h = cong-∙  (cofib→cofibCW zero h (eq s) (lt d)
                        ∘ inr ∘ invEq (SαEqGen 1 1 (eq s) (lt d)))
                        (push (fzero , false)) (sym (push (fzero , true)))
             ∙ cong₂ _∙_
                (λ i j → inr (h .fst (SuspBool→S¹ (merid (p i false) j))))
                (λ i j → inr (h .fst (SuspBool→S¹ (merid (p i true) (~ j)))))
             ∙ sym (rUnit _)

         CTB∘cofib→cofibCW∘BTC-Hom₀loop :
             cong (CTB∘cofib→cofibCW∘BTC zero (∙Π f' g') (eq s) (lt d))
                  (λ i → inr (fzero , loop i))
           ≡ (sym q ∙∙ cong (CTB∘cofib→cofibCW∘BTC zero f' (eq s) (lt d))
                            (λ i → inr (fzero , loop i)) ∙∙ q)
           ∙ (sym q ∙∙ cong (CTB∘cofib→cofibCW∘BTC zero g' (eq s) (lt d))
                            (λ i → inr (fzero , loop i)) ∙∙ q)
         CTB∘cofib→cofibCW∘BTC-Hom₀loop =
           cong (cong (CTB→ zero))
                (cong-∙∙ (cofib→cofibCW zero (∙Π f' g') (eq s) (lt d)) _ _ _
              ∙ cong₃ _∙∙_∙∙_ (sym (rUnit (push x₀))) (lem (∙Π f' g')
              ∙ cong-∙ inr _ _)
              (cong sym (sym (rUnit (push x₀))))
              ∙ wraplem _ _ _ _)
           ∙ (cong-∙ (CTB→ zero) _ _
           ∙ cong₂ _∙_ (cong (cong (CTB→ zero))
             λ i → compPath-filler (push x₀) (λ t → inr (sym (snd f') t)) i
                 ∙∙ (λ j → inr (doubleCompPath-filler (sym (snd f'))
                                 (cong (fst f') loop) (snd f') (~ i) j))
                 ∙∙ sym (compPath-filler (push x₀)
                                 (λ t → inr (sym (snd f') t)) i))
             λ i → (cong (CTB→ zero))
                   (compPath-filler (push x₀) (λ t → inr (sym (snd g') t)) i
                 ∙∙ (λ j → inr (doubleCompPath-filler (sym (snd g'))
                                 (cong (fst g') loop) (snd g') (~ i) j))
                 ∙∙ sym (compPath-filler (push x₀)
                          (λ t → inr (sym (snd g') t)) i)))
           ∙ cong₂ _∙_
               (sym (cong (cong (CTB→ zero))
                      (cong-∙∙ (cofib→cofibCW zero f' (eq s) (lt d)) _ _ _
                     ∙ cong₃ _∙∙_∙∙_ refl (lem f') refl))
                     ∙ rUnit (cong (CTB∘cofib→cofibCW∘BTC zero f' (eq s) (lt d))
                                   (λ i → inr (fzero , loop i)))
                     ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))
               (sym (cong (cong (CTB→ zero))
                       (cong-∙∙ (cofib→cofibCW zero g' (eq s) (lt d)) _ _ _
                     ∙ cong₃ _∙∙_∙∙_ refl (lem g') refl))
                     ∙ rUnit (cong (CTB∘cofib→cofibCW∘BTC zero g' (eq s) (lt d))
                                   (λ i → inr (fzero , loop i)))
                     ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))
       CTB∘cofib→cofibCW∘BTC-Hom (suc n) f' g' (eq s) (lt d)
         (inr (t , north)) = refl
       CTB∘cofib→cofibCW∘BTC-Hom (suc n) f' g' (eq s) (lt d)
         (inr (t , south)) = refl
       CTB∘cofib→cofibCW∘BTC-Hom (suc n) f' g' (eq s) (lt d)
         (inr ((zero , tt) , merid a i)) j = CTB∘cofib→cofibCW∘BTC-Hom₀merid j i
         where
         p : (x : _) → transport (λ i₂ → S₊ (predℕ (predℕ (s i₂)))) x ≡ x
         p x = cong (λ p → transport p x) (cong (cong S₊) (isSetℕ _ _ _ refl))
             ∙ transportRefl x

         q = cong (CTB∘cofib→cofibCW∘BTC (suc n) f' (eq s) (lt d))
                  (sym (push fzero)) ∙ refl

         cong-h-σ : (h : S₊∙ (suc (suc n)) →∙ X* (suc n)) (a : _)
           → _
         cong-h-σ h a = (push (CWskel∙ Xsk x₀ (suc n))
                ∙∙ (λ i → inr ((sym (snd h) ∙∙ cong (fst h) (σS a) ∙∙ snd h) i))
                ∙∙ sym (push (CWskel∙ Xsk x₀ (suc n))))

         cong-CTB→∘h-σ≡ : (h : S₊∙ (suc (suc n)) →∙ X* (suc n)) (a : _)
           → cong (CTB∘cofib→cofibCW∘BTC (suc n) h (eq s) (lt d))
                   (λ i → inr (fzero , merid a i))
           ≡ cong (CTB→ (suc n)) (cong-h-σ h a)
         cong-CTB→∘h-σ≡ h a = cong (cong (CTB→ (suc n)))
             (cong-∙∙ (cofib→cofibCW (suc n) h (eq s) (lt d)) _ _ _
           ∙ cong₃ _∙∙_∙∙_ refl
              (cong-∙ (cofib→cofibCW (suc n) h (eq s) (lt d) ∘ inr
                    ∘ invEq (SαEqGen (suc (suc n)) (suc (suc n)) (eq s) (lt d)))
                     (push (fzero , a)) (sym (push (fzero , ptSn (suc n))))
                    ∙ cong₂ _∙_
                        (λ j i → inr (h .fst (merid (p a j) i)))
                        (λ j i → inr (h .fst (merid (p (ptSn (suc n)) j) (~ i))))
                     ∙ sym (cong-∙ (λ x → inr (h .fst x))
                                   (merid a) (sym (merid (ptSn (suc n)))))) refl
           ∙ λ i → compPath-filler (push (CW↪ Xsk (suc n) (CWskel∙ Xsk x₀ n)))
                                    (λ i → inr (snd h (~ i))) (~ i)
           ∙∙ (λ j → inr (doubleCompPath-filler (sym (snd h))
                            (λ i → fst h (σS a i))
                            (snd h) i j))
           ∙∙ sym (compPath-filler (push (CW↪ Xsk (suc n) (CWskel∙ Xsk x₀ n)))
                                   (λ i → inr (snd h (~ i))) (~ i)))

         CTB∘cofib→cofibCW∘BTC-merid≡ : (h : S₊∙ (suc (suc n)) →∙ X* (suc n))
           → cong (CTB∘cofib→cofibCW∘BTC (suc n) h (eq s) (lt d))
                   (λ i → inr (fzero , merid (ptSn (suc n)) i)) ≡ refl
         CTB∘cofib→cofibCW∘BTC-merid≡ h =
             cong-CTB→∘h-σ≡ h (ptSn (suc n))
           ∙ cong (cong (CTB→ (suc n)))
                  (cong₃ _∙∙_∙∙_ refl
                    ((λ j i → inr ((cong₃ _∙∙_∙∙_
                                      refl (cong (cong (fst h)) σS∙) refl
                                  ∙ ∙∙lCancel (snd h)) j i))) refl
                  ∙ ∙∙lCancel _)

         CTB∘cofib→cofibCW∘BTC-merid≡' :
           (h : S₊∙ (suc (suc n)) →∙ X* (suc n)) (a : _)
           → cong (CTB∘cofib→cofibCW∘BTC (suc n) h (eq s) (lt d))
                   (λ i → inr (fzero , σS a i))
            ≡ cong-CTB→∘h-σ≡ h a i1
         CTB∘cofib→cofibCW∘BTC-merid≡' h a =
            cong-∙ (λ q → CTB∘cofib→cofibCW∘BTC (suc n) h (eq s) (lt d)
                            (inr (fzero , q)))
                   (merid a) (sym (merid (ptSn (suc n))))
          ∙ cong₂ _∙_ (cong-CTB→∘h-σ≡ h a)
                      (cong sym (CTB∘cofib→cofibCW∘BTC-merid≡ h))
          ∙ sym (rUnit (cong-CTB→∘h-σ≡ h a i1))

         cong-h-σ-Hom : (a : _) → cong-h-σ (·Susp (S₊∙ (suc n)) f' g') a
                           ≡ cong-h-σ f' a ∙ cong-h-σ g' a
         cong-h-σ-Hom a =
           cong₃ _∙∙_∙∙_ refl
            (λ i j → inr ((sym (rUnit (cong (fst (·Susp (S₊∙ (suc n)) f' g'))
                                             (σS a)))
                        ∙ cong-∙ (fst (·Susp (S₊∙ (suc n)) f' g'))
                                 (merid a) (sym (merid (ptSn (suc n))))
                        ∙ cong₂ _∙_ refl (cong sym
                          (cong₂ _∙_
                            (cong₃ _∙∙_∙∙_ refl
                               (cong (cong (fst f'))
                                     (rCancel (merid (ptSn (suc n))))) refl
                              ∙ ∙∙lCancel (snd f'))
                            (cong₃ _∙∙_∙∙_ refl
                               (cong (cong (fst g'))
                                     (rCancel (merid (ptSn (suc n))))) refl
                              ∙ ∙∙lCancel (snd g'))
                          ∙ sym (rUnit refl)))
                        ∙ sym (rUnit _)) i j)) refl
           ∙ cong₃ _∙∙_∙∙_ refl (cong-∙ inr _ _) refl
           ∙ wraplem _ _ _ _

         CTB∘cofib→cofibCW∘BTC-Hom₀merid :
           cong (CTB∘cofib→cofibCW∘BTC (suc n) (∙Π f' g') (eq s) (lt d))
                (λ i → inr (fzero , merid a i))
           ≡ (sym q ∙∙ cong (CTB∘cofib→cofibCW∘BTC (suc n) f' (eq s) (lt d))
                            (λ i → inr (fzero , σS a i)) ∙∙ q)
           ∙ (sym q ∙∙ cong (CTB∘cofib→cofibCW∘BTC (suc n) g' (eq s) (lt d))
                            (λ i → inr (fzero , σS a i)) ∙∙ q)
         CTB∘cofib→cofibCW∘BTC-Hom₀merid = cong-CTB→∘h-σ≡ (∙Π f' g') a
           ∙ cong (cong (CTB→ (suc n))) (cong-h-σ-Hom a)
           ∙ cong-∙ (CTB→ (suc n)) (cong-h-σ f' a) (cong-h-σ g' a)
           ∙ cong₂ _∙_
              (rUnit _ ∙ cong₃ _∙∙_∙∙_ (rUnit refl)
                        (sym (CTB∘cofib→cofibCW∘BTC-merid≡' f' a)) (rUnit refl))
              (rUnit _ ∙ cong₃ _∙∙_∙∙_ (rUnit refl)
                        (sym (CTB∘cofib→cofibCW∘BTC-merid≡' g' a)) (rUnit refl))

       CTB∘cofib→cofibCW∘BTC-Hom zero f' g' (eq s) (lt d) (push a i) = refl
       CTB∘cofib→cofibCW∘BTC-Hom (suc n) f' g' (eq s) (lt d) (push a i) = refl
       CTB∘cofib→cofibCW∘BTC-Hom n f' g' (eq s) (eq d) x =
         ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) d <ᵗsucm))
       CTB∘cofib→cofibCW∘BTC-Hom n f' g' (eq s) (gt d) x =
         ⊥.rec (¬-suc-n<ᵗn d)
       CTB∘cofib→cofibCW∘BTC-Hom n f' g' (gt s) q x = ⊥.rec (¬m<ᵗm s)

       CTB∘cofib→cofibCW∘BTC-Hom' : (x : _)
         → prefunctoriality.bouquetFunct (suc (suc (suc (suc n))))
              (finCellApprox∙Π .fst)
              (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) x
          ≡ SphereBouquet∙Π
             (prefunctoriality.bouquetFunct (suc (suc (suc (suc n))))
               (f .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) , refl)
             (prefunctoriality.bouquetFunct (suc (suc (suc (suc n))))
               (g .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) , refl)
               .fst x
       CTB∘cofib→cofibCW∘BTC-Hom' x =
         funExt⁻ (bouquetFunct≡ (∙Π f' g') λ _ → refl) x
         ∙ CTB∘cofib→cofibCW∘BTC-Hom n f' g' _ _ x
         ∙ λ i → SphereBouquet∙Π
                   (bouquetFunct≡ f' (λ _ → refl) (~ i) , (λ _ → inl tt))
                   (bouquetFunct≡ g' (λ _ → refl) (~ i) , (λ _ → inl tt)) .fst x

       goal' : goalTy (incl∙ Xsk x₀ ∘∙ f') (incl∙ Xsk x₀ ∘∙ g')
       goal' =
         funExt⁻ (cong fst (H̃ˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n)) Xsk (suc n)
           {f = (fst (∙Π (incl∙ Xsk x₀ ∘∙ f') (incl∙ Xsk x₀ ∘∙ g')) ∘
             invEq (hasCWskelSphere (suc n) .snd))} finCellApprox∙Π)) (genHₙSⁿ n)
           ∙ cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
             ((λ i → bouquetDegree (λ x → CTB∘cofib→cofibCW∘BTC-Hom' x i)
                       .fst (λ _ → pos 1))
           ∙ funExt⁻ (cong fst (bouquetDegree∙Π _ _ _
              (prefunctoriality.bouquetFunct (suc (suc (suc (suc n))))
               (f .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) , refl)
              (prefunctoriality.bouquetFunct (suc (suc (suc (suc n))))
               (g .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) , refl)))
              λ _ → pos 1))
           ∙ cong₂ (GroupStr._·_ (snd (H̃ᶜʷ X' (suc n))))
                   (funExt⁻ (cong fst (sym (H̃ˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n)) Xsk (suc n)
                     {f = incl ∘ fst f' ∘ invEq (hasCWskelSphere (suc n) .snd)} f)))
                     (genHₙSⁿ n))
                   ((funExt⁻ (cong fst (sym (H̃ˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n)) Xsk (suc n)
                     {f = incl ∘ fst g' ∘ invEq (hasCWskelSphere (suc n) .snd)} g)))
                     (genHₙSⁿ n)))

       goal : (f : _) (fp : incl∙ Xsk x₀ ∘∙ f' ≡ f)
              (g : _) (gp : incl∙ Xsk x₀ ∘∙ g' ≡ g) → goalTy f g
       goal = J> (J> goal')

  -- THe Hurewicz map as a group homomorphism
  HurewiczHom : {n : ℕ} (X : CW ℓ) (x : fst X) (conX : isConnected 2 (fst X))
              → GroupHom (π'Gr n (fst X , x)) (H̃ᶜʷ X (suc n))
  fst (HurewiczHom {n = n} X x conX) = HurewiczMap X x
  snd (HurewiczHom {n = n} X x conX) =
    makeIsGroupHom λ f g → HurewiczMapHom X x f g conX

-- Naturality of the Hurewicz map
HurewiczMapNat : {n : ℕ} (X Y : CW ℓ) (x : fst X) (y : fst Y)
                    (g : (fst X , x) →∙ (fst Y , y))
    → H̃ᶜʷ→ {C = X} {D = Y} (suc n) (fst g) .fst ∘ HurewiczMap X x
    ≡ HurewiczMap Y y ∘ π'∘∙Hom n g .fst
HurewiczMapNat {n = n} X Y x y g = funExt
  (ST.elim (λ _ → isOfHLevelPath 2 (GroupStr.is-set (H̃ᶜʷ Y (suc n) .snd)) _ _)
    λ f → funExt⁻ (sym (cong fst (H̃ᶜʷ→comp
             {C = Sᶜʷ (suc n)} {D = X} {E = Y} (suc n) (fst g) (fst f))))
             (genHₙSⁿ n))

-- The Hurewicz map on abelisanised homotopy groups
HurewiczHomAb : (X : CW ℓ) (x : fst X) (isC : isConnected 2 (fst X))
  (n : ℕ) → AbGroupHom (AbelianizationAbGroup (π'Gr n (fst X , x))) (H̃ᶜʷAb X n)
fst (HurewiczHomAb X x isC n) =
  Abi.rec _ (AbGroupStr.is-set (snd (H̃ᶜʷAb X n)))
            (HurewiczHom X x isC .fst)
            lem
  where
  lem : (a b c : _) → _
  lem a b c = IsGroupHom.pres· (HurewiczHom X x isC .snd) _ _
            ∙ cong₂ (GroupStr._·_ (H̃ᶜʷ X (suc n) .snd)) refl
                (IsGroupHom.pres· (HurewiczHom X x isC .snd) _ _
                ∙ AbGroupStr.+Comm (snd (H̃ᶜʷAb X n)) _ _
                ∙ sym (IsGroupHom.pres· (HurewiczHom X x isC .snd) _ _))
            ∙ sym (IsGroupHom.pres· (HurewiczHom X x isC .snd) _ _)
snd (HurewiczHomAb X x isC n) = makeIsGroupHom
  (Abi.elimProp2 _ (λ _ _ → GroupStr.is-set (snd (H̃ᶜʷ X (suc n))) _ _)
    (IsGroupHom.pres· (HurewiczHom X x isC .snd)))


--- Part 3: proof of the Hurewicz theorem ---

-- The Hurewicz map is an equivalence on cofibres of sphere bouquets
private
 makeHurewiczMapCofibEquiv :
   {n m k : ℕ} (α : FinSphereBouquetMap∙ m k n)
   (ϕ : GroupHom (AbelianizationGroup (π'Gr n (cofib∙ (fst α))))
                 (H̃ˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ (fst α)) (suc n)))
   → ((k : _) → fst ϕ (πᵃᵇFinSphereBouquetMapGenerator α k)
                ≡ genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ (fst α) k)
   → isEquiv (fst ϕ)
 makeHurewiczMapCofibEquiv α ϕ hyp =
   makeℤ[]/Equiv
     (GroupIso→GroupEquiv
       (invGroupIso (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree α)))
     (GroupIso→GroupEquiv
       (invGroupIso (GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap (fst α)))) ϕ
       λ k → cong (fst ϕ)
       (sym (cong (inv' (fst (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree α)))
         (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreePresGens α k))
       ∙ ret (fst (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree α)) _)
     ∙ hyp k
     ∙ sym (ret (fst (GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap (fst α)))
       (genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ (fst α) k))
     ∙ cong (ℤ[]/ImSphereMap→HₙSphereBouquetⁿ/ (fst α))
       (isGen-genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ (fst α) k)

HurewiczMapCofibEquiv : ∀ {n m k : ℕ}
  → (α : FinSphereBouquetMap∙ m k n)
  → (isC : isConnected 2 (cofib (fst α)))
  → isEquiv (fst (HurewiczHomAb (SphereBouquet/ᶜʷ (fst α)) (inl tt) isC n))
HurewiczMapCofibEquiv {n = n} {m} {k} α isC = makeHurewiczMapCofibEquiv α
  (HurewiczHomAb (SphereBouquet/ᶜʷ (fst α)) (inl tt) isC n) λ w →
    funExt⁻ (cong fst (H̃ˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n)) (SphereBouquet/ˢᵏᵉˡ (fst α))
                       (suc n) {f = realiseInr w} (finCellApproxInr' w)))
            (genHₙSⁿ n)
  ∙ cong [_] (Σ≡Prop (λ _ → isOfHLevelPathP' 1 (isSetΠ (λ _ → isSetℤ)) _ _)
      ((λ i x → sumFinℤ (λ a → degree (suc n) λ t
               → pickPetal x (CTB' n α trich₁ trich₂
                  (cofib→cofib≡' w (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm)
                   (preBTC' n α trich₁ trich₂ a .fst t) (~ i)))))
    ∙  funExt λ x → sumFin-choose _+_ 0 (λ _ → refl) +Comm
       (λ a → degree (suc n)
         λ s → pickPetal x (CTB' n α trich₁ trich₂
                (cofib→cofib n α w (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm)
                 trich₁ trich₂ (preBTC' n α trich₁ trich₂ a .fst s ))))
       (ℤFinGenerator (fin→SphereBouquet/Cell (fst α) trich₁ trich₂ w) x)
       (pickCell n trich₁)
       (nonVanish n α _ _ x w)
       (λ x' q → ⊥.rec (≠pickCell→Empty trich₁ x' q))))
  where
  pickCell : (n : ℕ) (t : _)
    → Fin (ScardGen (suc n) (suc n) (Trichotomyᵗ-suc t))
  pickCell n (lt s) = ⊥.rec (¬m<ᵗm s)
  pickCell n (eq s) = fzero
  pickCell n (gt s) = ⊥.rec (¬m<ᵗm s)

  ≠pickCell→Empty : (t : _)
    (s : Fin (ScardGen (suc n) (suc n) (Trichotomyᵗ-suc t)))
    → ¬ s ≡ pickCell n t → ⊥
  ≠pickCell→Empty (eq x) (zero , tt) s = s refl

  -- some abbreviations
  module _ (n : ℕ)
    (α : FinSphereBouquetMap∙ m k n)
    (trich₁ : _) (trich₂ : _) where

    CTB' = BouquetFuns.CTB (suc n)
     (SphereBouquet/CardGen m k (suc n) trich₁ trich₂)
     (SphereBouquet/αGen m k (fst α) (suc n) trich₁ trich₂)
     (SphereBouquet/EqGen m k (suc n) (fst α) (Trichotomyᵗ-suc trich₁)
       trich₁ trich₂)

    Pushout→Bouquet' = Pushout→Bouquet (suc n)
     (SphereBouquet/CardGen m k (suc n) trich₁ trich₂)
     (SphereBouquet/αGen m k (fst α) (suc n) trich₁ trich₂)
     (SphereBouquet/EqGen m k (suc n) (fst α) (Trichotomyᵗ-suc trich₁)
       trich₁ trich₂)

    Pushout→Bouquet'∘EqGen = Pushout→Bouquet'
                           ∘ fst (SphereBouquet/EqGen m k (suc n) (fst α)
                                  (Trichotomyᵗ-suc trich₁) trich₁ trich₂)

    preBTC' = preBTC (suc n)
          (ScardGen (suc n) (suc n) (Trichotomyᵗ-suc trich₁))
          (λ t → Sgen.Sfam∙ (suc n) n trich₂)
          (SαEqGen (suc n) (suc n) (Trichotomyᵗ-suc trich₁) trich₂)

  trich₁ = suc n ≟ᵗ suc n
  trich₂ = suc n ≟ᵗ suc (suc n)

  realiseInr : (w : Fin k)
    → realise (Sˢᵏᵉˡ (suc n)) → realise (SphereBouquet/ˢᵏᵉˡ (fst α))
  realiseInr w = fst (hasCWskelSphereBouquet/ (fst α) .snd)
        ∘ preπ'FinSphereBouquetMapGenerator α w .fst
        ∘ invEq (hasCWskelSphere (suc n) .snd)

  Sⁿ→cofib : {n : ℕ} (m k : _) (α : FinSphereBouquetMap∙ m k n)
      (w : Fin k) (r : _) (P : _)
      → Sgen.Sfam (suc n) r P → SphereBouquet/FamGen m k (fst α) r P
  Sⁿ→cofib m k α w (suc r) (lt x) s = tt
  Sⁿ→cofib m k α w (suc r) (eq x) s = inr (w , s)
  Sⁿ→cofib m k α w (suc r) (gt x) s = inr (inr (w , s))

  Sⁿ→cofib≡  : {n : ℕ} (m k : _) (α : FinSphereBouquetMap∙ m k n)
      (w : Fin k) (r : _) (P : _) (Q : _) (x : Sgen.Sfam (suc n) r Q)
     → invEq (SphereBouquet/EqGen m k r (fst α)
               (Trichotomyᵗ-suc P) P Q)
              (inl (Sⁿ→cofib m k α w r Q x))
      ≡ Sⁿ→cofib m k α w (suc r) (Trichotomyᵗ-suc P)
          (invEq (SαEqGen (suc n) r (Trichotomyᵗ-suc P) Q) (inl x))
  Sⁿ→cofib≡  m k α w (suc r) (lt s) Q x = refl
  Sⁿ→cofib≡  m k α w (suc r) (eq s) (lt t) x = push w
  Sⁿ→cofib≡  m k α w (suc r) (eq s) (eq t) x =
    ⊥.rec (falseDichotomies.eq-eq (s , t))
  Sⁿ→cofib≡  m k α w (suc r) (eq s) (gt t) x =
    ⊥.rec (¬-suc-n<ᵗn (transport (λ i → s (~ i) <ᵗ r) t))
  Sⁿ→cofib≡  m k α w (suc r) (gt s) (lt t) x = ⊥.rec (¬squeeze (t , s))
  Sⁿ→cofib≡  m k α w (suc r) (gt s) (eq t) x = refl
  Sⁿ→cofib≡  m k α w (suc r) (gt s) (gt t) x = refl

  module _ (n : ℕ) (α : FinSphereBouquetMap∙ m k n) where
    cofib→cofib : (w : _) (n' : Fin (suc (suc (suc n)))) (P : _) (Q : _)
     → cofib (invEq (SαEqGen (suc n) (fst n') (Trichotomyᵗ-suc P) Q) ∘ inl)
     → cofib (invEq (SphereBouquet/EqGen m k (fst n') (fst α)
                      (Trichotomyᵗ-suc P) P Q) ∘ inl)
    cofib→cofib w n' P Q (inl x) = inl tt
    cofib→cofib w n' P Q (inr x) =
      inr (Sⁿ→cofib m k α w (suc (fst n')) (Trichotomyᵗ-suc P) x)
    cofib→cofib w n' P Q (push a i) =
       (push (Sⁿ→cofib m k α w (fst n') Q a)
      ∙ λ i → inr (Sⁿ→cofib≡  m k α w (fst n') P Q a i)) i

    module _ (n : ℕ) (w : Fin k) (x : _)
      (p : Path (S₊ (suc n)) (ptSn (suc n)) (ptSn (suc n))) where
      teGen : ¬ (fst w ≡ fst x)
        → (cong (pickPetal x) (push w) ∙∙
           (λ i → pickPetal x (inr (w , p i))) ∙∙
           cong (pickPetal x) (sym (push w))) ≡ refl
      teGen nope with (fst x ≟ᵗ fst w)
      ... | lt x = sym (rUnit refl)
      ... | eq x = ⊥.rec (nope (sym x))
      ... | gt x = sym (rUnit refl)

      teGen' : (fst w ≡ fst x)
        → (cong (pickPetal x) (push w)
        ∙∙ (λ i → pickPetal x (inr (w , p i)))
        ∙∙ cong (pickPetal x) (sym (push w))) ≡ p
      teGen' aye with (fst x ≟ᵗ fst w)
      ... | lt ine = ⊥.rec (¬m<ᵗm (subst (fst x <ᵗ_) aye ine))
      ... | eq x = sym (rUnit p)
      ... | gt ine = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst x) aye ine))

  -- key lemma: roughly, Hurewicz map preserves generators
  nonVanish : (n : ℕ) (α : _) (trich₁ : _) (trich₂ : _) (x : Fin _) (w : _)
    → degree (suc n) (λ s →
             pickPetal x
              (CTB' n α trich₁ trich₂
               (cofib→cofib n α w (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) trich₁ trich₂
                (preBTC' n α trich₁ trich₂ (pickCell n trich₁) .fst s))))
     ≡ ℤFinGenerator (fin→SphereBouquet/Cell (fst α) trich₁ trich₂ w) x
  nonVanish zero α (eq s) (lt t) x w =
    cong (degree (suc zero))
         (funExt (λ a → cong (pickPetal x)
           λ i → CTB' zero α (eq (isSetℕ _ _ s refl i)) (lt t)
         (cofib→cofib zero α w (1 , tt) (eq (isSetℕ _ _ s refl i)) (lt t)
          (preBTC' zero α (eq (isSetℕ _ _ s refl i)) (lt t) fzero .fst a))))
        ∙ main pick∘CTB'∘cofib→cofib∘BTC' refl
   where
   pick∘CTB'∘cofib→cofib∘BTC' = pickPetal x
       ∘ CTB' zero α (eq refl) (lt t)
       ∘ cofib→cofib zero α w (1 , tt) (eq refl) (lt t)
       ∘ preBTC' zero α (eq refl) (lt t) fzero .fst

   CTB'∘cofib→cofib =
       CTB' zero α (eq refl) (lt t)
     ∘ cofib→cofib zero α w (1 , <ᵗ-trans <ᵗsucm <ᵗsucm) (eq refl) (lt t)

   lem : cong pick∘CTB'∘cofib→cofib∘BTC' loop
     ≡ cong (pickPetal x) (push w)
    ∙∙ (λ i → pickPetal x (inr (w , σSn 0 false i)))
    ∙∙ cong (pickPetal x) (sym (push w))
   lem = cong (cong (pickPetal x ∘ CTB'∘cofib→cofib)) lem1
    ∙ cong-∙∙ (pickPetal x ∘ CTB'∘cofib→cofib)
              (push tt) (λ i₁ → inr (loop i₁)) (sym (push tt))
    ∙ cong₃ _∙∙_∙∙_ refl
                    lem3
                    refl
    ∙ comm∙∙S¹ _ _
    where
    lem1 : cong (preBTC' zero α (eq refl) (lt t) fzero .fst) loop
       ≡ push tt ∙∙ (λ i → inr (loop i)) ∙∙ sym (push tt)
    lem1 = cong (λ p → push tt ∙∙ p ∙∙ sym (push tt))
              ((λ j i → inr (cong-∙ (invEq (SαEqGen 1 1
                                      (Trichotomyᵗ-suc (eq refl)) (lt t)))
                      (push (fzero , false)) (sym (push (fzero , true))) j i))
              ∙ λ j i → inr (rUnit loop (~ j) i))

    lem2 : cong (fst (SphereBouquet/EqGen m k (suc zero) (fst α)
               (Trichotomyᵗ-suc (eq refl)) (eq refl) (lt t)))
               (λ i → inr (w , loop i))
        ≡ (push (w , false) ∙ sym (push (w , true)))
    lem2 = (λ j i → transportRefl (SphereBouquet/EqBottomMainGen m k (fst α)
                                    .fst (inr (w , loop i))) j)
        ∙ cong-∙ (λ K → ⋁→cofibFst (λ _ → Bool , true) (inr (w , K)))
                  (merid false) (sym (merid true))

    lem3 : cong (pickPetal x ∘ CTB' zero α (eq refl) (lt t))
              (λ i → inr (inr (w , loop i)))
            ≡ (cong (pickPetal x) (push w )
            ∙∙ (λ i → pickPetal x (inr (w , σSn 0 false i)))
            ∙∙ cong (pickPetal x) (sym (push w)))
    lem3 =
      cong (cong (pickPetal x))
      ((λ j i → Pushout→Bouquet' zero α (eq refl) (lt t) (lem2 j i))
      ∙ cong-∙ (Pushout→Bouquet' zero α (eq refl) (lt t))
               (push (w , false)) (sym (push (w , true)))
      ∙ cong₂ _∙_ refl (sym (rUnit _))
      ∙ sym (GL.assoc _ _ _) ∙ sym (doubleCompPath≡compPath _ _ _))
      ∙ cong-∙∙ (pickPetal x)
                (push w) (λ i → (inr (w , σSn 0 false i))) (sym (push w))

    comm∙∙S¹ : ∀ (p q : ΩS¹) → p ∙∙ q ∙∙ sym p ≡ q
    comm∙∙S¹ p q = doubleCompPath≡compPath p q (sym p)
                 ∙ comm-ΩS¹ p _
                 ∙ sym (GL.assoc _ _ _)
                 ∙ cong (q ∙_) (lCancel p)
                 ∙ sym (rUnit q)

   pick∘CTB'∘cofib→cofib∘BTC'-const : ¬ (fst w ≡ fst x) → (r : _)
     → pick∘CTB'∘cofib→cofib∘BTC' r ≡ base
   pick∘CTB'∘cofib→cofib∘BTC'-const nope base = refl
   pick∘CTB'∘cofib→cofib∘BTC'-const nope (loop i) j =
     (lem ∙ teGen _ α zero w x (σS false) nope) j i

   pick∘CTB'∘cofib→cofib∘BTC'-id : (fst w ≡ fst x) → (r : _)
     → pick∘CTB'∘cofib→cofib∘BTC' r ≡ r
   pick∘CTB'∘cofib→cofib∘BTC'-id aye base = refl
   pick∘CTB'∘cofib→cofib∘BTC'-id aye (loop i) j =
     (lem ∙ teGen' _ α zero w x (σS false) aye) j i

   main : (pick∘CTB'∘cofib→cofib∘BTC* : _)
     → pick∘CTB'∘cofib→cofib∘BTC' ≡ pick∘CTB'∘cofib→cofib∘BTC*
     → degree 1 pick∘CTB'∘cofib→cofib∘BTC* ≡ ℤFinGenerator w x
   main _ p with (fst w ≟ᵗ fst x)
   ... | lt wa =
     cong (degree (suc zero))
      (sym p ∙ funExt (λ d → pick∘CTB'∘cofib→cofib∘BTC'-const
                              (λ s → ¬m<ᵗm (subst (_<ᵗ fst x) s wa)) d))
             ∙ degreeConst (suc zero)
   ... | eq x = (cong (degree (suc zero)) (sym p)
              ∙ cong (degree 1) (funExt (pick∘CTB'∘cofib→cofib∘BTC'-id x)))
              ∙ degreeIdfun (suc zero)
   ... | gt wa =
     cong (degree (suc zero))
      (sym p ∙ funExt (λ d → pick∘CTB'∘cofib→cofib∘BTC'-const
                             (λ s → ¬m<ᵗm (subst (fst x <ᵗ_) s wa)) d))
             ∙ degreeConst (suc zero)

  nonVanish (suc n) α (eq s) (lt t) x w =
    cong (degree (suc (suc n)))
      (funExt (λ asd → cong (pickPetal x)
        λ i → CTB' (suc n) α (eq (isSetℕ _ _ s refl i)) (lt t)
      (cofib→cofib (suc n) α w (suc (suc n) , <ᵗ-trans <ᵗsucm <ᵗsucm)
                                (eq (isSetℕ _ _ s refl i)) (lt t)
       (preBTC' (suc n) α (eq (isSetℕ _ _ s refl i)) (lt t) fzero .fst asd))))
      ∙ TR.rec (isProp→isOfHLevelSuc n (isSetℤ _ _))
          (λ hyp → main hyp (discreteℕ _ _) unlock)
          (isConnectedPath _
            (isConnectedPath _ (sphereConnected (suc (suc n))) _ _)
             (cong (λ x₃ → pickPetal x (CTB'∘cofib→cofib x₃)) (push tt))
               refl .fst)
   where
   pick∘CTB'∘cofib→cofib∘BTC' = pickPetal x
       ∘ CTB' (suc n) α (eq refl) (lt t)
       ∘ cofib→cofib (suc n) α w (suc (suc n) , <ᵗ-trans <ᵗsucm <ᵗsucm)
                     (eq refl) (lt t)
       ∘ preBTC' (suc n) α (eq refl) (lt t) fzero .fst

   CTB'∘cofib→cofib = CTB' (suc n) α (eq refl) (lt t)
         ∘ cofib→cofib (suc n) α w (suc (suc n) , <ᵗ-trans <ᵗsucm <ᵗsucm)
                (eq refl) (lt t)

   module _ (hyp : cong (λ w → pickPetal x (CTB'∘cofib→cofib w)) (push tt)
                 ≡ refl) where
    lem : (a : _) → cong pick∘CTB'∘cofib→cofib∘BTC' (merid a)
      ≡ cong (pickPetal x) (push w)
      ∙∙ cong (pickPetal x) (λ i → inr (w , σS a i))
      ∙∙ cong (pickPetal x) (sym (push w))
    lem a = cong (cong (pickPetal x ∘ CTB'∘cofib→cofib)) (lem1 a)
            ∙ cong-∙∙ (pickPetal x ∘ CTB'∘cofib→cofib) _ _ _
            ∙ cong₃ _∙∙_∙∙_
                hyp
                (cong (cong (pickPetal x))
                  (cong-∙ (λ z → CTB'∘cofib→cofib (inr z))
                    (merid a) (sym (merid (ptSn (suc n))))
                ∙ cong₂ _∙_ (lem2 a) (cong sym (lem2 (ptSn (suc n))))
                ∙ pathLem _ (push w)
                   (λ i → inr (w , σS a i)) _
                   (λ i → inr (transportRefl w (~ i) , north))
                   (λ i → inr (w , σS (ptSn (suc n)) i))
                  λ j i → inr (w , rCancel (merid (ptSn (suc n))) (~ j) i))
                ∙ cong-∙∙ (pickPetal x) _ _ _)
                (cong sym hyp)
            ∙ sym (rUnit _)
     where
     lem1 : (a : _)
       → cong (preBTC' (suc n) α (eq refl) (lt t) fzero .fst) (merid a)
        ≡ push tt ∙∙ (λ i → inr (σS a i)) ∙∙ sym (push tt)
     lem1 a = cong (λ p → push tt ∙∙ p ∙∙ sym (push tt))
              λ j i → inr ((cong-∙ (invEq
           (SαEqGen (suc (suc n)) (suc (suc n)) (Trichotomyᵗ-suc (eq refl))
            (lt t))) (push (fzero , a)) (sym (push (fzero , ptSn (suc n))))
          ∙ cong₂ _∙_ (cong merid (transportRefl a))
                      (cong (sym ∘ merid) (transportRefl (ptSn (suc n))))) j i)

     transportRefl-transportRefl : ∀ {ℓ} {A : Type ℓ} (x : A)
       → Square {A = A} (λ i → transportRefl (transportRefl x i) (~ i))
                         refl refl refl
     transportRefl-transportRefl x =
       (gen _ _ _ _ _ _ _ _
         (λ i j → transportRefl (transportRefl x i) j)
       ∙ rCancel _)
      where
      gen : ∀ {ℓ} {A : Type ℓ} (x y : A) (p : x ≡ y)
        (z : A) (l : x ≡ z) (w : A) (r : y ≡ w) (q : z ≡ w)
        (P : Square p q l r) → (λ i → P i (~ i)) ≡ r ∙ sym q
      gen x = J> (J> (J> (J> rUnit refl)))

     lem2 : (a : _)
       → cong (Pushout→Bouquet'∘EqGen (suc n) α (eq refl) (lt t))
              (λ i → inr (w , merid a i))
       ≡ push w
       ∙∙ (λ i → (inr (w , σS a i)))
       ∙∙ λ i → (inr (transportRefl w (~ i) , north))
     lem2 a =
       (cong (cong (Pushout→Bouquet' (suc n) α (eq refl) (lt t)))
                  (λ j i → transport refl (push (w , a) i))
                ∙ cong (cong (Pushout→Bouquet' (suc n) α (eq refl) (lt t)))
                  (cong₂ _∙_ refl refl)
                ∙ cong-∙ (Pushout→Bouquet' (suc n) α (eq refl) (lt t)) _ _
                ∙ cong₃ _∙∙_∙∙_ refl
                  (cong₂ _∙_ refl refl)
                  refl
                ∙ cong₂ _∙_ refl
                  (λ j i → inr (transportRefl-transportRefl w j i , north))
                ∙ sym (GL.assoc _ _ _)
                ∙ (λ j → push (transportRefl w j)
                  ∙ (λ i → inr (transportRefl w j
                         , σS (transportRefl a j) i))
                  ∙ λ i → inr (transp (λ i₁ → Fin k) (j ∧ ~ i) w , north))
                  ∙ sym (doubleCompPath≡compPath _ _ _))

     pathLem : ∀ {ℓ} {A : Type ℓ} {x : A}
       (y : A) (p : x ≡ y) (q : y ≡ y) (z : A) (r : y ≡ z)
       (q2 : y ≡ y) → refl ≡ q2
         → (p ∙∙ q ∙∙ r) ∙ (sym r ∙∙ sym q2 ∙∙ sym p)
         ≡ (p ∙∙ q ∙∙ sym p)
     pathLem =
       J> λ q → J> (J> cong₂ _∙_ (sym (rUnit q)) (sym (rUnit refl)))

    pick∘CTB'∘cofib→cofib∘BTC'-const : ¬ (fst w ≡ fst x) → (r : _)
      → pick∘CTB'∘cofib→cofib∘BTC' r ≡ north
    pick∘CTB'∘cofib→cofib∘BTC'-const nope north = refl
    pick∘CTB'∘cofib→cofib∘BTC'-const nope south = refl
    pick∘CTB'∘cofib→cofib∘BTC'-const nope (merid a i) j =
      (lem a ∙ teGen _ α (suc n) w x (σS a) nope) j i

    pick∘CTB'∘cofib→cofib∘BTC'-id : (fst w ≡ fst x) → (r : _)
      → pick∘CTB'∘cofib→cofib∘BTC' r ≡ r
    pick∘CTB'∘cofib→cofib∘BTC'-id aye north = refl
    pick∘CTB'∘cofib→cofib∘BTC'-id aye south = merid (ptSn (suc n))
    pick∘CTB'∘cofib→cofib∘BTC'-id aye (merid a i) j =
      ((lem a ∙ teGen' _ α (suc n) w x (σS a) aye)
      ◁ symP (compPath-filler (merid a) (sym (merid (ptSn (suc n)))))) j i

    main : Dec (fst w ≡ fst x) → (l : _)
      → degree (suc (suc n)) pick∘CTB'∘cofib→cofib∘BTC'
       ≡ ℤFinGenerator* w x {ℓ-zero} l
    main (yes p) l =
      cong (degree (suc (suc n))) (funExt (pick∘CTB'∘cofib→cofib∘BTC'-id p))
      ∙ degreeIdfun (suc (suc n))
      ∙ sym (ℤFinGenerator*₁ w x l p)
    main (no q) l  =
      cong (degree (suc (suc n))) (funExt (pick∘CTB'∘cofib→cofib∘BTC'-const q))
      ∙ degreeConst (suc (suc n))
      ∙ sym (ℤFinGenerator*₀ w x l q)

  nonVanish n α (eq s) (eq t) x w =
    ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) t <ᵗsucm))
  nonVanish n α (eq s) (gt t) x w =
    ⊥.rec (¬-suc-n<ᵗn t)
  nonVanish n α (gt s) trich₂ x w = ⊥.rec (¬m<ᵗm s)

  finCellApproxInr : (w : _)
    → finCellApprox (Sˢᵏᵉˡ (suc n)) (SphereBouquet/ˢᵏᵉˡ (fst α))
                     (realiseInr w) (suc (suc (suc n)))
  fmap (fst (finCellApproxInr w)) (r , s) =
    Sⁿ→cofib m k α w r (r ≟ᵗ suc (suc n))
  fcomm (fst (finCellApproxInr w)) (r , s) =
    Sⁿ→cofib≡  m k α w r _ _
  snd (finCellApproxInr w) =
    →FinSeqColimHomotopy _ _ λ s →
      cong (incl {n = suc (suc (suc n))})
           (lem1 _ s
          ∙ cong (SphereBouquet/FamTopElementGen m k (suc (suc (suc n))) (fst α)
                  <ᵗsucm (suc (suc (suc n)) ≟ᵗ suc (suc n)) .fst
                 ∘ preπ'FinSphereBouquetMapGenerator α w .fst)
                 (sym (lem2 s)))
    where
    lem1 : (P : _) (s : _)
      → Sⁿ→cofib m k α w (suc (suc (suc n))) P s
      ≡ SphereBouquet/FamTopElementGen m k (suc (suc (suc n)))
         (fst α) <ᵗsucm P .fst
          (preπ'FinSphereBouquetMapGenerator α w .fst
           (invEq
            (SfamGenTopElement (suc n) (suc (suc (suc n)))
             (<ᵗ-trans <ᵗsucm <ᵗsucm) P) s))
    lem1 (lt x) = λ _ → refl
    lem1 (eq x) =
      ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) (λ i → predℕ (x (~ i))) <ᵗsucm))
    lem1 (gt x) = λ _ → refl

    lem2 : (x : Sfam (suc n) (suc (suc (suc n))))
      → invEq (hasCWskelSphere (suc n) .snd) (incl x)
       ≡ invEq (SfamGenTopElement (suc n) (suc (suc (suc n)))
                (<ᵗ-trans {n = n} {m = suc n} {k = suc (suc n)} <ᵗsucm <ᵗsucm)
                (suc (suc (suc n)) ≟ᵗ suc (suc n))) x
    lem2 x = cong (invEq (hasCWskelSphere (suc n) .snd)) genLem
           ∙ retEq (hasCWskelSphere (suc n) .snd) _
     where
     gen : (P : _) (Q : _) (x : Sgen.Sfam (suc n) (suc (suc (suc n))) P)
       → x ≡ invEq (SαEqGen (suc n) (suc (suc n)) P Q)
                (inl (fst (SfamGenTopElement (suc n) (suc (suc n)) <ᵗsucm Q)
                  (invEq (SfamGenTopElement (suc n) (suc (suc (suc n)))
                    (<ᵗ-trans <ᵗsucm <ᵗsucm) P) x)))
     gen P (lt s) x = ⊥.rec (¬squeeze (s , <ᵗsucm))
     gen (lt t) (eq s) x = refl
     gen (eq t) (eq s) x =
       ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) (cong (predℕ ∘ predℕ) (sym t)) <ᵗsucm))
     gen (gt t) (eq s) x = refl
     gen P (gt s) x = ⊥.rec (¬m<ᵗm s)

     genLem : incl x
       ≡ fst (hasCWskelSphere (suc n) .snd)
              (invEq (SfamGenTopElement (suc n) (suc (suc (suc n)))
                      (<ᵗ-trans {n = n} {m = suc n} {k = suc (suc n)}
                        <ᵗsucm <ᵗsucm)
                      (suc (suc (suc n)) ≟ᵗ suc (suc n))) x)
     genLem = cong incl (gen _ _ x) ∙ sym (push _)


  cofib→cofib≡ : (w : _) (n' : Fin (suc (suc (suc n)))) (x : _)
    → cofib→cofib n α w n' (fst n' ≟ᵗ suc n) (fst n' ≟ᵗ suc (suc n)) x
    ≡ prefunctoriality.fn+1/fn (suc (suc (suc n)))
                               (fst (finCellApproxInr w)) n' x
  cofib→cofib≡ w n' (inl x) = refl
  cofib→cofib≡ w n' (inr x) = refl
  cofib→cofib≡ w n' (push a i) = refl

  finCellApproxInr' : (w : _)
    → finCellApprox (Sˢᵏᵉˡ (suc n))
        (SphereBouquet/ˢᵏᵉˡ (fst α)) (realiseInr w) (suc (suc (suc (suc n))))
  fmap (fst (finCellApproxInr' w)) m' x =
    Sⁿ→cofib m k α w (fst m') (fst m' ≟ᵗ suc (suc n)) x
  fcomm (fst (finCellApproxInr' w)) n x =
    Sⁿ→cofib≡ m k α w (fst n) _ _ x
  snd (finCellApproxInr' w) = →FinSeqColimHomotopy _ _ λ s →
      cong (incl {n = suc (suc (suc (suc n)))})
           (cong (Sⁿ→cofib m k α w (suc (suc (suc (suc n))))
                                   ((4 +ℕ n) ≟ᵗ (2 +ℕ n)))
                 (sym (secEq (_ , SˢᵏᵉˡConverges (suc n) 1) s))
               ∙ mainLemma ((4 +ℕ n) ≟ᵗ (2 +ℕ n))
                       (suc (suc (suc n)) ≟ᵗ suc n)
                       (suc (suc (suc n)) ≟ᵗ suc (suc n))
                 (invEq (invEq (SαEq (suc n) (1 +ℕ suc (suc n)))
                       ∘ inl , SˢᵏᵉˡConverges (suc n) 1) s))
    ∙ sym (push _)
    ∙ funExt⁻ (snd (finCellApproxInr w))
               (fincl (suc (suc (suc n)) , <ᵗsucm)
                 (invEq (invEq (SαEq (suc n) (1 +ℕ suc (suc n)))
                              ∘ inl , SˢᵏᵉˡConverges (suc n) 1) s))
    ∙ cong (realiseInr w)
            (push (invEq (invEq (SαEq (suc n) (1 +ℕ suc (suc n)))
                               ∘ inl , SˢᵏᵉˡConverges (suc n) 1) s))
      ∙ λ i → realiseInr w (incl {n = suc (suc (suc (suc n)))}
                             (secEq (_ , SˢᵏᵉˡConverges (suc n) 1) s i))
    where
    mainLemma : (P : _) (Q : _) (R : _) (s : _)
      → Sⁿ→cofib m k α w (suc (suc (suc (suc n)))) P
           (invEq (SαEqGen (suc n) (suc (suc (suc n))) P R) (inl s))
       ≡ invEq (SphereBouquet/EqGen m k (suc (suc (suc n))) (fst α) P Q R)
               (inl (Sⁿ→cofib m k α w (suc (suc (suc n))) R s))
    mainLemma (lt x) Q R _ = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x <ᵗsucm))
    mainLemma (eq x) Q R _ =
      ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) (sym (cong (predℕ ∘ predℕ) x))
                                            (<ᵗ-trans <ᵗsucm <ᵗsucm)))
    mainLemma (gt x) Q (lt s) _ = ⊥.rec (¬-suc-n<ᵗn s)
    mainLemma (gt x) Q (eq s) _ =
      ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) (sym (cong predℕ s)) <ᵗsucm))
    mainLemma (gt x) (lt t) (gt s) _ = ⊥.rec (¬m<ᵗm (<ᵗ-trans x t))
    mainLemma (gt x) (eq t) (gt s) _ =
      ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc (suc n))) (λ i → t (~ i)) x))
    mainLemma (gt x) (gt t) (gt s) _ = refl

  cofib→cofib≡' : (w : _) (n' : Fin (suc (suc (suc n)))) (x : _)
    → cofib→cofib n α w n' (fst n' ≟ᵗ suc n) (fst n' ≟ᵗ suc (suc n)) x
    ≡ prefunctoriality.fn+1/fn (suc (suc (suc (suc n))))
       (fst (finCellApproxInr' w)) (injectSuc n') x
  cofib→cofib≡' w n' (inl x) = refl
  cofib→cofib≡' w n' (inr x) = refl
  cofib→cofib≡' w n' (push a i) = refl

private
  preHurewiczLemma : (n : ℕ) (X : CWexplicit ℓ) (conX : isConnected 2 (fst X))
    → ((l : _) (str : _) (t : _)
      → isEquiv (HurewiczHomAb (CWexplicit→CWskel X .fst (suc (suc (suc n)))
                               , str) l t n .fst))
    → (x : fst X) → isEquiv (HurewiczHomAb (CWexplicit→CW X) x conX n .fst)
  preHurewiczLemma {ℓ = ℓ} n X conX ind' x =
    TR.rec (isPropIsEquiv _)
      (λ t → subst isEquiv (funExt (altEquiv≡ t)) (altEquiv t .fst .snd))
      (isConnected-CW↪∞ (suc zero) Xˢᵏᵉˡ x₀ .fst)
    where
    e∞ = snd (snd X)
    e∞⃗ = fst e∞
    e∞⃖ = invEq e∞
    x₀ = e∞⃗ x
    Xˢᵏᵉˡ = CWexplicit→CWskel X

    X∙ : Pointed _
    fst X∙ = fst X
    snd X∙ = x

    X₃₊ₙ = fst Xˢᵏᵉˡ (suc (suc (suc n)))
    X₃₊ₙ≅X∞ = realiseSubComplex (suc (suc (suc n))) Xˢᵏᵉˡ

    Xˢᵘᵇ : CW ℓ
    Xˢᵘᵇ = realise (subComplex Xˢᵏᵉˡ (suc (suc (suc n))))
        , ∣ (subComplex Xˢᵏᵉˡ (suc (suc (suc n))))
        , idEquiv _ ∣₁

    module _ (t : fiber (CW↪∞ Xˢᵏᵉˡ (suc zero)) x₀) where
      xˢᵘᵇ : fst Xˢᵘᵇ
      xˢᵘᵇ = fun X₃₊ₙ≅X∞ (CWskel∙ Xˢᵏᵉˡ (fst t) (suc (suc n)))

      Xˢᵘᵇ∙ : Pointed _
      fst Xˢᵘᵇ∙ = fst Xˢᵘᵇ
      snd Xˢᵘᵇ∙ = xˢᵘᵇ

      Xˢᵘᵇ→∙X₃₊ₙ : Xˢᵘᵇ∙ →∙ (X₃₊ₙ , CWskel∙ Xˢᵏᵉˡ (fst t) (suc (suc n)))
      fst Xˢᵘᵇ→∙X₃₊ₙ = inv' X₃₊ₙ≅X∞
      snd Xˢᵘᵇ→∙X₃₊ₙ = ret X₃₊ₙ≅X∞ _

      Xˢᵘᵇ→∙X : Xˢᵘᵇ∙ →∙ X∙
      Xˢᵘᵇ→∙X = (e∞⃖ , e∞⃖-incl)
             ∘∙ (incl∙ Xˢᵏᵉˡ (fst t)
             ∘∙ Xˢᵘᵇ→∙X₃₊ₙ)
        where
        e∞⃖-incl : e∞⃖ (incl (fst t)) ≡ x
        e∞⃖-incl = cong e∞⃖ (snd t) ∙ retEq e∞ x

      isConn₃₊ₙXˢᵘᵇ→∙X : isConnectedFun (suc (suc (suc n))) (fst Xˢᵘᵇ→∙X)
      isConn₃₊ₙXˢᵘᵇ→∙X =
        isConnectedComp (invEq (snd (snd X))) _ (suc (suc (suc n)))
         (isEquiv→isConnected _ (snd (invEquiv e∞)) _)
          (isConnectedComp incl (Xˢᵘᵇ→∙X₃₊ₙ .fst) (suc (suc (suc n)))
            (isConnected-CW↪∞ (suc (suc (suc n))) _)
            (isEquiv→isConnected _
              (isoToIsEquiv (invIso X₃₊ₙ≅X∞)) _))

      isConnX₃₊ₙ : isConnected 2 (fst Xˢᵏᵉˡ (suc (suc (suc n))))
      isConnX₃₊ₙ =
        connectedFunPresConnected 2
          (subst (isConnected 2) (ua e∞) conX) (λ b →
            isConnectedSubtr' (suc n) 2
              (isConnected-CW↪∞ (suc (suc (suc n))) Xˢᵏᵉˡ b))

      isConnXˢᵘᵇ : isConnected 2 (fst Xˢᵘᵇ)
      isConnXˢᵘᵇ = subst (isConnected 2) (isoToPath X₃₊ₙ≅X∞) isConnX₃₊ₙ

      HurewiczInst = HurewiczHomAb Xˢᵘᵇ xˢᵘᵇ isConnXˢᵘᵇ n

      isEquivHurewiczInst : isEquiv (fst HurewiczInst)
      isEquivHurewiczInst =
        transport (λ i → isEquiv (fst (HurewiczHomAb' i)))
         (ind' (CWskel∙ Xˢᵏᵉˡ (fst t) (suc (suc n)))
               ∣ subComplex Xˢᵏᵉˡ (suc (suc (suc n)))
               , isoToEquiv X₃₊ₙ≅X∞ ∣₁
               isConnX₃₊ₙ)
        where
        lem : Path (Σ[ X ∈ CW ℓ ] (Σ[ x ∈ fst X ] isConnected 2 (fst X)))
                  ((_ , ∣ subComplex Xˢᵏᵉˡ (suc (suc (suc n)))
                          , isoToEquiv X₃₊ₙ≅X∞ ∣₁)
                  , (CWskel∙ Xˢᵏᵉˡ (fst t) (suc (suc n))) , isConnX₃₊ₙ)
                  (Xˢᵘᵇ , xˢᵘᵇ , isConnXˢᵘᵇ)
        lem = ΣPathP ((Σ≡Prop (λ _ → squash₁)
                              (isoToPath X₃₊ₙ≅X∞))
                    , (ΣPathPProp (λ _ → isPropIsContr)
                       (toPathP (cong incl (transportRefl _)))))

        HurewiczHomAb' : (i : I) → _
        HurewiczHomAb' i =
          HurewiczHomAb (lem i .fst) (lem i .snd .fst) (lem i .snd .snd) n

      altEquiv : AbGroupEquiv (AbelianizationAbGroup (π'Gr n (fst X , x)))
                              (H̃ᶜʷAb (fst X , ∣ snd X ∣₁) n)
      altEquiv =
        compGroupEquiv
          (invGroupEquiv (connected→Abπ'Equiv n Xˢᵘᵇ→∙X isConn₃₊ₙXˢᵘᵇ→∙X))
           (compGroupEquiv ((fst HurewiczInst , isEquivHurewiczInst)
                           , snd HurewiczInst)
             (subComplexHomologyEquiv Xˢᵏᵉˡ n (suc (suc (suc n))) <ᵗsucm))

      altEquiv≡ : (a : _) → altEquiv .fst .fst a
                           ≡ HurewiczHomAb (fst X , ∣ snd X ∣₁) x conX n .fst a
      altEquiv≡ = Abi.elimProp _ (λ _ → squash/ _ _)
        (λ f → H̃ᶜʷ→≡Hurewicz _
            ∙ cong (HurewiczHomAb (fst X , ∣ snd X ∣₁) x conX n .fst)
                   (secEq (fst (connected→Abπ'Equiv n Xˢᵘᵇ→∙X isConn₃₊ₙXˢᵘᵇ→∙X))
                          (η f)))
        where
        H̃ᶜʷ→compInst = H̃ᶜʷ→comp {C = Sᶜʷ (suc n)} {D = Xˢᵘᵇ}
                        {E = realise Xˢᵏᵉˡ , ∣ Xˢᵏᵉˡ , (idEquiv _) ∣₁} (suc n)
                        (incl ∘ inv' X₃₊ₙ≅X∞)

        H̃ᶜʷ→≡Hurewicz : (t : _)
          → H̃ᶜʷ→ {C = subCW (suc (suc (suc n))) X}
                   {D = realise Xˢᵏᵉˡ , ∣ Xˢᵏᵉˡ , (idEquiv _) ∣₁} (suc n) incl
                   .fst (HurewiczHomAb Xˢᵘᵇ xˢᵘᵇ isConnXˢᵘᵇ n .fst (η t))
           ≡ HurewiczHomAb (fst X , ∣ snd X ∣₁) x conX n .fst
              (fst (fst (connected→Abπ'Equiv n Xˢᵘᵇ→∙X isConn₃₊ₙXˢᵘᵇ→∙X)) (η t))
        H̃ᶜʷ→≡Hurewicz =
          ST.elim (λ _ → isProp→isSet (squash/ _ _)) λ g →
            funExt⁻ (cong fst (sym (H̃ᶜʷ→compInst (fst g)))) (genHₙSⁿ n)
          ∙ λ i → H̃ᶜʷ→ {C = Sᶜʷ (suc n)}
                        {D = realise Xˢᵏᵉˡ , ∣ Xˢᵏᵉˡ , (idEquiv _) ∣₁} (suc n)
                     (λ z → secEq e∞ (incl (Xˢᵘᵇ→∙X₃₊ₙ .fst (fst g z))) (~ i))
                             .fst (genHₙSⁿ n)

-- Finally, the main theorem
HurewiczTheorem : (n : ℕ) (X : CW ℓ-zero)
  (conX : isConnected (suc (suc n)) (fst X)) (x : _)
  → isEquiv (HurewiczHomAb X x (isConnectedSubtr' n 2 conX) n .fst)
HurewiczTheorem n =
  uncurry λ X → PT.elim (λ _ → isPropΠ2  λ _ _ → isPropIsEquiv _)
   λ cw isc → PT.rec (isPropΠ (λ _ → isPropIsEquiv _))
     (λ cw' → main X cw cw' isc)
     (makeConnectedCW n cw isc)
   where
   isEqTransport : (cw1 cw2 : CW ℓ) (P : cw1 ≡ cw2)
     (con1 : isConnected 2 (fst cw1)) (con2 : isConnected 2 (fst cw2))
     (x' : fst cw1) (x : fst cw2) (PP : PathP (λ i → fst (P i)) x' x)
     → isEquiv (HurewiczHomAb cw1 x' con1 n .fst)
     → isEquiv (HurewiczHomAb cw2 x con2 n .fst)
   isEqTransport cw1 =
     J> λ con1 con2 x' →
      J> (subst (λ c → isEquiv (HurewiczHomAb cw1 x' c n .fst))
               (isPropIsContr _ _))

   module _ (X : Type) (cw : hasCWskel X) (cw' : isConnectedCW n X)
            (isc : isConnected (suc (suc n)) X) (x : X) where
     Xˢᵏᵉˡ Xˢᵏᵉˡ' : CWskel ℓ-zero
     Xˢᵏᵉˡ = fst cw
     Xˢᵏᵉˡ' = connectedCWskel→CWskel (fst cw')

     Xᶜʷ Xᶜʷ' : CWexplicit ℓ-zero
     Xᶜʷ = X , cw
     Xᶜʷ' = X , Xˢᵏᵉˡ' , (invEquiv (snd cw'))

     liftLem : (A : CW ℓ-zero) (a : fst A) (e : isConnected 2 (Lift _ (fst A)))
       → Path (Σ[ A ∈ CW ℓ-zero ] (Σ[ a ∈ fst A ] isConnected 2 (fst A)))
              (A , a , subst (isConnected 2) (ua (invEquiv LiftEquiv)) e)
              ((CWLift ℓ-zero A) , (lift a , e))
     liftLem A a e =
       ΣPathP ((Σ≡Prop (λ _ → squash₁) (ua LiftEquiv))
              , (ΣPathPProp (λ _ → isPropIsContr)
                 λ i → ua-gluePt LiftEquiv i a))

     main : isEquiv (HurewiczHomAb (X , ∣ cw ∣₁) x
                    (isConnectedSubtr' n 2 isc) n .fst)
     main =
       isEqTransport (CWexplicit→CW Xᶜʷ') (CWexplicit→CW Xᶜʷ)
           (Σ≡Prop (λ _ → squash₁) refl)
           (isConnectedSubtr' n 2 isc)
           (isConnectedSubtr' n 2 isc) x x refl
           (preHurewiczLemma n Xᶜʷ'
             (isConnectedSubtr' n 2 isc)
             (λ l str con' → PT.rec (isPropIsEquiv _)
             (λ {(α , e) → TR.rec (isPropIsEquiv _)
               (λ linl → isEqTransport _ (_ , str) (sym e)
                           (subst (isConnected 2) (cong fst e) con')
                           con'
                           (lift (inl tt))
                           l
                           (toPathP (sym linl))
                           (transport (λ i → isEquiv
                             (HurewiczHomAb
                              (liftLem (SphereBouquet/ᶜʷ (fst α)) (inl tt)
                                (subst (isConnected 2)
                                  (λ i → fst (e i)) con') i .fst)
                              (liftLem (SphereBouquet/ᶜʷ (fst α)) (inl tt)
                                (subst (isConnected 2)
                                  (λ i → fst (e i)) con') i .snd .fst)
                              (liftLem (SphereBouquet/ᶜʷ (fst α)) (inl tt)
                                (subst (isConnected 2)
                                  (λ i → fst (e i)) con') i .snd .snd)
                              n .fst))
                             (HurewiczMapCofibEquiv α _)))
                            (isConnectedPath 1 con' l
                              (transport (sym (cong fst e)) (lift (inl tt)))
                                .fst)})
             (connectedCW≃CofibFinSphereBouquetMap n X cw' str)) x)
