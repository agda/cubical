{-# OPTIONS --lossy-unification #-}

module Cubical.HITs.SphereBouquet.Degree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function

open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Order.Inductive

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Degree renaming (degreeConst to degree-const)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Wedge
open import Cubical.HITs.SphereBouquet.Base
open import Cubical.HITs.SphereBouquet.Properties

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Properties

open import Cubical.Homotopy.Group.Base

private
  variable
    ℓ ℓ' : Level

pickPetal : {n k : ℕ} (b : Fin k)
  → SphereBouquet n (Fin k) → S₊ n
pickPetal {n = n} b (inl x) = ptSn n
pickPetal {n = n} b (inr (b' , x)) with (fst b ≟ᵗ fst b')
... | lt x₁ = ptSn n
... | eq x₁ = x
... | gt x₁ = ptSn n
pickPetal {n = n} {k = k} b (push b' i) with (fst b ≟ᵗ fst b')
... | lt x = ptSn n
... | eq x = ptSn n
... | gt x = ptSn n

--a morphisms between bouquets gives a morphisms of free abelian groups by taking degrees
bouquetDegree : {n m k : ℕ}
  → (SphereBouquet n (Fin m) → SphereBouquet n (Fin k))
  → (AbGroupHom (ℤ[Fin m ]) (ℤ[Fin k ]))
fst (bouquetDegree {m = m} {k = k} f) r x =
  sumFinℤ {n = m} λ (a : Fin m) → r a ·ℤ (degree _ (pickPetal {k = k} x ∘ f ∘ inr ∘ (a ,_)))
snd (bouquetDegree {n = n} f) =
  makeIsGroupHom λ x y
    → funExt λ a'
      → (λ j → sumFinℤ (λ a
                → ·DistL+ (x a) (y a)
                     (degree _ (pickPetal a' ∘ f ∘ inr ∘ (a ,_))) j))
      ∙ sumFinℤHom (λ a → x a ·ℤ (degree _ (pickPetal a' ∘ f ∘ inr ∘ (a ,_))))
                    λ a → y a ·ℤ (degree _ (pickPetal a' ∘ f ∘ inr ∘ (a ,_)))

-- Useful lemma for proving functoriality of bouquetDegree
private
  ⋁gen→∙Kn≡ : {A : Type ℓ} {B : A → Pointed ℓ'} (m : ℕ)
       (f g : ⋁gen∙ A B →∙ coHomK-ptd m)
    → ((x : _) → fst f (inr x) ≡ fst g (inr x))
    → (x : _) → f .fst x ≡ g .fst x
  ⋁gen→∙Kn≡ {A = A} {B = B} m f g idd (inl x) = snd f ∙ sym (snd g)
  ⋁gen→∙Kn≡ {A = A} {B = B} m f g idd (inr (a , x)) =
    (sym (rUnitₖ m (f .fst (inr (a , x))))
      ∙∙ cong (λ z → f .fst (inr (a , x)) +[ m ]ₖ z)
           (sym (snd g)
           ∙∙ (cong (fst g) (push a)
           ∙∙ sym (idd _)
           ∙∙ cong (fst f) (sym (push a)))
           ∙∙ snd f)
      ∙∙ rUnitₖ m (f .fst (inr (a , x))))
      ∙ idd (a , x)
  ⋁gen→∙Kn≡ {A = A} {B = B} m f g idd (push x i) =
    lem _ (sym (snd f)) _ (cong (fst f) (push x))
      _ (sym (snd g)) _ (cong (fst g) (push x))
      (idd (x , snd (B x))) i
    where
    lem : (f' : coHomK m) (f∙ : 0ₖ m ≡ f')
          (fx : coHomK m) (f-p : f' ≡ fx)
          (g' : coHomK m) (g∙ : 0ₖ m ≡ g')
          (gx : coHomK m) (g-p : g' ≡ gx)
          (idd1 : fx ≡ gx)
      → PathP (λ i → f-p i ≡ g-p i)
          (sym f∙ ∙ g∙)
          ((sym (rUnitₖ m fx)
             ∙∙ cong (λ z → fx +[ m ]ₖ z)
                     (g∙ ∙∙ g-p ∙∙ sym idd1 ∙∙ sym f-p ∙∙ sym f∙)
             ∙∙ rUnitₖ m fx)
          ∙ idd1)
    lem = J> (J> (J> (J>  λ p → sym (rUnit refl) ◁ sym (help m p))))
      where
      help : (m : ℕ) (p : _)
        → (sym (rUnitₖ m (0ₖ m))
        ∙∙ cong (+ₖ-syntax m (0ₖ m))
                ((sym p ∙ refl) ∙ refl)
        ∙∙ rUnitₖ m (0ₖ m))
         ∙ p
        ≡ refl
      help zero p = isSetℤ _ _ _ _
      help (suc zero) p =
        cong (_∙ p) (sym (rUnit _)
            ∙ λ i j → lUnitₖ 1 (rUnit (rUnit (sym p) (~ i)) (~ i) j) i)
            ∙ lCancel p
      help (suc (suc m)) p =
        cong (_∙ p) (sym (rUnit _)
            ∙ λ i j → lUnitₖ (2 +ℕ m) (rUnit (rUnit (sym p) (~ i)) (~ i) j) i)
        ∙ lCancel p

  ⋁gen→∙Kn≡∙ : {A : Type ℓ} {B : A → Pointed ℓ'} (m : ℕ)
       (f g : ⋁gen∙ A B →∙ coHomK-ptd m)
    → ((x : _) → fst f (inr x) ≡ fst g (inr x))
    → f ≡ g
  ⋁gen→∙Kn≡∙ m f g hom =
    ΣPathP ((funExt (⋁gen→∙Kn≡ m f g hom))
         , (flipSquare ((λ i
           → (λ j → snd f (i ∧ j))
           ∙∙ (λ j → snd f (i ∨ j))
           ∙∙ sym (snd g))
          ◁ λ i → doubleCompPath-filler (snd f) refl (sym (snd g)) (~ i))))

-- bouquetDegree preserves id
bouquetDegreeId : {n m : ℕ}
  → bouquetDegree (idfun (SphereBouquet n (Fin m))) ≡ idGroupHom
bouquetDegreeId {n = n} {m = m} =
  agreeOnℤFinGenerator→≡ λ (x : Fin m)
    → funExt λ t
      → sym (isGeneratorℤFinGenerator'
               (λ w → degree n (λ x₁ → pickPetal t (inr (w , x₁)))) x)
      ∙ help x t
  where
  help :  (x t : Fin m)
    → degree n (λ x₁ → pickPetal t (inr (x , x₁))) ≡ ℤFinGenerator x t
  help x y with (fst x ≟ᵗ fst y)
  ... | lt p = cong (degree n) (funExt lem) ∙ degree-const n
    where
    lem : (x₁ : S₊ n) → pickPetal y (inr (x , x₁)) ≡ ptSn n
    lem x₁ with (fst y ≟ᵗ fst x)
    ... | lt x = refl
    ... | eq q = ⊥.rec (¬m<ᵗm (subst (fst x <ᵗ_) q p))
    ... | gt x = refl
  ... | eq p = cong (degree n) (funExt lem) ∙ degreeIdfun n
    where
    lem : (x₁ : S₊ n) → pickPetal y (inr (x , x₁)) ≡ x₁
    lem x₁ with (fst y ≟ᵗ fst x)
    ... | lt q = ⊥.rec (¬m<ᵗm (subst (fst y <ᵗ_) p q))
    ... | eq x = refl
    ... | gt q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst y) p q))
  ... | gt p = cong (degree n) (funExt lem) ∙ degree-const n
      where
    lem : (x₁ : S₊ n) → pickPetal y (inr (x , x₁)) ≡ ptSn n
    lem x₁ with (fst y ≟ᵗ fst x)
    ... | lt x = refl
    ... | eq q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst x) q p))
    ... | gt x = refl

bouquetDegreeConst : (n a b : ℕ)
  → bouquetDegree {n} {a} {b} (λ _ → inl tt) ≡ trivGroupHom
bouquetDegreeConst n a b =
  GroupHom≡ ((λ i r x → sumFinℤ (λ a → r a ·ℤ (degree-const n i)))
          ∙∙ (λ i r x → sumFinℤ (λ a → ·Comm (r a) (pos 0) i))
          ∙∙ λ i r x → sumFinℤ0 a i)

-- bouquetDegree preserves suspension
bouquetDegreeSusp₀ : {m k : ℕ}
  → (f : SphereBouquet zero (Fin m) → SphereBouquet zero (Fin k))
  → bouquetDegree f ≡ bouquetDegree (bouquetSusp→ f)
bouquetDegreeSusp₀ {m = m} {k = zero} f =
  subst (λ f → bouquetDegree f ≡ bouquetDegree (bouquetSusp→ f))
        f-const
        (bouquetDegreeConst zero _ _
      ∙ sym (bouquetDegreeConst (suc zero) _ _)
      ∙ cong bouquetDegree lem₂)
  where
  f-const : (λ _ → inl tt) ≡ f
  f-const = funExt (λ x → isContrSphereBouquetZero 0 .snd (f x))
  lem₂ : (λ _ → inl tt) ≡ bouquetSusp→ {n = zero} (λ _ → inl tt)
  lem₂ = funExt (λ x
    → isContrSphereBouquetZero 1 .snd (bouquetSusp→ (λ _ → inl tt) x))
bouquetDegreeSusp₀ {m = m} {k = suc k} f =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt λ r → funExt λ a → sumFinℤId m λ y → cong (r y ·ℤ_)
              (degreeSusp 0 (λ x → pickPetal a (f (inr (y , x))))
              ∙ λ i → degree 1 (λ z → help y a z i)))
    where
    help : (y : _) (a : _) (z : _)
      → suspFunS∙ (λ x → pickPetal a (f (inr (y , x)))) .fst z
       ≡ pickPetal a (bouquetSusp→ f (inr (y , z)))
    help y a base = refl
    help y a (loop i) j = help' j i
      where
      main : (ft ff : SphereBouquet zero (Fin (suc k)))
           → cong SuspBool→S¹ (merid (pickPetal a ff))
           ∙ cong SuspBool→S¹ (sym (merid (pickPetal a ft)))
           ≡ cong (pickPetal a) (cong sphereBouquetSuspFun (merid ff)
           ∙ sym (cong sphereBouquetSuspFun (merid ft)))
      main =
        SphereBouquet→Prop 0 fzero (λ _ → isPropΠ λ _ → isGroupoidS¹ _ _ _ _)
             λ x y → SphereBouquet→Prop 0 fzero (λ _ → isGroupoidS¹ _ _ _ _)
               λ x' y'
           → (cong₂ _∙_ (final y' x') (cong sym (final y x))
            ∙ sym (cong-∙ (pickPetal a)
                  (merid-lem x' y' i1) (sym (merid-lem x y i1))))
            ∙ λ i → cong (pickPetal a)
                  ((merid-lem x' y' (~ i) ∙ sym (merid-lem x y (~ i))))
        where
        merid-lem : (x : Fin (suc k)) (y : Bool)
          → cong (sphereBouquetSuspIso .Iso.fun) (merid (inr (x , y)))
           ≡ push x ∙∙ (λ i → inr (x , SuspBool→S¹ (merid y i))) ∙∙ sym (push x)
        merid-lem x y = cong-∙∙ (Iso.fun sphereBouquetSuspIso₀)
                                (push x)
                                (λ i → inr (x , (merid y ∙ sym (merid true)) i))
                                (sym (push x))
          ∙ cong (push x ∙∙_∙∙ sym (push x))
              (cong-∙ (λ z → Iso.fun sphereBouquetSuspIso₀ (inr (x , z)))
                                       (merid y) (sym (merid true))
              ∙ sym (rUnit _))

        pre-final : (y : Bool) (x : Fin (suc k))
          → cong SuspBool→S¹ (merid (pickPetal a (inr (x , y))))
          ≡ cong (pickPetal a) (push x)
          ∙∙ cong (pickPetal a) (λ i → inr (x , SuspBool→S¹ (merid y i)))
          ∙∙ cong (pickPetal a) (sym (push x))
        pre-final y x with (fst a ≟ᵗ fst x)
        ... | lt x₁ = rUnit refl
        ... | eq x₁ = rUnit _
        ... | gt x₁ = rUnit refl

        final : (y : Bool) (x : Fin (suc k))
          → cong SuspBool→S¹ (merid (pickPetal a (inr (x , y))))
          ≡ cong (pickPetal a) ((push x)
                           ∙∙ (λ i → inr (x , SuspBool→S¹ (merid y i)))
                           ∙∙ sym (push x))
        final y x =
            pre-final y x
          ∙ cong-∙∙ (pickPetal a)
                    (push x)
                    (λ i → inr (x , SuspBool→S¹ (merid y i)))
           (sym (push x))

      help' : cong (suspFunS∙ (λ x → pickPetal a (f (inr (y , x)))) .fst) loop
           ≡ cong (pickPetal a) λ i → bouquetSusp→ f (inr (y , loop i))
      help' =
          (λ j i → Iso.inv S¹IsoSuspBool
                    (cong-∙ (suspFun λ x → pickPetal a (f (inr (y , x))))
                      (merid false) (sym (merid true)) j i))
        ∙ cong-∙ (Iso.inv S¹IsoSuspBool)
                 (merid (pickPetal a (f (inr (y , false)))))
                 (sym (merid (pickPetal a (f (inr (y , true))))))
        ∙ main (f (inr (y , true))) ((f (inr (y , false))))
        ∙ cong (cong (pickPetal a)) (refl
             ∙ (sym  (cong-∙ sphereBouquetSuspFun
                     (merid (f (inr (y , false))))
                     (sym (merid (f (inr (y , true)))))))
             ∙ cong (cong sphereBouquetSuspFun)
               (sym (cong-∙ (suspFun f)
                      (merid (inr (y , false))) (sym (merid (inr (y , true)))))
             ∙ cong (cong (suspFun f))
                 (sym (cong-∙ (λ x → Iso.inv (Iso-SuspBouquet-Bouquet _ _)
                             (inr (y , x))) (merid false) (sym (merid true))))))
        ∙ λ j i → pickPetal a (sphereBouquetSuspFun
                    (suspFun f (Iso.inv (Iso-SuspBouquet-Bouquet _ _)
                      (inr (y , (merid false ∙ sym (merid true)) i)))))

bouquetDegreeSusp : {n m k : ℕ}
  → (f : SphereBouquet n (Fin m) → SphereBouquet n (Fin k))
  → bouquetDegree f ≡ bouquetDegree (bouquetSusp→ f)
bouquetDegreeSusp {n = zero} = bouquetDegreeSusp₀
bouquetDegreeSusp {n = suc n} {m = m} {k = k} f =
  agreeOnℤFinGenerator→≡ λ (x : Fin m)
    → funExt λ (b : Fin k) → sumFinℤId m
      λ z → cong (ℤFinGenerator x z ·ℤ_)
             (degreeSusp (suc n) (λ x₁ → pickPetal b (f (inr (z , x₁))))
           ∙ cong (Iso.fun (Hⁿ-Sⁿ≅ℤ (suc n) .fst))
                (cong ∣_∣₂ (funExt λ x → help b z x)))
  where
  f₁ : (b : Fin k) → SphereBouquet∙ (suc n) (Fin k) →∙ coHomK-ptd (suc n)
  fst (f₁ b) x = ∣ pickPetal b x ∣ₕ
  snd (f₁ b) = refl

  f₂ : (b : Fin k) → SphereBouquet∙ (suc n) (Fin k) →∙ coHomK-ptd (suc n)
  fst (f₂ b) x = ΩKn+1→Kn (suc n)
    λ i → ∣ pickPetal b (Bouquet→ΩBouquetSusp (Fin k) (λ _ → S₊∙ (suc n)) x i) ∣
  snd (f₂ b) = ΩKn+1→Kn-refl (suc n)

  f₁≡f₂ : (b : Fin k) (x : _) → f₁ b .fst x ≡ f₂ b .fst x
  f₁≡f₂ b = ⋁gen→∙Kn≡ (suc n) (f₁ b) (f₂ b) (uncurry main)
    where
    main : (x : Fin k) (y : S₊ (suc n))
      → f₁ b .fst (inr (x , y)) ≡ f₂ b .fst (inr (x , y))
    main x y =
      main'
      ∙ cong (ΩKn+1→Kn (suc n))
           (cong (cong ∣_∣ₕ)
             (sym (cong-∙∙ (pickPetal {n = 2 +ℕ n} b)
             (push x) (λ i → inr (x , σSn (suc n) y i)) (sym (push x)))))
      where
      main' : f₁ b .fst (inr (x , y))
            ≡ ΩKn+1→Kn (suc n)
               (cong ∣_∣ₕ (cong (pickPetal {n = 2 +ℕ n} b) (push x)
                      ∙∙ (λ i → pickPetal {n = 2 +ℕ n} b
                                  (inr (x , σSn (suc n) y i)))
                      ∙∙ cong (pickPetal {n = 2 +ℕ n} b) (sym (push x))))
      main' with (fst b ≟ᵗ fst x)
      ... | lt x = sym (cong (ΩKn+1→Kn (suc n))
                     (sym (rUnit refl)) ∙ ΩKn+1→Kn-refl (suc n))
      ... | eq x = sym (cong (ΩKn+1→Kn (suc n))
                         (cong (cong ∣_∣ₕ) (sym (rUnit (σSn (suc n) y))))
                 ∙ Iso.leftInv (Iso-Kn-ΩKn+1 (suc n)) ∣ y ∣)
      ... | gt x = sym (cong (ΩKn+1→Kn (suc n)) (sym (rUnit refl))
                      ∙ ΩKn+1→Kn-refl (suc n))

  help : (b : Fin k) (z : Fin m) (t : _)
    → Path (coHomK (2 +ℕ n))
            (∣ suspFun (λ x₁ → pickPetal b (f (inr (z , x₁)))) t ∣ₕ)
             ∣ pickPetal b (bouquetSusp→ f (inr (z , t))) ∣ₕ
  help b z north = refl
  help b z south = cong ∣_∣ₕ (sym (merid (ptSn (suc n))))
  help b z (merid a i) j =
    hcomp (λ r
     → λ {(i = i0) → ∣ north ∣
         ; (i = i1) → ∣ merid (ptSn (suc n)) (~ j ∧ r) ∣
         ; (j = i0) → ∣ compPath-filler
                         (merid (pickPetal b (f (inr (z , a)))))
                         (sym (merid (ptSn (suc n)))) (~ r) i ∣ₕ
         ; (j = i1) → (cong (Kn→ΩKn+1 (suc n)) (f₁≡f₂ b (f (inr (z , a))))
                     ∙ Iso.rightInv (Iso-Kn-ΩKn+1 (suc n))
                        (λ i → ∣ pickPetal b (bouquetSusp→ f
                                  (inr (z , merid a i))) ∣)) r i})
          (Kn→ΩKn+1 (suc n) ∣ pickPetal b (f (inr (z , a))) ∣ i)

-- bouquetDegree preserves composition
bouquetDegreeComp∙Suc : {n m k l : ℕ}
  → (f : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
  → (g : SphereBouquet∙ (suc n) (Fin l) →∙ SphereBouquet∙ (suc n) (Fin m))
  → bouquetDegree ((fst f) ∘ (fst g))
   ≡ compGroupHom (bouquetDegree (fst g)) (bouquetDegree (fst f))
bouquetDegreeComp∙Suc {n} {m} {k} {l} f g =
  agreeOnℤFinGenerator→≡
    λ (x : Fin l)
    → funExt λ t
      → sumFinℤId l
         (λ a →
           ·Comm (ℤFinGenerator x a) _
      ∙ cong (degree (suc n)
              (λ x₁ → pickPetal t (fst f (fst g (inr (a , x₁))))) ·ℤ_)
             (ℤFinGeneratorComm x a))
      ∙ sym (isGeneratorℤFinGenerator
          (λ a → degree (suc n)
                   (λ x₁ → pickPetal t (fst f (fst g (inr (a , x₁)))))) x)
      ∙ main n m (λ s → fst g (inr (x , s)))
                 ((λ s → pickPetal t (fst f s))
                 , (cong (pickPetal t) (snd f)))
      ∙ sumFinℤId m λ a →
          degreeComp' (suc n)
              (λ x₁ → pickPetal t (fst f (inr (a , x₁))))
              (λ x₁ → pickPetal a (fst g (inr (x , x₁))))
         ∙ λ j → simplify x a (~ j)
              ·ℤ degree (suc n) (λ x₁ → pickPetal t (fst f (inr (a , x₁))))
  where
  main : (n m : ℕ) (w : S₊ (suc n) → SphereBouquet (suc n) (Fin m))
       (F : ((SphereBouquet (suc n) (Fin m)) , inl tt) →∙ S₊∙ (suc n))
   → degree (suc n) (λ s → fst F (w s))
    ≡ sumFinℤ (λ a → degree (suc n) (λ s → fst F (inr (a , pickPetal a (w s)))))
  main n zero w (F , Fp) =
      (λ j → degree (suc n) (λ s → F (lem w j s)))
    ∙ (λ j → degree (suc n) (λ s → Fp j))
    ∙ degree-const (suc n)
    where
    lem : (f : S₊ (suc n) → SphereBouquet (suc n) (Fin zero))
       → (f ≡ λ _ → inl tt)
    lem f = funExt λ x → sym (isContrSphereBouquetZero (suc n) .snd (f x))
  main n (suc m) w F =
    cong (Iso.fun (Hⁿ-Sⁿ≅ℤ n .fst))
      (cong ∣_∣₂ (funExt (λ x → asSum F (w x)))
            ∙ sym (sumFinKComm
                (λ a s → ∣ fst F (inr (a , pickPetal a (w s))) ∣ₕ)))
    ∙ sym (sumFinGroupℤComm _ (Hⁿ-Sⁿ≅ℤ n)
            (λ a → ∣ (λ s → ∣ fst F (inr (a , pickPetal a (w s))) ∣ₕ) ∣₂))
    where
    asSum : (F : (SphereBouquet (suc n) (Fin (suc m)) , inl tt) →∙ S₊∙ (suc n))
         → (p : SphereBouquet (suc n) (Fin (suc m)))
         → ∣ F .fst p ∣ₕ
          ≡ sumFinK {m = suc n} (λ i → ∣ fst F (inr (i , pickPetal i p)) ∣ₕ)
    asSum F =
      ⋁gen→∙Kn≡ (suc n)
       ((λ p → ∣ F .fst p ∣ₕ) , cong ∣_∣ₕ (snd F))
       ((λ p → sumFinK {m = suc n}
                 (λ i → ∣ fst F (inr (i , pickPetal i p)) ∣ₕ)) , sumPt)
       (uncurry main-lem)
      where
      id₁ : (x : Fin (suc m)) (y : _)
        → fst F (inr (x , pickPetal x (inr (x , y)))) ≡ fst F (inr (x , y))
      id₁ (x , p) y with (x ≟ᵗ x)
      ... | lt x₁ = ⊥.rec (¬m<ᵗm x₁)
      ... | eq x₁ = refl
      ... | gt x₁ = ⊥.rec (¬m<ᵗm x₁)

      id₂ : (x : _) (x' : Fin (suc m)) (y : _) (q : ¬ x' ≡ x)
         → ∣ fst F (inr (x' , pickPetal x' (inr (x , y)))) ∣ₕ ≡ 0ₖ (suc n)
      id₂ (x , p) (x' , t) y con with (x' ≟ᵗ x)
      ... | lt x₁ = cong ∣_∣ₕ (cong (fst F) (sym (push (x' , t))) ∙ snd F)
      ... | eq x₁ = ⊥.rec (con (Σ≡Prop (λ _ → isProp<ᵗ) x₁))
      ... | gt x₁ = cong ∣_∣ₕ (cong (fst F) (sym (push (x' , t))) ∙ snd F)

      sumPt : sumFinK (λ i → ∣ fst F (inr (i , pickPetal i (inl tt))) ∣ₕ)
            ≡ 0ₖ (suc n)
      sumPt = sumFinGen0 _+ₖ_ (0ₖ (suc n)) (rUnitₖ _) _
               (λ i → ∣ fst F (inr (i , pickPetal i (inl tt))) ∣ₕ)
               (λ s → cong ∣_∣ₕ (cong (fst F) (sym (push s)) ∙ snd F))

      main-lem : (x : Fin (suc m)) (y : S₊ (suc n))
        → ∣ F .fst (inr (x , y)) ∣ₕ
        ≡ sumFinK {n = suc m} {m = suc n}
            (λ i → ∣ fst F (inr (i , pickPetal i (inr (x , y)))) ∣ₕ)
      main-lem x y = sym (sumFin-choose _+ₖ_ (0ₖ (suc n)) (rUnitₖ _) (commₖ _)
        (λ i → ∣ fst F (inr (i , pickPetal i (inr (x , y)))) ∣ₕ)
        ∣ F .fst (inr (x , y)) ∣ₕ x
          (cong ∣_∣ₕ (id₁ x y))
          λ x' → id₂ x x' y)

  simplify : (x : Fin l) (a : Fin m)
    → sumFinℤ (λ a₁ → ℤFinGenerator x a₁
                       ·ℤ degree (suc n)
                            (λ x₁ → pickPetal a (fst g (inr (a₁ , x₁)))))
     ≡ degree (suc n) (λ x₁ → pickPetal a (fst g (inr (x , x₁))))
  simplify x a =
       sumFinℤId l
           (λ p → ·Comm (ℤFinGenerator x p)
                    (degree (suc n) (λ x₁ → pickPetal a (fst g (inr (p , x₁)))))
         ∙ λ i → degree (suc n) (λ x₁ → pickPetal a (fst g (inr (p , x₁))))
                 ·ℤ ℤFinGeneratorComm x p i)
     ∙ sym (isGeneratorℤFinGenerator
             (λ a₁ → degree (suc n)
                       (λ x₁ → pickPetal a (fst g (inr (a₁ , x₁))))) x)

bouquetDegreeCompPos : {n m k l : ℕ}
  → (f : SphereBouquet (suc n) (Fin m) → SphereBouquet (suc n) (Fin k))
  → (g : SphereBouquet (suc n) (Fin l) → SphereBouquet (suc n) (Fin m))
  → bouquetDegree (f ∘ g) ≡ compGroupHom (bouquetDegree g) (bouquetDegree f)
bouquetDegreeCompPos {n = n} {m = m} {k = k} {l = l} f g =
  PT.rec2 (isSetGroupHom _ _)
          (λ Hf Hg → bouquetDegreeComp∙Suc (f , Hf) (g , Hg))
          (isConnectedSphereBouquet (f (inl tt)))
          (isConnectedSphereBouquet (g (inl tt)))

bouquetDegreeComp : {n m k l : ℕ}
  → (f : SphereBouquet n (Fin m) → SphereBouquet n (Fin k))
  → (g : SphereBouquet n (Fin l) → SphereBouquet n (Fin m))
  → bouquetDegree (f ∘ g) ≡ compGroupHom (bouquetDegree g) (bouquetDegree f)
bouquetDegreeComp {n = zero} f g =
     bouquetDegreeSusp (f ∘ g)
  ∙∙ Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      ((λ i → bouquetDegree (bouquetSusp→∘ g f (~ i)) .fst)
    ∙ cong fst (bouquetDegreeCompPos (bouquetSusp→ f) (bouquetSusp→ g)))
  ∙∙ sym (cong₂ compGroupHom (bouquetDegreeSusp g) (bouquetDegreeSusp f))
bouquetDegreeComp {n = suc n} f g = bouquetDegreeCompPos f g

bouquetDegreeComp∙ : {n m k l : ℕ}
  (f : SphereBouquet∙ n (Fin m) →∙ SphereBouquet∙ n (Fin k))
  (g : SphereBouquet∙ n (Fin l) →∙ SphereBouquet∙ n (Fin m))
  → bouquetDegree ((fst f) ∘ (fst g))
   ≡ compGroupHom (bouquetDegree (fst g)) (bouquetDegree (fst f))
bouquetDegreeComp∙ {n = zero} {m} {k = k} {l = l} f g =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (cong fst (bouquetDegreeSusp (fst f ∘ fst g))
  ∙ sym (cong (fst ∘ bouquetDegree) (bouquetSusp→∘ (fst g) (fst f)))
  ∙ cong fst (bouquetDegreeComp∙Suc (bouquetSusp→ (fst f) , refl)
                                    (bouquetSusp→ (fst g) , refl))
  ∙ cong fst (cong₂ compGroupHom (sym (bouquetDegreeSusp (fst g)))
                                 (sym (bouquetDegreeSusp (fst f)))))
bouquetDegreeComp∙ {n = suc n} = bouquetDegreeComp∙Suc

bouquetDegree∙Π : (n m k : ℕ)
  (f g : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
  → bouquetDegree (SphereBouquet∙Π f g .fst)
   ≡ addGroupHom ℤ[Fin m ] ℤ[Fin k ] (bouquetDegree (fst f)) (bouquetDegree (fst g))
bouquetDegree∙Π n m k f g =
  agreeOnℤFinGenerator→≡
    λ s → funExt λ y → (sym (isGeneratorℤFinGenerator' _ s)
      ∙ cong (degree (suc n)) (funExt (main n s y f g))
       ∙ degreeHom {n = n}
         ((λ x₁ → pickPetal y (fst f (inr (s , x₁))))
                 , cong (pickPetal y) (cong (fst f) (sym (push s)) ∙ snd f))
         ((λ x₁ → pickPetal y (fst g (inr (s , x₁))))
                 , cong (pickPetal y) (cong (fst g) (sym (push s)) ∙ snd g))
      ∙ isGeneratorℤFinGenerator' _ s
      ∙ cong sumFinℤ (funExt λ x →
        ·DistR+ (ℤFinGenerator s x)
                (degree (suc n) (λ x₁ → pickPetal y (fst f (inr (x , x₁)))))
                (degree (suc n) (λ x₁ → pickPetal y (fst g (inr (x , x₁))))))
      ∙ sumFinℤHom _ _) --
  where
  main : (n : ℕ) (s : Fin m) (y : _)
    (f g : SphereBouquet∙ (suc n) (Fin m)
     →∙ SphereBouquet∙ (suc n) (Fin k)) (x : S₊ (suc n))
     → pickPetal y (SphereBouquet∙Π f g .fst (inr (s , x)))
    ≡ (∙Π ((λ x₁ → pickPetal y (fst f (inr (s , x₁)))) ,
           (λ i → pickPetal y (((λ i₁ → fst f (push s (~ i₁))) ∙ snd f) i)))
          ((λ x₁ → pickPetal y (fst g (inr (s , x₁)))) ,
           (λ i → pickPetal y (((λ i₁ → fst g (push s (~ i₁))) ∙ snd g) i)))
           .fst x)
  main zero s y f g base = refl
  main zero s y f g (loop i) = refl
  main (suc n) s y f g north = refl
  main (suc n) s y f g south = refl
  main (suc n) s y f g (merid a i) j = lem j i
    where
    lem : cong (pickPetal y) (cong (λ x → SphereBouquet∙Π f g .fst (inr (s , x)))
                                   (merid a))
        ≡ (sym (cong (pickPetal y) ((λ i₁ → fst f (push s (~ i₁))) ∙ snd f))
          ∙∙ cong (pickPetal y) (cong (λ x → fst f (inr (s , x))) (σS a))
          ∙∙ cong (pickPetal y) ((λ i₁ → fst f (push s (~ i₁))) ∙ snd f))
        ∙ (sym (cong (pickPetal y) ((λ i₁ → fst g (push s (~ i₁))) ∙ snd g))
          ∙∙ cong (pickPetal y) (cong (λ x → fst g (inr (s , x))) (σS a))
          ∙∙ cong (pickPetal y) ((λ i₁ → fst g (push s (~ i₁))) ∙ snd g))
    lem = (cong-∙ (pickPetal y) _ _
      ∙ cong₂ _∙_
        (cong-∙∙ (pickPetal y) (sym ((λ i₁ → fst f (push s (~ i₁))) ∙ snd f)) _ _)
        (cong-∙∙ (pickPetal y) (sym ((λ i₁ → fst g (push s (~ i₁))) ∙ snd g)) _ _))
