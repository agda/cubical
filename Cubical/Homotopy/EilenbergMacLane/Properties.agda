{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Homotopy.EilenbergMacLane.Properties where

open import Cubical.Homotopy.EilenbergMacLane.Base
  renaming (elim to EM-elim ; elim2 to EM-elim2)
open import Cubical.Homotopy.EilenbergMacLane.WedgeConnectivity
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.AbGroup.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

open import Cubical.Functions.Morphism

open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_·_)

open import Cubical.HITs.Truncation as Trunc
open import Cubical.HITs.EilenbergMacLane1
  renaming (rec to EMrec ; elim to EM₁elim)
open import Cubical.HITs.Susp

private
  variable ℓ ℓ' ℓ'' : Level

isConnectedEM₁ : (G : Group ℓ) → isConnected 2 (EM₁ G)
isConnectedEM₁ G = ∣ embase ∣ , h
    where
      h : (y : hLevelTrunc 2 (EM₁ G)) → ∣ embase ∣ ≡ y
      h = Trunc.elim (λ y → isOfHLevelSuc 1 (isOfHLevelTrunc 2 ∣ embase ∣ y))
            (elimProp G (λ x → isOfHLevelTrunc 2 ∣ embase ∣ ∣ x ∣) refl)

module _ {G' : AbGroup ℓ} where
  private
    G = fst G'
    open AbGroupStr (snd G') renaming (_+_ to _+G_)


  isConnectedEM : (n : ℕ) → isConnected (suc n) (EM G' n)
  fst (isConnectedEM zero) = ∣ 0g ∣
  snd (isConnectedEM zero) y = isOfHLevelTrunc 1 _ _
  isConnectedEM (suc zero) = isConnectedEM₁ (AbGroup→Group G')
  fst (isConnectedEM (suc (suc n))) = ∣ 0ₖ _ ∣
  snd (isConnectedEM (suc (suc n))) =
    Trunc.elim (λ _ → isOfHLevelTruncPath)
      (Trunc.elim (λ _ → isOfHLevelSuc (3 + n) (isOfHLevelTruncPath {n = (3 + n)}))
        (raw-elim G'
          (suc n)
          (λ _ → isOfHLevelTrunc (3 + n) _ _)
          refl))


module _ (Ĝ : Group ℓ) where
  private
    G = fst Ĝ
  open GroupStr (snd Ĝ)

  emloop-id : emloop 1g ≡ refl
  emloop-id =
    emloop 1g                                 ≡⟨ rUnit (emloop 1g) ⟩
    emloop 1g ∙ refl                          ≡⟨ cong (emloop 1g ∙_) (rCancel (emloop 1g) ⁻¹) ⟩
    emloop 1g ∙ (emloop 1g ∙ (emloop 1g) ⁻¹)  ≡⟨ ∙assoc _ _ _ ⟩
    (emloop 1g ∙ emloop 1g) ∙ (emloop 1g) ⁻¹  ≡⟨ cong (_∙ emloop 1g ⁻¹)
                                                   ((emloop-comp Ĝ 1g 1g) ⁻¹) ⟩
    emloop (1g · 1g) ∙ (emloop 1g) ⁻¹         ≡⟨ cong (λ g → emloop {Group = Ĝ} g
                                                             ∙ (emloop 1g) ⁻¹)
                                                      (·IdR 1g) ⟩
    emloop 1g ∙ (emloop 1g) ⁻¹                ≡⟨ rCancel (emloop 1g) ⟩
    refl ∎

  emloop-inv : (g : G) → emloop (inv g) ≡ (emloop g) ⁻¹
  emloop-inv g =
    emloop (inv g)                              ≡⟨ rUnit (emloop (inv g)) ⟩
    emloop (inv g) ∙ refl                       ≡⟨ cong (emloop (inv g) ∙_)
                                                      (rCancel (emloop g) ⁻¹) ⟩
    emloop (inv g) ∙ (emloop g ∙ (emloop g) ⁻¹) ≡⟨ ∙assoc _ _ _ ⟩
    (emloop (inv g) ∙ emloop g) ∙ (emloop g) ⁻¹ ≡⟨ cong (_∙ emloop g ⁻¹)
                                                      ((emloop-comp Ĝ (inv g) g) ⁻¹) ⟩
    emloop (inv g · g) ∙ (emloop g) ⁻¹          ≡⟨ cong (λ h → emloop {Group = Ĝ} h
                                                            ∙ (emloop g) ⁻¹)
                                                      (·InvL g) ⟩
    emloop 1g ∙ (emloop g) ⁻¹                 ≡⟨ cong (_∙ (emloop g) ⁻¹) emloop-id ⟩
    refl ∙ (emloop g) ⁻¹                      ≡⟨ (lUnit ((emloop g) ⁻¹)) ⁻¹ ⟩
    (emloop g) ⁻¹ ∎

  isGroupoidEM₁ : isGroupoid (EM₁ Ĝ)
  isGroupoidEM₁ = emsquash

  --------- Ω (EM₁ G) ≃ G ---------

  {- since we write composition in diagrammatic order,
     and function composition in the other order,
     we need right multiplication here -}
  rightEquiv : (g : G) → G ≃ G
  rightEquiv g = isoToEquiv isom
    where
    isom : Iso G G
    isom .Iso.fun = _· g
    isom .Iso.inv = _· inv g
    isom .Iso.rightInv h =
      (h · inv g) · g ≡⟨ (·Assoc h (inv g) g) ⁻¹ ⟩
        h · inv g · g ≡⟨ cong (h ·_) (·InvL g) ⟩
             h · 1g ≡⟨ ·IdR h ⟩ h ∎
    isom .Iso.leftInv h =
      (h · g) · inv g ≡⟨ (·Assoc h g (inv g)) ⁻¹ ⟩
        h · g · inv g ≡⟨ cong (h ·_) (·InvR g) ⟩
             h · 1g ≡⟨ ·IdR h ⟩ h ∎

  compRightEquiv : (g h : G)
    → compEquiv (rightEquiv g) (rightEquiv h) ≡ rightEquiv (g · h)
  compRightEquiv g h = equivEq (funExt (λ x → (·Assoc x g h) ⁻¹))

  CodesSet : EM₁ Ĝ → hSet ℓ
  CodesSet = EMrec Ĝ (isOfHLevelTypeOfHLevel 2) (G , is-set) RE REComp
    where
      RE : (g : G) → Path (hSet ℓ) (G , is-set) (G , is-set)
      RE g = Σ≡Prop (λ X → isPropIsOfHLevel {A = X} 2) (ua (rightEquiv g))

      lemma₁ : (g h : G) → Square
        (ua (rightEquiv g)) (ua (rightEquiv (g · h)))
        refl (ua (rightEquiv h))
      lemma₁ g h = invEq
                   (Square≃doubleComp (ua (rightEquiv g)) (ua (rightEquiv (g · h)))
                     refl (ua (rightEquiv h)))
                   (ua (rightEquiv g) ∙ ua (rightEquiv h)
                       ≡⟨ (uaCompEquiv (rightEquiv g) (rightEquiv h)) ⁻¹ ⟩
                    ua (compEquiv (rightEquiv g) (rightEquiv h))
                       ≡⟨ cong ua (compRightEquiv g h) ⟩
                    ua (rightEquiv (g · h)) ∎)

      REComp : (g h : G) → Square (RE g) (RE (g · h)) refl (RE h)
      REComp g h = ΣSquareSet (λ _ → isProp→isSet isPropIsSet) (lemma₁ g h)
  Codes : EM₁ Ĝ → Type ℓ
  Codes x = CodesSet x .fst

  encode : (x : EM₁ Ĝ) → embase ≡ x → Codes x
  encode x p = subst Codes p 1g

  decode : (x : EM₁ Ĝ) → Codes x → embase ≡ x
  decode = elimSet Ĝ (λ x → isOfHLevelΠ 2 (λ c → isGroupoidEM₁ (embase) x))
    emloop λ g → ua→ λ h → emcomp h g

  decode-encode : (x : EM₁ Ĝ) (p : embase ≡ x) → decode x (encode x p) ≡ p
  decode-encode x p = J (λ y q → decode y (encode y q) ≡ q)
    (emloop (transport refl 1g) ≡⟨ cong emloop (transportRefl 1g) ⟩
     emloop 1g ≡⟨ emloop-id ⟩ refl ∎) p

  encode-decode : (x : EM₁ Ĝ) (c : Codes x) → encode x (decode x c) ≡ c
  encode-decode = elimProp Ĝ (λ x → isOfHLevelΠ 1 (λ c → CodesSet x .snd _ _))
    λ g → encode embase (decode embase g) ≡⟨ refl ⟩
          encode embase (emloop g) ≡⟨ refl ⟩
          transport (ua (rightEquiv g)) 1g ≡⟨ uaβ (rightEquiv g) 1g ⟩
          1g · g ≡⟨ ·IdL g ⟩
          g ∎

  ΩEM₁Iso : Iso (Path (EM₁ Ĝ) embase embase) G
  Iso.fun ΩEM₁Iso = encode embase
  Iso.inv ΩEM₁Iso = emloop
  Iso.rightInv ΩEM₁Iso = encode-decode embase
  Iso.leftInv ΩEM₁Iso = decode-encode embase

  ΩEM₁≡ : (Path (EM₁ Ĝ) embase embase) ≡ G
  ΩEM₁≡ = isoToPath ΩEM₁Iso

--------- Ω (EMₙ₊₁ G) ≃ EMₙ G ---------
module _ {G : AbGroup ℓ} where
  open AbGroupStr (snd G)
    renaming (_+_ to _+G_ ; -_ to -G_ ; +Assoc to +AssocG)

  CODE : (n : ℕ) → EM G (suc (suc n)) → TypeOfHLevel ℓ (3 + n)
  CODE n =
    Trunc.elim (λ _ → isOfHLevelTypeOfHLevel (3 + n))
      λ { north → EM G (suc n) , hLevelEM G (suc n)
        ; south → EM G (suc n) , hLevelEM G (suc n)
        ; (merid a i) → fib n a i}
    where
    fib : (n : ℕ) → (a : EM-raw G (suc n))
        → Path (TypeOfHLevel _ (3 + n))
                (EM G (suc n) , hLevelEM G (suc n))
                (EM G (suc n) , hLevelEM G (suc n))
    fib zero a = Σ≡Prop (λ _ → isPropIsOfHLevel 3)
                   (isoToPath (addIso 1 a))
    fib (suc n) a = Σ≡Prop (λ _ → isPropIsOfHLevel (4 + n))
                            (isoToPath (addIso (suc (suc n)) ∣ a ∣))

  decode' : (n : ℕ) (x : EM G (suc (suc n))) → CODE n x .fst → 0ₖ (suc (suc n)) ≡ x
  decode' n =
    Trunc.elim (λ _ → isOfHLevelΠ (4 + n)
            λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
           λ { north → f n
             ; south → g n
             ; (merid a i) → main a i}
     where
     f : (n : ℕ) → _
     f n = σ-EM' n

     g : (n : ℕ) → EM G (suc n) → ∣ ptEM-raw ∣ ≡ ∣ south ∣
     g n x = σ-EM' n x ∙ cong ∣_∣ₕ (merid ptEM-raw)

     lem₂ : (n : ℕ) (a x : _)
       → Path (Path (EM G (suc (suc n))) _ _)
               ((λ i → cong ∣_∣ₕ (σ-EM n x) i) ∙ sym (cong ∣_∣ₕ (σ-EM n a)) ∙ (λ i → ∣ merid a i ∣ₕ))
               (g n (EM-raw→EM G (suc n) x))
     lem₂ zero a x =
       cong (f zero x ∙_)
         (cong (_∙ cong ∣_∣ₕ (merid a)) (cong (cong ∣_∣ₕ) (symDistr (merid a) (sym (merid embase)))
                                     ∙ cong-∙ ∣_∣ₕ (merid embase) (sym (merid a)))
          ∙∙ sym (∙assoc _ _ _)
          ∙∙ cong (cong ∣_∣ₕ (merid embase) ∙_) (lCancel (cong ∣_∣ₕ (merid a)))
           ∙ sym (rUnit _))
     lem₂ (suc n) a x =
       cong (f (suc n) ∣ x ∣ ∙_)
         ((cong (_∙ cong ∣_∣ₕ (merid a)) (cong (cong ∣_∣ₕ) (symDistr (merid a) (sym (merid north)))
                                      ∙ cong-∙ ∣_∣ₕ (merid north) (sym (merid a)))
          ∙∙ sym (∙assoc _ _ _)
          ∙∙ cong (cong ∣_∣ₕ (merid north) ∙_) (lCancel (cong ∣_∣ₕ (merid a)))
           ∙ sym (rUnit _)))

     lem : (n : ℕ) (x a : EM-raw G (suc n))
             → f n (transport (sym (cong (λ x → CODE n x .fst) (cong ∣_∣ₕ (merid a))))
                    (EM-raw→EM G (suc n) x))
                ≡ cong ∣_∣ₕ (σ-EM n x) ∙ sym (cong ∣_∣ₕ (σ-EM n a))
     lem zero x a = (λ i → cong ∣_∣ₕ (merid (transportRefl x i -[ 1 ]ₖ a) ∙ sym (merid embase)))
                  ∙∙ σ-EM'-hom zero x (-ₖ a)
                  ∙∙ cong (f zero x ∙_) (σ-EM'-ₖ zero a)
     lem (suc n) x a =
          cong (f (suc n)) (λ i → transportRefl ∣ x ∣ i -[ 2 + n ]ₖ ∣ a ∣)
        ∙∙ σ-EM'-hom (suc n) ∣ x ∣ (-ₖ ∣ a ∣)
        ∙∙ cong (f (suc n) ∣ x ∣ ∙_) (σ-EM'-ₖ (suc n) ∣ a ∣)

     main : (a : _)
         → PathP (λ i → CODE n ∣ merid a i ∣ₕ .fst
                       → 0ₖ (suc (suc n)) ≡ ∣ merid a i ∣ₕ) (f n) (g n)
     main a =
       toPathP (funExt
         (EM-elim _ (λ _ → isOfHLevelPathP (2 + (suc n)) (isOfHLevelTrunc (4 + n) _ _) _ _)
           λ x →
            ((λ i → transp (λ j → Path (EM G (2 + n)) ∣ ptEM-raw ∣ ∣ merid a (i ∨ j) ∣)
                         i (compPath-filler (lem n x a i) (cong ∣_∣ₕ (merid a)) i) ))
         ∙∙ sym (∙assoc _ _ _)
         ∙∙ lem₂ n a x))

  encode' : (n : ℕ) (x : EM G (suc (suc n))) → 0ₖ (suc (suc n)) ≡ x → CODE n x .fst
  encode' n x p = subst (λ x → CODE n x .fst) p (0ₖ (suc n))

  decode'-encode' : (n : ℕ) (x : EM G (2 + n)) (p : 0ₖ (2 + n) ≡ x)
    → decode' n x (encode' n x p) ≡ p
  decode'-encode' zero x =
    J (λ x p → decode' 0 x (encode' 0 x p) ≡ p)
      (σ-EM'-0ₖ 0)
  decode'-encode' (suc n) x =
    J (λ x p → decode' (suc n) x (encode' (suc n) x p) ≡ p)
       (σ-EM'-0ₖ (suc n))

  encode'-decode' : (n : ℕ) (x : _)
    → encode' n (0ₖ (suc (suc n))) (decode' n (0ₖ (suc (suc n))) x) ≡ x
  encode'-decode' zero x =
        cong (encode' zero (0ₖ 2)) (cong-∙ ∣_∣ₕ (merid x) (sym (merid embase)))
     ∙∙ substComposite (λ x → CODE zero x .fst)
                              (cong ∣_∣ₕ (merid x)) (sym (cong ∣_∣ₕ (merid ptEM-raw))) embase
     ∙∙ (cong (subst (λ x₁ → CODE zero x₁ .fst) (λ i → ∣ merid embase (~ i) ∣ₕ))
                                 (λ i → lUnitₖ 1 (transportRefl x i) i)
      ∙ (λ i → rUnitₖ 1 (transportRefl x i) i))
  encode'-decode' (suc n) =
    Trunc.elim (λ _ → isOfHLevelTruncPath {n = 4 + n})
      λ x → cong (encode' (suc n) (0ₖ (3 + n))) (cong-∙ ∣_∣ₕ (merid x) (sym (merid north)))
    ∙∙ substComposite (λ x → CODE (suc n) x .fst)
         (cong ∣_∣ₕ (merid x)) (sym (cong ∣_∣ₕ (merid ptEM-raw))) (0ₖ (2 + n))
    ∙∙ cong (subst (λ x₁ → CODE (suc n) x₁ .fst) (λ i → ∣ merid ptEM-raw (~ i) ∣ₕ))
            (λ i → lUnitₖ (2 + n) (transportRefl ∣ x ∣ₕ i) i)
     ∙ (λ i → rUnitₖ (2 + n) (transportRefl ∣ x ∣ₕ i) i)

  Iso-EM-ΩEM+1 : (n : ℕ) → Iso (EM G n) (typ (Ω (EM∙ G (suc n))))
  Iso-EM-ΩEM+1 zero = invIso (ΩEM₁Iso (AbGroup→Group G))
  Iso.fun (Iso-EM-ΩEM+1 (suc n)) = decode' n (0ₖ (2 + n))
  Iso.inv (Iso-EM-ΩEM+1 (suc n)) = encode' n ∣ north ∣
  Iso.rightInv (Iso-EM-ΩEM+1 (suc n)) = decode'-encode' _ _
  Iso.leftInv (Iso-EM-ΩEM+1 (suc n)) = encode'-decode' _

  EM≃ΩEM+1 : (n : ℕ) → EM G n ≃ typ (Ω (EM∙ G (suc n)))
  EM≃ΩEM+1 n = isoToEquiv (Iso-EM-ΩEM+1 n)

  -- Some properties of the isomorphism
  EM→ΩEM+1 : (n : ℕ) → EM G n → typ (Ω (EM∙ G (suc n)))
  EM→ΩEM+1 n = Iso.fun (Iso-EM-ΩEM+1 n)

  ΩEM+1→EM : (n : ℕ) → typ (Ω (EM∙ G (suc n))) → EM G n
  ΩEM+1→EM n = Iso.inv (Iso-EM-ΩEM+1 n)

  EM→ΩEM+1-0ₖ : (n : ℕ) → EM→ΩEM+1 n (0ₖ n) ≡ refl
  EM→ΩEM+1-0ₖ zero = emloop-1g _
  EM→ΩEM+1-0ₖ (suc zero) = cong (cong ∣_∣ₕ) (rCancel (merid ptEM-raw))
  EM→ΩEM+1-0ₖ (suc (suc n)) = cong (cong ∣_∣ₕ) (rCancel (merid ptEM-raw))

  EM→ΩEM+1-hom : (n : ℕ) (x y : EM G n)
    → EM→ΩEM+1 n (x +[ n ]ₖ y) ≡ EM→ΩEM+1 n x ∙ EM→ΩEM+1 n y
  EM→ΩEM+1-hom zero x y = emloop-comp _ x y
  EM→ΩEM+1-hom (suc zero) x y = σ-EM'-hom zero x y
  EM→ΩEM+1-hom (suc (suc n)) x y = σ-EM'-hom (suc n) x y

  EM→ΩEM+1-sym : (n : ℕ) (x : EM G n) → EM→ΩEM+1 n (-ₖ x) ≡ sym (EM→ΩEM+1 n x)
  EM→ΩEM+1-sym n =
    morphLemmas.distrMinus _+ₖ_ _∙_ (EM→ΩEM+1 n) (EM→ΩEM+1-hom n)
      (0ₖ n) refl
      -ₖ_ sym
      (λ x → sym (lUnit x)) (λ x → sym (rUnit x))
      (lCancelₖ n) rCancel
      ∙assoc
      (EM→ΩEM+1-0ₖ n)

  ΩEM+1→EM-sym : (n : ℕ) (p : typ (Ω (EM∙ G (suc n))))
    → ΩEM+1→EM n (sym p) ≡ -ₖ (ΩEM+1→EM n p)
  ΩEM+1→EM-sym n p = sym (cong (ΩEM+1→EM n) (EM→ΩEM+1-sym n (ΩEM+1→EM n p)
                    ∙ cong sym (Iso.rightInv (Iso-EM-ΩEM+1 n) p)))
                    ∙ Iso.leftInv (Iso-EM-ΩEM+1 n) (-ₖ ΩEM+1→EM n p)

  ΩEM+1→EM-hom : (n : ℕ) → (p q : typ (Ω (EM∙ G (suc n))))
    → ΩEM+1→EM n (p ∙ q) ≡ (ΩEM+1→EM n p) +[ n ]ₖ (ΩEM+1→EM n q)
  ΩEM+1→EM-hom n =
    morphLemmas.isMorphInv (λ x y → x +[ n ]ₖ y) (_∙_) (EM→ΩEM+1 n)
      (EM→ΩEM+1-hom n) (ΩEM+1→EM n)
      (Iso.rightInv (Iso-EM-ΩEM+1 n)) (Iso.leftInv (Iso-EM-ΩEM+1 n))

  ΩEM+1→EM-refl : (n : ℕ) → ΩEM+1→EM n refl ≡ 0ₖ n
  ΩEM+1→EM-refl zero = transportRefl 0g
  ΩEM+1→EM-refl (suc zero) = refl
  ΩEM+1→EM-refl (suc (suc n)) = refl

  EM→ΩEM+1∙ : (n : ℕ) → EM∙ G n →∙ Ω (EM∙ G (suc n))
  EM→ΩEM+1∙ n .fst = EM→ΩEM+1 n
  EM→ΩEM+1∙ zero .snd = emloop-1g (AbGroup→Group G)
  EM→ΩEM+1∙ (suc zero) .snd = cong (cong ∣_∣ₕ) (rCancel (merid embase))
  EM→ΩEM+1∙ (suc (suc n)) .snd = cong (cong ∣_∣ₕ) (rCancel (merid north))

  EM≃ΩEM+1∙ : (n : ℕ) → EM∙ G n ≡ Ω (EM∙ G (suc n))
  EM≃ΩEM+1∙ n = ua∙ (EM≃ΩEM+1 n) (EM→ΩEM+1-0ₖ n)

  isHomogeneousEM : (n : ℕ) → isHomogeneous (EM∙ G n)
  isHomogeneousEM n x =
    ua∙ (isoToEquiv (addIso n x)) (lUnitₖ n x)

  isCommΩEM-base : (n : ℕ) (x : _)
    (p q : typ (Ω (EM G  (suc n) , x))) → p ∙ q ≡ q ∙ p
  isCommΩEM-base n =
    EM-raw'-elim _ _ (λ _ → isOfHLevelΠ2 (2 + n)
                     λ _ _ → isOfHLevelPath (2 + n)
                              (hLevelEM _ (suc n) _ _) _ _)
    (EM-raw'-trivElim _ _
     (λ _ → isOfHLevelΠ2 (suc n) λ _ _ → hLevelEM _ (suc n) _ _ _ _)
      (lem n))
    where
    * : (n : ℕ) → _
    * n = EM-raw'→EM G (suc n) (snd (EM-raw'∙ G (suc n)))

    lem : (n : ℕ) (p q : typ (Ω (EM G (suc n) , * n)))
             →  p ∙ q ≡ q ∙ p
    lem zero = isCommΩEM zero
    lem (suc n) = isCommΩEM (suc n)

  -- ΩEM+1→EM for arbitrarily based loops. Defining it by pattern
  -- matching is more involved but should give better computational
  -- properties.
  ΩEM+1→EM-gen : (n : ℕ) (x : EM G (suc n)) → x ≡ x → EM G n
  ΩEM+1→EM-gen zero =
    elimSet _ (λ _ → isSetΠ λ _ → is-set) (ΩEM+1→EM 0)
      λ g → toPathP (funExt
        λ q → transportRefl (ΩEM+1→EM 0
                (transport (λ i → Path (EM G (suc zero))
                   (emloop g (~ i)) (emloop g (~ i))) q))
      ∙ cong (ΩEM+1→EM 0)
           (fromPathP
             (doubleCompPath-filler (emloop g) q (sym (emloop g))
           ▷ (doubleCompPath≡compPath _ _ _
           ∙∙ cong (emloop g ∙_) (isCommΩEM 0 q (sym (emloop g)))
           ∙∙ ∙assoc _ _ _
           ∙∙ cong (_∙ q) (rCancel (emloop g))
           ∙∙ sym (lUnit q)))))
  ΩEM+1→EM-gen (suc n) =
    Trunc.elim (λ _ → isOfHLevelΠ (4 + n)
             λ _ → isOfHLevelSuc (3 + n) (hLevelEM _ (suc n)))
      λ { north → ΩEM+1→EM (suc n)
        ; south p → ΩEM+1→EM (suc n) (cong ∣_∣ₕ (merid ptEM-raw)
                                    ∙∙ p
                                    ∙∙ cong ∣_∣ₕ (sym (merid ptEM-raw)))
        ; (merid a i) → help a i}
        where
        help : (a : EM-raw G (suc n))
          → PathP (λ i → Path (EM G (suc (suc n))) ∣ merid a i ∣ ∣ merid a i ∣
                        → EM G (suc n))
                   (ΩEM+1→EM (suc n))
                   λ p → ΩEM+1→EM (suc n) (cong ∣_∣ₕ (merid ptEM-raw)
                                         ∙∙ p
                                         ∙∙ cong ∣_∣ₕ (sym (merid ptEM-raw)))
        help a =
          toPathP (funExt (λ p →
            (transportRefl (ΩEM+1→EM (suc n)
              (transport (λ i → Path (EM G (suc (suc n)))
                                  ∣ merid a (~ i) ∣ ∣ merid a (~ i) ∣) p))
           ∙ cong (ΩEM+1→EM (suc n))
             (flipTransport
               (((rUnit p
                 ∙ cong (p ∙_) (sym (lCancel _)))
                ∙ isCommΩEM-base (suc n) ∣ south ∣ p _)
              ∙∙ sym (∙assoc _ _ p)
              ∙∙ cong₂ _∙_ (cong (cong ∣_∣ₕ)
                            (sym (cong sym (symDistr
                             (sym (merid a)) (merid ptEM-raw)))))
                           (isCommΩEM-base _ _ _ p)
              ∙∙ sym (doubleCompPath≡compPath _ _ _)
              ∙∙ λ j → transp (λ i → Path (EM G (suc (suc n)))
                              ∣ merid a (i ∨ ~ j) ∣ ∣ merid a (i ∨ ~ j) ∣) (~ j)
                       (cong ∣_∣ₕ (compPath-filler'
                          (sym (merid a)) (merid ptEM-raw) (~ j))
                     ∙∙ p
                     ∙∙ cong ∣_∣ₕ (compPath-filler
                         (sym (merid ptEM-raw)) (merid a) (~ j))))))))

  EM→ΩEM+1∘EM-raw→EM : (n : ℕ) (x : EM-raw G (suc n))
    → EM→ΩEM+1 (suc n) (EM-raw→EM _ _ x) ≡ cong ∣_∣ₕ (merid x ∙ sym (merid ptEM-raw))
  EM→ΩEM+1∘EM-raw→EM zero x = refl
  EM→ΩEM+1∘EM-raw→EM (suc n) x = refl

  EM→ΩEM+1-gen : (n : ℕ) (x : EM G (suc n))
    → EM G n → x ≡ x
  EM→ΩEM+1-gen n x p =
       sym (rUnitₖ (suc n) x)
    ∙∙ cong (x +ₖ_) (EM→ΩEM+1 n p)
    ∙∙ rUnitₖ (suc n) x

  ΩEM+1-gen→EM-0ₖ : (n : ℕ) (x : _)
    → ΩEM+1→EM-gen n (0ₖ (suc n)) x
    ≡ ΩEM+1→EM n x
  ΩEM+1-gen→EM-0ₖ zero p = refl
  ΩEM+1-gen→EM-0ₖ (suc n) p = refl

  EM→ΩEM+1-gen-0ₖ : (n : ℕ) (x : _)
    → EM→ΩEM+1-gen n (0ₖ (suc n)) x
    ≡ EM→ΩEM+1 n x
  EM→ΩEM+1-gen-0ₖ zero x = sym (rUnit _)
    ∙ λ j i → lUnitₖ 1 (EM→ΩEM+1 zero x i) j
  EM→ΩEM+1-gen-0ₖ (suc n) x = sym (rUnit _)
    ∙ λ j i → lUnitₖ (suc (suc n)) (EM→ΩEM+1 (suc n) x i) j

  EM→ΩEM+1→EM-gen : (n : ℕ) (x : EM G (suc n))
    → (y : EM G n) → ΩEM+1→EM-gen n x (EM→ΩEM+1-gen n x y) ≡ y
  EM→ΩEM+1→EM-gen n =
    EM-raw'-elim _ _
      (λ _ → isOfHLevelΠ (suc (suc n))
            (λ _ → isOfHLevelPath (suc (suc n))
            (hLevelEM _ n) _ _))
     (EM-raw'-trivElim _ n
       (λ _ → isOfHLevelΠ (suc n) λ _ → hLevelEM _ n _ _)
       λ y → cong (λ p → ΩEM+1→EM-gen n p
                     (EM→ΩEM+1-gen n p y))
              (EM-raw'→EM∙ G (suc n))
            ∙ (λ i → ΩEM+1-gen→EM-0ₖ n (EM→ΩEM+1-gen-0ₖ n y i) i)
            ∙ Iso.leftInv (Iso-EM-ΩEM+1 n) y)

  ΩEM+1→EM→ΩEM+1-gen : (n : ℕ) (x : EM G (suc n))
    → (y : x ≡ x) → EM→ΩEM+1-gen n x (ΩEM+1→EM-gen n x y) ≡ y
  ΩEM+1→EM→ΩEM+1-gen n =
    EM-raw'-elim _ _
      (λ _ → isOfHLevelΠ (suc (suc n))
              (λ _ → isOfHLevelPath (suc (suc n))
              (hLevelEM _ (suc n) _ _) _ _))
     (EM-raw'-trivElim _ n
       (λ _ → isOfHLevelΠ (suc n)
         λ _ → hLevelEM _ (suc n) _ _ _ _)
     (subst (λ p → (y : p ≡ p)
       → EM→ΩEM+1-gen n p (ΩEM+1→EM-gen n p y) ≡ y)
       (sym (EM-raw'→EM∙ _ (suc n)))
       λ p → (λ i → EM→ΩEM+1-gen-0ₖ n (ΩEM+1-gen→EM-0ₖ n p i) i)
            ∙ Iso.rightInv (Iso-EM-ΩEM+1 n) p))

  Iso-EM-ΩEM+1-gen : (n : ℕ) (x : EM G (suc n))
    → Iso (EM G n) (x ≡ x)
  Iso.fun (Iso-EM-ΩEM+1-gen n x) = EM→ΩEM+1-gen n x
  Iso.inv (Iso-EM-ΩEM+1-gen n x) = ΩEM+1→EM-gen n x
  Iso.rightInv (Iso-EM-ΩEM+1-gen n x) = ΩEM+1→EM→ΩEM+1-gen n x
  Iso.leftInv (Iso-EM-ΩEM+1-gen n x) = EM→ΩEM+1→EM-gen n x

  ΩEM+1→EM-gen-refl : (n : ℕ) (x : EM G (suc n))
    → ΩEM+1→EM-gen n x refl ≡ 0ₖ n
  ΩEM+1→EM-gen-refl n =
    EM-raw'-elim _ (suc n)
      (λ _ → isOfHLevelPath (suc (suc n)) (hLevelEM _ n) _ _)
      (EM-raw'-trivElim _ n
        (λ _ → hLevelEM _ n _ _)
        (lem n))
    where
    lem : (n : ℕ) → ΩEM+1→EM-gen n
      (EM-raw'→EM G (suc n) (snd (EM-raw'∙ G (suc n)))) refl
      ≡ 0ₖ n
    lem zero = ΩEM+1→EM-refl 0
    lem (suc n) = ΩEM+1→EM-refl (suc n)

  ΩEM+1→EM-gen-hom : (n : ℕ) (x : EM G (suc n)) (p q : x ≡ x)
    → ΩEM+1→EM-gen n x (p ∙ q) ≡ ΩEM+1→EM-gen n x p +ₖ ΩEM+1→EM-gen n x q
  ΩEM+1→EM-gen-hom n =
    EM-raw'-elim _ (suc n)
      (λ _ → isOfHLevelΠ2 (suc (suc n))
        (λ _ _ → isOfHLevelPath (suc (suc n)) (hLevelEM _ n) _ _))
      (EM-raw'-trivElim _ n
        (λ _ → isOfHLevelΠ2 (suc n) (λ _ _ → hLevelEM _ n _ _))
          (lem n))
    where
    lem : (n : ℕ) (p q : EM-raw'→EM G (suc n) (snd (EM-raw'∙ G (suc n)))
                        ≡ EM-raw'→EM G (suc n) (snd (EM-raw'∙ G (suc n))))
      → ΩEM+1→EM-gen n _ (p ∙ q)
       ≡ ΩEM+1→EM-gen n _ p
       +ₖ ΩEM+1→EM-gen n _ q
    lem zero p q = ΩEM+1→EM-hom 0 p q
    lem (suc n) p q = ΩEM+1→EM-hom (suc n) p q

-- Some HLevel lemmas about function spaces (EM∙ G n →∙ EM∙ H m), mainly used for
-- the cup product
module _ where
  open AbGroupStr renaming (_+_ to comp)

  isContr-↓∙ : {G : AbGroup ℓ} {H : AbGroup ℓ'} (n : ℕ) → isContr (EM∙ G (suc n) →∙ EM∙ H n)
  fst (isContr-↓∙ {G = G} {H = H} zero) = (λ _ → 0g (snd H)) , refl
  snd (isContr-↓∙{G = G} {H = H} zero) (f , p) =
    Σ≡Prop (λ x → is-set (snd H) _ _)
      (funExt (raw-elim G 0 (λ _ → is-set (snd H) _ _) (sym p)))
  fst (isContr-↓∙ {G = G} {H = H} (suc n)) = (λ _ → 0ₖ (suc n)) , refl
  fst (snd (isContr-↓∙ {G = G} {H = H} (suc n)) f i) x =
    Trunc.elim {B = λ x → 0ₖ (suc n) ≡ fst f x}
    (λ _ → isOfHLevelPath (4 + n) (isOfHLevelSuc (3 + n) (hLevelEM H (suc n))) _ _)
    (raw-elim _ _ (λ _ → hLevelEM H (suc n) _ _) (sym (snd f)))
    x i
  snd (snd (isContr-↓∙ (suc n)) f i) j = snd f (~ i ∨ j)

  isContr-↓∙' : {G : AbGroup ℓ} {H : AbGroup ℓ'} (n : ℕ)
              → isContr ((EM-raw G (suc n) , ptEM-raw) →∙ EM∙ H n)
  isContr-↓∙' zero = isContr-↓∙ zero
  fst (isContr-↓∙' (suc n)) = (λ _ → 0ₖ (suc n)) , refl
  fst (snd (isContr-↓∙' {H = H} (suc n)) f i) x =
    raw-elim _  _ {A = λ x → 0ₖ (suc n) ≡ fst f x}
      (λ _ → hLevelEM H (suc n) _ _) (sym (snd f)) x i
  snd (snd (isContr-↓∙' (suc n)) f i) j = snd f (~ i ∨ j)

  isOfHLevel→∙EM : ∀ {ℓ} {A : Pointed ℓ} {G : AbGroup ℓ'} (n m : ℕ)
    → isOfHLevel (suc m) (A →∙ EM∙ G n)
    → isOfHLevel (suc (suc m)) (A →∙ EM∙ G (suc n))
  isOfHLevel→∙EM {A = A} {G = G} n m hlev = step₃
    where
    step₁ : isOfHLevel (suc m) (A →∙ Ω (EM∙ G (suc n)))
    step₁ =
      subst (isOfHLevel (suc m))
      (λ i → A →∙ ua∙ {A = Ω (EM∙ G (suc n))} {B = EM∙ G n}
      (invEquiv (EM≃ΩEM+1 n))
      (ΩEM+1→EM-refl n) (~ i)) hlev

    step₂ : isOfHLevel (suc m) (typ (Ω (A →∙ EM∙ G (suc n) ∙)))
    step₂ = isOfHLevelRetractFromIso (suc m) (invIso (invIso (ΩfunExtIso _ _))) step₁

    step₃ : isOfHLevel (suc (suc m)) (A →∙ EM∙ G (suc n))
    step₃ = isOfHLevelΩ→isOfHLevel m
      λ f → subst (λ x → isOfHLevel (suc m) (typ (Ω x)))
               (isHomogeneous→∙ (isHomogeneousEM (suc n)) f)
                step₂

  isOfHLevel↑∙ : {G : AbGroup ℓ} {H : AbGroup ℓ'}
            → ∀ n m → isOfHLevel (2 + n) (EM∙ G (suc m) →∙ EM∙ H (suc (n + m)))
  isOfHLevel↑∙ zero m = isOfHLevel→∙EM m 0 (isContr→isProp (isContr-↓∙ m))
  isOfHLevel↑∙ (suc n) m = isOfHLevel→∙EM (suc (n + m)) (suc n) (isOfHLevel↑∙ n m)

  isOfHLevel↑∙-lem : {G : AbGroup ℓ} {H : AbGroup ℓ'}
            → ∀ n m → isOfHLevel (2 + n) (EM-raw∙ G (suc m) →∙ EM∙ H (suc (n + m)))
  isOfHLevel↑∙-lem zero m = isOfHLevel→∙EM m 0 (isContr→isProp (isContr-↓∙' m))
  isOfHLevel↑∙-lem (suc n) m = isOfHLevel→∙EM (suc (n + m)) (suc n) (isOfHLevel↑∙-lem n m)

  EM₁→∙Iso : {G : AbGroup ℓ} {H : AbGroup ℓ'} (m : ℕ)
    → Iso (EM-raw'∙ G 1 →∙ EM∙ H (suc m)) (fst G → typ (Ω (EM∙ H (suc m))))
  Iso.fun (EM₁→∙Iso m) f g = sym (snd f) ∙∙ cong (fst f) (emloop-raw g) ∙∙ snd f
  fst (Iso.inv (EM₁→∙Iso m) f) embase-raw = 0ₖ (suc m)
  fst (Iso.inv (EM₁→∙Iso m) f) (emloop-raw g i) = f g i
  snd (Iso.inv (EM₁→∙Iso m) f) = refl
  Iso.rightInv (EM₁→∙Iso m) f = funExt λ x → sym (rUnit _)
  Iso.leftInv (EM₁→∙Iso m) (f , p) =
    →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ { embase-raw → sym p
                ; (emloop-raw g i) j
               → doubleCompPath-filler (sym p) (cong f (emloop-raw g)) p (~ j) i})

  isOfHLevel↑∙' : {G : AbGroup ℓ} {H : AbGroup ℓ'}
            → ∀ n m → isOfHLevel (2 + n) (EM-raw'∙ G m →∙ EM∙ H (n + m))
  isOfHLevel↑∙' {H = H} zero zero =
    isOfHLevelΣ 2 (isOfHLevelΠ 2 (λ _ → AbGroupStr.is-set (snd H)))
                   λ _ → isOfHLevelPath 2 (AbGroupStr.is-set (snd H)) _ _
  isOfHLevel↑∙' zero (suc zero) =
    subst (isOfHLevel 2) (sym (isoToPath (EM₁→∙Iso 0)))
      (isSetΠ λ _ → emsquash _ _)
  isOfHLevel↑∙' zero (suc (suc m)) = isOfHLevel↑∙-lem zero (suc m)
  isOfHLevel↑∙' {H = H} (suc n) zero =
    isOfHLevelΣ (2 + suc n) (isOfHLevelΠ (2 + suc n)
      (λ _ → subst (isOfHLevel (suc (suc (suc n))))
                    (cong (EM H) (cong suc (+-comm 0 n)))
                    (hLevelEM H (suc n))))
        λ _ → isOfHLevelPath (suc (suc (suc n)))
                (subst (isOfHLevel (suc (suc (suc n))))
                       (cong (EM H) (cong suc (+-comm 0 n)))
                    (hLevelEM H (suc n))) _ _
  isOfHLevel↑∙' {G = G} {H = H} (suc n) (suc zero) =
    subst (isOfHLevel (2 + suc n)) (sym (isoToPath (EM₁→∙Iso (suc n)))
                                   ∙ λ i → EM-raw'∙ G 1 →∙ EM∙ H (suc (+-comm 1 n i)))
          (isOfHLevelΠ (2 + suc n) λ x →  (isOfHLevelTrunc (4 + n) _ _))
  isOfHLevel↑∙' {G = G} {H = H} (suc n) (suc (suc m)) =
    subst (isOfHLevel (2 + suc n))
      (λ i → (EM-raw'∙ G (suc (suc m))
           →∙ EM∙ H (suc (+-suc n (suc m) (~ i)))))
      (isOfHLevel↑∙-lem (suc n) (suc m))

  →∙EMPath : ∀ {ℓ} {G : AbGroup ℓ} (A : Pointed ℓ') (n : ℕ)
           → Ω (A →∙ EM∙ G (suc n) ∙) ≡ (A →∙ EM∙ G n ∙)
  →∙EMPath {G = G} A n =
      ua∙ (isoToEquiv (ΩfunExtIso A (EM∙ G (suc n)))) refl
    ∙ (λ i → (A →∙ EM≃ΩEM+1∙ {G = G} n (~ i) ∙))

  private
    contr∙-lem : {G : AbGroup ℓ} {H : AbGroup ℓ'} {L : AbGroup ℓ''} (n m : ℕ)
      → isContr (EM∙ G (suc n) →∙ (EM∙ H (suc m) →∙ EM∙ L (suc (n + m)) ∙))
    fst (contr∙-lem n m) = (λ _ → (λ _ → 0ₖ _) , refl), refl
    snd (contr∙-lem {G = G} {H = H} {L = L} n m) (f , p) =
      →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
        (sym (funExt (help n f p)))
      where
      help : (n : ℕ) → (f : EM G (suc n) → EM∙ H (suc m) →∙ EM∙ L (suc (n + m)))
          → f (snd (EM∙ G (suc n))) ≡ snd (EM∙ H (suc m) →∙ EM∙ L (suc (n + m)) ∙)
          → (x : _) → (f x) ≡ ((λ _ → 0ₖ _) , refl)
      help zero f p =
        raw-elim G zero
          (λ _ → isOfHLevel↑∙ zero m _ _) p
      help (suc n) f p =
        Trunc.elim (λ _ → isOfHLevelPath (4 + n)
               (subst (λ x → isOfHLevel x (EM∙ H (suc m) →∙ EM∙ L (suc ((suc n) + m))))
                      (λ i → suc (suc (+-comm (suc n) 1 i)))
                      (isOfHLevelPlus' {n = 1} (3 + n) (isOfHLevel↑∙ (suc n) m))) _ _)
          (raw-elim G (suc n)
            (λ _ → isOfHLevel↑∙ (suc n) m _ _) p)

    contr∙-lem' : {G : AbGroup ℓ} {H : AbGroup ℓ'} {L : AbGroup ℓ''} (n m : ℕ)
      → isContr (EM∙ G (suc n) →∙ (EM-raw'∙ H (suc m) →∙ EM∙ L (suc (n + m)) ∙))
    fst (contr∙-lem' n m) = (λ _ → (λ _ → 0ₖ _) , refl) , refl
    snd (contr∙-lem' {G = G} {H = H} {L = L} n m) (f , p) =
      →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
        (funExt λ x → sym (help' n f p x))
      where
      help' : (n : ℕ) → (f : EM G (suc n) → EM-raw'∙ H (suc m) →∙ EM∙ L (suc (n + m)))
        → f (snd (EM∙ G (suc n))) ≡ snd (EM-raw'∙ H (suc m) →∙ EM∙ L (suc (n + m)) ∙)
        → (x : _) → (f x) ≡ ((λ _ → 0ₖ _) , refl)
      help' zero f p =
        raw-elim _ zero (λ _ → isOfHLevel↑∙' zero (suc m) _ _) p
      help' (suc n) f p =
        Trunc.elim (λ _ → isOfHLevelPath (4 + n)
                           (subst2 (λ x y → isOfHLevel x (EM-raw'∙ H (suc m) →∙ EM∙ L y))
                             (λ i → suc (suc (suc (+-comm n 1 i))))
                             (cong suc (+-suc n m))
                             (isOfHLevelPlus' {n = 1} (suc (suc (suc n)))
                             (isOfHLevel↑∙' {G = H} {H = L} (suc n) (suc m)))) _ _)
                   (raw-elim _ (suc n) (λ _ → isOfHLevelPath' (2 + n)
                     (subst (λ y → isOfHLevel (suc (suc (suc n)))
                            (EM-raw'∙ H (suc m) →∙ EM∙ L y))
                     (+-suc (suc n) m)
                     (isOfHLevel↑∙' {G = H} {H = L} (suc n) (suc m))) _ _) p)

    contr∙-lem'' :  {G : AbGroup ℓ} {H : AbGroup ℓ'} {L : AbGroup ℓ''} (n m : ℕ)
                → isContr (EM-raw'∙ G (suc n)
                →∙ (EM-raw'∙ H (suc m) →∙ EM∙ L (suc (n + m)) ∙))
    fst (contr∙-lem'' n m) = (λ _ → (λ _ → 0ₖ (suc (n + m))) , refl) , refl
    snd (contr∙-lem'' {G = G} {H = H} {L = L} n m) (f , p) =
      →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
        (funExt λ x → sym (help n f p x))
      where
      help : (n : ℕ) → (f : EM-raw' G (suc n) → EM-raw'∙ H (suc m) →∙ EM∙ L (suc (n + m)))
          → f (snd (EM-raw'∙ G (suc n))) ≡ snd (EM-raw'∙ H (suc m) →∙ EM∙ L (suc (n + m)) ∙)
          → (x : _) → (f x) ≡ ((λ _ → 0ₖ _) , refl)
      help zero f p =
        EM-raw'-trivElim G zero (λ _ → isOfHLevel↑∙' _ _ _ _) p
      help (suc n) f p =
        EM-raw'-trivElim _ _ (λ _ → isOfHLevelPath' (suc (suc n))
          (subst (λ y → isOfHLevel (suc (suc (suc n))) (EM-raw'∙ H (suc m) →∙ EM∙ L y))
                         (cong suc (+-suc n m))
                         (isOfHLevel↑∙' {G = H} {H = L} (suc n) (suc m))) _ _) p

  isOfHLevel↑∙∙ : {G : AbGroup ℓ} {H : AbGroup ℓ'} {L : AbGroup ℓ''}
     → ∀ n m l → isOfHLevel (2 + l) (EM∙ G (suc n)
                                  →∙ (EM∙ H (suc m)
                                   →∙ EM∙ L (suc (suc (l + n + m))) ∙))
  isOfHLevel↑∙∙ {G = G} {H = H} {L = L} n m zero =
    isOfHLevelΩ→isOfHLevel 0 λ f
      → subst
          isProp (cong (λ x → typ (Ω x))
          (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)) f))
          (isOfHLevelRetractFromIso 1 (ΩfunExtIso _ _) h)
    where
    h : isProp (EM∙ G (suc n)
             →∙ (Ω (EM∙ H (suc m)
              →∙ EM∙ L (suc (suc (n + m))) ∙)))
    h =
      subst isProp
        (λ i → EM∙ G (suc n)
            →∙ (→∙EMPath {G = L} (EM∙ H (suc m)) (suc (n + m)) (~ i)))
        (isContr→isProp (contr∙-lem n m))
  isOfHLevel↑∙∙ {G = G} {H = H} {L = L} n m (suc l) =
    isOfHLevelΩ→isOfHLevel (suc l)
      λ f →
      subst (isOfHLevel (2 + l))
          (cong (λ x → typ (Ω x))
          (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)) f))
          (isOfHLevelRetractFromIso (2 + l) (ΩfunExtIso _ _) h)
    where
    h : isOfHLevel (2 + l)
         (EM∙ G (suc n)
           →∙ (Ω (EM∙ H (suc m)
             →∙ EM∙ L (suc (suc (suc (l + n + m)))) ∙)))
    h =
      subst (isOfHLevel (2 + l))
        (λ i → EM∙ G (suc n)
             →∙ →∙EMPath {G = L} (EM∙ H (suc m)) (suc (suc (l + n + m))) (~ i))
        (isOfHLevel↑∙∙ n m l)

  isOfHLevel↑∙∙' : {G : AbGroup ℓ} {H : AbGroup ℓ'} {L : AbGroup ℓ''}
     → ∀ n m l → isOfHLevel (2 + l) (EM∙ G (suc n)
                                  →∙ (EM-raw'∙ H (suc m)
                                   →∙ EM∙ L (suc (suc (l + n + m))) ∙))
  isOfHLevel↑∙∙' {G = G} {H = H} {L = L} n m zero =
    isOfHLevelΩ→isOfHLevel 0
      λ f → subst
          isProp (cong (λ x → typ (Ω x))
          (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)) f))
          (isOfHLevelRetractFromIso 1 (ΩfunExtIso _ _)
          lem)
    where
    lem : isProp (EM∙ G (suc n)
             →∙ (Ω (EM-raw'∙ H (suc m)
              →∙ EM∙ L (suc (suc (n + m))) ∙)))
    lem = subst isProp
        (λ i → EM∙ G (suc n)
            →∙ (→∙EMPath {G = L} (EM-raw'∙ H (suc m)) (suc (n + m)) (~ i)))
        (isContr→isProp (contr∙-lem' n m))
  isOfHLevel↑∙∙' {G = G} {H = H} {L = L} n m (suc l) =
    isOfHLevelΩ→isOfHLevel (suc l)
      λ f →
      subst (isOfHLevel (2 + l))
          (cong (λ x → typ (Ω x))
          (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)) f))
          (isOfHLevelRetractFromIso (2 + l) (ΩfunExtIso _ _) lem)
    where
    lem : isOfHLevel (2 + l)
         (EM∙ G (suc n)
           →∙ (Ω (EM-raw'∙ H (suc m)
             →∙ EM∙ L (suc (suc (suc (l + n + m)))) ∙)))
    lem =
      subst (isOfHLevel (2 + l))
        (λ i → EM∙ G (suc n)
             →∙ →∙EMPath {G = L} (EM-raw'∙ H (suc m)) (suc (suc (l + n + m))) (~ i))
        (isOfHLevel↑∙∙' n m l)

  isOfHLevel↑∙∙'' : {G : AbGroup ℓ} {H : AbGroup ℓ'} {L : AbGroup ℓ''}
     → ∀ n m l → isOfHLevel (2 + l) (EM-raw'∙ G (suc n)
                                  →∙ (EM-raw'∙ H (suc m)
                                   →∙ EM∙ L (suc (suc (l + n + m))) ∙))
  isOfHLevel↑∙∙'' {G = G} {H = H} {L = L} n m zero =
    isOfHLevelΩ→isOfHLevel 0
      λ f → subst
          isProp (cong (λ x → typ (Ω x))
          (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)) f))
          (isOfHLevelRetractFromIso 1 (ΩfunExtIso _ _)
          lem)
    where
    lem : isProp (EM-raw'∙ G (suc n)
             →∙ (Ω (EM-raw'∙ H (suc m)
              →∙ EM∙ L (suc (suc (n + m))) ∙)))
    lem = subst isProp
        (λ i → EM-raw'∙ G (suc n)
            →∙ (→∙EMPath {G = L} (EM-raw'∙ H (suc m)) (suc (n + m)) (~ i)))
        (isContr→isProp (contr∙-lem'' _ _))
  isOfHLevel↑∙∙'' {G = G} {H = H} {L = L} n m (suc l) =
    isOfHLevelΩ→isOfHLevel (suc l)
      λ f →
      subst (isOfHLevel (2 + l))
          (cong (λ x → typ (Ω x))
          (isHomogeneous→∙ (isHomogeneous→∙ (isHomogeneousEM _)) f))
          (isOfHLevelRetractFromIso (2 + l) (ΩfunExtIso _ _) lem)
    where
    lem : isOfHLevel (2 + l)
         (EM-raw'∙ G (suc n)
           →∙ (Ω (EM-raw'∙ H (suc m)
             →∙ EM∙ L (suc (suc (suc (l + n + m)))) ∙)))
    lem =
      subst (isOfHLevel (2 + l))
        (λ i → EM-raw'∙ G (suc n)
             →∙ →∙EMPath {G = L} (EM-raw'∙ H (suc m)) (suc (suc (l + n + m))) (~ i))
        (isOfHLevel↑∙∙'' n m l)

-- A homomorphism φ : G → H of AbGroups induces a homomorphism
-- φ' : K(G,n) → K(H,n)
inducedFun-EM-raw : {G' : AbGroup ℓ} {H' : AbGroup ℓ'}
                     → AbGroupHom G' H'
                     → ∀ n
                     → EM-raw G' n → EM-raw H' n
inducedFun-EM-raw f =
  elim+2 (fst f)
    (EMrec _ emsquash embase
     (λ g → emloop (fst f g))
      λ g h → compPathR→PathP (sym
                (sym (lUnit _)
              ∙∙ cong (_∙ (sym (emloop (fst f h))))
                      (cong emloop (IsGroupHom.pres· (snd f) g h)
                          ∙ emloop-comp _ (fst f g) (fst f h))
              ∙∙ sym (∙assoc _ _ _)
              ∙∙ cong (emloop (fst f g) ∙_) (rCancel _)
              ∙∙ sym (rUnit _))))
    (λ n ind → λ { north → north
                  ; south → south
                  ; (merid a i) → merid (ind a) i} )

inducedFun-EM-raw-id : {G' : AbGroup ℓ} (n : ℕ) (x : EM-raw G' n)
  → inducedFun-EM-raw (idGroupHom {G = AbGroup→Group G'}) n x ≡ x
inducedFun-EM-raw-id zero x = refl
inducedFun-EM-raw-id (suc zero) = EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
    λ { embase-raw → refl ; (emloop-raw g i) → refl}
inducedFun-EM-raw-id (suc (suc n)) north = refl
inducedFun-EM-raw-id (suc (suc n)) south = refl
inducedFun-EM-raw-id (suc (suc n)) (merid a i) j = merid (inducedFun-EM-raw-id (suc n) a j) i

inducedFun-EM-raw-comp : {G' : AbGroup ℓ} {H' : AbGroup ℓ'} {L' : AbGroup ℓ''}
  (ϕ : AbGroupHom G' H') (ψ : AbGroupHom H' L') (n : ℕ)
  → (x : EM-raw G' n) → inducedFun-EM-raw (compGroupHom ϕ ψ) n x
                       ≡ inducedFun-EM-raw ψ n (inducedFun-EM-raw ϕ n x)
inducedFun-EM-raw-comp ϕ ψ zero x = refl
inducedFun-EM-raw-comp ϕ ψ (suc zero) =
  EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
    λ { embase-raw → refl ; (emloop-raw g i) → refl}
inducedFun-EM-raw-comp ϕ ψ (suc (suc n)) north = refl
inducedFun-EM-raw-comp ϕ ψ (suc (suc n)) south = refl
inducedFun-EM-raw-comp ϕ ψ (suc (suc n)) (merid a i) j =
  merid (inducedFun-EM-raw-comp ϕ ψ (suc n) a j) i

inducedFun-EM : {G' : AbGroup ℓ} {H' : AbGroup ℓ'}
                     → AbGroupHom G' H'
                     → ∀ n
                     → EM G' n → EM H' n
inducedFun-EM f zero = inducedFun-EM-raw f zero
inducedFun-EM f (suc zero) = inducedFun-EM-raw f (suc zero)
inducedFun-EM f (suc (suc n)) = Trunc.map (inducedFun-EM-raw f (2 + n))

EM-raw→EM-funct : {G : AbGroup ℓ} {H : AbGroup ℓ'}
     (n : ℕ) (ψ : AbGroupHom G H) (y : EM-raw G n)
  → EM-raw→EM _ _ (inducedFun-EM-raw ψ n y)
   ≡ inducedFun-EM ψ n (EM-raw→EM _ _ y)
EM-raw→EM-funct zero ψ y = refl
EM-raw→EM-funct (suc zero) ψ y = refl
EM-raw→EM-funct (suc (suc n)) ψ y = refl

inducedFun-EM-id : {G' : AbGroup ℓ} (n : ℕ) (x : EM G' n)
  → inducedFun-EM (idGroupHom {G = AbGroup→Group G'}) n x ≡ x
inducedFun-EM-id zero x = refl
inducedFun-EM-id (suc zero) = inducedFun-EM-raw-id (suc zero)
inducedFun-EM-id (suc (suc n)) =
  Trunc.elim (λ _ → isOfHLevelPath (4 + n) (hLevelEM _ (suc (suc n))) _ _)
    λ x → cong ∣_∣ₕ (inducedFun-EM-raw-id _ x)

inducedFun-EM-comp : {G' : AbGroup ℓ} {H' : AbGroup ℓ'} {L' : AbGroup ℓ''}
  (ϕ : AbGroupHom G' H') (ψ : AbGroupHom H' L') (n : ℕ)
  → (x : EM G' n) → inducedFun-EM (compGroupHom ϕ ψ) n x
                       ≡ inducedFun-EM ψ n (inducedFun-EM ϕ n x)
inducedFun-EM-comp ϕ ψ zero x = refl
inducedFun-EM-comp ϕ ψ (suc zero) = inducedFun-EM-raw-comp ϕ ψ (suc zero)
inducedFun-EM-comp ϕ ψ (suc (suc n)) =
  Trunc.elim (λ _ → isOfHLevelPath (4 + n) (hLevelEM _ (suc (suc n))) _ _)
    λ x → cong ∣_∣ₕ (inducedFun-EM-raw-comp ϕ ψ (suc (suc n)) x)

inducedFun-EM0ₖ : {G' : AbGroup ℓ} {H' : AbGroup ℓ'} {ϕ : AbGroupHom G' H'} (n : ℕ)
  → inducedFun-EM ϕ n (0ₖ n) ≡ 0ₖ n
inducedFun-EM0ₖ {ϕ = ϕ} zero = IsGroupHom.pres1 (snd ϕ)
inducedFun-EM0ₖ (suc zero) = refl
inducedFun-EM0ₖ (suc (suc n)) = refl

inducedFun-EM-pres+ₖ : {G' : AbGroup ℓ} {H' : AbGroup ℓ'}
     (ϕ : AbGroupHom G' H') (n : ℕ) (x y : EM G' n)
  → inducedFun-EM ϕ n (x +ₖ y) ≡ inducedFun-EM ϕ n x +ₖ inducedFun-EM ϕ n y
inducedFun-EM-pres+ₖ ϕ zero x y = IsGroupHom.pres· (snd ϕ) x y
inducedFun-EM-pres+ₖ {G' = G'} {H' = H'} ϕ (suc n) =
  EM-elim2 (suc n) (λ _ _ → isOfHLevelPath (2 + suc n) (hLevelEM _ (suc n)) _ _)
    (wedgeConEM.fun _ _ n n
      (λ _ _ → isOfHLevelPath' (suc n + suc n)
                 (subst (λ m → isOfHLevel (suc (suc m)) (EM H' (suc n)))
                   (sym (+-suc n n))
                   (isOfHLevelPlus' {n = n} (3 + n)
                     (hLevelEM _ (suc n))))
                 _ _)
      (l n)
      (r n)
      (l≡r n))
  where
  lem : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) → EM-raw→EM G (suc n) ptEM-raw ≡ 0ₖ _
  lem zero = refl
  lem (suc n) = refl

  l : (n : ℕ) (y : EM-raw G' (suc n))
    → inducedFun-EM ϕ (suc n) ((EM-raw→EM G' (suc n) ptEM-raw)
                               +ₖ EM-raw→EM G' (suc n) y)
     ≡ inducedFun-EM ϕ (suc n) (EM-raw→EM G' (suc n) ptEM-raw)
     +ₖ inducedFun-EM ϕ (suc n) (EM-raw→EM G' (suc n) y)
  l n y = (cong (inducedFun-EM ϕ (suc n))
                (cong (_+ₖ EM-raw→EM G' (suc n) y) (lem n)
               ∙ lUnitₖ (suc n) (EM-raw→EM G' (suc n) y)))
        ∙∙ sym (lUnitₖ _ (inducedFun-EM ϕ (suc n) (EM-raw→EM G' (suc n) y)))
        ∙∙ cong (_+ₖ (inducedFun-EM ϕ (suc n) (EM-raw→EM G' (suc n) y)))
                (sym (inducedFun-EM0ₖ {ϕ = ϕ} (suc n))
               ∙ cong (inducedFun-EM ϕ (suc n)) (sym (lem n)))

  r : (n : ℕ) (x : EM-raw G' (suc n))
      → inducedFun-EM ϕ (suc n)
          (EM-raw→EM G' (suc n) x +ₖ EM-raw→EM G' (suc n) ptEM-raw)
       ≡ inducedFun-EM ϕ (suc n) (EM-raw→EM G' (suc n) x)
       +ₖ inducedFun-EM ϕ (suc n) (EM-raw→EM G' (suc n) ptEM-raw)
  r n x = cong (inducedFun-EM ϕ (suc n))
             (cong (EM-raw→EM G' (suc n) x +ₖ_) (lem n)
            ∙ rUnitₖ (suc n) (EM-raw→EM G' (suc n) x))
        ∙∙ sym (rUnitₖ _ (inducedFun-EM ϕ (suc n) (EM-raw→EM G' (suc n) x)))
        ∙∙ cong (inducedFun-EM ϕ (suc n) (EM-raw→EM G' (suc n) x) +ₖ_)
             (sym (inducedFun-EM0ₖ {ϕ = ϕ} (suc n))
            ∙ cong (inducedFun-EM ϕ (suc n)) (sym (lem n)))

  l≡r : (n : ℕ) → l n ptEM-raw ≡ r n ptEM-raw
  l≡r zero = refl
  l≡r (suc n) = refl

inducedFun-EM-pres-ₖ : {G' : AbGroup ℓ} {H' : AbGroup ℓ'}
     (ϕ : AbGroupHom G' H') (n : ℕ) (x : EM G' n)
  → inducedFun-EM ϕ n (-ₖ x) ≡ -ₖ (inducedFun-EM ϕ n x)
inducedFun-EM-pres-ₖ ϕ n =
  morphLemmas.distrMinus _+ₖ_ _+ₖ_
    (inducedFun-EM ϕ n) (inducedFun-EM-pres+ₖ ϕ n) (0ₖ n) (0ₖ n) (-ₖ_) (-ₖ_)
    (lUnitₖ n) (rUnitₖ n)
    (lCancelₖ n) (rCancelₖ n)
    (assocₖ n) (inducedFun-EM0ₖ n)

EMFun-EM→ΩEM+1 : {G : AbGroup ℓ} {H : AbGroup ℓ'}
    {ϕ : AbGroupHom G H} (n : ℕ) (x : EM G n)
  → PathP (λ i → inducedFun-EM0ₖ {ϕ = ϕ} (suc n) (~ i)
                 ≡ inducedFun-EM0ₖ {ϕ = ϕ} (suc n) (~ i))
           (EM→ΩEM+1 n (inducedFun-EM ϕ n x))
           (cong (inducedFun-EM ϕ (suc n)) (EM→ΩEM+1 n x))
EMFun-EM→ΩEM+1 {ϕ = ϕ} zero x = refl
EMFun-EM→ΩEM+1 {ϕ = ϕ} (suc zero) x =
     cong-∙ ∣_∣ₕ (merid (inducedFun-EM ϕ (suc zero) x))
                (sym (merid embase))
  ∙∙ sym (cong-∙ (inducedFun-EM ϕ (suc (suc zero)))
         (cong ∣_∣ₕ (merid x)) (cong ∣_∣ₕ (sym (merid embase))))
  ∙∙ cong (cong (inducedFun-EM ϕ (suc (suc zero))))
          (sym (cong-∙ ∣_∣ₕ (merid x) (sym (merid embase))))
EMFun-EM→ΩEM+1 {ϕ = ϕ} (suc (suc n)) =
  Trunc.elim (λ _ → isOfHLevelPath (4 + n)
                (isOfHLevelTrunc (5 + n) _ _) _ _)
    λ a → cong-∙ ∣_∣ₕ (merid (inducedFun-EM-raw ϕ (2 + n) a))
                      (sym (merid north))
        ∙∙ sym (cong-∙ (inducedFun-EM ϕ (suc (suc (suc n))))
               (cong ∣_∣ₕ (merid a)) (cong ∣_∣ₕ (sym (merid north))))
        ∙∙ cong (cong (inducedFun-EM ϕ (suc (suc (suc n)))))
               (sym (cong-∙ ∣_∣ₕ (merid a) (sym (merid north))))


inducedFun-EM-rawIso : {G' : AbGroup ℓ} {H' : AbGroup ℓ'}
                     → AbGroupEquiv G' H'
                     → ∀ n → Iso (EM-raw G' n) (EM-raw H' n)
Iso.fun (inducedFun-EM-rawIso e n) = inducedFun-EM-raw (_ , (snd e)) n
Iso.inv (inducedFun-EM-rawIso e n) = inducedFun-EM-raw (_ , isGroupHomInv e) n
Iso.rightInv (inducedFun-EM-rawIso e n) = h n
  where
  h : (n : ℕ) → section (inducedFun-EM-raw (fst e .fst , snd e) n)
      (inducedFun-EM-raw (invEq (fst e) , isGroupHomInv e) n)
  h = elim+2
    (secEq (fst e))
    (elimSet _ (λ _ → emsquash _ _) refl
                       (λ g → compPathR→PathP
                          (sym (cong₂ _∙_ (cong emloop (secEq (fst e) g))
                                (sym (lUnit _))
                               ∙ rCancel _))))
    λ n p → λ { north → refl
               ; south → refl
               ; (merid a i) k → merid (p a k) i}
Iso.leftInv (inducedFun-EM-rawIso e n) = h n
  where
  h : (n : ℕ) → retract (Iso.fun (inducedFun-EM-rawIso e n))
                          (Iso.inv (inducedFun-EM-rawIso e n))
  h = elim+2
    (retEq (fst e))
    (elimSet _ (λ _ → emsquash _ _) refl
                       (λ g → compPathR→PathP
                          ((sym (cong₂ _∙_ (cong emloop (retEq (fst e) g)) (sym (lUnit _))
                               ∙ rCancel _)))))
    λ n p → λ { north → refl
               ; south → refl
               ; (merid a i) k → merid (p a k) i}

module _ {G : AbGroup ℓ} {H : AbGroup ℓ'} (e : AbGroupEquiv G H) where
  Iso→EMIso : ∀ n → Iso (EM G n) (EM H n)
  Iso.fun (Iso→EMIso n) = inducedFun-EM (GroupEquiv→GroupHom e) n
  Iso.inv (Iso→EMIso n) = inducedFun-EM (GroupEquiv→GroupHom (invGroupEquiv e)) n
  Iso.rightInv (Iso→EMIso zero) = Iso.rightInv (inducedFun-EM-rawIso e zero)
  Iso.rightInv (Iso→EMIso (suc zero)) =
    Iso.rightInv (inducedFun-EM-rawIso e (suc zero))
  Iso.rightInv (Iso→EMIso (suc (suc n))) =
    Iso.rightInv (mapCompIso (inducedFun-EM-rawIso e (suc (suc n))))
  Iso.leftInv (Iso→EMIso zero) =
    Iso.leftInv (inducedFun-EM-rawIso e zero)
  Iso.leftInv (Iso→EMIso (suc zero)) =
    Iso.leftInv (inducedFun-EM-rawIso e (suc zero))
  Iso.leftInv (Iso→EMIso (suc (suc n))) =
    Iso.leftInv (mapCompIso (inducedFun-EM-rawIso e (suc (suc n))))

  Iso→EMIso∙ : ∀ n → Iso.fun (Iso→EMIso n) (EM∙ G n .snd) ≡ EM∙ H n .snd
  Iso→EMIso∙ zero = IsGroupHom.pres1 (e .snd)
  Iso→EMIso∙ (suc zero) = refl
  Iso→EMIso∙ (suc (suc n)) = refl

  Iso→EMIso⁻∙ : ∀ n → Iso.inv (Iso→EMIso n) (EM∙ H n .snd) ≡ EM∙ G n .snd
  Iso→EMIso⁻∙ zero = IsGroupHom.pres1 (invGroupEquiv e .snd)
  Iso→EMIso⁻∙ (suc zero) = refl
  Iso→EMIso⁻∙ (suc (suc n)) = refl

Iso→EMIsoInv : {G : AbGroup ℓ} {H : AbGroup ℓ'} (e : AbGroupEquiv G H)
  → ∀ n → Iso.inv (Iso→EMIso e n) ≡ Iso.fun (Iso→EMIso (invGroupEquiv e) n)
Iso→EMIsoInv e zero = refl
Iso→EMIsoInv e (suc zero) = refl
Iso→EMIsoInv e (suc (suc n)) = refl

EM⊗-commIso : {G : AbGroup ℓ} {H : AbGroup ℓ'}
  → ∀ n →  Iso (EM (G ⨂ H) n) (EM (H ⨂ G) n)
EM⊗-commIso {G = G} {H = H} = Iso→EMIso (GroupIso→GroupEquiv ⨂-commIso)

EM⊗-assocIso : {G : AbGroup ℓ} {H : AbGroup ℓ'} {L : AbGroup ℓ''}
  → ∀ n → Iso (EM (G ⨂ (H ⨂ L)) n) (EM ((G ⨂ H) ⨂ L) n)
EM⊗-assocIso = Iso→EMIso (GroupIso→GroupEquiv (GroupEquiv→GroupIso ⨂assoc))
