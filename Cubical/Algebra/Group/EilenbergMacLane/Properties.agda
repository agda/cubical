{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Algebra.Group.EilenbergMacLane.Properties where

open import Cubical.Algebra.Group.EilenbergMacLane.Base renaming (elim to EM-elim)
open import Cubical.Algebra.Group.EilenbergMacLane.WedgeConnectivity
open import Cubical.Algebra.Group.EilenbergMacLane.GroupStructure
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
  renaming (rec to trRec; elim to trElim)
open import Cubical.HITs.EilenbergMacLane1 renaming (rec to EMrec)
open import Cubical.HITs.Truncation
  renaming (elim to trElim ; rec to trRec ; rec2 to trRec2)
open import Cubical.HITs.Susp

private
  variable ℓ ℓ' ℓ'' : Level

isConnectedEM₁ : (G : Group ℓ) → isConnected 2 (EM₁ G)
isConnectedEM₁ G = ∣ embase ∣ , h
    where
      h : (y : hLevelTrunc 2 (EM₁ G)) → ∣ embase ∣ ≡ y
      h = trElim (λ y → isOfHLevelSuc 1 (isOfHLevelTrunc 2 ∣ embase ∣ y))
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
    trElim (λ _ → isOfHLevelTruncPath)
      (trElim (λ _ → isOfHLevelSuc (3 + n) (isOfHLevelTruncPath {n = (3 + n)}))
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
                                                      (rid 1g) ⟩
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
                                                      (invl g) ⟩
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
      (h · inv g) · g ≡⟨ (assoc h (inv g) g) ⁻¹ ⟩
        h · inv g · g ≡⟨ cong (h ·_) (invl g) ⟩
             h · 1g ≡⟨ rid h ⟩ h ∎
    isom .Iso.leftInv h =
      (h · g) · inv g ≡⟨ (assoc h g (inv g)) ⁻¹ ⟩
        h · g · inv g ≡⟨ cong (h ·_) (invr g) ⟩
             h · 1g ≡⟨ rid h ⟩ h ∎

  compRightEquiv : (g h : G)
    → compEquiv (rightEquiv g) (rightEquiv h) ≡ rightEquiv (g · h)
  compRightEquiv g h = equivEq (funExt (λ x → (assoc x g h) ⁻¹))

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
          1g · g ≡⟨ lid g ⟩
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
    renaming (_+_ to _+G_ ; -_ to -G_ ; assoc to assocG)

  CODE : (n : ℕ) → EM G (suc (suc n)) → TypeOfHLevel ℓ (3 + n)
  CODE n =
    trElim (λ _ → isOfHLevelTypeOfHLevel (3 + n))
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
    trElim (λ _ → isOfHLevelΠ (4 + n)
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
    trElim (λ _ → isOfHLevelTruncPath {n = 4 + n})
      λ x → cong (encode' (suc n) (0ₖ (3 + n))) (cong-∙ ∣_∣ₕ (merid x) (sym (merid north)))
    ∙∙ substComposite (λ x → CODE (suc n) x .fst)
         (cong ∣_∣ₕ (merid x)) (sym (cong ∣_∣ₕ (merid ptEM-raw))) (0ₖ (2 + n))
    ∙∙ cong (subst (λ x₁ → CODE (suc n) x₁ .fst) (λ i → ∣ merid ptEM-raw (~ i) ∣ₕ))
            (λ i → lUnitₖ (2 + n) (transportRefl ∣ x ∣ₕ i) i)
     ∙ (λ i → rUnitₖ (2 + n) (transportRefl ∣ x ∣ₕ i) i)

  Iso-EM-ΩEM+1 : (n : ℕ) → Iso (EM G n) (typ (Ω (EM∙ G (suc n))))
  Iso-EM-ΩEM+1 zero = invIso (ΩEM₁Iso (AbGroup→Group G))
  Iso.fun (Iso-EM-ΩEM+1 (suc zero)) = decode' 0 (0ₖ 2)
  Iso.inv (Iso-EM-ΩEM+1 (suc zero)) = encode' 0 (0ₖ 2)
  Iso.rightInv (Iso-EM-ΩEM+1 (suc zero)) = decode'-encode' 0 (0ₖ 2)
  Iso.leftInv (Iso-EM-ΩEM+1 (suc zero)) = encode'-decode' 0
  Iso.fun (Iso-EM-ΩEM+1 (suc (suc n))) = decode' (suc n) (0ₖ (3 + n))
  Iso.inv (Iso-EM-ΩEM+1 (suc (suc n))) = encode' (suc n) (0ₖ (3 + n))
  Iso.rightInv (Iso-EM-ΩEM+1 (suc (suc n))) = decode'-encode' (suc n) (0ₖ (3 + n))
  Iso.leftInv (Iso-EM-ΩEM+1 (suc (suc n))) = encode'-decode' (suc n)

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
    trElim {B = λ x → 0ₖ (suc n) ≡ fst f x}
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

  isOfHLevel↑∙' : {G : AbGroup ℓ} {H : AbGroup ℓ'}
            → ∀ n m → isOfHLevel (2 + n) (EM-raw∙ G (suc m) →∙ EM∙ H (suc (n + m)))
  isOfHLevel↑∙' zero m = isOfHLevel→∙EM m 0 (isContr→isProp (isContr-↓∙' m))
  isOfHLevel↑∙' (suc n) m = isOfHLevel→∙EM (suc (n + m)) (suc n) (isOfHLevel↑∙' n m)

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
        trElim (λ _ → isOfHLevelPath (4 + n)
               (subst (λ x → isOfHLevel x (EM∙ H (suc m) →∙ EM∙ L (suc ((suc n) + m))))
                      (λ i → suc (suc (+-comm (suc n) 1 i)))
                      (isOfHLevelPlus' {n = 1} (3 + n) (isOfHLevel↑∙ (suc n) m))) _ _)
          (raw-elim G (suc n)
            (λ _ → isOfHLevel↑∙ (suc n) m _ _) p)

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
                          ((sym (cong₂ _∙_ (cong emloop (secEq (fst e) g)) (sym (lUnit _))
                               ∙ rCancel _)))))
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

Iso→EMIso : {G : AbGroup ℓ} {H : AbGroup ℓ'}
  → AbGroupEquiv G H → ∀ n → Iso (EM G n) (EM H n)
Iso→EMIso is zero = inducedFun-EM-rawIso is zero
Iso→EMIso is (suc zero) = inducedFun-EM-rawIso is 1
Iso→EMIso is (suc (suc n)) = mapCompIso (inducedFun-EM-rawIso is (suc (suc n)))

EM⊗-commIso : {G : AbGroup ℓ} {H : AbGroup ℓ'}
  → ∀ n →  Iso (EM (G ⨂ H) n) (EM (H ⨂ G) n)
EM⊗-commIso {G = G} {H = H} = Iso→EMIso (GroupIso→GroupEquiv ⨂-commIso)

EM⊗-assocIso : {G : AbGroup ℓ} {H : AbGroup ℓ'} {L : AbGroup ℓ''}
  → ∀ n → Iso (EM (G ⨂ (H ⨂ L)) n) (EM ((G ⨂ H) ⨂ L) n)
EM⊗-assocIso = Iso→EMIso (GroupIso→GroupEquiv (GroupEquiv→GroupIso ⨂assoc))
