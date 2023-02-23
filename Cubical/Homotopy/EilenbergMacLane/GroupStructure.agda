{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Homotopy.EilenbergMacLane.GroupStructure where

open import Cubical.Homotopy.EilenbergMacLane.Base hiding (elim2)
open import Cubical.Homotopy.EilenbergMacLane.WedgeConnectivity
open import Cubical.Homotopy.Loopspace

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.AbGroup.Base

open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Path

open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.Truncation as TR
  renaming (elim to trElim ; rec to trRec ; rec2 to trRec2)
open import Cubical.HITs.Susp

open import Cubical.Functions.Morphism

private
  variable ℓ : Level

module _ {G : AbGroup ℓ} where
  infixr 34 _+ₖ_
  infixr 34 _-ₖ_
  open AbGroupStr (snd G) renaming (_+_ to _+G_ ; -_ to -G_ ; +Assoc to +AssocG)

  private
    help : (n : ℕ) → n + (4 + n) ≡ (2 + n) + (2 + n)
    help n = +-suc n (3 + n) ∙ cong suc (+-suc n (suc (suc n)))

    hLevHelp : (n : ℕ) → isOfHLevel ((2 + n) + (2 + n)) (EM G (2 + n))
    hLevHelp n =
      transport (λ i → isOfHLevel (help n i) (EM G (2 + n)))
            (isOfHLevelPlus {n = 4 + n} n (isOfHLevelTrunc (4 + n)))

    helper : (g h : fst G)
      → PathP (λ i → Path (EM₁ (AbGroup→Group G))
               (emloop h i) (emloop h i)) (emloop g) (emloop g)
    helper g h =
      compPath→Square
        ((sym (emloop-comp _ h g)
          ∙∙ cong emloop (+Comm h g)
          ∙∙ emloop-comp _ g h))

  _+ₖ_ : {n : ℕ} → EM G n → EM G n → EM G n
  _+ₖ_ {n = zero} = _+G_
  _+ₖ_ {n = suc zero} =
    rec _ (isGroupoidΠ (λ _ → emsquash))
      (λ x → x)
      (λ x → funExt (looper x))
      λ g h i j x → el g h x i j
    where
    looper : fst G → (x : _) → x ≡ x
    looper g = (elimSet _ (λ _ → emsquash _ _)
                     (emloop g)
                     (helper g))

    el : (g h : fst G) (x : EM₁ (AbGroup→Group G))
      → Square (looper g x)
                (looper (g +G h) x)
                refl (looper h x)
    el g h =
      elimProp _ (λ _ → isOfHLevelPathP' 1 (emsquash _ _) _ _)
        (emcomp g h)

  _+ₖ_ {n = suc (suc n)} =
    trRec2 (isOfHLevelTrunc (4 + n))
      (wedgeConEM.fun G G (suc n) (suc n)
        (λ _ _ → hLevHelp n)
        ∣_∣ ∣_∣ refl)

  σ-EM : (n : ℕ) → EM-raw G (suc n) → Path (EM-raw G (2 + n)) ptEM-raw ptEM-raw
  σ-EM n x = merid x ∙ sym (merid ptEM-raw)

  -ₖ_ : {n : ℕ} → EM G n → EM G n
  -ₖ_ {n = zero} x = -G x
  -ₖ_ {n = suc zero} =
    rec _ emsquash
      embase
      (λ g → sym (emloop g))
      λ g h → sym (emloop-sym _ g)
            ◁ (flipSquare
                (flipSquare (emcomp (-G g) (-G h))
               ▷ emloop-sym _ h)
            ▷ (cong emloop (+Comm (-G g) (-G h)
                          ∙ sym (GroupTheory.invDistr (AbGroup→Group G) g h))
             ∙ emloop-sym _ (g +G h)))
  -ₖ_ {n = suc (suc n)} =
    map λ { north → north
          ; south → north
          ; (merid a i) → σ-EM n a (~ i)}

  _-ₖ_ : {n : ℕ} → EM G n → EM G n → EM G n
  _-ₖ_ {n = n} x y = _+ₖ_ {n = n} x (-ₖ_ {n = n} y)

  +ₖ-syntax : (n : ℕ) →  EM G n → EM G n → EM G n
  +ₖ-syntax n = _+ₖ_ {n = n}

  -ₖ-syntax : (n : ℕ) → EM G n → EM G n
  -ₖ-syntax n = -ₖ_ {n = n}

  -'ₖ-syntax : (n : ℕ) → EM G n → EM G n → EM G n
  -'ₖ-syntax n = _-ₖ_ {n = n}

  syntax +ₖ-syntax n x y = x +[ n ]ₖ y
  syntax -ₖ-syntax n x = -[ n ]ₖ x
  syntax -'ₖ-syntax n x y = x -[ n ]ₖ y

  lUnitₖ : (n : ℕ) (x : EM G n) → 0ₖ n +[ n ]ₖ x ≡ x
  lUnitₖ zero x = +IdL x
  lUnitₖ (suc zero) _ = refl
  lUnitₖ (suc (suc n)) =
    trElim (λ _ → isOfHLevelTruncPath {n = 4 + n})
      λ _ → refl

  rUnitₖ : (n : ℕ) (x : EM G n) → x +[ n ]ₖ 0ₖ n ≡ x
  rUnitₖ zero x = +IdR x
  rUnitₖ (suc zero) =
    elimSet _ (λ _ → emsquash _ _)
            refl
            λ _ _ → refl
  rUnitₖ (suc (suc n)) =
    trElim (λ _ → isOfHLevelTruncPath {n = 4 + n})
      (wedgeConEM.right G G (suc n) (suc n)
      (λ _ _ → hLevHelp n)
      ∣_∣ ∣_∣ refl)

  commₖ : (n : ℕ) (x y : EM G n) → x +[ n ]ₖ y ≡ y +[ n ]ₖ x
  commₖ zero = +Comm
  commₖ (suc zero) =
    wedgeConEM.fun G G 0 0 (λ _ _ → emsquash _ _)
      (λ x → sym (rUnitₖ 1 x))
      (rUnitₖ 1)
      refl
  commₖ (suc (suc n)) =
    elim2 (λ _ _ → isOfHLevelTruncPath {n = 4 + n})
      (wedgeConEM.fun G G _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (hLevHelp n) _ _)
      (λ x → sym (rUnitₖ (2 + n) ∣ x ∣))
      (λ x → rUnitₖ (2 + n) ∣ x ∣)
      refl)

  cong₂+₁ : (p q : typ (Ω (EM∙ G 1)))
          → cong₂ (λ x y → x +[ 1 ]ₖ y) p q ≡ p ∙ q
  cong₂+₁ p q =
      (cong₂Funct (λ x y → x +[ 1 ]ₖ y) p q)
   ∙ (λ i → (cong (λ x → rUnitₖ 1 x i) p) ∙ (cong (λ x → lUnitₖ 1 x i) q))

  cong₂+₂ : (n : ℕ) (p q : typ (Ω (EM∙ G  (suc (suc n)))))
          → cong₂ (λ x y → x +[ (2 + n) ]ₖ y) p q ≡ p ∙ q
  cong₂+₂ n p q =
      (cong₂Funct (λ x y → x +[ (2 + n) ]ₖ y) p q)
   ∙ (λ i → (cong (λ x → rUnitₖ (2 + n) x i) p) ∙ (cong (λ x → lUnitₖ (2 + n) x i) q))

  isCommΩEM : (n : ℕ) (p q : typ (Ω (EM∙ G  (suc n)))) → p ∙ q ≡ q ∙ p
  isCommΩEM zero p q =
       sym (cong₂+₁ p q)
    ∙∙ (λ i j → commₖ 1 (p j) (q j) i)
    ∙∙ cong₂+₁ q p
  isCommΩEM (suc n) p q =
       (sym (cong₂+₂ n p q)
    ∙∙ (λ i j → commₖ (suc (suc n)) (p j) (q j) i)
    ∙∙ cong₂+₂ n q p)

  cong-₁ : (p : typ (Ω (EM∙ G 1))) → cong (λ x → -[ 1 ]ₖ x) p ≡ sym p
  cong-₁ p = main embase p
    where
    decoder : (x : EM G 1) → embase ≡ x → x ≡ embase
    decoder =
      elimSet _
        (λ _ → isSetΠ λ _ → emsquash _ _)
        (λ p i → -[ 1 ]ₖ (p i))
        λ g → toPathP
          (funExt λ x →
            (λ i → transport (λ i → Path (EM G 1) (emloop g i) embase)
               (cong (-ₖ_ {n = 1})
                 (transp (λ j → Path (EM G 1) embase (emloop g (~ j ∧ ~ i))) i
                   (compPath-filler x (sym (emloop g)) i) )))
         ∙∙ (λ i → transp (λ j → Path (EM G 1) (emloop g (i ∨ j)) embase) i
                           (compPath-filler'
                             (sym (emloop g))
                             (cong-∙ (-ₖ_ {n = 1})
                                   x (sym (emloop g)) i) i))
      ∙∙ (cong (sym (emloop g) ∙_) (isCommΩEM 0 (cong (-ₖ_ {n = 1}) x) (emloop g)))
      ∙∙ ∙assoc _ _ _
      ∙∙ cong (_∙ (cong (-ₖ_ {n = 1}) x)) (lCancel (emloop g))
       ∙ sym (lUnit _))

    main : (x : EM G 1) (p : embase ≡ x) → decoder x p ≡ sym p
    main x = J (λ x p → decoder x p ≡ sym p) refl

  cong-₂ : (n : ℕ) (p : typ (Ω (EM∙ G (2 + n))))
    → cong (λ x → -[ 2 + n ]ₖ x) p ≡ sym p
  cong-₂ n p = main _ p
    where
    pp : (a : _)
      → PathP (λ i → 0ₖ (suc (suc n)) ≡ ∣ merid a i ∣ₕ → ∣ merid a i ∣ₕ ≡ 0ₖ (2 + n))
               (cong (λ x → -[ 2 + n ]ₖ x))
               λ p → cong ∣_∣ₕ (sym (merid ptEM-raw)) ∙ cong (λ x → -[ 2 + n ]ₖ x) p
    pp a =
      toPathP
        (funExt λ x →
          (λ k → transp (λ i → Path (EM G (2 + n)) ∣ merid a (i ∨ k) ∣ ∣ ptEM-raw ∣) k
                         (compPath-filler' (cong ∣_∣ₕ (sym (merid a)))
                          (cong (-ₖ-syntax (suc (suc n)))
                           (transp (λ j → Path (EM G (2 + n)) ∣ ptEM-raw ∣ ∣ merid a (~ j ∧ ~ k) ∣) k
                            (compPath-filler x (sym (cong ∣_∣ₕ (merid a))) k))) k))
               ∙∙ cong (cong ∣_∣ₕ (sym (merid a)) ∙_)
                       (cong-∙ (λ x → -[ 2 + n ]ₖ x) x (sym (cong ∣_∣ₕ (merid a)))
                      ∙ isCommΩEM (suc n) (cong (λ x → -[ 2 + n ]ₖ x) x) (cong ∣_∣ₕ (σ-EM n a)))
               ∙∙ (λ k → (λ i → ∣ merid a (~ i ∨ k) ∣)
                        ∙ (λ i → ∣ compPath-filler' (merid a) (sym (merid ptEM-raw)) (~ k) i ∣)
                        ∙ cong (λ x → -ₖ-syntax (suc (suc n)) x) x)
                ∙ sym (lUnit _))

    decoder : (x : EM G (2 + n))
            → 0ₖ (2 + n) ≡ x → x ≡ 0ₖ (2 + n)
    decoder =
      trElim (λ _ → isOfHLevelΠ (4 + n) λ _ → isOfHLevelTruncPath {n = 4 + n})
             λ { north → pp ptEM-raw i0
               ; south → pp ptEM-raw i1
               ; (merid a i) → pp a i}

    main : (x : EM G (2 + n)) (p : 0ₖ (2 + n) ≡ x) → decoder x p ≡ sym p
    main x = J (λ x p → decoder x p ≡ sym p) refl

  rCancelₖ : (n : ℕ) (x : EM G n) → x +[ n ]ₖ (-[ n ]ₖ x) ≡ 0ₖ n
  rCancelₖ zero x = +InvR x
  rCancelₖ (suc zero) =
    elimSet _ (λ _ → emsquash _ _)
      refl
      λ g → flipSquare (cong₂+₁ (emloop g) (λ i → -ₖ-syntax 1 (emloop g i))
           ∙ rCancel (emloop g))
  rCancelₖ (suc (suc n)) =
    trElim (λ _ → isOfHLevelTruncPath {n = 4 + n})
      λ { north → refl
        ; south i → +ₖ-syntax (suc (suc n)) ∣ merid ptEM-raw (~ i) ∣
                      (-ₖ-syntax (suc (suc n)) ∣ merid ptEM-raw (~ i) ∣)
        ; (merid a i) j
          → hcomp (λ r → λ { (i = i0) → 0ₖ (2 + n)
                             ; (i = i1) → ∣ merid ptEM-raw (~ j ∧ r) ∣ₕ -[ 2 + n ]ₖ ∣ merid ptEM-raw (~ j ∧ r) ∣
                             ; (j = i0) → ∣ compPath-filler (merid a) (sym (merid ptEM-raw)) (~ r) i ∣
                                        -[ 2 + n ]ₖ ∣ compPath-filler (merid a) (sym (merid ptEM-raw)) (~ r) i ∣
                             ; (j = i1) → 0ₖ (2 + n)})
                   (help' a j i) }
    where
    help' : (a : _)
      → cong₂ (λ x y → ∣ x ∣ -[ suc (suc n) ]ₖ ∣ y ∣) (σ-EM n a) (σ-EM n a) ≡ refl
    help' a =
         cong₂+₂ n (cong ∣_∣ₕ (σ-EM n a)) (cong (λ x → -[ 2 + n ]ₖ ∣ x ∣) (σ-EM n a))
      ∙∙ cong (cong ∣_∣ₕ (σ-EM n a) ∙_) (cong-₂ n (cong ∣_∣ₕ (σ-EM n a)))
      ∙∙ rCancel _

  lCancelₖ : (n : ℕ) (x : EM G n) → (-[ n ]ₖ x) +[ n ]ₖ x ≡ 0ₖ n
  lCancelₖ n x = commₖ n (-[ n ]ₖ x) x ∙ rCancelₖ n x

  assocₖ : (n : ℕ) (x y z : EM G n)
        → (x +[ n ]ₖ (y +[ n ]ₖ z) ≡ (x +[ n ]ₖ y) +[ n ]ₖ z)
  assocₖ zero = +AssocG
  assocₖ (suc zero) =
    elimSet _ (λ _ → isSetΠ2 λ _ _ → emsquash _ _)
      (λ _ _ → refl)
      λ g i y z k → lem g y z k i
    where
    lem : (g : fst G) (y z : _)
        → cong (λ x → x +[ suc zero ]ₖ (y +[ suc zero ]ₖ z)) (emloop g)
         ≡ cong (λ x → (x +[ suc zero ]ₖ y) +[ suc zero ]ₖ z) (emloop g)
    lem g =
      elimProp _ (λ _ → isPropΠ λ _ → emsquash _ _ _ _)
        (elimProp _ (λ _ → emsquash _ _ _ _)
          refl)
  assocₖ (suc (suc n)) =
    elim2 (λ _ _ → isOfHLevelΠ (4 + n) λ _ → isOfHLevelTruncPath {n = 4 + n})
      λ a b → trElim (λ _ → isOfHLevelTruncPath {n = 4 + n})
                (λ c → main c a b)
    where
    lem : (c : _) (a b : _)
      → PathP (λ i → (∣ a ∣ₕ +[ suc (suc n) ]ₖ (∣ b ∣ₕ +[ suc (suc n) ]ₖ ∣ merid c i ∣ₕ)
                    ≡ (∣ a ∣ₕ +[ suc (suc n) ]ₖ ∣ b ∣ₕ) +[ suc (suc n) ]ₖ ∣ merid c i ∣ₕ))
               (cong (λ x → ∣ a ∣ₕ +[ suc (suc n) ]ₖ x) (rUnitₖ (suc (suc n)) ∣ b ∣)
                   ∙ sym (rUnitₖ (suc (suc n)) (∣ a ∣ₕ +[ suc (suc n) ]ₖ ∣ b ∣ₕ)))
               ((λ i → ∣ a ∣ₕ +[ suc (suc n) ]ₖ (∣ b ∣ₕ +[ suc (suc n) ]ₖ ∣ merid ptEM-raw (~ i) ∣ₕ))
             ∙∙ cong (λ x → ∣ a ∣ₕ +[ suc (suc n) ]ₖ x) (rUnitₖ (suc (suc n)) ∣ b ∣)
                 ∙ sym (rUnitₖ (suc (suc n)) (∣ a ∣ₕ +[ suc (suc n) ]ₖ ∣ b ∣ₕ))
             ∙∙ λ i → (∣ a ∣ₕ +[ suc (suc n) ]ₖ ∣ b ∣ₕ) +[ suc (suc n) ]ₖ ∣ merid ptEM-raw i ∣ₕ)
    lem c =
      raw-elim G (suc n)
        (λ _ → isOfHLevelΠ (2 + n)
          (λ _ → isOfHLevelPathP' (2 + n) (isOfHLevelTrunc (4 + n) _ _) _ _))
           (raw-elim G (suc n)
            (λ _ → isOfHLevelPathP' (2 + n) (isOfHLevelTrunc (4 + n) _ _) _ _)
             ((sym (rUnit refl)
             ◁ λ _ → refl)
             ▷ (sym (lCancel (cong ∣_∣ₕ (merid ptEM-raw)))
             ∙ λ i → (λ j → ∣ merid ptEM-raw (~ j ∨ ~ i) ∣ₕ)
                   ∙∙ lUnit (λ j → ∣ merid ptEM-raw (~ j ∧ ~ i) ∣ₕ) i
                   ∙∙ cong ∣_∣ₕ (merid ptEM-raw))))
    main : (c a b : _)
      → (∣ a ∣ₕ +[ suc (suc n) ]ₖ (∣ b ∣ₕ +[ suc (suc n) ]ₖ ∣ c ∣ₕ)
       ≡ (∣ a ∣ₕ +[ suc (suc n) ]ₖ ∣ b ∣ₕ) +[ suc (suc n) ]ₖ ∣ c ∣ₕ)
    main north a b = lem ptEM-raw a b i0
    main south a b = lem ptEM-raw a b i1
    main (merid c i) a b = lem c a b i

  σ-EM' : (n : ℕ) (x : EM G (suc n))
        → Path (EM G (suc (suc n)))
                (0ₖ (suc (suc n)))
                (0ₖ (suc (suc n)))
  σ-EM' zero x = cong ∣_∣ₕ (σ-EM zero x)
  σ-EM' (suc n) =
    trElim (λ _ → isOfHLevelTrunc (5 + n) _ _)
      λ x → cong ∣_∣ₕ (σ-EM (suc n) x)

  σ-EM'-0ₖ : (n : ℕ) → σ-EM' n (0ₖ (suc n)) ≡ refl
  σ-EM'-0ₖ zero = cong (cong ∣_∣ₕ) (rCancel (merid ptEM-raw))
  σ-EM'-0ₖ (suc n) = cong (cong ∣_∣ₕ) (rCancel (merid ptEM-raw))

  private
    lUnit-rUnit-coh : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (r : refl ≡ p)
        → lUnit p ∙ cong (_∙ p) r
         ≡ rUnit p ∙ cong (p ∙_) r
    lUnit-rUnit-coh p =
      J (λ p r → lUnit p ∙ cong (_∙ p) r ≡ rUnit p ∙ cong (p ∙_) r) refl

  σ-EM'-hom : (n : ℕ) → (a b : _) → σ-EM' n (a +ₖ b) ≡ σ-EM' n a ∙ σ-EM' n b
  σ-EM'-hom zero =
    wedgeConEM.fun G G 0 0 (λ _ _ → isOfHLevelTrunc 4 _ _ _ _) l r p
    where
    l : _
    l x = cong (σ-EM' zero) (lUnitₖ 1 x)
        ∙∙ lUnit (σ-EM' zero x)
        ∙∙ cong (_∙ σ-EM' zero x) (sym (σ-EM'-0ₖ zero))

    r : _
    r x =
         cong (σ-EM' zero) (rUnitₖ 1 x)
      ∙∙ rUnit (σ-EM' zero x)
      ∙∙ cong (σ-EM' zero x ∙_) (sym (σ-EM'-0ₖ zero))

    p : _
    p = lUnit-rUnit-coh (σ-EM' zero embase) (sym (σ-EM'-0ₖ zero))
  σ-EM'-hom (suc n) =
    elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
      (wedgeConEM.fun G G _ _
        (λ x y → transport (λ i → isOfHLevel (help n i)
                            ((σ-EM' (suc n) (∣ x ∣ₕ +ₖ ∣ y ∣ₕ)
                           ≡ σ-EM' (suc n) ∣ x ∣ₕ ∙ σ-EM' (suc n) ∣ y ∣ₕ)))
                    (isOfHLevelPlus {n = 4 + n} n
                      (isOfHLevelPath (4 + n)
                        (isOfHLevelTrunc (5 + n) _ _) _ _)))
        (λ x → cong (σ-EM' (suc n)) (lUnitₖ (suc (suc n)) ∣ x ∣)
            ∙∙ lUnit (σ-EM' (suc n) ∣ x ∣)
            ∙∙ cong (_∙ σ-EM' (suc n) ∣ x ∣) (sym (σ-EM'-0ₖ (suc n))))
        (λ x → cong (σ-EM' (suc n)) (rUnitₖ (2 + n) ∣ x ∣)
      ∙∙ rUnit (σ-EM' (suc n) ∣ x ∣)
      ∙∙ cong (σ-EM' (suc n) ∣ x ∣ ∙_) (sym (σ-EM'-0ₖ (suc n))))
        (lUnit-rUnit-coh (σ-EM' (suc n) (0ₖ (2 + n))) (sym (σ-EM'-0ₖ (suc n)))))

  σ-EM'-ₖ : (n : ℕ) → (a : _) → σ-EM' n (-ₖ a) ≡ sym (σ-EM' n a)
  σ-EM'-ₖ n =
    morphLemmas.distrMinus
      (λ x y → x +[ suc n ]ₖ y) (_∙_)
      (σ-EM' n) (σ-EM'-hom n)
      (0ₖ (suc n)) refl
      (λ x → -ₖ x) sym
      (λ x → sym (lUnit x)) (λ x → sym (rUnit x))
      (lCancelₖ (suc n)) rCancel
      ∙assoc (σ-EM'-0ₖ n)

  -Dist : (n : ℕ) (x y : EM G n) → -[ n ]ₖ (x +[ n ]ₖ y) ≡ (-[ n ]ₖ x) +[ n ]ₖ (-[ n ]ₖ y)
  -Dist zero x y = (GroupTheory.invDistr (AbGroup→Group G) x y) ∙ commₖ zero _ _
  -Dist (suc zero) = k
    where -- useless where clause. Needed for fast type checking for some reason.
    l : _
    l x = refl

    r : _
    r x = cong (λ z → -[ 1 ]ₖ z) (rUnitₖ 1 x) ∙ sym (rUnitₖ 1 (-[ 1 ]ₖ x))

    p : r ptEM-raw ≡ l ptEM-raw
    p = sym (rUnit refl)

    k = wedgeConEM.fun G G 0 0 (λ _ _ → emsquash _ _) l r (sym p)

  -Dist (suc (suc n)) =
    elim2 (λ _ _ → isOfHLevelTruncPath {n = 4 + n})
      (wedgeConEM.fun G G (suc n) (suc n)
        (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (hLevHelp n) _ _)
        (λ x → refl)
        (λ x → cong (λ z → -[ (suc (suc n)) ]ₖ z)
                     (rUnitₖ (suc (suc n)) ∣ x ∣ₕ)
                     ∙ sym (rUnitₖ (suc (suc n)) (-[ (suc (suc n)) ]ₖ ∣ x ∣ₕ)))
        (rUnit refl))

  addIso : (n : ℕ) (x : EM G n) → Iso (EM G n) (EM G n)
  Iso.fun (addIso n x) y = y +[ n ]ₖ x
  Iso.inv (addIso n x) y = y -[ n ]ₖ x
  Iso.rightInv (addIso n x) y =
       sym (assocₖ n y (-[ n ]ₖ x) x)
    ∙∙ cong (λ x → y +[ n ]ₖ x) (lCancelₖ n x)
    ∙∙ rUnitₖ n y
  Iso.leftInv (addIso n x) y =
    sym (assocₖ n y x (-[ n ]ₖ x))
    ∙∙ cong (λ x → y +[ n ]ₖ x) (rCancelₖ n x)
    ∙∙ rUnitₖ n y

-0ₖ : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) → -[ n ]ₖ (0ₖ {G = G} n) ≡ 0ₖ n
-0ₖ {G = G} zero = GroupTheory.inv1g (AbGroup→Group G)
-0ₖ (suc zero) = refl
-0ₖ (suc (suc n)) = refl

-ₖ² : ∀ {ℓ} {G : AbGroup ℓ} (k : ℕ) (x : EM G k) → (-ₖ (-ₖ x)) ≡ x
-ₖ² {G = G} zero x = GroupTheory.invInv (AbGroup→Group G) x
-ₖ² (suc zero) = EM-raw'-elim _ _ (λ _ → hLevelEM _ 1 _ _)
  λ { embase-raw → refl ; (emloop-raw g i) → refl}
-ₖ² {G = G} (suc (suc k)) =
  TR.elim (λ _ → isOfHLevelPath (4 + k) (isOfHLevelTrunc (4 + k)) _ _)
    λ { north → refl
      ; south → cong ∣_∣ₕ (merid ptEM-raw)
      ; (merid a i) → help a i}
    where
    help : (a : _)
      → PathP (λ i → Path (EM G (suc (suc k)))
                        (-ₖ (-ₖ ∣ merid a i ∣ₕ)) ∣ merid a i ∣ₕ)
               refl
               (cong ∣_∣ₕ (merid ptEM-raw))
    help a = flipSquare (
         cong (cong (-ₖ_ {n = suc (suc k)}))
         (cong (cong ∣_∣ₕ) (symDistr (merid a) (sym (merid ptEM-raw)))
       ∙ cong-∙ ∣_∣ₕ (merid (ptEM-raw)) (sym (merid a)))
       ∙ cong-∙ (-ₖ_ {n = suc (suc k)})
          (cong ∣_∣ₕ (merid ptEM-raw)) (sym (cong ∣_∣ₕ (merid a)))
       ∙ cong (_∙ cong (-ₖ_ {n = suc (suc k)})
                    (sym (cong ∣_∣ₕ (merid a))))
              (λ i j → ∣ rCancel (merid ptEM-raw) i (~ j) ∣ₕ)
       ∙ sym (lUnit _)
       ◁ λ i j → ∣ compPath-filler (merid a) (sym (merid ptEM-raw)) (~ i) j ∣ₕ)
