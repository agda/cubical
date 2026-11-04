{-
  Properties of Premetric Spaces ; Numbered lemmas are from
  Formalising real numbers in homotopy type theory, Gaëtan Gilbert, 2017
-}
module Cubical.Relation.Premetric.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ renaming (_≤_ to _≤ℕ_ ; _<_ to _<ℕ_)
open import Cubical.Data.Rationals as ℚ using ([_/_] ; eq/)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Positive as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Nat

open import Cubical.Relation.Premetric.Base

open JoinProperties ℕ≤Pseudolattice
open 1/2∈ℚ
open PositiveHalvesℚ

private
  variable
    ℓ ℓ' : Level

module PremetricTheory (M' : PremetricSpace ℓ ℓ') where
  private
    M = fst M'
  open PremetricStr (snd M')

  subst≈ : ∀ x y {ε δ} → ⟨ ε ⟩₊ ≡ ⟨ δ ⟩₊ → x ≈[ ε ] y → x ≈[ δ ] y
  subst≈ x y = subst (x ≈[_] y) ∘ ℚ₊≡

  subst≈L : ∀ {x y z ε} → x ≡ y → x ≈[ ε ] z → y ≈[ ε ] z
  subst≈L = subst (_≈[ _ ] _)

  subst≈R : ∀ {x y z ε} → y ≡ z → x ≈[ ε ] y → x ≈[ ε ] z
  subst≈R = subst (_ ≈[ _ ]_)

  isMonotone≈< : ∀ {x y ε δ} → ε <₊ δ → x ≈[ ε ] y → x ≈[ δ ] y
  isMonotone≈< {x} {y} {ε} {δ} ε<δ x≈y = subst≈ x y (minusPlus₊ δ ε) $
    isTriangular≈ x x y [ δ -₊ ε ]⟨ ε<δ ⟩ ε (isRefl≈ x [ δ -₊ ε ]⟨ ε<δ ⟩) x≈y

  isMonotone≈≤ : ∀ {x y ε δ} → ε ≤₊ δ → x ≈[ ε ] y → x ≈[ δ ] y
  isMonotone≈≤ {x} {y} {ε} {δ} ε≤δ x≈y with ⟨ ε ⟩₊ ℚ.≟ ⟨ δ ⟩₊
  ... | lt ε<δ = isMonotone≈< ε<δ x≈y
  ... | eq ε≡δ = subst≈ x y ε≡δ x≈y
  ... | gt δ<ε = ⊥.rec (ℚ.isIrrefl< ⟨ ε ⟩₊ (ℚ.isTrans≤< ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟨ ε ⟩₊ ε≤δ δ<ε))

  -- immediate consequence of isRounded≈, but with the gap as part of the data:
  isRounded≈Gap : ∀ {x y} ε → x ≈[ ε ] y
                → ∃[ (δ , Δ) ∈ ℚ₊ × ℚ₊ ] (⟨ δ +₊ Δ ⟩₊ ≡ ⟨ ε ⟩₊) × (x ≈[ δ ] y)
  isRounded≈Gap ε = PT.map isRounded≈GapΣ ∘ isRounded≈ _ _ _ where
    isRounded≈GapΣ : _ → Σ (ℚ₊ × ℚ₊) λ _ → _ × _
    isRounded≈GapΣ (δ , δ<ε , x≈[δ]y) .fst .fst = δ
    isRounded≈GapΣ (δ , δ<ε , x≈[δ]y) .fst .snd = [ ε -₊ δ ]⟨ δ<ε ⟩
    isRounded≈GapΣ (δ , δ<ε , x≈[δ]y) .snd .fst = ℚ.+Comm ⟨ δ ⟩₊ _ ∙ minusPlus₊ ε δ
    isRounded≈GapΣ (δ , δ<ε , x≈[δ]y) .snd .snd = x≈[δ]y

  module PremetricReasoning where

    private
      variable
        x y z w : M
        ε δ η θ κ : ℚ₊

      +≈ : x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε +₊ δ ] z
      +≈ = isTriangular≈ _ _ _ _ _

      data _≈_≈_[_:+_] (x y z : M) (δ η : ℚ₊) : Type (ℓ-max ℓ ℓ') where
        ≈step+ : x ≈[ δ ] y → y ≈[ η ] z → x ≈ y ≈ z [ δ :+ η ]
        ≈end   : x ≡ y      → y ≡ z      → x ≈ y ≈ z [ δ :+ η ]

      is≈Step+ : x ≈ y ≈ z [ δ :+ η ] → Type
      is≈Step+ (≈step+ _ _) = Unit
      is≈Step+ (≈end   _ _) = ⊥.⊥

      step+₊ : x ≈ y ≈ z [ δ :+ η ] → ℚ₊ → ℚ₊ → ℚ₊
      step+₊ (≈step+ _ _) = _+₊_
      step+₊ (≈end   _ _) = const

    infixr 2 step≈
    step≈ : ∀ x {w} ε {δ η}
          → (r : y ≈ z ≈ w [ δ :+ η ])
          → x ≈[ ε ] y
          → x ≈ z ≈ w [ step+₊ r ε δ :+ η ]
    step≈ x ε (≈step+ y≈ ≈w) x≈ = ≈step+ (+≈ x≈ y≈) ≈w
    step≈ x ε (≈end   y≡ ≡w) x≈ = ≈step+ (subst≈R y≡ x≈) (subst≈R ≡w (isRefl≈ _ _))

    syntax step≈ x ε y≈w x≈y = x ≈[ ε ]⟨ x≈y ⟩ y≈w

    infixr 2 step≈≡
    step≈≡ : ∀ x {w} ε {θ δ η}
           → ⟨ θ ⟩₊ ≡ ⟨ ε ⟩₊
           → (r : y ≈ z ≈ w [ δ :+ η ])
           → x ≈[ θ ] y
           → x ≈ z ≈ w [ step+₊ r ε δ :+ η ]
    step≈≡ x ε θ≡ε r = step≈ x ε r ∘ subst≈ x _ θ≡ε

    syntax step≈≡ x ε θ≡ε y≈w x≈y = x ≈≡[ ε ]⟨ θ≡ε ⟩⟨ x≈y ⟩ y≈w

    infixr 2 step≈<
    step≈< : ∀ x {w} ε {θ δ η}
           → θ <₊ ε
           → (r : y ≈ z ≈ w [ δ :+ η ])
           → x ≈[ θ ] y
           → x ≈ z ≈ w [ step+₊ r ε δ :+ η ]
    step≈< x ε θ<ε r = step≈ x ε r ∘ isMonotone≈< θ<ε

    syntax step≈< x ε θ<ε y≈w x≈y = x ≈<[ ε ]⟨ θ<ε ⟩⟨ x≈y ⟩ y≈w

    infixr 2 step≈≤
    step≈≤ : ∀ x {w} ε {θ δ η}
           → θ ≤₊ ε
           → (r : y ≈ z ≈ w [ δ :+ η ])
           → x ≈[ θ ] y
           → x ≈ z ≈ w [ step+₊ r ε δ :+ η ]
    step≈≤ x ε θ≤ε r = step≈ x ε r ∘ isMonotone≈≤ θ≤ε

    syntax step≈≤ x ε θ≤ε y≈w x≈y = x ≈≤[ ε ]⟨ θ≤ε ⟩⟨ x≈y ⟩ y≈w

    infix 3 ≈⁻_
    ≈⁻_ : x ≈[ ε ] y → y ≈[ ε ] x
    ≈⁻_ = isSym≈ _ _ _

    infixr 2 step≡→≈
    step≡→≈ : ∀ x {w} {δ η}
            → (r : y ≈ z ≈ w [ δ :+ η ])
            → x ≡ y
            → x ≈ z ≈ w [ δ :+ η ]
    step≡→≈ x (≈step+ y≈ ≈w) x≡ = ≈step+ (subst≈L (sym x≡) y≈) ≈w
    step≡→≈ x (≈end   y≡ ≡w) x≡ = ≈end (x≡ ∙ y≡) ≡w

    syntax step≡→≈ x y≈w x≡y = x ≡→≈⟨ x≡y ⟩ y≈w

    infix 3 _≈∎
    _≈∎ : ∀ x → x ≈ x ≈ x [ 1 :+ 1 ] -- these values will be discarded by step≈/begin≈
    _≈∎ x = ≈end refl refl

    infix 1 begin≈[_]⟨_⟩_
    begin≈[_]⟨_⟩_ : ∀ ε {δ} {x y} → ⟨ δ ⟩₊ ≡ ⟨ ε ⟩₊
                 → (r : x ≈ y ≈ y [ δ :+ 1 ])
                 → {is≈Step+ r}
                 → x ≈[ ε ] y
    begin≈[ ε ]⟨ p ⟩ ≈step+ x≈y _ = subst≈ _ _ p x≈y

    infix 1 begin≈[_]⟨⟩_
    begin≈[_]⟨⟩_ : ∀ ε {x y}
                → (r : x ≈ y ≈ y [ ε :+ 1 ])
                → {is≈Step+ r}
                → x ≈[ ε ] y
    begin≈[ ε ]⟨⟩ ≈step+ x≈y _ = x≈y

  open PremetricReasoning

  -- Cauchy Approximations/Sequences

  isCauchy : (ℚ₊ → M) → Type ℓ'
  isCauchy x = ∀ (ε δ : ℚ₊) → x ε ≈[ ε +₊ δ ] x δ

  isPropIsCauchy : ∀ x → isProp (isCauchy x)
  isPropIsCauchy _ = isPropΠ2 λ _ _ → isProp≈ _ _ _

  isCauchySeqΣ : (ℕ → M) → Type ℓ'
  isCauchySeqΣ x = (ε : ℚ₊) → Σ[ N ∈ ℕ ] ∀ m n → N ≤ℕ m → N ≤ℕ n → x m ≈[ ε ] x n

  isCauchySeq : (ℕ → M) → Type ℓ'
  isCauchySeq x = (ε : ℚ₊) → ∃[ N ∈ ℕ ] ∀ m n → N ≤ℕ m → N ≤ℕ n → x m ≈[ ε ] x n

  isPropIsCauchySeq : ∀ x → isProp (isCauchySeq x)
  isPropIsCauchySeq _ = isPropΠ λ _ → squash₁

  isCauchySeqΣ→isCauchySeq : ∀ x → isCauchySeqΣ x → isCauchySeq x
  isCauchySeqΣ→isCauchySeq _ = ∣_∣₁ ∘_

  isCauchySeqΣ→isCauchy : ∀ x → isCauchySeqΣ x → Σ[ y ∈ (ℚ₊ → M) ] isCauchy y
  isCauchySeqΣ→isCauchy x icsΣ .fst = x ∘ fst ∘ icsΣ
  isCauchySeqΣ→isCauchy x icsΣ .snd = λ ε δ → let N = fst ∘ icsΣ in
    begin≈[ ε +₊ δ ]⟨⟩
    x (N ε)             ≈[ ε ]⟨ snd (icsΣ ε) _ _ (≤-refl) (L≤∨ {N ε}) ⟩
    x (max (N ε) (N δ)) ≈[ δ ]⟨ snd (icsΣ δ) _ _ (R≤∨ {N ε}) (≤-refl) ⟩
    x (N δ)             ≈∎

  -- Alternative formulation with "∀ N ≤ m < n" (useful for convergence of series)

  isCauchySeqΣ< : (ℕ → M) → Type ℓ'
  isCauchySeqΣ< x = (ε : ℚ₊) → Σ[ N ∈ ℕ ] ∀ m n → N ≤ℕ m → m <ℕ n → x m ≈[ ε ] x n

  isCauchySeq< : (ℕ → M) → Type ℓ'
  isCauchySeq< x = (ε : ℚ₊) → ∃[ N ∈ ℕ ] ∀ m n → N ≤ℕ m → m <ℕ n → x m ≈[ ε ] x n

  isPropIsCauchySeq< : ∀ x → isProp (isCauchySeq< x)
  isPropIsCauchySeq< _ = isPropΠ λ _ → squash₁

  -- this formalizes "WLOG assume m < n"
  module SeqΣWLOG<
    (x : ℕ → M) (ε : ℚ₊) (cs< : Σ[ N ∈ ℕ ] ∀ m n → N ≤ℕ m → m <ℕ n → x m ≈[ ε ] x n) where

    go : Σ[ N ∈ ℕ ] ∀ m n → N ≤ℕ m → N ≤ℕ n → x m ≈[ ε ] x n
    go .fst = fst cs<
    go .snd m n N≤m N≤n with m ℕ.≟ n
    ... | lt m<n = snd cs< m n N≤m m<n
    ... | eq m≡n = subst ((x m ≈[ ε ]_) ∘ x) m≡n (isRefl≈ (x m) ε)
    ... | gt n<m = isSym≈ (x n) (x m) ε (snd cs< n m N≤n n<m)

  -- Conversions from/to isCauchy, isCauchySeq, isCauchySeqΣ

  isCauchySeqΣ<→isCauchySeq< : ∀ x → isCauchySeqΣ< x → isCauchySeq< x
  isCauchySeqΣ<→isCauchySeq< _ = ∣_∣₁ ∘_

  isCauchySeqΣ<→isCauchySeqΣ : ∀ x → isCauchySeqΣ< x → isCauchySeqΣ x
  isCauchySeqΣ<→isCauchySeqΣ x icsΣ< ε = SeqΣWLOG<.go x ε (icsΣ< ε)

  isCauchySeq<→isCauchySeq : ∀ x → isCauchySeq< x → isCauchySeq x
  isCauchySeq<→isCauchySeq x ics< ε = PT.map (SeqΣWLOG<.go x ε) (ics< ε)

  isCauchySeqΣ→isCauchySeqΣ< : ∀ x → isCauchySeqΣ x → isCauchySeqΣ< x
  isCauchySeqΣ→isCauchySeqΣ< x icsΣ ε .fst = fst (icsΣ ε)
  isCauchySeqΣ→isCauchySeqΣ< x icsΣ ε .snd = λ m n N≤m m<n →
    snd (icsΣ ε) m n N≤m $ ≤-trans N≤m (<-weaken m<n)

  isCauchySeqΣ→isCauchySeq< : ∀ x → isCauchySeqΣ x → isCauchySeq< x
  isCauchySeqΣ→isCauchySeq< = ((∣_∣₁ ∘_) ∘_) ∘ isCauchySeqΣ→isCauchySeqΣ<

  isCauchySeq→isCauchySeq< : ∀ x → isCauchySeq x → isCauchySeq< x
  isCauchySeq→isCauchySeq< x ics ε = PT.map
    (λ (N , cs) → N , λ m n N≤m m<n → cs m n N≤m $ ≤-trans N≤m (<-weaken m<n))
    (ics ε)

  isCauchySeqΣ<→isCauchy : ∀ x → isCauchySeqΣ< x → Σ[ y ∈ (ℚ₊ → M) ] isCauchy y
  isCauchySeqΣ<→isCauchy x = isCauchySeqΣ→isCauchy x ∘ isCauchySeqΣ<→isCauchySeqΣ x

  -- Limits

  isLimit : (ℚ₊ → M) → M → Type ℓ'
  isLimit x l = ∀ ε θ → x ε ≈[ ε +₊ θ ] l

  isPropIsLimit : ∀ x l → isProp (isLimit x l)
  isPropIsLimit x l = isPropΠ2 λ ε δ → isProp≈ (x ε) l (ε +₊ δ)

  limit : (ℚ₊ → M) → Type (ℓ-max ℓ ℓ')
  limit x = Σ[ l ∈ M ] isLimit x l

  isPropLimit : ∀ x → isProp (limit x)
  isPropLimit x (l , l-lim) (l' , l'-lim) = Σ≡Prop (isPropIsLimit x) $
    isSeparated≈ l l' λ ε → begin≈[ ε ]⟨ /2+/2≡id ⟨ ε ⟩₊ ⟩
      l         ≈≡[ ε /2₊ ]⟨ /4+/4≡/2 ⟨ ε ⟩₊ ⟩⟨ ≈⁻ l-lim (ε /4₊) (ε /4₊) ⟩
      x (ε /4₊) ≈≡[ ε /2₊ ]⟨ /4+/4≡/2 ⟨ ε ⟩₊ ⟩⟨   l'-lim (ε /4₊) (ε /4₊) ⟩
      l'        ≈∎

  isLimitSeq : (ℕ → M) → M → Type ℓ'
  isLimitSeq x l = ∀ ε → ∃[ N ∈ ℕ ] (∀ n → N ≤ℕ n → x n ≈[ ε ] l)

  isPropIsLimitSeq : ∀ x l → isProp (isLimitSeq x l)
  isPropIsLimitSeq x l = isPropΠ λ _ → squash₁

  limitSeq : (ℕ → M) → Type (ℓ-max ℓ ℓ')
  limitSeq x = Σ[ l ∈ M ] isLimitSeq x l

  isPropLimitSeq : ∀ x → isProp (limitSeq x)
  isPropLimitSeq x (l , l-lim) (l' , l'-lim) = Σ≡Prop (isPropIsLimitSeq x) $
    isSeparated≈ l l' λ ε → proof _ , isProp≈ l l' ε by do
      N , N≤→≈ ← l-lim  (ε /2₊)
      M , M≤→≈ ← l'-lim (ε /2₊)
      return (begin≈[ ε ]⟨ /2+/2≡id ⟨ ε ⟩₊ ⟩
        l           ≈[ ε /2₊ ]⟨ ≈⁻ N≤→≈ _ L≤∨ ⟩
        x (max N M) ≈[ ε /2₊ ]⟨ M≤→≈ _ (R≤∨ {N}) ⟩
        l'          ≈∎)

  isLimit≈< : ∀ x l → isLimit x l → ∀ ε δ → (ε <₊ δ) → x ε ≈[ δ ] l
  isLimit≈< x l l-lim ε δ ε<δ = begin≈[ δ ]⟨ ℚ.+Comm ⟨ ε ⟩₊ (δ -₊ ε) ∙ minusPlus₊ δ ε ⟩
    x ε ≈[ ε +₊ [ δ -₊ ε ]⟨ ε<δ ⟩ ]⟨ l-lim ε [ δ -₊ ε ]⟨ ε<δ ⟩ ⟩
    l   ≈∎

  -- Lemma 2.8
  isLim≈+ : ∀ u x l ε δ → isLimit x l → u ≈[ δ ] x ε → u ≈[ ε +₊ δ ] l
  isLim≈+ u x l ε δ l-lim = PT.rec (isProp≈ u l _)
    (λ (η , η<δ , u≈xε) →
    begin≈[ ε +₊ δ ]⟨
      ℚ.+Comm ⟨ η ⟩₊ _ ∙
      sym (ℚ.+Assoc ⟨ ε ⟩₊ (δ -₊ η) ⟨ η ⟩₊) ∙
      cong (⟨ ε ⟩₊ ℚ.+_) (minusPlus₊ δ η) ⟩
      u    ≈[ η ]⟨ u≈xε ⟩
      x ε  ≈[ ε +₊ [ δ -₊ η ]⟨ η<δ ⟩ ]⟨ l-lim ε [ δ -₊ η ]⟨ η<δ ⟩ ⟩
      l    ≈∎)
    ∘ isRounded≈ u (x ε) δ

  isLim≈- : ∀ u x l ε δ Δ → isLimit x l → u ≈[ ε -₊ δ , Δ ] x δ → u ≈[ ε ] l
  isLim≈- u x l ε δ Δ l-lim =
    subst≈ u l (ℚ.+Comm ⟨ δ ⟩₊ _ ∙ minusPlus₊ ε δ) ∘ isLim≈+ u x l δ (ε -₊ δ , Δ) l-lim

  -- Lemma 2.9
  isLim≈+₂ : ∀ x y l l' ε δ η → isLimit x l → isLimit y l'
           → x δ ≈[ ε ] y η → l ≈[ δ +₊ (η +₊ ε) ] l'
  isLim≈+₂ x y l l' ε δ η l-lim l'-lim =
      isSym≈ l' l (δ +₊ (η +₊ ε))
    ∘ isLim≈+ l' x l δ (η +₊ ε) l-lim
    ∘ isSym≈ (x δ) l' (η +₊ ε)
    ∘ isLim≈+ (x δ) y l' η ε l'-lim

  isLim≈-₂ : ∀ x y l l' ε δ η Δ → isLimit x l → isLimit y l'
           → x δ ≈[ ε -₊ (δ +₊ η) , Δ ] y η → l ≈[ ε ] l'
  isLim≈-₂ x y l l' ε δ η Δ l-lim l'-lim = subst≈ l l'
    (⟨ δ +₊ (η +₊ (ε -₊ (δ +₊ η) , Δ)) ⟩₊ ≡⟨ ℚ.+Assoc ⟨ δ ⟩₊ ⟨ η ⟩₊ _ ⟩
    ⟨ δ +₊ η ⟩₊ ℚ.+ (ε -₊ (δ +₊ η))       ≡⟨ ℚ.+Comm ⟨ δ +₊ η ⟩₊ _ ⟩
    (ε -₊ (δ +₊ η)) ℚ.+ ⟨ δ +₊ η ⟩₊       ≡⟨ minusPlus₊ ε (δ +₊ η) ⟩
    ⟨ ε ⟩₊                                ∎)
    ∘ isLim≈+₂ x y l l' (ε -₊ (δ +₊ η) , Δ) δ η l-lim l'-lim

  limit→limitSeq : ∀ x xcsΣ → limit (fst (isCauchySeqΣ→isCauchy x xcsΣ)) → limitSeq x
  limit→limitSeq x xcsΣ (l , l-lim) .fst   = l
  limit→limitSeq x xcsΣ (l , l-lim) .snd ε =
    let N , N≤→≈ = xcsΣ (ε /2₊) ; y , yc = isCauchySeqΣ→isCauchy x xcsΣ
    in return
      ( N
      , λ n N≤n → subst≈ _ _ (/2+/2≡id ⟨ ε ⟩₊) (
        isLim≈+ (x n) y l (ε /2₊) (ε /2₊) l-lim (N≤→≈ n N N≤n ≤-refl)))

  -- Completeness

  isComplete : Type (ℓ-max ℓ ℓ')
  isComplete = ∀ x → isCauchy x → limit x

  isSeqΣComplete : Type (ℓ-max ℓ ℓ')
  isSeqΣComplete = ∀ x → isCauchySeqΣ x → limitSeq x

  is∥SeqΣ∥₁Complete : Type (ℓ-max ℓ ℓ')
  is∥SeqΣ∥₁Complete = ∀ x → ∥ isCauchySeqΣ x ∥₁ → limitSeq x

  isSeqComplete : Type (ℓ-max ℓ ℓ')
  isSeqComplete = ∀ x → isCauchySeq x → limitSeq x

  isPropIsComplete : isProp isComplete
  isPropIsComplete = isPropΠ λ _ → isProp→ (isPropLimit _)

  isPropIsSeqΣComplete : isProp isSeqΣComplete
  isPropIsSeqΣComplete = isPropΠ λ _ → isProp→ (isPropLimitSeq _)

  isPropIs∥SeqΣ∥₁Complete : isProp is∥SeqΣ∥₁Complete
  isPropIs∥SeqΣ∥₁Complete = isPropΠ λ _ → isProp→ (isPropLimitSeq _)

  isPropIsSeqComplete : isProp isSeqComplete
  isPropIsSeqComplete = isPropΠ λ _ → isProp→ (isPropLimitSeq _)

  isSeqΣComplete→is∥SeqΣ∥₁Complete : isSeqΣComplete → is∥SeqΣ∥₁Complete
  isSeqΣComplete→is∥SeqΣ∥₁Complete is-com x = PT.rec (isPropLimitSeq x) (is-com x)

  is∥SeqΣ∥₁Complete→isSeqΣComplete : is∥SeqΣ∥₁Complete → isSeqΣComplete
  is∥SeqΣ∥₁Complete→isSeqΣComplete is-com x = (is-com x) ∘ ∣_∣₁

  isSeqΣComplete≃is∥SeqΣ∥₁Complete : isSeqΣComplete ≃ is∥SeqΣ∥₁Complete
  isSeqΣComplete≃is∥SeqΣ∥₁Complete =
    propBiimpl→Equiv isPropIsSeqΣComplete isPropIs∥SeqΣ∥₁Complete
    isSeqΣComplete→is∥SeqΣ∥₁Complete is∥SeqΣ∥₁Complete→isSeqΣComplete

  isSeqComplete→isSeqΣComplete : isSeqComplete → isSeqΣComplete
  isSeqComplete→isSeqΣComplete is-com x = is-com x ∘ isCauchySeqΣ→isCauchySeq x

  isSeqComplete→is∥SeqΣ∥₁Complete : isSeqComplete → is∥SeqΣ∥₁Complete
  isSeqComplete→is∥SeqΣ∥₁Complete =
    isSeqΣComplete→is∥SeqΣ∥₁Complete ∘ isSeqComplete→isSeqΣComplete

  isComplete→isSeqΣComplete : isComplete → isSeqΣComplete
  isComplete→isSeqΣComplete is-com x xcsΣ =
    limit→limitSeq x xcsΣ (uncurry is-com (isCauchySeqΣ→isCauchy x xcsΣ))

  -- with countable choice, we could also prove `is∥SeqΣ∥₁Complete→isSeqComplete`,
  -- as `isCauchySeq x`, would be equivalent to `∥ isCauchySeqΣ x ∥₁`;
  -- in particular, we could strengthen the result below to `isComplete→isSeqComplete`.
  isComplete→is∥SeqΣ∥₁Complete : isComplete → is∥SeqΣ∥₁Complete
  isComplete→is∥SeqΣ∥₁Complete =
    isSeqΣComplete→is∥SeqΣ∥₁Complete ∘ isComplete→isSeqΣComplete
