{-# OPTIONS --safe -W noUnsupportedIndexedMatch #-}

module Cubical.Data.Nat.Primes.Split where

open import Cubical.Data.Nat.Primes.Imports
open import Cubical.Data.Nat.Primes.Lemmas
open import Cubical.Data.Empty as ⊥ hiding (elim)


private
    variable
        ℓ ℓ' : Level

    decToN : {A : Type ℓ} → Dec A → ℕ
    decToN (yes _) = 1
    decToN (no  _) = 0

-- splitting naturals below a bound
-- into those for which a given decidable property holds
-- and those for which it does not
module _ (P : ℕ → Type ℓ) (Pdec : ∀ n → Dec (P n)) where

    goodSplit : ℕ → Type ℓ
    goodSplit n = Σ[ (goods , bads) ∈ List ℕ × List ℕ ]
                   (All P goods × All (λ n → ¬ (P n)) bads)
                 × (All (_< n) goods × All (_< n) bads)
                 × ((length goods) + (length bads) ≡ n)

    splitBelow-aux : (n : ℕ) → goodSplit n → Dec (P n) → goodSplit (suc n)
    splitBelow-aux n ((ws , ls) , (Pws , ¬Pls) , (ws<n , ls<n) , sum) (yes Pn) =
        (n ∷ ws , ls) ,
        (Pn ∷ Pws , ¬Pls) ,
        ((0 , refl) ∷ ws<sn , ls<sn) ,
        cong suc sum where
            ws<sn = mapAll (λ x<n → <-trans x<n (0 , refl)) ws<n
            ls<sn = mapAll (λ x<n → <-trans x<n (0 , refl)) ls<n
    splitBelow-aux n ((ws , ls) , (Pws , ¬Pls) , (ws<n , ls<n) , sum) (no ¬Pn) =
        (ws , n ∷ ls) ,
        (Pws , ¬Pn ∷ ¬Pls) ,
        (ws<sn , (0 , refl) ∷ ls<sn) ,
        +-suc _ _ ∙ cong suc sum where
            ws<sn = mapAll (λ x<n → <-trans x<n (0 , refl)) ws<n
            ls<sn = mapAll (λ x<n → <-trans x<n (0 , refl)) ls<n

    splitBelow : (top : ℕ) → goodSplit top
    splitBelow zero = ([] , []) , ([] , []) , ([] , []) , refl
    splitBelow (suc n) = splitBelow-aux n (splitBelow n) (Pdec n)

-- definitions and properties of counting:
-- how many naturals in a given range have a given decidable property?
-- note: lower bound included, upper bound excluded (if equal nothing counted)
module _ (P : ℕ → Type ℓ) (Pdec : ∀ n → Dec (P n)) where
    countBelow : ℕ → ℕ
    countBelow top = length ((splitBelow P Pdec top) .fst .fst)

    countRange : (low top : ℕ) → low ≤ top → ℕ
    countRange low top _ = length (splitBelow
                           (λ n → (P n) × (low ≤ n)) (DecProd Pdec (≤Dec low)) top
                           .fst .fst)

    least→count=0 : {n : ℕ} → (∀ z → P z → n ≤ z) → countBelow n ≡ 0
    least→count=0 {n} least = answer where
        split = splitBelow P Pdec n
        goods = split .fst .fst
        Pgoods = split .snd .fst .fst
        goods<n = split .snd .snd .fst .fst

        answer : countBelow n ≡ 0
        answer with goods | goods<n | Pgoods
        ... | [] | [] | [] = refl
        ... | x ∷ _ | x<n ∷ _ | Px ∷ _ = ⊥.rec (<-asym x<n (least x Px))

    countRefl≡0 : (n : ℕ) → countRange n n (0 , refl) ≡ 0
    countRefl≡0 n = answer where
        split = splitBelow (λ x → (P x) × (n ≤ x)) (DecProd Pdec (≤Dec n)) n
        ws = split .fst .fst
        Pws = split .snd .fst .fst
        ws<n = split .snd .snd .fst .fst

        answer : length ws ≡ 0
        answer with ws | Pws | ws<n
        ... | [] | [] | [] = refl
        ... | _ | (_ , n≤w) ∷ _ | w<n ∷ _ = ⊥.rec (<-asym w<n n≤w)

    countRangeSuc : (l t : ℕ) → (l≤t : l ≤ t) →
                    (DPt : Dec (P t)) → (DPt ≡ Pdec t) →
                    (decToN DPt) + countRange l t l≤t ≡ countRange l (suc t) (≤-suc l≤t)
    countRangeSuc l t l≤t (yes Pt) p = answer where
        Q = λ n → (P n) × (l ≤ n)
        dprod = λ a → DecProd-aux P (l ≤_) (Pdec a) (≤Dec l a)
        IH = splitBelow Q dprod t

        replace : Σ[ Qt ∈ Q t ] yes Qt ≡ dprod t
        replace with dprod t
        ... | no ¬Qt = ⊥.rec (¬Qt (Pt , l≤t))
        ... | yes Qt = Qt , refl

        answer : suc (length (IH .fst .fst))
                 ≡ length (splitBelow-aux Q dprod t IH (dprod t) .fst .fst)
        answer = cong (λ x → length (splitBelow-aux Q dprod t IH x .fst .fst)) (replace .snd)

    countRangeSuc l t l≤t (no ¬Pt) p = answer where
        Q = λ n → (P n) × (l ≤ n)
        dprod = λ a → DecProd-aux P (l ≤_) (Pdec a) (≤Dec l a)
        IH = splitBelow Q dprod t

        replace : Σ[ ¬Qt ∈ ¬ (Q t) ] no ¬Qt ≡ dprod t
        replace with dprod t
        ... | no ¬Qt = ¬Qt , refl
        ... | yes (Pt , _) = ⊥.rec (¬Pt Pt)

        answer : length (IH .fst .fst)
                 ≡ length (splitBelow-aux Q dprod t IH (dprod t) .fst .fst)
        answer = cong (λ x → length (splitBelow-aux Q dprod t IH x .fst .fst)) (replace .snd)

    countBelowSuc : (n : ℕ) → (DPn : Dec (P n)) → (DPn ≡ Pdec n) →
                    (decToN DPn) + countBelow n ≡ countBelow (suc n)
    countBelowSuc n (yes Pn) p =
        cong (λ x → length (splitBelow-aux P Pdec n (splitBelow P Pdec n) x .fst .fst)) p
    countBelowSuc n (no ¬Pn) p =
        cong (λ x → length (splitBelow-aux P Pdec n (splitBelow P Pdec n) x .fst .fst)) p


    countWorks-aux : (l t : ℕ) → (l≤st : l ≤ (suc t)) →
                     ((l≤t : l ≤ t) → (countRange l t l≤t) + (countBelow l) ≡ countBelow t) →
                     ((l < suc t) ⊎ (l ≡ suc t)) →
                     (countRange l (suc t) l≤st) + (countBelow l) ≡ countBelow (suc t)
    countWorks-aux l t l≤st recf (inr l=st) = (cong (_+ countBelow l) p2 ∙ p1) ∙ p3 where
        p1 : countRange l l (0 , refl) + countBelow l ≡ countBelow l
        p1 = cong (_+ countBelow l) (countRefl≡0 l)
        p2 : countRange l (suc t) l≤st ≡ countRange l l (0 , refl)
        p2 = sym (cong₂ (λ x l≤x → countRange l x l≤x)
                        l=st
                        (isProp→PathP (λ i → isProp≤) (0 , refl) l≤st))
        p3 : countBelow l ≡ countBelow (suc t)
        p3 = cong (countBelow) l=st

    countWorks-aux l t l≤st recf (inl l<st) = induct (recf l≤t) where
        l≤t : l ≤ t
        l≤t = pred-≤-pred l<st
        induct : (countRange l t l≤t) + (countBelow l) ≡ countBelow t →
                 (countRange l (suc t) l≤st) + (countBelow l) ≡ countBelow (suc t)
        induct IH = sym (cong (_+ countBelow l) p1) ∙ p3 ∙ p2 where
            p1 : decToN (Pdec t) + countRange l t l≤t ≡ countRange l (suc t) l≤st
            p1 = countRangeSuc l t l≤t (Pdec t) refl
            p2 : decToN (Pdec t) + countBelow t ≡ countBelow (suc t)
            p2 = countBelowSuc t (Pdec t) refl
            p3 : decToN (Pdec t) + countRange l t l≤t + countBelow l ≡
                    decToN (Pdec t) + countBelow t
            p3 = sym (+-assoc (decToN (Pdec t)) (countRange l t l≤t) (countBelow l))
                    ∙ cong (decToN (Pdec t) +_) IH

    countWorks : (low top : ℕ) → (l≤t : low ≤ top) →
                 (countRange low top l≤t) + (countBelow low) ≡ countBelow top
    countWorks l zero l≤0 = cong (λ x → countBelow x) (≤0→≡0 l≤0)
    countWorks l (suc t) l≤st = countWorks-aux l t l≤st (countWorks l t) (≤-split l≤st)


    leastAboveLow-aux : (l t : ℕ) → (l<st : l < (suc t)) →
                        (Pl : P l) → (Pdec l ≡ yes Pl) → (∀ z → (l < z) × (P z) → (suc t) ≤ z) →
                        (l < t) ⊎ (l ≡ t) →
                        (l < t → countRange l t (pred-≤-pred l<st) ≡ 1) →
                        countRange l (suc t) (<-weaken l<st) ≡ 1
    leastAboveLow-aux l t l<st Pl p least (inr l=t) _ =
        sym (countRangeSuc l t (0 , l=t) (Pdec t) refl) ∙ p3 where
            p1 : decToN (Pdec t) ≡ 1
            p1 = cong (λ x → decToN (Pdec x)) (sym l=t) ∙ cong decToN p
            p2 : countRange l t (0 , l=t) ≡ 0
            p2 = cong₂ (λ x l≤x → countRange l x l≤x)
                       (sym l=t)
                       (isProp→PathP (λ i → isProp≤) (0 , l=t) (0 , refl))
                 ∙ countRefl≡0 l
            p3 : decToN (Pdec t) + countRange l t (0 , l=t) ≡ 1
            p3 = add-equations p1 p2
    leastAboveLow-aux l t l<st Pl p least (inl l<t) recf =
        p2 ∙ cong (_+ countRange l t (pred-≤-pred l<st)) p1 ∙ IH where
            IH : countRange l t (pred-≤-pred l<st) ≡ 1
            IH = recf l<t
            p1 : decToN (Pdec t) ≡ 0
            p1 with Pdec t
            ... | no   _ = refl
            ... | yes Pt = ⊥.rec (<-asym (least t (l<t , Pt)) (0 , refl))
            p2 : countRange l (suc t) (<-weaken l<st)
                 ≡ (decToN (Pdec t)) + countRange l t (pred-≤-pred l<st)
            p2 = sym (countRangeSuc l t (pred-≤-pred l<st) (Pdec t) refl)

    leastAboveLow : (l t : ℕ) → (Pl : P l) → (Pdec l ≡ yes Pl) →
                    (∀ z → (l < z) × (P z) → t ≤ z) → (l<t : l < t) →
                    countRange l t (<-weaken l<t) ≡ 1
    leastAboveLow _ zero _ _ _ l<0 = ⊥.rec (¬-<-zero l<0)
    leastAboveLow l (suc t) Pl p least l<st =
        leastAboveLow-aux l t l<st Pl p least (<-split l<st)
                          (leastAboveLow l t Pl p (λ z Qz → <-weaken (least z Qz)))


    countBelow-lt-aux : (x y : ℕ) → (Px : P x) → (Pdec x ≡ yes Px) →
                        x < (suc y) → (x < y) ⊎ (x ≡ y) →
                        (x < y → countBelow x < countBelow y) →
                        countBelow x < countBelow (suc y)
    countBelow-lt-aux x _ Px p _ (inr x=y) _ = 0 , q ∙ cong (countBelow ∘ suc) x=y where
        q : suc (countBelow x) ≡ countBelow (suc x)
        q = countBelowSuc x (yes Px) (sym p)
    countBelow-lt-aux x y Px p x<sy (inl x<y) recf =
        <≤-trans (recf x<y) (decToN (Pdec y) , countBelowSuc y (Pdec y) refl)

    countBelow-lt : (x y : ℕ) →
                    (Px : P x) → (Pdec x ≡ yes Px) →
                    x < y → countBelow x < countBelow y
    countBelow-lt _ zero _ _ x<0 = ⊥.rec (¬-<-zero x<0)
    countBelow-lt x (suc y) Px p x<sy =
        countBelow-lt-aux x y Px p x<sy
        (<-split x<sy) (countBelow-lt x y Px p)

    countBelowYesInj : (x y : ℕ) →  (Px : P x) → (Py : P y) →
                       (Pdec x ≡ yes Px) → (Pdec y ≡ yes Py) →
                       countBelow x ≡ countBelow y → x ≡ y
    countBelowYesInj x y Px Py q1 q2 p with x ≟ y
    ... | eq x=y = x=y
    ... | lt x<y = ⊥.rec (<≠ (countBelow-lt x y Px q1 x<y) p)
    ... | gt y<x = ⊥.rec (<≠ (countBelow-lt y x Py q2 y<x) (sym p))
