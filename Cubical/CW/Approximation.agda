{-# OPTIONS --lossy-unification #-}
{- Cellular approximation theorems for
-- cellular maps and homotopies
-}

module Cubical.CW.Approximation where

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.Map
open import Cubical.CW.Homotopy

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.PropositionalTruncation as PT hiding (elimFin)
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout

open import Cubical.Axiom.Choice

open import Cubical.Homotopy.Connected

open Sequence
open FinSequenceMap

private
  variable
    ℓ ℓ' ℓ'' : Level

---- Part 1. Definitions -----

-- finite cellular approximations
finCellApprox : (C : CWskel ℓ) (D : CWskel ℓ')
  (f : realise C → realise D) (m : ℕ) → Type (ℓ-max ℓ ℓ')
finCellApprox C D f m =
  Σ[ ϕ ∈ finCellMap m C D ]
    (FinSeqColim→Colim m {X = realiseSeq D}
   ∘ finCellMap→FinSeqColim C D ϕ
   ≡ f ∘ FinSeqColim→Colim m {X = realiseSeq C})

idFinCellApprox : (m : ℕ)
  {C : CWskel ℓ} → finCellApprox C C (idfun _) m
fst (idFinCellApprox m {C}) = idFinCellMap m C
snd (idFinCellApprox m {C}) =
  →FinSeqColimHomotopy _ _ λ x → refl

compFinCellApprox : (m : ℕ)
  {C : CWskel ℓ} {D : CWskel ℓ'} {E : CWskel ℓ''}
  {g : realise D → realise E}
  {f : realise C → realise D}
  → finCellApprox D E g m → finCellApprox C D f m
  → finCellApprox C E (g ∘ f) m
fst (compFinCellApprox m {g = g} {f} (F , p) (G , q)) = composeFinCellMap m F G
snd (compFinCellApprox m {C = C} {g = g} {f} (F , p) (G , q)) =
  →FinSeqColimHomotopy _ _ λ x
    → funExt⁻ p _
     ∙ cong g (funExt⁻ q (fincl _ x))

-- a finite cellular homotopies relative a homotopy in the colimit
finCellHomRel : {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ)
  (f g : finCellMap m C D)
  (h∞ : (n : Fin (suc m)) (c : fst C (fst n))
    → Path (realise D) (incl (f .fmap n c)) (incl (g .fmap n c)))
  → Type (ℓ-max ℓ ℓ')
finCellHomRel {C = C} {D = D} m f g h∞ =
  Σ[ ϕ ∈ finCellHom m f g ]
    ((n : Fin (suc m)) (x : fst C (fst n))
     → Square (h∞ n x)
               (cong incl (finCellHom.fhom ϕ n x))
               (push (f .fmap n x)) (push (g .fmap n x)))

---- Part 2. The cellular (n)-approxiation theorem: -----
-- Given CW skeleta Cₙ and Dₙ with a map f : C∞ → D∞ between their
-- realisations, there exists a finite cellular map fₙ : Cₙ → Dₙ s.t.
-- (n < m) s.t. incl ∘ fₙ = f ∘ incl

-- Construction
module _ (C : CWskel ℓ) (D : CWskel ℓ') (f : realise C → realise D) where
  find-connected-component : (d : realise D) → ∃[ d0 ∈ fst D 1 ] incl d0 ≡ d
  find-connected-component = CW→Prop D (λ _ → squash₁) λ a → ∣ a , refl ∣₁

  find-connected-component-C₀ : (c : fst C 1)
    → ∃[ d0 ∈ fst D 1 ] incl d0 ≡ f (incl c)
  find-connected-component-C₀ c = find-connected-component (f (incl c))

  -- existence of f₁ : C₁ → D₁
  approx₁ : ∃[ f₁ ∈ (fst C 1 → fst D 1) ] ((c : _) → incl (f₁ c) ≡ f (incl c))
  approx₁ =
    invEq (_ , satAC∃Fin-C0 C (λ _ → fst D 1) (λ c d0 → incl d0 ≡ f (incl c)))
      find-connected-component-C₀

  approx : (m : ℕ)
    → ∃[ fₙ ∈ ((n : Fin (suc m)) → Σ[ h ∈ (fst C (fst n) → fst D (fst n)) ]
            ((c : _) → incl (h c) ≡ f (incl c))) ]
        ((n : Fin m) (c : fst C (fst n))
          → fₙ (fsuc n) .fst (CW↪ C (fst n) c)
           ≡ CW↪ D (fst n) (fₙ (injectSuc n) .fst c))
  approx zero = ∣ (λ { (zero , p)
    → (λ x → ⊥.rec (CW₀-empty C x))
     , λ x → ⊥.rec (CW₀-empty C x)})
     , (λ {()}) ∣₁
  approx (suc zero) =
      PT.map (λ a1 →
        (λ { (zero , p) → (λ x → ⊥.rec (CW₀-empty C x))
                          , λ x → ⊥.rec (CW₀-empty C x)
           ; (suc zero , p) → a1})
           , λ {(zero , p) c → ⊥.rec (CW₀-empty C c)})
    approx₁
  approx (suc (suc m)) =
      PT.rec
      squash₁
      (λ {(p , f')
      → PT.rec squash₁ (λ r
        → PT.map (λ ind → mainₗ p f' r ind
                          , mainᵣ p f' r ind)
          (mere-fib-f-coh (p flast .fst)
            r (p (suc m , <ᵗsucm) .snd)))
            (fst-lem (p flast .fst)
                     (p flast .snd))})
      (approx (suc m))
    where
    open CWskel-fields C
    fst-lem : (fm : fst C (suc m) → fst D (suc m))
      → ((c : fst C (suc m)) → incl (fm c) ≡ f (incl c))
      → ∥ ((x : A (suc m)) (y : S₊ m)
         → CW↪ D (suc m) (fm (α (suc m) (x , y)))
          ≡ CW↪ D (suc m) (fm (α (suc m) (x , ptSn m)))) ∥₁
    fst-lem fm fh =
      invEq propTrunc≃Trunc1
       (invEq (_ , InductiveFinSatAC 1 (CWskel-fields.card C (suc m)) _)
        λ a → fst propTrunc≃Trunc1
           (sphereToTrunc (suc m) λ y →
             TR.map fst (isConnectedCong _ _ (isConnected-CW↪∞ (suc (suc m)) D)
                     (sym (push _)
                     ∙ (fh (CWskel-fields.α C (suc m) (a , y))
                     ∙ cong f (push _
                           ∙ cong incl (cong (invEq (CWskel-fields.e C (suc m)))
                               (push (a , y) ∙ sym (push (a , ptSn m))))
                           ∙ sym (push _))
                    ∙ sym (fh (CWskel-fields.α C (suc m) (a , ptSn m))))
                     ∙ push _) .fst)))

    module _ (fm : fst C (suc m) → fst D (suc m))
             (fm-coh : (x : A (suc m)) (y : S₊ m) →
                       CW↪ D (suc m) (fm (α (suc m) (x , y)))
                     ≡ CW↪ D (suc m) (fm (α (suc m) (x , ptSn m)))) where
      module _ (ind : ((c : fst C (suc m)) → incl (fm c) ≡ f (incl c))) where
        fib-f-incl : (c : fst C (suc (suc m))) → Type _
        fib-f-incl c = Σ[ x ∈ fst D (suc (suc m)) ] incl x ≡ f (incl c)

        fib-f-l : (c : fst C (suc m)) → fib-f-incl (CW↪ C (suc m) c)
        fst (fib-f-l c) = CW↪ D (suc m) (fm c)
        snd (fib-f-l c) = sym (push _) ∙∙ ind c ∙∙ cong f (push _)

        fib-f-r : (x : A (suc m))
          → fib-f-incl (invEq (e (suc m)) (inr x))
        fib-f-r x = subst fib-f-incl (cong (invEq (e (suc m)))
                                     (push (x , ptSn m)))
                                     (fib-f-l (α (suc m) (x , ptSn m)))

        fib-f-l-coh : (x : A (suc m))
          → PathP (λ i → fib-f-incl (invEq (e (suc m)) (push (x , ptSn m) i)))
                   (fib-f-l (α (suc m) (x , ptSn m)))
                   (fib-f-r x)
        fib-f-l-coh x i =
          transp (λ j → fib-f-incl (invEq (e (suc m)) (push (x , ptSn m) (i ∧ j))))
                 (~ i)
                 (fib-f-l (α (suc m) (x , ptSn m)))

        mere-fib-f-coh : ∥ ((x : A (suc m)) (y : S₊ m)
           → PathP (λ i → fib-f-incl (invEq (e (suc m)) (push (x , y) i)))
                    (fib-f-l (α (suc m) (x , y)))
                    (fib-f-r x)) ∥₁
        mere-fib-f-coh = invEq propTrunc≃Trunc1
          (invEq (_ , InductiveFinSatAC 1 (card (suc m)) _)
            λ a → fst propTrunc≃Trunc1 (sphereToTrunc (suc m)
              (sphereElim' m
                (λ x → isOfHLevelRetractFromIso m
                (invIso (PathPIdTruncIso (suc m)))
                (isOfHLevelPathP' m (isProp→isOfHLevelSuc m
                  (isContr→isProp
                    (isConnected-CW↪∞  (suc (suc m)) D _))) _ _))
                ∣ fib-f-l-coh a ∣ₕ)))

      module _ (ind : ((c : fst C (suc m)) → incl (fm c) ≡ f (incl c)))
               (ind2 : ((x : A (suc m)) (y : S₊ m)
             → PathP (λ i → fib-f-incl ind (invEq (e (suc m)) (push (x , y) i)))
                      (fib-f-l ind (α (suc m) (x , y)))
                      (fib-f-r ind x)))
        where
        toFiber : (c : fst C (suc (suc m)))
               → fiber (incl {n = (suc (suc m))}) (f (incl c))
        toFiber = CWskel-elim C (suc m) (fib-f-l ind) (fib-f-r ind) ind2

        toFiberβ : (c : fst C (suc m)) → toFiber (CW↪ C (suc m) c) ≡ fib-f-l ind c
        toFiberβ = CWskel-elim-inl C (suc m) (fib-f-l ind) (fib-f-r ind) ind2

    module _ (p : (n : Fin (suc (suc m)))
        → Σ[ h ∈ (fst C (fst n) → fst D (fst n)) ]
            ((c : fst C (fst n)) → incl (h c) ≡ f (incl c)))
      (f' : (n : Fin (suc m)) (c : fst C (fst n))
         → p (fsuc n) .fst (CW↪ C (fst n) c) ≡
            CW↪ D (fst n) (p (injectSuc n) .fst c))
      (r : (n : A (suc m)) (y : S₊ m) →
            CW↪ D (suc m) (p flast .fst (α (suc m) (n , y)))
          ≡ CW↪ D (suc m) (p flast .fst (α (suc m) (n , ptSn m))))
      (ind : (n : Fin _) (y : S₊ m) →
             PathP
             (λ i →
                fib-f-incl (p flast .fst) r (p flast .snd)
                (invEq (e (suc m)) (push (n , y) i)))
             (fib-f-l (p flast .fst) r (p flast .snd)
              (α (suc m) (n , y)))
             (fib-f-r (p flast .fst) r (p flast .snd) n)) where

      FST-base : Σ[ h ∈ (fst C (suc (suc m)) → fst D (suc (suc m))) ]
                   ((c : fst C (suc (suc m))) → incl (h c) ≡ f (incl c))
      fst FST-base = fst ∘ toFiber _ _ _ ind
      snd FST-base = snd ∘ toFiber _ _ _ ind

      Goalₗ : (n : Fin (suc (suc (suc m)))) → Type _
      Goalₗ n = Σ[ h ∈ (fst C (fst n) → fst D (fst n)) ]
            ((c : fst C (fst n)) → incl (h c) ≡ f (incl c))

      mainₗ : (n : Fin (suc (suc (suc m)))) → Goalₗ n
      mainₗ = elimFin FST-base p

      mainᵣ : (n : Fin (suc (suc m))) (c : fst C (fst n))
        → mainₗ (fsuc n) .fst (CW↪ C (fst n) c)
        ≡ CW↪ D (fst n) (mainₗ (injectSuc n) .fst c)
      mainᵣ = elimFin (λ c
        → funExt⁻ (cong fst (elimFinβ {A = Goalₗ} FST-base p .fst))
                    (CW↪ C (suc m) c)
        ∙ cong fst (toFiberβ _ _ _ ind c)
        ∙ cong (CW↪ D (suc m))
          (sym (funExt⁻
           (cong fst (elimFinβ {A = Goalₗ} FST-base p .snd flast)) c)))
        λ x c → funExt⁻ (cong fst (elimFinβ {A = Goalₗ}
                  FST-base p .snd (fsuc x))) (CW↪ C (fst x) c)
              ∙ f' x c
              ∙ cong (CW↪ D (fst x))
                  (sym (funExt⁻ (cong fst
                   ((elimFinβ {A = Goalₗ} FST-base p .snd) (injectSuc x))) c))

-- first main result
CWmap→finCellMap : (C : CWskel ℓ) (D : CWskel ℓ')
  (f : realise C → realise D) (m : ℕ)
  → ∥ finCellApprox C D f m ∥₁
CWmap→finCellMap C D f m =
  PT.map (λ {(g , hom)
  → finsequencemap (fst ∘ g) (λ r x → sym (hom r x))
   , →FinSeqColimHomotopy _ _ (g flast .snd)})
     (approx C D f m)

-- Version for finite CW complexes
finCWmap→CellMap : ∀ {ℓ ℓ'} (n : ℕ) (C : finCWskel ℓ n) (D : CWskel ℓ')
  (f : realise (finCWskel→CWskel n C) → realise D)
  → ∃[ ϕ ∈ cellMap (finCWskel→CWskel n C) D ]
      realiseCellMap ϕ ≡ f
finCWmap→CellMap n C D f =
  PT.map (λ {(ϕ , p) → ψ ϕ (funExt⁻ p)
  , funExt λ x
    → subst (λ x → realiseCellMap (ψ ϕ (funExt⁻ p)) x ≡ f x)
            (Iso.rightInv (converges→ColimIso
              {seq = realiseSeq (finCWskel→CWskel n C)} n (C .snd .snd)) x)
            (cong (incl {n = n})
              (silly ϕ (funExt⁻ p) _)
            ∙ funExt⁻ p (fincl (n , (<ᵗsucm {n}))
               (Iso.inv (converges→ColimIso n (C .snd .snd)) x)))})
  (CWmap→finCellMap
    (finCWskel→CWskel n C) D f n)
  where
  open SequenceMap renaming (map to smap)
  open FinSequenceMap
  module _ (ϕ : finCellMap n (finCWskel→CWskel n C) D)
           (ϕid : (x : FinSeqColim n
                      (realiseSeq (finCWskel→CWskel n C)))
         → FinSeqColim→Colim n
            (finCellMap→FinSeqColim (finCWskel→CWskel n C) D ϕ x)
          ≡ f (FinSeqColim→Colim n x)) where
    -- ψm' : (m : ℕ) → fst (finCWskel→CWskel n C) m → fst D m
    -- ψm' m with (m ≟ suc n)
    -- ... | lt q = fmap ϕ (m , q)
    -- ... | eq q = fmap ϕ (m , {!!})
    -- ... | gt q = {!!}

    C≃ : (k : ℕ) → fst C n ≃ fst C (k +ℕ n)
    C≃ zero = idEquiv _
    C≃ (suc k) = compEquiv (C≃ k) (_ , snd (snd C) k)

    C→D : (k : ℕ) → fst C (k +ℕ n) → fst D (k +ℕ n)
    C→D k = CW↪Iterate D n k
          ∘ fmap ϕ (n , <ᵗsucm {n})
          ∘ invEq (C≃ k)

    C→D-cellular : (k : ℕ) (x : fst (finCWskel→CWskel n C) (k +ℕ n))
      → C→D (suc k) (CW↪ (finCWskel→CWskel n C) (k +ℕ n) x)
       ≡ CW↪ D (k +ℕ n) (C→D k x)
    C→D-cellular k x =
      cong (CW↪ D (k +ℕ n) ∘ CW↪Iterate D n k ∘ fmap ϕ (n , <ᵗsucm))
        (cong (invEq (C≃ k)) (retEq (_ , snd (snd C) k) x))

    mainlem : ∀ {ℓ ℓ'} (D : ℕ → Type ℓ) (C : ℕ → Type ℓ') (n : ℕ)
      → (C→D : (k : ℕ) → C (k +ℕ n) → D (k +ℕ n))
      → (D↑ : (n : ℕ) → D n → D (suc n))
      → (C↑ : (n : ℕ) → C n → C (suc n))
      → (cm : (k : ℕ) (x : _)
              → C→D (suc k) (C↑ (k +ℕ n) x)
              ≡ D↑ (k +ℕ n) (C→D k x))
      (r : ℕ) (k : ℕ) (p4 : r +ℕ n ≡ k)
      (x : C k) (z : ℕ) (p0 : suc r ≡ z) (p1 : suc k ≡ z +ℕ n)
                          (m : ℕ) (p3 : r +ℕ n ≡ m)
                          (p2 : z +ℕ n ≡ suc m)
      → D↑ m (subst D p3 (C→D r (subst C (sym p4) x)))
      ≡ subst D p2 (C→D z (subst C p1 (C↑ k x)))
    mainlem C D n C→D D↑ C↑ cm r =
      J> λ x → J> λ p1 → J> λ p2
        → cong (D↑ (r +ℕ n))
                (transportRefl _ ∙ cong (C→D r) (transportRefl _))
        ∙ sym ((λ i → subst C (isSetℕ _ _ p2 refl i)
                        (C→D (suc r) (subst D (isSetℕ _ _ p1 refl i)
                          (C↑ (r +ℕ n) x))))
             ∙ transportRefl _
             ∙ cong (C→D (suc r)) (transportRefl _)
             ∙ cm r x)

    ψm : (m : ℕ) → fst (finCWskel→CWskel n C) m → fst D m
    ψm m with (Dichotomyℕ n m)
    ... | inl q = subst (fst D) (snd q)
                ∘ C→D (fst q)
                ∘ subst (fst C) (sym (snd q))
    ... | inr q = fmap ϕ (m , <ᵗ-trans (<→<ᵗ q) (<ᵗsucm {n}))

    ψ : cellMap (finCWskel→CWskel n C) D
    smap ψ = ψm
    comm ψ m x with (Dichotomyℕ n m) | Dichotomyℕ n (suc m)
    ... | inl n≤m | inl n≤sucm =
        mainlem (fst D) (fst C) n C→D (CW↪ D) (CW↪ (finCWskel→CWskel n C))
          C→D-cellular _ _ _ _ _
            (inj-+m  {m = n} (cong suc (snd n≤m)
              ∙ sym (cong predℕ (cong suc (snd n≤sucm))))) _ _ _ _
    ... | inl n≤m | inr n>sucm =
      ⊥.rec (<-asym (<≤-trans n>sucm n≤m) (1 , refl))
    ... | inr n>m | inl (zero , n≤sucm) =
        (cong (CW↪ D m)
          (cong (λ p → fmap ϕ (m , p) x) (isProp<ᵗ _ _))
        ∙ fcomm ϕ (m , <→<ᵗ n>m) x)
      ∙ cong (λ p → fmap ϕ (suc m , p) c) (isProp<ᵗ _ _)
      ∙ λ j → transp (λ i → fst D (n≤sucm (i ∨ ~ j))) (~ j)
                (fmap ϕ (n≤sucm (~ j) ,
                  isProp→PathP {B = λ j → n≤sucm (~ j) <ᵗ suc n}
                    (λ _ → isProp<ᵗ) (<→<ᵗ n>m) <ᵗsucm j)
                 (transp (λ i → fst C (n≤sucm (~ i ∨ ~ j))) (~ j)
                   c))
      where
      c = CW↪ (finCWskel→CWskel n C) m x
      lem : n>m ≡ (0 , sym n≤sucm)
      lem = isProp≤ _ _
    ... | inr n>m | inl (suc diff , n≤sucm) =
      ⊥.rec (<-asym (<≤-trans (diff , +-suc diff n ∙ n≤sucm) n>m) (0 , refl))
    ... | inr n>m | inr n>sucm =
         cong (CW↪ D m)
           (funExt⁻ (cong (fmap ϕ) (ΣPathP (refl , (isProp<ᵗ _ _)))) x)
       ∙ fcomm ϕ (m , <→<ᵗ n>m) x
       ∙ funExt⁻ (cong (fmap ϕ) (ΣPathP (refl , (isProp<ᵗ _ _)))) _

    silly : (x : _) → smap ψ n x ≡ fmap ϕ (n , <ᵗsucm {n}) x
    silly x with (Dichotomyℕ n n)
    ... | inl (zero , p) =
       cong (λ p → subst (fst D) p (C→D zero (subst (fst C) (sym p) x)))
            (isSetℕ _ _ p refl)
      ∙ transportRefl _
      ∙ cong (C→D zero) (transportRefl x)
    ... | inl (suc diff , p) =
      ⊥.rec (¬m<ᵗm {n} (<→<ᵗ (diff , (+-suc diff n ∙ p))))
    ... | inr p = ⊥.rec (¬m<ᵗm (<→<ᵗ p))

---- Part 3. The (finite) cellular approximation theorem for cellular homotopies: -----
-- Given two (m)-finite cellular maps fₙ, gₙ : Cₙ → Dₙ agreeing on
-- Dₘ ↪ D∞, there is a finite cellular homotopy fₙ ∼ₘ gₙ.

-- some abbreviations
private
  module SeqHomotopyTypes {ℓ ℓ'} {C : Sequence ℓ} {D : Sequence ℓ'} (m : ℕ)
    (f-c g-c : FinSequenceMap (Sequence→FinSequence m C)
                              (Sequence→FinSequence m D))
    where
    f = fmap f-c
    g = fmap g-c
    f-hom = fcomm f-c
    g-hom = fcomm g-c

    cell-hom : (n : Fin (suc m)) (c : obj C (fst n)) → Type ℓ'
    cell-hom n c = Sequence.map D (f n c) ≡ Sequence.map D (g n c)

    cell-hom-coh : (n : Fin m) (c : obj C (fst n))
      → cell-hom (injectSuc n) c
      → cell-hom (fsuc n) (Sequence.map C c) → Type ℓ'
    cell-hom-coh n c h h' =
      Square (cong (Sequence.map D) h) h'
             (cong (Sequence.map D) (f-hom n c))
             (cong (Sequence.map D) (g-hom n c))

-- construction
module approx {C : CWskel ℓ} {D : CWskel ℓ'}
  (m : ℕ) (f-c g-c : finCellMap m C D)
  (h∞' : FinSeqColim→Colim m ∘ finCellMap→FinSeqColim C D f-c
       ≡ FinSeqColim→Colim m ∘ finCellMap→FinSeqColim C D g-c) where
  open SeqHomotopyTypes m f-c g-c
  open CWskel-fields C

  h∞ : (n : Fin (suc m)) (c : fst C (fst n))
        → Path (realise D) (incl (fmap f-c n c)) (incl (fmap g-c n c))
  h∞ n c = funExt⁻ h∞' (fincl n c)

  pathToCellularHomotopy₁ : (t : 1 <ᵗ suc m) (c : fst C 1)
    → ∃[ h ∈ cell-hom (1 , t) c ]
         Square (h∞ (1 , t) c)
                (cong incl h)
                (push (f (1 , t) c))
                (push (g (1 , t) c))
  pathToCellularHomotopy₁ t c =
    TR.rec squash₁
      (λ {(d , p)
      → ∣ d
      , (λ i j
      → hcomp (λ k →
           λ {(i = i0) → doubleCompPath-filler
                            (sym (push (f (1 , t) c)))
                            (h∞ _ c)
                            (push (g (1 , t) c)) (~ k) j
            ; (i = i1) → incl (d j)
            ; (j = i0) → push (f (1 , t) c) (~ k ∨ i)
            ; (j = i1) → push (g (1 , t) c) (~ k ∨ i)})
              (p (~ i) j)) ∣₁})
    (isConnectedCong 1 (CW↪∞ D 2)
      (isConnected-CW↪∞ 2 D) h∞* .fst)
    where
    h∞* : CW↪∞ D 2 (CW↪ D 1 (f (1 , t) c)) ≡ CW↪∞ D 2 (CW↪ D 1 (g (1 , t) c))
    h∞* = sym (push (f (1 , t) c)) ∙∙ h∞ _ c ∙∙ push (g (1 , t) c)

  -- induction step
  pathToCellularHomotopy-ind : (n : Fin m)
    → (hₙ : (c : fst C (fst n)) → Σ[ h ∈ cell-hom (injectSuc n) c ]
                                     (Square (h∞ (injectSuc n) c)
                                            (cong incl h)
                                            (push (f (injectSuc n) c))
                                            (push (g (injectSuc n) c))))
    → ∃[ hₙ₊₁ ∈ ((c : fst C (suc (fst n)))
                → Σ[ h ∈ cell-hom (fsuc n) c ]
                     (Square (h∞ (fsuc n) c)
                             (cong incl h)
                             (push (f (fsuc n) c))
                             (push (g (fsuc n) c)))) ]
                    ((c : _) → cell-hom-coh n c (hₙ c .fst)
                                  (hₙ₊₁ (CW↪ C (fst n) c) .fst))

  pathToCellularHomotopy-ind (zero ,  q) ind =
    fst (propTrunc≃ (isoToEquiv (compIso (invIso rUnit×Iso)
      (Σ-cong-iso-snd
        λ _ → isContr→Iso isContrUnit
        ((λ x → ⊥.rec (CW₀-empty C x))
       , λ t → funExt λ x → ⊥.rec (CW₀-empty C x))))))
       (invEq propTrunc≃Trunc1
         (invEq (_ , satAC-CW₁ 1 C _)
           λ c → fst propTrunc≃Trunc1
             (pathToCellularHomotopy₁ (fsuc (zero , q) .snd) c)))
  pathToCellularHomotopy-ind (suc n' , w) ind =
    PT.map (λ q → hₙ₊₁ q , hₙ₊₁-coh q) Πfiber-cong²-hₙ₊₁-push∞
    where
    n : Fin m
    n = (suc n' , w)
    Pushout→C = invEq (e (suc n'))

    hₙ'-filler : (x : fst C (suc n')) → _
    hₙ'-filler x =
      doubleCompPath-filler
            (sym (f-hom n x))
            (ind x .fst)
            (g-hom n x)

    hₙ' : (x : fst C (suc n'))
      → f (fsuc n) (CW↪ C (suc n') x)
       ≡ g (fsuc n) (CW↪ C (suc n') x)
    hₙ' x = hₙ'-filler x i1

    -- homotopy for inl
    hₙ₊₁-inl : (x : fst C (suc n'))
      → cell-hom (fsuc n) (invEq (e (suc n')) (inl x))
    hₙ₊₁-inl x = cong (CW↪ D (suc (suc n'))) (hₙ' x)

    -- hₙ₊₁-inl coherent with h∞
    h∞-push-coh : (x : fst C (suc n'))
      → Square (h∞ (injectSuc n) x) (h∞ (fsuc n) (CW↪ C (fst n) x))
                (push (f (injectSuc n) x) ∙ (λ i₁ → incl (f-hom n x i₁)))
                (push (g (injectSuc n) x) ∙ (λ i₁ → incl (g-hom n x i₁)))
    h∞-push-coh x i j =
      hcomp (λ k
        → λ {(i = i0) → h∞' j (fincl (injectSuc n) x)
            ; (i = i1) → h∞' j (fincl (fsuc n) (CW↪ C (fst n) x))
            ; (j = i0) → cong-∙ (FinSeqColim→Colim m)
                                 (fpush n (f (injectSuc n) x))
                                 (λ i₁ → fincl (fsuc n) (f-hom n x i₁)) k i
            ; (j = i1) → cong-∙ (FinSeqColim→Colim m)
                                 (fpush n (g (injectSuc n) x))
                                 (λ i₁ → fincl (fsuc n) (g-hom n x i₁)) k i})
            (h∞' j (fpush n x i))

    hₙ₊₁-inl-coh : (x : fst C (fst n))
      → Square (h∞ (fsuc n) (invEq (e (fst n)) (inl x)))
                (cong incl (hₙ₊₁-inl x))
                (push (f (fsuc n) (invEq (e (fst n)) (inl x))))
                (push (g (fsuc n) (invEq (e (fst n)) (inl x))))
    hₙ₊₁-inl-coh x i j =
      hcomp (λ k
        → λ {(i = i0) → h∞ (fsuc n) (CW↪ C (fst n) x) j
            ; (i = i1) → push (hₙ' x j) k
            ; (j = i0) → push (f (fsuc n) (CW↪ C (fst n) x)) (k ∧ i)
            ; (j = i1) → push (g (fsuc n) (CW↪ C (fst n) x)) (k ∧ i)})
       (hcomp (λ k
         → λ {(i = i0) → h∞-push-coh x k j
             ; (i = i1) → incl (hₙ'-filler x k j)
             ; (j = i0) → compPath-filler'
                             (push (f (injectSuc n) x))
                             ((λ i₁ → incl (f-hom n x i₁))) (~ i) k
             ; (j = i1) → compPath-filler'
                             (push (g (injectSuc n) x))
                             ((λ i₁ → incl (g-hom n x i₁))) (~ i) k})
           (ind x .snd i j))

    module _ (x : A (suc n')) (y : S₊ n') where
      push-path-filler : I → I → Pushout (α (suc n')) fst
      push-path-filler i j =
        compPath-filler'' (push (x , y)) (sym (push (x , ptSn n'))) i j

      push-path :
        Path (Pushout (α (suc n')) fst)
             (inl (α (suc n') (x , y)))
             (inl (α (suc n') (x , ptSn n')))
      push-path j = push-path-filler i1 j

      D∞PushSquare : Type ℓ'
      D∞PushSquare =
        Square {A = realise D}
          (cong (CW↪∞ D (suc (suc (suc n'))))
            (hₙ₊₁-inl (snd C .snd .fst (suc n') (x , y))))
          (cong (CW↪∞ D (suc (suc (suc n'))))
            (hₙ₊₁-inl (snd C .snd .fst (suc n') (x , ptSn n'))))
          (λ i → incl (CW↪ D (suc (suc n'))
                        (f (fsuc n) (Pushout→C (push-path i)))))
          (λ i → incl (CW↪ D (suc (suc n'))
                        (g (fsuc n) (Pushout→C (push-path i)))))

      cong² : PathP (λ i → cell-hom (fsuc n)
                             (Pushout→C (push-path i)))
                    (hₙ₊₁-inl (α (suc n') (x , y)))
                    (hₙ₊₁-inl (α (suc n') (x , ptSn n')))
            → D∞PushSquare
      cong² p i j = incl (p i j)

      isConnected-cong² : isConnectedFun (suc n') cong²
      isConnected-cong² =
        isConnectedCong² (suc n') (CW↪∞ D (3 +ℕ n'))
          (isConnected-CW↪∞ (3 +ℕ n') D)

      hₙ₊₁-push∞ : D∞PushSquare
      hₙ₊₁-push∞ i j =
        hcomp (λ k
        → λ {(i = i0) → hₙ₊₁-inl-coh (α (suc n') (x , y)) k j
            ; (i = i1) → hₙ₊₁-inl-coh (α (suc n') (x , ptSn n')) k j
            ; (j = i0) → push (f (fsuc n) (Pushout→C (push-path i))) k
            ; (j = i1) → push (g (fsuc n) (Pushout→C (push-path i))) k})
        (hcomp (λ k
         → λ {(i = i0) → h∞' j (fincl (fsuc n)
                            (Pushout→C (push (x , y) (~ k))))
             ; (i = i1) → h∞' j (fincl (fsuc n)
                            (Pushout→C (push (x , ptSn n') (~ k))))
             ; (j = i0) → incl (f (fsuc n)
                                 (Pushout→C (push-path-filler k i)))
             ; (j = i1) → incl (g (fsuc n)
                                 (Pushout→C (push-path-filler k i)))})
         (h∞' j (fincl (fsuc n) (Pushout→C (inr x)))))

      fiber-cong²-hₙ₊₁-push∞ : hLevelTrunc (suc n') (fiber cong² hₙ₊₁-push∞)
      fiber-cong²-hₙ₊₁-push∞ = isConnected-cong² hₙ₊₁-push∞ .fst

      hₙ₊₁-coh∞ : (q : fiber cong² hₙ₊₁-push∞)
        → Cube (hₙ₊₁-inl-coh (α (suc n') (x , y)))
                (hₙ₊₁-inl-coh (α (suc n') (x , ptSn n')))
                (λ j k → h∞' k (fincl (fsuc n) (Pushout→C (push-path j))))
                (λ j k → incl (fst q j k))
                (λ j i → push (f (fsuc n) (Pushout→C (push-path j))) i)
                λ j i → push (g (fsuc n) (Pushout→C (push-path j))) i
      hₙ₊₁-coh∞ q j i k =
        hcomp (λ r
          → λ {(i = i0) → h∞' k (fincl (fsuc n) (Pushout→C (push-path j)))
              ; (i = i1) → q .snd (~ r) j k
              ; (j = i0) → hₙ₊₁-inl-coh (α (suc n') (x , y)) i k
              ; (j = i1) → hₙ₊₁-inl-coh (α (suc n') (x , ptSn n')) i k
              ; (k = i0) → push (f (fsuc n) (Pushout→C (push-path j))) i
              ; (k = i1) → push (g (fsuc n) (Pushout→C (push-path j))) i})
         (hcomp (λ r
           → λ {(i = i0) → h∞' k (fincl (fsuc n) (Pushout→C (push-path j)))
               ; (j = i0) → hₙ₊₁-inl-coh (α (suc n') (x , y)) (i ∧ r) k
               ; (j = i1) → hₙ₊₁-inl-coh (α (suc n') (x , ptSn n')) (i ∧ r) k
               ; (k = i0) → push (f (fsuc n)
                               (Pushout→C (push-path j))) (i ∧ r)
               ; (k = i1) → push (g (fsuc n)
                               (Pushout→C (push-path j))) (i ∧ r)})
          (hcomp (λ r
            → λ {(i = i0) → h∞' k (fincl (fsuc n)
                                     (Pushout→C (push-path-filler r j)))
                ; (j = i0) → h∞' k (fincl (fsuc n) (invEq (e (suc n'))
                                    (push (x , y) (~ r))))
                ; (j = i1) → h∞' k (fincl (fsuc n) (invEq (e (suc n'))
                                    (push (x , ptSn n') (~ r))))
                ; (k = i0) → incl (f (fsuc n)
                               (Pushout→C (push-path-filler r j)))
                ; (k = i1) → incl (g (fsuc n)
                               (Pushout→C (push-path-filler r j)))})
            (h∞' k (fincl (fsuc n) (Pushout→C (inr x))))))

    Πfiber-cong²-hₙ₊₁-push∞ :
      ∥ ((x : _) (y : _) → fiber (cong² x y) (hₙ₊₁-push∞ x y)) ∥₁
    Πfiber-cong²-hₙ₊₁-push∞ =
      Iso.inv propTruncTrunc1Iso
        (invEq (_ , InductiveFinSatAC 1 _ _)
        λ x → Iso.fun propTruncTrunc1Iso
                (sphereToTrunc (suc n') (fiber-cong²-hₙ₊₁-push∞ x)))

    module _ (q : (x : Fin (fst (snd C) (suc n'))) (y : S₊ n')
                → fiber (cong² x y) (hₙ₊₁-push∞ x y)) where
      agrees : (x : fst C (suc n')) (ϕ : cell-hom (fsuc n) (CW↪ C (suc n') x))
        → Type _
      agrees x ϕ = Square (h∞ (fsuc n) (CW↪ C (suc n') x))
            (cong incl ϕ)
            (push (f (fsuc n) (CW↪ C (suc n') x)))
            (push (g (fsuc n) (CW↪ C (suc n') x)))

      main-inl : (x : fst C (suc n'))
        → Σ (cell-hom (fsuc n) (CW↪ C (suc n') x))
             (agrees x)
      main-inl x = hₙ₊₁-inl x , hₙ₊₁-inl-coh x

      main-push : (x : A (suc n')) (y : S₊ n')
       → PathP (λ i → Σ[ ϕ ∈ (cell-hom (fsuc n) (Pushout→C (push-path x y i))) ]
                (Square (h∞ (fsuc n) (Pushout→C (push-path x y i)))
                        (λ j → incl (ϕ j))
                        (push (f (fsuc n) (Pushout→C (push-path x y i))))
                        (push (g (fsuc n) (Pushout→C (push-path x y i))))))
                 (main-inl (α (suc n') (x , y)))
                 (main-inl (α (suc n') (x , ptSn n')))
      main-push x y = ΣPathP (fst (q x y) , hₙ₊₁-coh∞ x y (q x y))

      hₙ₊₁ : (c : fst C (fst (fsuc n)))
        → Σ[ ϕ ∈ (cell-hom (fsuc n) c) ]
            Square (h∞ (fsuc n) c)
            (cong incl ϕ)
            (push (f (fsuc n) c))
            (push (g (fsuc n) c))
      hₙ₊₁ = CWskel-elim' C n' main-inl main-push

      hₙ₊₁-coh-pre : (c : fst C (suc n')) →
        Square (cong (CW↪ D (suc (suc n'))) (ind c .fst))
               (hₙ₊₁-inl c)
               (cong (CW↪ D (suc (suc n'))) (f-hom n c))
               (cong (CW↪ D (suc (suc n'))) (g-hom n c))
      hₙ₊₁-coh-pre c i j = CW↪ D (suc (suc n')) (hₙ'-filler c i j)

      hₙ₊₁-coh : (c : fst C (suc n')) →
        Square (cong (CW↪ D (suc (suc n'))) (ind c .fst))
               (hₙ₊₁ (CW↪ C (suc n') c) .fst)
               (cong (CW↪ D (suc (suc n'))) (f-hom n c))
               (cong (CW↪ D (suc (suc n'))) (g-hom n c))
      hₙ₊₁-coh c = hₙ₊₁-coh-pre c
        ▷ λ i → CWskel-elim'-inl C n'
                  {B = λ c → Σ[ ϕ ∈ cell-hom (fsuc n) c ]
                    Square (h∞ (fsuc n) c)  (cong incl ϕ)
                      (push (f (fsuc n) c)) (push (g (fsuc n) c))}
                  main-inl main-push c (~ i) .fst

-- converting the above to something on the right form
private
  pathToCellularHomotopy-main :
    {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ) (f-c g-c : finCellMap m C D)
    (h∞' : FinSeqColim→Colim m ∘ finCellMap→FinSeqColim C D f-c
         ≡ FinSeqColim→Colim m ∘ finCellMap→FinSeqColim C D g-c)
    → ∥ finCellHomRel m f-c g-c (approx.h∞ m f-c g-c h∞') ∥₁
  pathToCellularHomotopy-main {C = C} zero f-c g-c h∞' =
    ∣ fincellhom (λ {(zero , p) x → ⊥.rec (CW₀-empty C x)})
                (λ { (zero , p) x → ⊥.rec (CW₀-empty C x)})
   , (λ { (zero , p) x → ⊥.rec (CW₀-empty C x)}) ∣₁
  pathToCellularHomotopy-main {C = C} {D = D} (suc zero) f-c g-c h∞' =
    PT.map (λ {(d , h)
      → (fincellhom (λ {(zero , p) x → ⊥.rec (CW₀-empty C x)
                       ; (suc zero , p) → d})
                     λ {(zero , p) → λ x → ⊥.rec (CW₀-empty C x)})
       , (λ {(zero , p) x → ⊥.rec (CW₀-empty C x)
           ; (suc zero , tt) → h})})
           (invEq (_ , satAC∃Fin-C0 C _ _) k)
    where
    k : (c : _) → _
    k c = (approx.pathToCellularHomotopy₁ (suc zero) f-c g-c
                   h∞' tt c)
  pathToCellularHomotopy-main {C = C} {D = D} (suc (suc m)) f-c g-c h∞' =
    PT.rec squash₁
      (λ ind → PT.map
        (λ {(f , p)
          → (fincellhom (main-hom ind f p)
                         (main-coh ind f p))
           , (∞coh ind f p)})
        (pathToCellularHomotopy-ind flast
          λ c → (finCellHom.fhom (ind .fst) flast c)
              , (ind .snd flast c)))
      (pathToCellularHomotopy-main {C = C} {D = D} (suc m)
            (finCellMap↓ f-c)
            (finCellMap↓ g-c)
            h')
    where
    open approx _ f-c g-c h∞'
    finSeqColim↑ : ∀ {ℓ} {X : Sequence ℓ} {m : ℕ}
      → FinSeqColim m X → FinSeqColim (suc m) X
    finSeqColim↑ (fincl n x) = fincl (injectSuc n) x
    finSeqColim↑ {m = suc m} (fpush n x i) = fpush (injectSuc n) x i

    h' : FinSeqColim→Colim (suc m) ∘
        finCellMap→FinSeqColim C D (finCellMap↓ f-c)
        ≡
        FinSeqColim→Colim (suc m) ∘
        finCellMap→FinSeqColim C D (finCellMap↓ g-c)
    h' = funExt λ { (fincl n x) j → h∞' j (fincl (injectSuc n) x)
                  ; (fpush n x i) j → h∞' j (fpush (injectSuc n) x i)}

    open SeqHomotopyTypes

    module _
      (ind : finCellHomRel (suc m)
              (finCellMap↓ f-c) (finCellMap↓ g-c)
                ((approx.h∞ (suc m) (finCellMap↓ f-c) (finCellMap↓ g-c) h')))
      (f : (c : fst C (suc (suc m))) →
          Σ[ h ∈ (cell-hom (suc (suc m)) f-c g-c flast c) ]
          (Square (h∞ flast c) (cong incl h)
             (push (fmap f-c flast c)) (push (fmap g-c flast c))))
      (fp : (c : fst C (suc m)) →
        cell-hom-coh (suc (suc m)) f-c g-c flast c
        (finCellHom.fhom (ind .fst) flast c)
        (f (CW↪ C (suc m) c) .fst)) where

      main-hom-typ : (n : Fin (suc (suc (suc m))))
        → Type _
      main-hom-typ n =
        (x : C .fst (fst n))
          → CW↪ D (fst n) (f-c .fmap n x)
           ≡ CW↪ D (fst n) (g-c .fmap n x)

      main-hom : (n : Fin (suc (suc (suc m)))) → main-hom-typ n
      main-hom = elimFin (fst ∘ f) (finCellHom.fhom (fst ind))

      main-homβ = elimFinβ {A = main-hom-typ} (fst ∘ f)
                   (finCellHom.fhom (fst ind))

      main-coh : (n : Fin (suc (suc m))) (c : C .fst (fst n))
        → Square
          (cong (CW↪ D (suc (fst n)))
           (main-hom (injectSuc n) c))
          (main-hom (fsuc n)
           (CW↪ C (fst n) c))
          (cong (CW↪ D (suc (fst n))) (fcomm f-c n c))
          (cong (CW↪ D (suc (fst n))) (fcomm g-c n c))
      main-coh =
        elimFin
          (λ c → cong (cong (CW↪ D (suc (suc m))))
                       (funExt⁻ (main-homβ .snd flast) c)
                ◁ fp c
                ▷ sym (funExt⁻ (main-homβ .fst) (CW↪ C (suc m) c)))
          λ n c
           → cong (cong (CW↪ D (suc (fst n))))
               (funExt⁻ (main-homβ .snd (injectSuc n)) c)
            ◁ finCellHom.fcoh (fst ind) n c
            ▷ sym (funExt⁻ (main-homβ .snd (fsuc n)) (CW↪ C (fst n) c))

      ∞coh : (n : Fin (suc (suc (suc m)))) (x : fst C (fst n))
          → Square (h∞ n x) (λ i → incl (main-hom n x i))
                    (push (f-c .fmap n x)) (push (g-c .fmap n x))
      ∞coh = elimFin
        (λ c → f c .snd ▷ λ i j → incl (main-homβ .fst (~ i) c j))
        λ n c → ind .snd n c ▷ λ i j → incl (main-homβ .snd n (~ i) c j)

-- second main theorem
pathToCellularHomotopy :
  {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ) (f-c g-c : finCellMap m C D)
  → ((x : fst C m) → Path (realise D) (incl (fmap f-c flast x))
                                        (incl (fmap g-c flast x)))
  → ∥ finCellHom m f-c g-c ∥₁
pathToCellularHomotopy {C} {D} m f-c g-c h =
  PT.map fst
    (pathToCellularHomotopy-main m f-c g-c
      (→FinSeqColimHomotopy _ _ h))
