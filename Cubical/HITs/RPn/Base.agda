{-

   A defintion of the real projective spaces following:

   [BR17] U. Buchholtz, E. Rijke, The real projective spaces in homotopy type theory.
           (2017) https://arxiv.org/abs/1704.05770

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.RPn.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Bundle

open import Cubical.Foundations.SIP
open import Cubical.Structures.Pointed
open import Cubical.Structures.TypeEqvTo

open import Cubical.Data.Bool
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥ hiding (elim)
open import Cubical.Data.Sum as ⊎ hiding (elim)

open import Cubical.HITs.PropositionalTruncation as PropTrunc hiding (elim)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Pushout.Flattening

private
  variable
    ℓ ℓ' ℓ'' : Level

-- Definition II.1 in [BR17], see also Cubical.Functions.Bundle

2-EltType₀    = TypeEqvTo    ℓ-zero Bool -- Σ[ X ∈ Type₀ ] ∥ X ≃ Bool ∥
2-EltPointed₀ = PointedEqvTo ℓ-zero Bool -- Σ[ X ∈ Type₀ ] X × ∥ X ≃ Bool ∥

Bool* : 2-EltType₀
Bool* = Bool , ∣ idEquiv _ ∣


-- Our first goal is to 'lift' `_⊕_ : Bool → Bool ≃ Bool` to a function `_⊕_ : A → A ≃ Bool`
--  for any 2-element type (A, ∣e∣).

-- `isContr-BoolPointedIso` and `isContr-2-EltPointed-iso` are contained in the proof
--  of Lemma II.2 in [BR17], though we prove `isContr-BoolPointedIso` more directly
--  with ⊕ -- [BR17] proves it for just the x = false case and uses notEquiv to get
--  the x = true case.

-- (λ y → x ⊕ y) is the unqiue pointed isomorphism (Bool , false) ≃ (Bool , x)
isContr-BoolPointedIso : ∀ x → isContr ((Bool , false) ≃[ pointed-iso ] (Bool , x))
fst (isContr-BoolPointedIso x) = ((λ y → x ⊕ y) , isEquiv-⊕ x) , ⊕-comm x false
snd (isContr-BoolPointedIso x) (e , p)
  = Σ≡Prop (λ e → isSetBool (equivFun e false) x)
           (Σ≡Prop isPropIsEquiv (funExt λ { false → ⊕-comm x false ∙ sym p
                                           ; true  → ⊕-comm x true  ∙ sym q }))
  where q : e .fst true ≡ not x
        q with dichotomyBool (invEq e (not x))
        ... | inl q = invEq≡→equivFun≡ e q
        ... | inr q = ⊥.rec (not≢const x (sym (invEq≡→equivFun≡ e q) ∙ p))

-- Since isContr is a mere proposition, we can eliminate a witness ∣e∣ : ∥ X ≃ Bool ∥ to get
--  that there is therefore a unique pointed isomorphism (Bool , false) ≃ (X , x) for any
--  2-element pointed type (X , x, ∣e∣).
isContr-2-EltPointed-iso : (X∙ : 2-EltPointed₀)
                         → isContr ((Bool , false , ∣ idEquiv Bool ∣) ≃[ PointedEqvTo-iso Bool ] X∙)
isContr-2-EltPointed-iso (X , x , ∣e∣)
  = PropTrunc.rec isPropIsContr
                  (λ e → J (λ X∙ _ → isContr ((Bool , false) ≃[ pointed-iso ] X∙))
                           (isContr-BoolPointedIso (e .fst x))
                           (sym (pointed-sip _ _ (e , refl))))
                  ∣e∣

-- This unique isomorphism must be _⊕_ 'lifted' to X. This idea is alluded to at the end of the
--  proof of Theorem III.4 in [BR17], where the authors reference needing ⊕-comm.
module ⊕* (X : 2-EltType₀) where

  _⊕*_ : typ X → typ X → Bool
  y ⊕* z = invEquiv (fst (fst (isContr-2-EltPointed-iso (fst X , y , snd X)))) .fst z

  -- we've already shown that this map is an equivalence on the right

  isEquivʳ : (y : typ X) → isEquiv (y ⊕*_)
  isEquivʳ y = invEquiv (fst (fst (isContr-2-EltPointed-iso (fst X , y , snd X)))) .snd

  Equivʳ : typ X → typ X ≃ Bool
  Equivʳ y = (y ⊕*_) , isEquivʳ y

  -- any mere proposition that holds for (Bool, _⊕_) holds for (typ X, _⊕*_)
  -- this amounts to just carefully unfolding the PropTrunc.elim and J in isContr-2-EltPointed-iso
  elim : ∀ {ℓ'} (P : (A : Type₀) (_⊕'_ : A → A → Bool) → Type ℓ') (propP : ∀ A _⊕'_ → isProp (P A _⊕'_))
         → P Bool _⊕_ → P (typ X) _⊕*_
  elim {ℓ'} P propP r = PropTrunc.elim {P = λ ∣e∣ → P (typ X) (R₁ ∣e∣)} (λ _ → propP _ _)
                                       (λ e → EquivJ (λ A e → P A (R₂ A e)) r e)
                                       (snd X)
    where R₁ : ∥ fst X ≃ Bool ∥ → typ X → typ X → Bool
          R₁ ∣e∣ y = invEq (fst (fst (isContr-2-EltPointed-iso (fst X , y , ∣e∣))))
          R₂ : (B : Type₀) → B ≃ Bool → B → B → Bool
          R₂ A e y = invEq (fst (fst (J (λ A∙ _ → isContr ((Bool , false) ≃[ pointed-iso ] A∙))
                                        (isContr-BoolPointedIso (e .fst y))
                                        (sym (pointed-sip (A , y) (Bool , e .fst y) (e , refl))))))

  -- as a consequence, we get that ⊕* is commutative, and is therefore also an equivalence on the left

  comm : (y z : typ X) → y ⊕* z ≡ z ⊕* y
  comm = elim (λ A _⊕'_ → (x y : A) → x ⊕' y ≡ y ⊕' x)
              (λ _ _ → isPropΠ2 (λ _ _ → isSetBool _ _))
              ⊕-comm

  isEquivˡ : (y : typ X) → isEquiv (_⊕* y)
  isEquivˡ y = subst isEquiv (funExt (λ z → comm y z)) (isEquivʳ y)

  Equivˡ : typ X → typ X ≃ Bool
  Equivˡ y = (_⊕* y) , isEquivˡ y

-- Lemma II.2 in [BR17], though we do not use it here
-- Note: Lemma II.3 is `pointed-sip`, used in `PointedEqvTo-sip`
isContr-2-EltPointed : isContr (2-EltPointed₀)
fst isContr-2-EltPointed = (Bool , false , ∣ idEquiv Bool ∣)
snd isContr-2-EltPointed A∙ = PointedEqvTo-sip Bool _ A∙ (fst (isContr-2-EltPointed-iso A∙))


--------------------------------------------------------------------------------

-- Now we mutually define RP n and its double cover (Definition III.1 in [BR17]),
--  and show that the total space of this double cover is S n (Theorem III.4).

RP  : ℕ₋₁ → Type₀
cov⁻¹ : (n : ℕ₋₁) → RP n → 2-EltType₀ -- (see Cubical.Functions.Bundle)

RP neg1 = ⊥
RP (ℕ→ℕ₋₁ n) = Pushout (pr (cov⁻¹ (-1+ n))) (λ _ → tt)
{-
                         tt
   Total (cov⁻¹ (n-1)) — — — > Unit
            |                    ∙
        pr  |                    ∙  inr
            |                    ∙
            V                    V
        RP (n-1) ∙ ∙ ∙ ∙ ∙ ∙ > RP n := Pushout pr (const tt)
                      inl
-}

cov⁻¹ neg1 x = Bool*
cov⁻¹ (ℕ→ℕ₋₁ n) (inl x)          = cov⁻¹ (-1+ n) x
cov⁻¹ (ℕ→ℕ₋₁ n) (inr _)          = Bool*
cov⁻¹ (ℕ→ℕ₋₁ n) (push (x , y) i) = ua ((λ z → y ⊕* z) , ⊕*.isEquivʳ (cov⁻¹ (-1+ n) x) y) i , ∣p∣ i
  where open ⊕* (cov⁻¹ (-1+ n) x)
        ∣p∣ = isProp→PathP (λ i → squash {A = ua (⊕*.Equivʳ (cov⁻¹ (-1+ n) x) y) i ≃ Bool})
                           (str (cov⁻¹ (-1+ n) x)) (∣ idEquiv _ ∣)
{-
                         tt
   Total (cov⁻¹ (n-1)) — — — > Unit
            |                    |
        pr  |     // ua α //     | Bool
            |                    |
            V                    V
        RP (n-1) - - - - - - > Type
                  cov⁻¹ (n-1)

   where α : ∀ (x : Total (cov⁻¹ (n-1))) → cov⁻¹ (n-1) (pr x) ≃ Bool
         α (x , y) = (λ z → y ⊕* z) , ⊕*.isEquivʳ y
-}

TotalCov≃Sn : ∀ n → Total (cov⁻¹ n) ≃ S n
TotalCov≃Sn neg1 = isoToEquiv (iso (λ { () }) (λ { () }) (λ { () }) (λ { () }))
TotalCov≃Sn (ℕ→ℕ₋₁ n) =
  Total (cov⁻¹ (ℕ→ℕ₋₁ n))           ≃⟨ i ⟩
  Pushout Σf Σg                      ≃⟨ ii ⟩
  join (Total (cov⁻¹ (-1+ n))) Bool  ≃⟨ iii ⟩
  S (ℕ→ℕ₋₁ n)                       ■
  where
{-
    (i) First we want to show that `Total (cov⁻¹ (ℕ→ℕ₋₁ n))` is equivalent to a pushout.
    We do this using the flattening lemma, which states:

    Given f,g,F,G,e such that the following square commutes:

             g
       A — — — — > C                 Define:   E : Pushout f g → Type
       |           |                           E (inl b) = F b
    f  |   ua e    |  G                        E (inr c) = G c
       V           V                           E (push a i) = ua (e a) i
       B — — — — > Type
             F

    Then, the total space `Σ (Pushout f g) E` is the following pushout:

                                Σg := (g , e a)
            Σ[ a ∈ A ] F (f a) — — — — — — — — > Σ[ c ∈ C ] G c
                   |                                ∙
    Σf := (f , id) |                                ∙
                   V                                V
            Σ[ b ∈ B ] F b ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ > Σ (Pushout f g) E

    In our case, setting `f = pr (cov⁻¹ (n-1))`, `g = λ _ → tt`, `F = cov⁻¹ (n-1)`, `G = λ _ → Bool`,
     and `e = λ (x , y) → ⊕*.Equivʳ (cov⁻¹ (n-1) x) y` makes E equal (up to funExt) to `cov⁻¹ n`.

    Thus the flattening lemma gives us that `Total (cov⁻¹ n) ≃ Pushout Σf Σg`.
-}
    open FlatteningLemma {- f = -} (λ x → pr (cov⁻¹ (-1+ n)) x)  {- g = -} (λ _ → tt)
                         {- F = -} (λ x → typ (cov⁻¹ (-1+ n) x)) {- G = -} (λ _ → Bool)
                         {- e = -} (λ { (x , y) → ⊕*.Equivʳ (cov⁻¹ (-1+ n) x) y })
                         hiding (Σf ; Σg)

    cov⁻¹≃E : ∀ x → typ (cov⁻¹ (ℕ→ℕ₋₁ n) x) ≃ E x
    cov⁻¹≃E (inl x) = idEquiv _
    cov⁻¹≃E (inr x) = idEquiv _
    cov⁻¹≃E (push a i) = idEquiv _

    -- for easier reference, we copy these definitons here
    Σf : Σ[ x ∈ Total (cov⁻¹ (-1+ n)) ] typ (cov⁻¹ (-1+ n) (fst x)) → Total (cov⁻¹ (-1+ n))
    Σg : Σ[ x ∈ Total (cov⁻¹ (-1+ n)) ] typ (cov⁻¹ (-1+ n) (fst x)) → Unit × Bool
    Σf ((x , y) , z) = (x , z)       -- ≡ (f a , x)
    Σg ((x , y) , z) = (tt , y ⊕* z) -- ≡ (g a , (e a) .fst x)
      where open ⊕* (cov⁻¹ (-1+ n) x)

    i : Total (cov⁻¹ (ℕ→ℕ₋₁ n)) ≃ Pushout Σf Σg
    i = (Σ[ x ∈ RP (ℕ→ℕ₋₁ n) ] typ (cov⁻¹ (ℕ→ℕ₋₁ n) x)) ≃⟨ Σ-cong-equiv-snd cov⁻¹≃E ⟩
        (Σ[ x ∈ RP (ℕ→ℕ₋₁ n) ] E x)                     ≃⟨ flatten ⟩
        Pushout Σf Σg                                   ■
{-
    (ii) Next we want to show that `Pushout Σf Σg` is equivalent to `join (Total (cov⁻¹ (n-1))) Bool`.
    Since both are pushouts, this can be done by defining a diagram equivalence:

                          Σf                                                  Σg
    Total (cov⁻¹ (n-1)) < — — Σ[ x ∈ Total (cov⁻¹ (n-1)) ] cov⁻¹ (n-1) (pr x) — — > Unit × Bool
            |                                        ∙                                   |
        id  |≃                                    u  ∙≃                             snd  |≃
            V                                        V                                   V
    Total (cov⁻¹ (n-1)) < — — — — — — — Total (cov⁻¹ (n-1)) × Bool — — — — — — — — — > Bool
                              proj₁                                      proj₂

    where the equivalence u above must therefore satisfy: `u .fst x ≡ (Σf x , snd (Σg x))`
    Unfolding this, we get: `u .fst ((x , y) , z) ≡ ((x , z) , (y ⊕* z))`

    It suffices to show that the map y ↦ y ⊕* z is an equivalence, since we can then express u as
     the following composition of equivalences:
    ((x , y) , z) ↦ (x , (y , z)) ↦ (x , (z , y)) ↦ (x , (z , y ⊕* z)) ↦ ((x , z) , y ⊕* z)

    This was proved above by ⊕*.isEquivˡ.
-}
    u : ∀ {n} → (Σ[ x ∈ Total (cov⁻¹ n) ] typ (cov⁻¹ n (fst x))) ≃ (Total (cov⁻¹ n) × Bool)
    u {n} = Σ[ x ∈ Total (cov⁻¹ n) ] typ (cov⁻¹ n (fst x))      ≃⟨ Σ-assoc ⟩
            Σ[ x ∈ RP n ] (typ (cov⁻¹ n x)) × (typ (cov⁻¹ n x)) ≃⟨ Σ-cong-equiv-snd (λ x → swapΣEquiv) ⟩
            Σ[ x ∈ RP n ] (typ (cov⁻¹ n x)) × (typ (cov⁻¹ n x)) ≃⟨ Σ-cong-equiv-snd
                                                                   (λ x → Σ-cong-equiv-snd
                                                                     (λ y → ⊕*.Equivˡ (cov⁻¹ n x) y)) ⟩
            Σ[ x ∈ RP n ] (typ (cov⁻¹ n x)) × Bool              ≃⟨ invEquiv Σ-assoc ⟩
            Total (cov⁻¹ n) × Bool                              ■

    H : ∀ x → u .fst x ≡ (Σf x , snd (Σg x))
    H x = refl

    nat : 3-span-equiv (3span Σf Σg) (3span {A2 = Total (cov⁻¹ (-1+ n)) × Bool} fst snd)
    nat = record { e0 = idEquiv _ ; e2 = u ; e4 = ΣUnit _
                 ; H1 = λ x → cong fst (H x)
                 ; H3 = λ x → cong snd (H x) }

    ii : Pushout Σf Σg ≃ join (Total (cov⁻¹ (-1+ n))) Bool
    ii = compEquiv (pathToEquiv (spanEquivToPushoutPath nat)) (joinPushout≃join _ _)

{-
    (iii) Finally, it's trivial to show that `join (Total (cov⁻¹ (n-1))) Bool` is equivalent to
     `Susp (Total (cov⁻¹ (n-1)))`. Induction then gives us that `Susp (Total (cov⁻¹ (n-1)))`
     is equivalent to `S n`, which completes the proof.
-}

    iii : join (Total (cov⁻¹ (-1+ n))) Bool ≃ S (ℕ→ℕ₋₁ n)
    iii = join (Total (cov⁻¹ (-1+ n))) Bool ≃⟨ invEquiv Susp≃joinBool ⟩
          Susp (Total (cov⁻¹ (-1+ n)))      ≃⟨ congSuspEquiv (TotalCov≃Sn (-1+ n)) ⟩
          S (ℕ→ℕ₋₁ n)                      ■

-- the usual covering map S n → RP n, with fibers exactly cov⁻¹

cov : (n : ℕ₋₁) → S n → RP n
cov n = pr (cov⁻¹ n) ∘ invEq (TotalCov≃Sn n)

fibcov≡cov⁻¹ : ∀ n (x : RP n) → fiber (cov n) x ≡ cov⁻¹ n x .fst
fibcov≡cov⁻¹ n x =
  fiber (cov n)        x ≡[ i ]⟨ fiber {A = ua e i} (pr (cov⁻¹ n) ∘ ua-unglue e i) x ⟩
  fiber (pr (cov⁻¹ n)) x ≡⟨ ua (fibPrEquiv (cov⁻¹ n) x) ⟩
  cov⁻¹ n x .fst         ∎
  where e = invEquiv (TotalCov≃Sn n)


--------------------------------------------------------------------------------

-- Finally, we state the trivial equivalences for RP 0 and RP 1 (Example III.3 in [BR17])

RP0≃Unit : RP 0 ≃ Unit
RP0≃Unit = isoToEquiv (iso (λ _ → tt) (λ _ → inr tt) (λ _ → refl) (λ { (inr tt) → refl }))

RP1≡S1 : RP 1 ≡ S 1
RP1≡S1 = Pushout {A = Total (cov⁻¹ 0)} {B = RP 0} (pr (cov⁻¹ 0)) (λ _ → tt) ≡⟨ i ⟩
         Pushout {A = Total (cov⁻¹ 0)} {B = Unit} (λ _ → tt)     (λ _ → tt) ≡⟨ ii ⟩
         Pushout {A = S 0}             {B = Unit} (λ _ → tt)     (λ _ → tt) ≡⟨ PushoutSusp≡Susp ⟩
         S 1                                                                ∎
  where i = λ i → Pushout {A = Total (cov⁻¹ 0)}
                          {B = ua RP0≃Unit i}
                          (λ x → ua-gluePt RP0≃Unit i (pr (cov⁻¹ 0) x))
                          (λ _ → tt)
        ii = λ j → Pushout {A = ua (TotalCov≃Sn 0) j} (λ _ → tt) (λ _ → tt)
