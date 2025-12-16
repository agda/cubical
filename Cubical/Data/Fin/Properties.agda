module Cubical.Data.Fin.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥∥rec) hiding (elimFin)

open import Cubical.Data.Fin.Base as Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.FinData.Base renaming (Fin to FinData) hiding (¬Fin0 ; toℕ ; predFin)

open import Cubical.Relation.Nullary

open import Cubical.Induction.WellFounded

open import Cubical.Algebra.AbGroup.Base

private
 variable
   a b ℓ : Level
   n : ℕ
   A : Type a

-- Fin 0 is empty, and thus a proposition.
isPropFin0 : isProp (Fin 0)
isPropFin0 = Empty.rec ∘ ¬Fin0

isPropFin1 : isProp (Fin 1)
isPropFin1 (zero , tt) (zero , tt) = refl

-- Fin 1 has only one value.
isContrFin1 : isContr (Fin 1)
isContrFin1
  = fzero , λ
  { (zero , _) → toℕ-injective {k = 1} refl
  ; (suc k , sk<1) → Empty.rec sk<1
  }

Unit≃Fin1 : Unit ≃ Fin 1
Unit≃Fin1 =
  isoToEquiv
    (iso
      (const fzero)
      (const tt)
      (isContrFin1 .snd)
      (isContrUnit .snd)
    )

-- Regardless of k, Fin k is a set.
isSetFin : ∀{k} → isSet (Fin k)
isSetFin {k} = isSetΣ isSetℕ (λ x → isProp→isSet (isProp<ᵗ {x} {k}))

discreteFin : ∀ {n} → Discrete (Fin n)
discreteFin {n} (x , hx) (y , hy) with discreteℕ x y
... | yes prf = yes (Σ≡Prop (λ z → isProp<ᵗ {z} {n}) prf)
... | no prf = no λ h → prf (cong fst h)

inject<-ne : ∀ {n} (i : Fin n) → ¬ injectSuc i ≡ flast {k = n}
inject<-ne {n} (k , k<nᵗ) p = <→≢ (<ᵗ→< k<nᵗ) (cong fst p)

Fin-fst-≡ : ∀ {n} {i j : Fin n} → fst i ≡ fst j → i ≡ j
Fin-fst-≡ {n} = Σ≡Prop (λ x → isProp<ᵗ {x} {n})

private
  subst-app : (B : A → Type b) (f : (x : A) → B x) {x y : A} (x≡y : x ≡ y) →
              subst B x≡y (f x) ≡ f y
  subst-app B f {x = x} =
    J (λ y e → subst B e (f x) ≡ f y) (substRefl {B = B} (f x))

-- Computation rules for the eliminator.
module _ (P  : (k : ℕ) → Fin k → Type ℓ)
         (fz : ∀ {k} → P (suc k) fzero)
         (fs : ∀ {k} {fn : Fin k} → P k fn → P (suc k) (fsuc fn))
         {k : ℕ} where

  elim-fzero : Fin.elim P fz fs {k = suc k} fzero ≡ fz {k}
  elim-fzero =
    let B = (λ z → P (suc k) z) in
    subst B (toℕ-injective {suc k} refl) (fz {k})
      ≡⟨ cong (λ p → subst B p (fz {k})) (isSetFin {suc k} _ _ _ _) ⟩
    subst B refl (fz {k})
      ≡⟨ substRefl {B = B} (fz {k}) ⟩
    fz {k} ∎

  elim-fsuc : (fk : Fin k) → Fin.elim P fz fs (fsuc fk) ≡ fs (Fin.elim P fz fs fk)
  elim-fsuc fk =
    let B = (λ z → P (suc k) z) in
    subst B (toℕ-injective {suc k} refl) (fs (Fin.elim P fz fs fk))
      ≡⟨ cong (λ p → subst B p (fs (Fin.elim P fz fs fk))) (isSetFin {suc k} _ _ _ _) ⟩
    subst B refl (fs (Fin.elim P fz fs fk))
      ≡⟨ substRefl {B = B} (fs (Fin.elim P fz fs fk)) ⟩
    fs (Fin.elim P fz fs fk) ∎

-- Helper function for the reduction procedure below.
--
-- If n = expand o k m, then n is congruent to m modulo k.
expand : ℕ → ℕ → ℕ → ℕ
expand 0 k m = m
expand (suc o) k m = k + expand o k m

expand≡ : ∀ k m o → expand o k m ≡ o · k + m
expand≡ k m zero = refl
expand≡ k m (suc o)
  = cong (k +_) (expand≡ k m o) ∙ +-assoc k (o · k) m

-- Expand a pair. This is useful because the whole function is
-- injective.
expand× : ∀{k} → (Fin k × ℕ) → ℕ
expand× {k} (f , o) = expand o k (toℕ {k} f)

private
  lemma₀ : ∀{k m n r} → r ≡ n → k + m ≡ n → k ≤ r
  lemma₀ {k = k} {m} p q = m , +-comm m k ∙ q ∙ sym p

  expand×Inj : ∀ k → {t1 t2 : Fin (suc k) × ℕ} → expand× {suc k} t1 ≡ expand× {suc k} t2 → t1 ≡ t2
  expand×Inj k {f1 , zero} {f2 , zero} p i
    = toℕ-injective {suc k} {fj = f1} {f2} p i , zero
  expand×Inj k {f1 , suc o1} {(r , r<sk) , zero} p
    = Empty.rec (<ᵗ-asym {r} {suc k} r<sk (lemma₀ refl p))
  expand×Inj k {(r , r<sk) , zero} {f2 , suc o2} p
    = Empty.rec (<ᵗ-asym {r} {suc k} r<sk (lemma₀ refl (sym p)))
  expand×Inj k {f1 , suc o1} {f2 , suc o2}
    = cong (λ { (f , o) → (f , suc o) })
    ∘ expand×Inj k {f1 , o1} {f2 , o2}
    ∘ inj-m+ {suc k}

  expand×Emb : ∀ k → isEmbedding (expand× {k})
  expand×Emb 0 = Empty.rec ∘ ¬Fin0 ∘ fst
  expand×Emb (suc k)
    = injEmbedding isSetℕ (expand×Inj k)

-- A Residue is a family of types representing evidence that a
-- natural is congruent to a value of a finite type.
Residue : ℕ → ℕ → Type₀
Residue k n = Σ[ tup ∈ Fin k × ℕ ] expand× {k} tup ≡ n

-- There is at most one canonical finite value congruent to each
-- natural.
isPropResidue : ∀ k n → isProp (Residue k n)
isPropResidue k = isEmbedding→hasPropFibers (expand×Emb k)

-- A value of a finite type is its own residue.
Fin→Residue : ∀{k} → (f : Fin k) → Residue k (toℕ {k} f)
Fin→Residue f = (f , 0) , refl

-- Fibers of numbers that differ by k are equivalent in a more obvious
-- way than via the fact that they are propositions.
Residue+k : (k n : ℕ) → Residue k n → Residue k (k + n)
Residue+k k n ((f , o) , p) = (f , suc o) , cong (k +_) p

Residue-k : (k n : ℕ) → Residue k (k + n) → Residue k n
Residue-k k n (((r , r<k) , zero) , p) = Empty.rec (<ᵗ-asym {r} {k} r<k (lemma₀ p refl))
Residue-k k n ((f , suc o) , p) = ((f , o) , inj-m+ p)

Residue+k-k
  : (k n : ℕ)
  → (R : Residue k (k + n))
  → Residue+k k n (Residue-k k n R) ≡ R
Residue+k-k k n (((r , r<k) , zero) , p) = Empty.rec (<ᵗ-asym {r} {k} r<k (lemma₀ p refl))
Residue+k-k k n ((f , suc o) , p)
  = Σ≡Prop (λ tup → isSetℕ (expand× {k} tup) (k + n)) refl

Residue-k+k
  : (k n : ℕ)
  → (R : Residue k n)
  → Residue-k k n (Residue+k k n R) ≡ R
Residue-k+k k n ((f , o) , p)
  = Σ≡Prop (λ tup → isSetℕ (expand× {k} tup) n) refl

private
  Residue≃ : ∀ k n → Residue k n ≃ Residue k (k + n)
  Residue≃ k n
    = Residue+k k n
    , isoToIsEquiv (iso (Residue+k k n) (Residue-k k n)
                        (Residue+k-k k n) (Residue-k+k k n))

Residue≡ : ∀ k n → Residue k n ≡ Residue k (k + n)
Residue≡ k n = ua (Residue≃ k n)

-- For positive `k`, all `n` have a canonical residue mod `k`.
module Reduce (k₀ : ℕ) where
  k : ℕ
  k = suc k₀

  base : ∀ n (n<k : n < k) → Residue k n
  base n n<k = Fin→Residue (n , <→<ᵗ n<k)

  step : ∀ n → Residue k n → Residue k (k + n)
  step n = transport (Residue≡ k n)

  reduce : ∀ n → Residue k n
  reduce = +induction k₀ (Residue k) base step

  reduce≡
    : ∀ n → transport (Residue≡ k n) (reduce n) ≡ reduce (k + n)
  reduce≡ n
    = sym (+inductionStep k₀ _ base step n)

  reduceP
    : ∀ n → PathP (λ i → Residue≡ k n i) (reduce n) (reduce (k + n))
  reduceP n = toPathP (reduce≡ n)

open Reduce using (reduce; reduce≡) public

extract : ∀{k n} → Residue k n → Fin k
extract = fst ∘ fst

private
  lemma₅
    : ∀ k n (R : Residue k n)
    →  extract R ≡ extract (transport (Residue≡ k n) R)
  lemma₅ k n = sym ∘ cong extract ∘ uaβ (Residue≃ k n)

-- The residue of n modulo k is the same as the residue of k + n.
extract≡ : ∀ k n → extract (reduce k n) ≡ extract (reduce k (suc k + n))
extract≡ k n
  = lemma₅ (suc k) n (reduce k n) ∙ cong extract (Reduce.reduce≡ k n)

isContrResidue : ∀{k n} → isContr (Residue (suc k) n)
isContrResidue {k} {n} = inhProp→isContr (reduce k n) (isPropResidue (suc k) n)

-- the modulo operator on ℕ

_%_ : ℕ → ℕ → ℕ
n % zero = n
n % (suc k) = toℕ {suc k} (extract (reduce k n))

_/_ : ℕ → ℕ → ℕ
n / zero = zero
n / (suc k) = reduce k n .fst .snd

moddiv : ∀ n k → (n / k) · k + n % k ≡ n
moddiv n zero = refl
moddiv n (suc k) = sym (expand≡ _ _ (n / suc k)) ∙ reduce k n .snd

n%k≡n[modk] : ∀ n k → Σ[ o ∈ ℕ ] o · k + n % k ≡ n
n%k≡n[modk] n k = (n / k) , moddiv n k

n%sk<ᵗsk : (n k : ℕ) → (n % suc k) <ᵗ suc k
n%sk<ᵗsk n k = extract (reduce k n) .snd

fznotfs : ∀ {m : ℕ} {k : Fin m} → ¬ fzero ≡ fsuc k
fznotfs {m} p = subst F p tt
  where
    F : Fin (suc m) → Type₀
    F (zero , _) = Unit
    F (suc _ , _) = ⊥

fsuc-inj : {fj fk : Fin n} → fsuc fj ≡ fsuc fk → fj ≡ fk
fsuc-inj {n} {fj} {fk} = toℕ-injective {n} {fj} {fk} ∘ injSuc ∘ cong (toℕ {k = suc n})

punchOut : ∀ {m} {i j : Fin (suc m)} → (¬ i ≡ j) → Fin m
punchOut {_} {i} {j} p with fsplit i | fsplit j
punchOut {_} {i} {j} p | inl prfi | inl prfj =
  Empty.elim (p (i ≡⟨ sym prfi ⟩ fzero ≡⟨ prfj ⟩ j ∎))
punchOut {_} {i} {j} p | inl prfi | inr (kj , prfj) =
  kj
punchOut {zero} {i} {j} p  | inr (ki , prfi) | inl prfj =
  Empty.elim (p (
    i ≡⟨ sym (isContrFin1 .snd i) ⟩
    c ≡⟨ isContrFin1 .snd j ⟩
    j ∎
  ))
  where c = isContrFin1 .fst
punchOut {suc _} {i} {j} p | inr (ki , prfi) | inl prfj =
  fzero
punchOut {zero} {i} {j} p | inr (ki , prfi) | inr (kj , prfj) =
  Empty.elim ((p (
    i ≡⟨ sym (isContrFin1 .snd i) ⟩
    c ≡⟨ isContrFin1 .snd j ⟩
    j ∎)
  ))
  where c = isContrFin1 .fst
punchOut {suc _} {i} {j} p | inr (ki , prfi) | inr (kj , prfj) =
  fsuc (punchOut {i = ki} {j = kj}
    (λ q → p (i ≡⟨ sym prfi ⟩ fsuc ki ≡⟨ cong fsuc q ⟩ fsuc kj ≡⟨ prfj ⟩ j ∎))
  )

punchOut-inj
  : ∀ {m} {i j k : Fin (suc m)} (i≢j : ¬ i ≡ j) (i≢k : ¬ i ≡ k)
  → punchOut i≢j ≡ punchOut i≢k → j ≡ k
punchOut-inj {_} {i} {j} {k} i≢j i≢k p with fsplit i | fsplit j | fsplit k
punchOut-inj {zero} {i} {j} {k} i≢j i≢k p | _ | _ | _ =
  Empty.elim (i≢j (i ≡⟨ sym (isContrFin1 .snd i) ⟩ c ≡⟨ isContrFin1 .snd j ⟩ j ∎))
    where c = isContrFin1 .fst
punchOut-inj {suc _} {i} {j} {k} i≢j i≢k p | inl prfi | inl prfj | _ =
  Empty.elim (i≢j (i ≡⟨ sym prfi ⟩ fzero ≡⟨ prfj ⟩ j ∎))
punchOut-inj {suc _} {i} {j} {k} i≢j i≢k p | inl prfi | _ | inl prfk =
  Empty.elim (i≢k (i ≡⟨ sym prfi ⟩ fzero ≡⟨ prfk ⟩ k ∎))
punchOut-inj {suc _} {i} {j} {k} i≢j i≢k p | inl prfi | inr (kj , prfj) | inr (kk , prfk) =
  j       ≡⟨ sym prfj ⟩
  fsuc kj ≡⟨ cong fsuc p ⟩
  fsuc kk ≡⟨ prfk ⟩
  k       ∎
punchOut-inj {suc _} {i} {j} {k} i≢j i≢k p | inr (ki , prfi) | inl prfj | inl prfk =
  j     ≡⟨ sym prfj ⟩
  fzero ≡⟨ prfk ⟩
  k     ∎
punchOut-inj {suc _} {i} {j} {k} i≢j i≢k p | inr (ki , prfi) | inr (kj , prfj) | inr (kk , prfk) =
  j ≡⟨ sym prfj ⟩
  fsuc kj ≡⟨ cong fsuc lemma4 ⟩
  fsuc kk ≡⟨ prfk ⟩
  k ∎
  where
    lemma1 = λ q → i≢j (i ≡⟨ sym prfi ⟩ fsuc ki ≡⟨ cong fsuc q ⟩ fsuc kj ≡⟨ prfj ⟩ j ∎)
    lemma2 = λ q → i≢k (i ≡⟨ sym prfi ⟩ fsuc ki ≡⟨ cong fsuc q ⟩ fsuc kk ≡⟨ prfk ⟩ k ∎)
    lemma3 = fsuc-inj p
    lemma4 = punchOut-inj lemma1 lemma2 lemma3
punchOut-inj {suc m} {i} {j} {k} i≢j i≢k p | inr (ki , prfi) | inl prfj | inr (kk , prfk) =
  Empty.rec (fznotfs p)
punchOut-inj {suc _} {i} {j} {k} i≢j i≢k p | inr (ki , prfi) | inr (kj , prfj) | inl prfk =
  Empty.rec (fznotfs (sym p))

pigeonhole-special
  : ∀ {n}
  → (f : Fin (suc n) → Fin n)
  → Σ[ i ∈ Fin (suc n) ] Σ[ j ∈ Fin (suc n) ] (¬ i ≡ j) × (f i ≡ f j)
pigeonhole-special {zero} f = Empty.rec (¬Fin0 (f fzero))
pigeonhole-special {suc n} f =
  proof (any? {n = suc n}
    (λ (i : Fin (suc n)) →
      discreteFin {suc n} (f (injectSuc i)) (f (suc n , <ᵗsucm {n}))
    ))
  where
    proof
      : Dec (Σ (Fin (suc n)) (λ z → f (injectSuc z) ≡ f (suc n , <ᵗsucm {n})))
      → Σ[ i ∈ Fin (suc (suc n)) ] Σ[ j ∈ Fin (suc (suc n)) ] (¬ i ≡ j) × (f i ≡ f j)
    proof (yes (i , prf)) = injectSuc i , (suc n , <ᵗsucm {n}) , inject<-ne i , prf
    proof (no h) =
      let
        g : Fin (suc n) → Fin n
        g k = punchOut
          {i = f (suc n , <ᵗsucm {n})}
          {j = f (injectSuc k)}
          (λ p → h (k , Fin-fst-≡ {suc n} (sym (cong fst p))))
        i , j , i≢j , p = pigeonhole-special g
      in
        injectSuc i
      , injectSuc j
      , (λ q → i≢j (Fin-fst-≡ {suc n} (cong fst q)))
      , punchOut-inj
          {i = f (suc n , <ᵗsucm {n})}
          {j = f (injectSuc i)}
          {k = f (injectSuc j)}
          (λ q → h (i , Fin-fst-≡ {suc n} (sym (cong fst q))))
          (λ q → h (j , Fin-fst-≡ {suc n} (sym (cong fst q))))
          (Fin-fst-≡ {n} (cong fst p))

pigeonhole
  : ∀ {m n}
  → m < n
  → (f : Fin n → Fin m)
  → Σ[ i ∈ Fin n ] Σ[ j ∈ Fin n ] (¬ i ≡ j) × (f i ≡ f j)
pigeonhole {m} {n} (zero , sm≡n) f =
  transport transport-prf (pigeonhole-special f′)
  where
    f′ : Fin (suc m) → Fin m
    f′ = subst (λ h → Fin h → Fin m) (sym sm≡n) f

    f′≡f : PathP (λ i → Fin (sm≡n i) → Fin m) f′ f
    f′≡f i = transport-fillerExt (cong (λ h → Fin h → Fin m) (sym sm≡n)) (~ i) f

    transport-prf
      : (Σ[ i ∈ Fin (suc m) ] Σ[ j ∈ Fin (suc m) ] (¬ i ≡ j) × (f′ i ≡ f′ j))
      ≡ (Σ[ i ∈ Fin n ] Σ[ j ∈ Fin n ] (¬ i ≡ j) × (f i ≡ f j))
    transport-prf φ =
      Σ[ i ∈ Fin (sm≡n φ) ] Σ[ j ∈ Fin (sm≡n φ) ]
        (¬ i ≡ j) × (f′≡f φ i ≡ f′≡f φ j)
pigeonhole {m} {n} (suc k , prf) f =
  let
    g : Fin (suc n′) → Fin n′
    g k = fst (f′ k) , <ᵗ-trans {n = fst (f′ k)} {m = m} {k = n′} (snd (f′ k)) m<n′
    i , j , ¬q , r = pigeonhole-special g
  in transport transport-prf (i , j , ¬q , Σ≡Prop (λ z → isProp<ᵗ {n = z} {m = m}) (cong fst r))
  where
    n′ : ℕ
    n′ = k + suc m

    n≡sn′ : n ≡ suc n′
    n≡sn′ =
      n ≡⟨ sym prf ⟩
      suc (k + suc m) ≡⟨ refl ⟩
      suc n′ ∎

    m<n′ : m <ᵗ n′
    m<n′ = subst (m <ᵗ_) (sym (+-suc k m)) (<ᵗ-+ {n = m} {k = k})

    f′ : Fin (suc n′) → Fin m
    f′ = subst (λ h → Fin h → Fin m) n≡sn′ f

    f′≡f : PathP (λ i → Fin (n≡sn′ (~ i)) → Fin m) f′ f
    f′≡f i = transport-fillerExt (cong (λ h → Fin h → Fin m) n≡sn′) (~ i) f

    transport-prf
      : (Σ[ i ∈ Fin (suc n′) ] Σ[ j ∈ Fin (suc n′) ] (¬ i ≡ j) × (f′ i ≡ f′ j))
      ≡ (Σ[ i ∈ Fin n ] Σ[ j ∈ Fin n ] (¬ i ≡ j) × (f i ≡ f j))
    transport-prf φ =
      Σ[ i ∈ Fin (n≡sn′ (~ φ)) ] Σ[ j ∈ Fin (n≡sn′ (~ φ)) ]
        (¬ i ≡ j) × (f′≡f φ i ≡ f′≡f φ j)

Fin-inj′ : {n m : ℕ} → n < m → ¬ Fin m ≡ Fin n
Fin-inj′ n<m p =
  let
    i , j , i≢j , q = pigeonhole n<m (transport p)
  in i≢j (
    i ≡⟨ refl ⟩
    fst (pigeonhole n<m (transport p)) ≡⟨ transport-p-inj {p = p} q ⟩
    fst (snd (pigeonhole n<m (transport p))) ≡⟨ refl ⟩
    j ∎
  )
  where
    transport-p-inj
      : ∀ {A B : Type ℓ} {x y : A} {p : A ≡ B}
      → transport p x ≡ transport p y
      → x ≡ y
    transport-p-inj {x = x} {y = y} {p = p} q =
      x ≡⟨ sym (transport⁻Transport p x) ⟩
      transport (sym p) (transport p x) ≡⟨ cong (transport (sym p)) q ⟩
      transport (sym p) (transport p y) ≡⟨ transport⁻Transport p y ⟩
      y ∎

Fin-inj : (n m : ℕ) → Fin n ≡ Fin m → n ≡ m
Fin-inj n m p with n ≟ m
... | eq prf = prf
... | lt n<m = Empty.rec (Fin-inj′ n<m (sym p))
... | gt n>m = Empty.rec (Fin-inj′ n>m p)

≤-·sk-cancel : ∀ {m} {k} {n} → m · suc k ≤ n · suc k → m ≤ n
≤-·sk-cancel {m} {k} {n} (d , p) = o , inj-·sm {m = k} goal where
  r = d % suc k
  o = d / suc k
  resn·k : Residue (suc k) (n · suc k)
  resn·k = ((r , n%sk<ᵗsk d k) , (o + m)) , reason where
   reason = expand× ((r , n%sk<ᵗsk d k) , o + m) ≡⟨ expand≡ (suc k) r (o + m) ⟩
            (o + m) · suc k + r                 ≡[ i ]⟨ +-comm (·-distribʳ o m (suc k) (~ i)) r i ⟩
            r + (o · suc k + m · suc k)         ≡⟨ +-assoc r (o · suc k) (m · suc k) ⟩
            (r + o · suc k) + m · suc k         ≡⟨ cong (_+ m · suc k) (+-comm r (o · suc k) ∙ moddiv d (suc k)) ⟩
            d + m · suc k                       ≡⟨ p ⟩
            n · suc k ∎

  residuek·n : ∀ k n → (r : Residue (suc k) (n · suc k)) → ((fzero , n) , expand≡ (suc k) 0 n ∙ +-zero _) ≡ r
  residuek·n _ _ = isContr→isProp isContrResidue _

  r≡0 : r ≡ 0
  r≡0 = cong (toℕ {suc k} ∘ extract) (sym (residuek·n k n resn·k))
  d≡o·sk : d ≡ o · suc k
  d≡o·sk = sym (moddiv d (suc k)) ∙∙ cong (o · suc k +_) r≡0 ∙∙ +-zero _
  goal : (o + m) · suc k ≡ n · suc k
  goal = sym (·-distribʳ o m (suc k)) ∙∙ cong (_+ m · suc k) (sym d≡o·sk) ∙∙ p

<-·sk-cancel : ∀ {m} {k} {n} → m · suc k < n · suc k → m < n
<-·sk-cancel {m} {k} {n} p = goal where
  ≤-helper : m ≤ n
  ≤-helper = ≤-·sk-cancel (pred-≤-pred (<≤-trans p (≤-suc ≤-refl)))
  goal : m < n
  goal = case <-split (suc-≤-suc ≤-helper) of λ
    { (inl g) → g
    ; (inr e) → Empty.rec (¬m<m (subst (λ m → m · suc k < n · suc k) e p))
    }

factorEquiv : ∀ {n} {m} → Fin n × Fin m ≃ Fin (n · m)
factorEquiv {zero} {m} = uninhabEquiv (¬Fin0 ∘ fst) ¬Fin0
factorEquiv {suc n} {m} = intro , isEmbedding×isSurjection→isEquiv (isEmbeddingIntro , isSurjectionIntro) where
  intro : Fin (suc n) × Fin m → Fin (suc n · m)
  intro (nn , mm) = nm , nm<ᵗn·m where
    nm : ℕ
    nm = expand× {suc n} (nn , toℕ {m} mm)
    nn< : toℕ {k = suc n} nn < suc n
    nn< = <ᵗ→< (snd nn)
    mm<m : toℕ {k = m} mm < m
    mm<m = <ᵗ→< (snd mm)
    nm<n·m : toℕ {k = m} mm · suc n + toℕ {k = suc n} nn < suc n · m
    nm<n·m =
      toℕ {k = m} mm · suc n + toℕ {k = suc n} nn   <≤⟨ <-k+ nn< ⟩
      toℕ {k = m} mm · suc n + suc n                ≡≤⟨ +-comm (toℕ {k = m} mm · suc n) (suc n) ⟩
      suc (toℕ {k = m} mm) · suc n                  ≤≡⟨ ≤-·k mm<m ⟩
      m · suc n                                     ≡⟨ sym (·-comm (suc n) m) ⟩
      suc n · m                                     ∎ where open <-Reasoning

    nm<ᵗn·m : nm <ᵗ (suc n · m)
    nm<ᵗn·m = <→<ᵗ (subst (λ k → k < suc n · m) (sym (expand≡ (suc n) (toℕ {k = suc n} nn) (toℕ {k = m} mm))) nm<n·m)

  intro-injective : ∀ {o} {p} → intro o ≡ intro p → o ≡ p
  intro-injective {o} {p} io≡ip = λ i → io′≡ip′ i .fst , sndFin i where
      io′≡ip′ : (fst o , toℕ {k = m} (snd o)) ≡ (fst p , toℕ {k = m} (snd p))
      io′≡ip′ = expand×Inj _ (cong fst io≡ip)

      sndFin : Path (Fin m) (snd o) (snd p)
      sndFin = toℕ-injective {k = m} (cong snd io′≡ip′)
  isEmbeddingIntro : isEmbedding intro
  isEmbeddingIntro = injEmbedding (isSetFin {k = suc n · m}) intro-injective

  elimF : ∀ nm → fiber intro nm
  elimF nm = ((nnFin , mmFin) , toℕ-injective {k = suc n · m} (expand≡ (suc n) nn mm ∙ nmmoddiv)) where
    k : ℕ
    k = toℕ {k = suc n · m} nm
    mm : ℕ
    mm = k / suc n
    nn : ℕ
    nn = k % suc n

    nmmoddiv : mm · suc n + nn ≡ k
    nmmoddiv = moddiv k (suc n)

    mm·sn<m·sn : mm · suc n < m · suc n
    mm·sn<m·sn =
      mm · suc n      ≤<⟨ nn , +-comm nn (mm · suc n) ⟩
      mm · suc n + nn <≡⟨ subst (λ l → l < suc n · m) (sym nmmoddiv) (<ᵗ→< (snd nm)) ⟩
      suc n · m       ≡⟨ ·-comm (suc n) m ⟩
      m · suc n       ∎ where open <-Reasoning

    mm<m : mm < m
    mm<m = <-·sk-cancel mm·sn<m·sn
    nnFin : Fin (suc n)
    nnFin = nn , n%sk<ᵗsk k _
    mmFin : Fin m
    mmFin = mm , <→<ᵗ mm<m

    eqNat : toℕ {k = suc n · m} (intro (nnFin , mmFin))
          ≡ toℕ {k = suc n · m} nm
    eqNat = expand≡ (suc n) nn mm ∙ nmmoddiv

  isSurjectionIntro : isSurjection intro
  isSurjectionIntro = ∣_∣₁ ∘ elimF

-- Fin (m + n) ≡ Fin m ⊎ Fin n
-- ===========================

o<m→o<m+n : (m n o : ℕ) → o < m → o < (m + n)
o<m→o<m+n m n o (k , p) = (n + k) , (n + k + suc o    ≡⟨ sym (+-assoc n k _)  ⟩
                                     n + (k + suc o)  ≡⟨ cong (λ - → n + -) p ⟩
                                     n + m            ≡⟨ +-comm n m           ⟩
                                     m + n            ∎)

∸-<-lemma : (m n o : ℕ) → o < m + n → m ≤ o → o ∸ m < n
∸-<-lemma zero    n o       o<m+n m<o = o<m+n
∸-<-lemma (suc m) n zero    o<m+n m<o = Empty.rec (¬-<-zero m<o)
∸-<-lemma (suc m) n (suc o) o<m+n m<o =
  ∸-<-lemma m n o (pred-≤-pred o<m+n) (pred-≤-pred m<o)

-- A convenient wrapper on top of trichotomy, as we will be interested in
-- whether `m < n` or `n ≤ m`.
_≤?_ : (m n : ℕ) → (m < n) ⊎ (n ≤ m)
_≤?_ m n with m ≟ n
_≤?_ m n | lt m<n = inl m<n
_≤?_ m n | eq m=n = inr (subst (λ - → - ≤ m) m=n ≤-refl)
_≤?_ m n | gt n<m = inr (<-weaken n<m)

¬-<-and-≥ : {m n : ℕ} → m < n → ¬ n ≤ m
¬-<-and-≥ {m}     {zero}  m<n n≤m = ¬-<-zero m<n
¬-<-and-≥ {zero}  {suc n} m<n n≤m = ¬-<-zero n≤m
¬-<-and-≥ {suc m} {suc n} m<n n≤m = ¬-<-and-≥ (pred-≤-pred m<n) (pred-≤-pred n≤m)

m+n∸n=m : (n m : ℕ) → (m + n) ∸ n ≡ m
m+n∸n=m zero    k = +-zero k
m+n∸n=m (suc m) k = (k + suc m) ∸ suc m   ≡⟨ cong (λ - → - ∸ suc m) (+-suc k m) ⟩
                    suc (k + m) ∸ (suc m) ≡⟨ refl                               ⟩
                    (k + m) ∸ m           ≡⟨ m+n∸n=m m k                        ⟩
                    k                     ∎

∸-lemma : {m n : ℕ} → m ≤ n → m + (n ∸ m) ≡ n
∸-lemma {zero}  {k}     _   = refl {x = k}
∸-lemma {suc m} {zero}  m≤k = Empty.rec (¬-<-and-≥ (suc-≤-suc zero-≤) m≤k)
∸-lemma {suc m} {suc k} m≤k =
  suc m + (suc k ∸ suc m)   ≡⟨ refl                                 ⟩
  suc (m + (suc k ∸ suc m)) ≡⟨ refl                                 ⟩
  suc (m + (k ∸ m))         ≡⟨ cong suc (∸-lemma (pred-≤-pred m≤k)) ⟩
  suc k                     ∎

Fin+≅Fin⊎Fin : (m n : ℕ) → Iso (Fin (m + n)) (Fin m ⊎ Fin n)
Iso.fun (Fin+≅Fin⊎Fin m n) = f
  where
    f : Fin (m + n) → Fin m ⊎ Fin n
    f (k , k<m+n) with k ≤? m
    f (k , k<m+n) | inl k<m = inl (k , <→<ᵗ k<m) -- (k , k<m)
    f (k , k<m+n) | inr k≥m = inr ((k ∸ m) , <→<ᵗ (∸-<-lemma m n k (<ᵗ→< k<m+n) k≥m))
Iso.inv (Fin+≅Fin⊎Fin m n) = g
  where
    g :  Fin m  ⊎  Fin n  →  Fin (m + n)
    g (inl (k , k<m)) = k     , <→<ᵗ (o<m→o<m+n m n k (<ᵗ→< k<m))
    g (inr (k , k<n)) = m + k , <→<ᵗ (<-k+ {k = m} (<ᵗ→< k<n))
Iso.rightInv (Fin+≅Fin⊎Fin m n) = sec-f-g
  where
    sec-f-g : _
    sec-f-g (inl (k , k<m)) with k ≤? m
    sec-f-g (inl (k , k<m)) | inl _   = cong inl (Σ≡Prop (λ z → isProp<ᵗ {n = z} {m = m}) refl)
    sec-f-g (inl (k , k<m)) | inr m≤k = Empty.rec (¬-<-and-≥ (<ᵗ→< k<m) m≤k)
    sec-f-g (inr (k , k<n)) with (m + k) ≤? m
    sec-f-g (inr (k , k<n)) | inl p   = Empty.rec (¬m+n<m {m} {k} p)
    sec-f-g (inr (k , k<n)) | inr k≥m = cong inr (Σ≡Prop (λ z → isProp<ᵗ {n = z} {m = n}) rem)
      where
        rem : (m + k) ∸ m ≡ k
        rem = subst (λ - → - ∸ m ≡ k) (+-comm k m) (m+n∸n=m m k)
Iso.leftInv  (Fin+≅Fin⊎Fin m n) = ret-f-g
  where
    ret-f-g : _
    ret-f-g (k , k<m+n) with k ≤? m
    ret-f-g (k , k<m+n) | inl _   = Σ≡Prop (λ z → isProp<ᵗ {n = z} {m = m + n}) refl
    ret-f-g (k , k<m+n) | inr m≥k = Σ≡Prop (λ z → isProp<ᵗ {n = z} {m = m + n}) (∸-lemma m≥k)

Fin+≡Fin⊎Fin : (m n : ℕ) → Fin (m + n) ≡ Fin m ⊎ Fin n
Fin+≡Fin⊎Fin m n = isoToPath (Fin+≅Fin⊎Fin m n)

-- Equivalence between FinData and Fin

FinData→Fin : (N : ℕ) → FinData N → Fin N
FinData→Fin zero ()
FinData→Fin (suc N) zero = zero , tt
FinData→Fin (suc N) (suc k) = fsuc (FinData→Fin N k)

Fin→FinData : (N : ℕ) → Fin N → FinData N
Fin→FinData zero (k , p) = Empty.rec p
Fin→FinData (suc N) (0 , p) = zero
Fin→FinData (suc N) ((suc k) , p) = suc (Fin→FinData N (k , p))

secFin : (n : ℕ) → section (FinData→Fin n) (Fin→FinData n)
secFin 0 (k , p) = Empty.rec p
secFin (suc N) (0 , p) = Fin-fst-≡ {n = suc N} refl
secFin (suc N) (suc k , p) = Fin-fst-≡ {n = suc N} (cong suc (cong fst (secFin N (k , p))))

retFin : (n : ℕ) → retract (FinData→Fin n) (Fin→FinData n)
retFin 0 ()
retFin (suc N) zero = refl
retFin (suc N) (suc k) = cong FinData.suc (cong (Fin→FinData N) (Fin-fst-≡ {N} refl) ∙ retFin N k)

FinDataIsoFin : (N : ℕ) → Iso (FinData N) (Fin N)
Iso.fun (FinDataIsoFin N) = FinData→Fin N
Iso.inv (FinDataIsoFin N) = Fin→FinData N
Iso.rightInv (FinDataIsoFin N) = secFin N
Iso.leftInv (FinDataIsoFin N) = retFin N

FinData≃Fin : (N : ℕ) → FinData N ≃ Fin N
FinData≃Fin N = isoToEquiv (FinDataIsoFin N)

FinData≡Fin : (N : ℕ) → FinData N ≡ Fin N
FinData≡Fin N = ua (FinData≃Fin N)

-- decidability of Fin

DecFin : (n : ℕ) → Dec (Fin n)
DecFin 0 = no ¬Fin0
DecFin (suc n) = yes fzero

-- propositional truncation of Fin

Dec∥Fin∥ : (n : ℕ) → Dec ∥ Fin n ∥₁
Dec∥Fin∥ n = Dec∥∥ (DecFin n)

-- some properties about cardinality

Fin>0→isInhab : (n : ℕ) → 0 < n → Fin n
Fin>0→isInhab 0 p = Empty.rec (¬-<-zero p)
Fin>0→isInhab (suc n) p = fzero

Fin>1→hasNonEqualTerm : (n : ℕ) → 1 < n → Σ[ i ∈ Fin n ] Σ[ j ∈ Fin n ] ¬ i ≡ j
Fin>1→hasNonEqualTerm 0 p = Empty.rec (snotz (≤0→≡0 p))
Fin>1→hasNonEqualTerm 1 p = Empty.rec (snotz (≤0→≡0 (pred-≤-pred p)))
Fin>1→hasNonEqualTerm (suc (suc n)) _ = fzero , fone , fzero≠fone

isEmpty→Fin≡0 : (n : ℕ) → ¬ Fin n → 0 ≡ n
isEmpty→Fin≡0 0 _ = refl
isEmpty→Fin≡0 (suc n) p = Empty.rec (p fzero)

isInhab→Fin>0 : (n : ℕ) → Fin n → 0 < n
isInhab→Fin>0 0 i = Empty.rec (¬Fin0 i)
isInhab→Fin>0 (suc n) _ = suc-≤-suc zero-≤

hasNonEqualTerm→Fin>1 : (n : ℕ) → (i j : Fin n) → ¬ i ≡ j → 1 < n
hasNonEqualTerm→Fin>1 0 i _ _ = Empty.rec (¬Fin0 i)
hasNonEqualTerm→Fin>1 1 i j p = Empty.rec (p (isContr→isProp isContrFin1 i j))
hasNonEqualTerm→Fin>1 (suc (suc n)) _ _ _ = suc-≤-suc (suc-≤-suc zero-≤)

Fin≤1→isProp : (n : ℕ) → n ≤ 1 → isProp (Fin n)
Fin≤1→isProp 0 _ = isPropFin0
Fin≤1→isProp 1 _ = isContr→isProp isContrFin1
Fin≤1→isProp (suc (suc n)) p = Empty.rec (¬-<-zero (pred-≤-pred p))

isProp→Fin≤1 : (n : ℕ) → isProp (Fin n) → n ≤ 1
isProp→Fin≤1 0 _ = ≤-solver 0 1
isProp→Fin≤1 1 _ = ≤-solver 1 1
isProp→Fin≤1 (suc (suc n)) p = Empty.rec (fzero≠fone (p fzero fone))

-- Characterisation of Π over (Fin (suc n))
CharacΠFinIso : ∀ {ℓ} (n : ℕ) {B : Fin (suc n) → Type ℓ}
  → Iso ((x : _) → B x) (B fzero × ((x : _) → B (fsuc x)))
Iso.fun (CharacΠFinIso n {B = B}) f = f fzero , f ∘ fsuc
Iso.inv (CharacΠFinIso n {B = B}) (x , f) (zero , p) =
  subst B (Fin-fst-≡ {suc n}
                     {i = fzero}
                     {j = zero , p}
                     refl) x
Iso.inv (CharacΠFinIso n {B = B}) (x , f) (suc y , p) =
  subst B (Fin-fst-≡ {n = suc n}
                     {i = fsuc (y , p)}
                     {j = (suc y , p)}
                     refl)
                     (f (y , p))
Iso.rightInv (CharacΠFinIso n {B = B}) (x , f) =
  ΣPathP ((λ j →
    transp (λ i → B (isSetFin {suc n}
                  fzero fzero (Fin-fst-≡ {n = suc n}
                                         {i = fzero}
                                         {j = fzero}
                                         (λ _ → zero))
                              refl j i)) j x)
  , funExt λ x → (λ j → subst B (pathid x j)
                           (f (fst x , x .snd)))
                ∙ (λ i → transp (λ j → B (path₃ x (i ∨ j))) i (f (path₂ x i))))
  where
  module _ (x : Fin n) where
    path₁ : _
    path₁ = Fin-fst-≡ {n = suc n}
                      {i = (fsuc (fst x , x .snd))}
                      {j = fsuc x} refl

    path₂ : _
    path₂ = Fin-fst-≡ {n = n} refl

    path₃ : _
    path₃ = cong fsuc path₂

    pathid : path₁ ≡ path₃
    pathid = isSetFin {suc n} _ _ _ _

Iso.leftInv (CharacΠFinIso n {B = B}) f =
  funExt λ { (zero , p) j
    → transp (λ i → B (Fin-fst-≡ {n = suc n}
                                 {i = fzero}
                                 {j = zero , p}
                                 refl (i ∨ j)))
              j (f (Fin-fst-≡ {n = suc n}
                              {i = fzero}
                              {j = zero , p}
                              refl j))
           ; (suc x , p) j → transp (λ i → B (q x p (i ∨ j))) j (f (q x p j))}
  where
  q : (x : _) (p : _) → _
  q x p = Fin-fst-≡ {n = suc n} {i = (fsuc (x , p))}
                    {j = suc x , p}
                    refl

-- properties of finite sums
module _ (_+A_ : A → A → A) (0A : A)
  (rUnit : (x : _) → x +A 0A ≡ x)
   where
  sumFinGen0 : (n : ℕ) (f : Fin n → A)
    → ((x : _) → f x ≡ 0A)
    → sumFinGen {n = n} _+A_ 0A f
    ≡ 0A
  sumFinGen0 zero f ind = refl
  sumFinGen0 (suc n) f ind =
    cong₂ _+A_
      (ind flast)
      (sumFinGen0 n (f ∘ injectSuc) (λ x → ind (injectSuc x))) ∙ rUnit 0A

  module _ (comm : (x y : A) → x +A y ≡ y +A x) where
    private
      lUnitA : (x : _) → 0A +A x ≡ x
      lUnitA x = comm _ _ ∙ rUnit x

    sumFin-choose :
      {n : ℕ} (f : Fin n → A)
      → (a : A) (x : Fin n)
      → (f x ≡ a)
      → ((x' : Fin n) → ¬ (x' ≡ x) → f x' ≡ 0A)
      → sumFinGen {n = n} _+A_ 0A f ≡ a
    sumFin-choose {zero} f a x p t = Empty.rec (¬Fin0 x)
    sumFin-choose {suc n} f a x p t with (n ≟ fst x)
    ... | lt x₁ =
      Empty.rec (¬m<m {suc n} ((fst (<ᵗ→< {n = x .fst} {suc n} (x .snd))) + fst x₁
           , (sym (+-assoc (fst (<ᵗ→< {n = x .fst} {suc n} (x .snd))) (fst x₁) (suc (suc n)))
           ∙ (cong (fst (<ᵗ→< {n = x .fst} {suc n} (x .snd)) +_ ) (+-suc (fst x₁) (suc n))))
           ∙ sym ((sym (<ᵗ→< {n = x .fst} (x .snd) .snd))
                ∙ cong (fst (<ᵗ→< {n = x .fst} {suc n} ((x .snd))) +_) (sym (cong suc (x₁ .snd))))))
    ... | eq x₁ =
      cong (f flast +A_) (sumFinGen0 n _
        λ h → t _ λ q → ¬m<m (subst (_< n) (cong fst q ∙ sym x₁) (<ᵗ→< (h .snd))))
             ∙ rUnit _ ∙ sym (cong f x=flast) ∙ p
      where
      x=flast : x ≡ flast
      x=flast = Σ≡Prop (λ z → isProp<ᵗ {n = z} {m = suc n}) (sym x₁)
    ... | gt x₁ =
      cong₂ _+A_
         (t flast (λ p → ¬m<m (subst (_< n) (sym (cong fst p)) x₁)))
         refl
      ∙ lUnitA _
      ∙ sumFin-choose {n = n} (f ∘ injectSuc) a (fst x , <→<ᵗ x₁)
          (cong f (Σ≡Prop (λ z → isProp<ᵗ {n = z} {m = suc n}) refl) ∙ p)
          λ a r → t (injectSuc a) λ d → r (Σ≡Prop (λ z → isProp<ᵗ {n = z} {m = n})
          (cong fst d))

    module _ (assocA : (x y z : A) → x +A (y +A z) ≡ (x +A y) +A z) where
      sumFinGenHom : (n : ℕ) (f g : Fin n → A)
        → sumFinGen {n = n} _+A_ 0A (λ x → f x +A g x)
         ≡ (sumFinGen {n = n} _+A_ 0A f +A sumFinGen {n = n} _+A_ 0A g)
      sumFinGenHom zero f g = sym (rUnit 0A)
      sumFinGenHom (suc n) f g =
          cong ((f flast +A g flast) +A_) (sumFinGenHom n (f ∘ injectSuc) (g ∘ injectSuc))
        ∙ move4 (f flast) (g flast)
                (sumFinGen {n = n} _+A_ 0A (λ x → f (injectSuc x)))
                (sumFinGen {n = n} _+A_ 0A (λ x → g (injectSuc x)))
                _+A_ assocA comm

sumFinGenId : {n : ℕ} (_+_ : A → A → A) (0A : A)
  (f g : Fin n → A) → f ≡ g → sumFinGen {n = n} _+_ 0A f ≡ sumFinGen {n = n} _+_ 0A g
sumFinGenId {n = n} _+_ 0A f g p i = sumFinGen {n = n} _+_ 0A (p i)

Fin≡ : {m : ℕ} (a b : Fin m) → fst a ≡ fst b → a ≡ b
Fin≡ {m} (a , Ha) (b , Hb) H i =
  (H i , hcomp (λ j → λ { (i = i0) → Ha
                        ; (i = i1) → isProp<ᵗ {b}{m} (transp (λ j → H j <ᵗ m) i0 Ha) Hb j })
               (transp (λ j → H (i ∧ j) <ᵗ m) (~ i) Ha))

fsuc-injectSuc : {m : ℕ} (n : Fin m)
  → injectSuc {n = suc m} (fsuc n) ≡ fsuc (injectSuc n)
fsuc-injectSuc {m = suc m} (x , p) = toℕ-injective {suc (suc (suc m))} refl

elimFin : ∀ {ℓ} {m : ℕ} {A : Fin (suc m) → Type ℓ}
                 (max : A flast)
                 (f : (x : Fin m) → A (injectSuc x))
              → (x : _) → A x
elimFin {m = zero} {A = A} max f (zero , p) = max
elimFin {m = suc m} {A = A} max f (zero , p) = f (zero , tt)
elimFin {m = suc zero} {A = A} max f (suc zero , p) = max
elimFin {m = suc (suc m)} {A = A} max f (suc x , p) =
  elimFin {m = suc m} {A = λ x → A (fsuc x)} max (λ t → f (fsuc t)) (x , p)

elimFin-alt : ∀ {ℓ} {m : ℕ} {A : Fin (suc m) → Type ℓ}
                 (max : A fzero)
                 (f : (x : Fin m) → A (fsuc x))
              → (x : _) → A x
elimFin-alt {m = zero} max f (zero , p) = max
elimFin-alt {m = suc m} max f (zero , p) = max
elimFin-alt {m = suc m} max f (suc x , p) = f (x , p)

elimFinβ : ∀ {ℓ} {m : ℕ} {A : Fin (suc m) → Type ℓ}
                 (max : A flast)
                 (f : (x : Fin m) → A (injectSuc x))
              → ((elimFin {A = A} max f flast ≡ max))
               × ((x : Fin m) → elimFin {A = A} max f (injectSuc x) ≡ f x)
elimFinβ {m = zero} {A = A} max f = refl , λ {()}
elimFinβ {m = suc zero} {A = A} max f = refl , λ {(zero , p) → refl}
elimFinβ {m = suc (suc m)} {A = A} max f =
  elimFinβ {m = (suc m)} {A = λ x → A (fsuc x)} max _ .fst
  , elimFin-alt {m = (suc m)} {A = λ x → elimFin max f (injectSuc {n = suc (suc m)} x) ≡ f x}
             refl
             (elimFinβ {m = (suc m)} {A = λ x → A (fsuc x)} max _ .snd)

inhabitedFibres?Fin : ∀ {ℓ} {A : Type ℓ}
  (da : Discrete A) (n : ℕ) (f : Fin n → A)
  → inhabitedFibres? f
inhabitedFibres?Fin {A = A} da zero f y = inr λ x → Empty.rec (¬Fin0 x)
inhabitedFibres?Fin {A = A} da (suc n) f y with da (f fzero) y
... | yes p = inl (fzero , p)
... | no ¬p with (inhabitedFibres?Fin da n (f ∘ fsuc) y)
... | inl q = inl ((fsuc (fst q)) , snd q)
... | inr q = inr (elimFin-alt ¬p q)

-- Decompositions in terms of ⊎ and ×
Iso-Fin1⊎Fin-FinSuc : {n : ℕ} → Iso (Fin 1 ⊎ Fin n) (Fin (suc n))
Iso.fun (Iso-Fin1⊎Fin-FinSuc {n = n}) = ⊎.rec (λ _ → flast) injectSuc
Iso.inv (Iso-Fin1⊎Fin-FinSuc {n = n}) = elimFin (inl flast) inr
Iso.rightInv (Iso-Fin1⊎Fin-FinSuc {n = n}) =
  let β = elimFinβ {m = n} {A = λ _ → Fin 1 ⊎ Fin n} (inl flast) inr in
  elimFin (cong (⊎.rec (λ _ → flast) injectSuc) (β .fst))
          (λ x → cong (⊎.rec (λ _ → flast) injectSuc) (β .snd x))
Iso.leftInv (Iso-Fin1⊎Fin-FinSuc {n = n}) (inl (zero , p)) =
  let β = elimFinβ {m = n} {A = λ _ → Fin 1 ⊎ Fin n} (inl flast) inr in
  (β .fst) ∙ cong inl (Fin≡ {m = 1} flast (zero , p) refl)
Iso.leftInv (Iso-Fin1⊎Fin-FinSuc {n = n}) (inr x) =
  (elimFinβ {m = n} {A = λ _ → Fin 1 ⊎ Fin n} (inl flast) inr) .snd x

Iso-Fin⊎Fin-Fin+ : {n m : ℕ} → Iso (Fin n ⊎ Fin m) (Fin (n + m))
Iso.fun (Iso-Fin⊎Fin-Fin+ {n = zero} {m = m}) (inr x) = x
Iso.inv (Iso-Fin⊎Fin-Fin+ {n = zero} {m = m}) x = inr x
Iso.rightInv (Iso-Fin⊎Fin-Fin+ {n = zero} {m = m}) x = refl
Iso.leftInv (Iso-Fin⊎Fin-Fin+ {n = zero} {m = m}) (inr x) = refl
Iso-Fin⊎Fin-Fin+ {n = suc n} {m = m} =
  compIso (⊎Iso (invIso Iso-Fin1⊎Fin-FinSuc) idIso)
    (compIso ⊎-assoc-Iso
      (compIso (⊎Iso idIso (Iso-Fin⊎Fin-Fin+ {n = n} {m = m}))
        Iso-Fin1⊎Fin-FinSuc))

Iso-Unit-Fin1 : Iso Unit (Fin 1)
Iso.fun Iso-Unit-Fin1 tt = fzero
Iso.inv Iso-Unit-Fin1 (x , p) = tt
Iso.rightInv Iso-Unit-Fin1 (zero , p) = Σ≡Prop (λ z → isProp<ᵗ {z} {1}) refl
Iso.leftInv Iso-Unit-Fin1 x = refl

Iso-Bool-Fin2 : Iso Bool (Fin 2)
Iso.fun Iso-Bool-Fin2 false = flast
Iso.fun Iso-Bool-Fin2 true = fzero
Iso.inv Iso-Bool-Fin2 (zero , p) = true
Iso.inv Iso-Bool-Fin2 (suc x , p) = false
Iso.rightInv Iso-Bool-Fin2 (zero , p) = refl
Iso.rightInv Iso-Bool-Fin2 (suc zero , p) =
  Σ≡Prop (λ z → isProp<ᵗ {z} {suc (suc zero)}) refl
Iso.leftInv Iso-Bool-Fin2 false = refl
Iso.leftInv Iso-Bool-Fin2 true = refl

Iso-Fin×Fin-Fin· : {n m : ℕ} → Iso (Fin n × Fin m) (Fin (n · m))
Iso-Fin×Fin-Fin· {n = zero} {m = m} =
  iso (λ {()}) (λ{()}) (λ{()}) (λ{()})
Iso-Fin×Fin-Fin· {n = suc n} {m = m} =
  compIso
    (compIso
      (compIso (Σ-cong-iso-fst (invIso Iso-Fin1⊎Fin-FinSuc))
        (compIso Σ-swap-Iso
          (compIso ×DistR⊎Iso
            (⊎Iso (compIso
              (Σ-cong-iso-snd (λ _ → invIso Iso-Unit-Fin1)) rUnit×Iso)
              Σ-swap-Iso))))
      (⊎Iso idIso (Iso-Fin×Fin-Fin· {n})))
    (Iso-Fin⊎Fin-Fin+ {n = m} {m = n · m})

Iso-FinSuc→-Fin→× : ∀ {ℓ} (n : ℕ) {A : Fin (suc n) → Type ℓ}
  → Iso ((x : Fin (suc n)) → A x)
         (((x : _) → A (fsuc x)) × A fzero)
fst (Iso.fun (Iso-FinSuc→-Fin→× n) f) x = f (fsuc x)
snd (Iso.fun (Iso-FinSuc→-Fin→× n) f) = f fzero
Iso.inv (Iso-FinSuc→-Fin→× n) (f , s) (zero , w) = s
Iso.inv (Iso-FinSuc→-Fin→× (suc n)) (f , s) (suc t , w) = f (t , w)
fst (Iso.rightInv (Iso-FinSuc→-Fin→× (suc n)) (f , s) i) (w , t) = f (w , t)
snd (Iso.rightInv (Iso-FinSuc→-Fin→× n) (f , s) i) = s
Iso.leftInv (Iso-FinSuc→-Fin→× n) f i (zero , tt) = f fzero
Iso.leftInv (Iso-FinSuc→-Fin→× (suc n)) f i (suc s , t) = f (suc s , t)

Iso-Fin×Bool-Fin : {n : ℕ} → Iso (Fin n × Bool) (Fin (2 · n))
Iso-Fin×Bool-Fin {n} =
  compIso (compIso Σ-swap-Iso
    (Σ-cong-iso-fst Iso-Bool-Fin2)) (Iso-Fin×Fin-Fin· {n = 2} {m = n})

module _ {m : ℕ} where
  Fin→Unit⊎Fin : (x : Fin (suc m)) → Unit ⊎ Fin m
  Fin→Unit⊎Fin = elimFin (inl tt) inr

  Unit⊎Fin→Fin : Unit ⊎ Fin m → Fin (suc m)
  Unit⊎Fin→Fin (inl x) = flast
  Unit⊎Fin→Fin (inr x) = injectSuc x

  Iso-Fin-Unit⊎Fin : Iso (Fin (suc m)) (Unit ⊎ Fin m)
  Iso.fun Iso-Fin-Unit⊎Fin = Fin→Unit⊎Fin
  Iso.inv Iso-Fin-Unit⊎Fin = Unit⊎Fin→Fin
  Iso.rightInv Iso-Fin-Unit⊎Fin (inl x) = elimFinβ {m = m} {A = λ _ → Unit ⊎ Fin m} (inl tt) inr .fst
  Iso.rightInv Iso-Fin-Unit⊎Fin (inr x) = elimFinβ {m = m} {A = λ _ → Unit ⊎ Fin m} (inl tt) inr .snd x
  Iso.leftInv Iso-Fin-Unit⊎Fin =
    elimFin {m = m} {A = λ x → Unit⊎Fin→Fin (Fin→Unit⊎Fin x) ≡ x}
      (cong Unit⊎Fin→Fin (elimFinβ {m = m} {A = λ _ → Unit ⊎ Fin m} (inl tt) inr .fst))
      (λ x → cong Unit⊎Fin→Fin (elimFinβ {m = m} {A = λ _ → Unit ⊎ Fin m} (inl tt) inr .snd x))


-- Swapping two elements in Fin n
module _ {n : ℕ} where
  swapFin : (x y : Fin n) → Fin n → Fin n
  swapFin (x , xp) (y , yp) (z , zp) with (discreteℕ z x) | (discreteℕ z y)
  ... | yes p | yes p₁ = z , zp
  ... | yes p | no ¬p = y , yp
  ... | no ¬p | yes p = x , xp
  ... | no ¬p | no ¬p₁ = (z , zp)

  swapFinβₗ : (x y : Fin n) → swapFin x y x ≡ y
  swapFinβₗ (x , xp) (y , yp) with (discreteℕ x x) | discreteℕ x y
  ... | yes p | yes p₁ = Σ≡Prop (λ z → isProp<ᵗ {z} {n}) p₁
  ... | yes p | no ¬p = refl
  ... | no ¬p | q = Empty.rec (¬p refl)

  swapFinβᵣ : (x y : Fin n) → swapFin x y y ≡ x
  swapFinβᵣ (x , xp) (y , yp) with (discreteℕ y y) | discreteℕ y x
  ... | yes p | yes p₁ = Σ≡Prop (λ z → isProp<ᵗ {z} {n}) p₁
  ... | yes p | no ¬p = refl
  ... | no ¬p | q = Empty.rec (¬p refl)

  swapFin² : (x y z : Fin n) → swapFin x y (swapFin x y z) ≡ z
  swapFin² (x , xp) (y , yp) (z , zp) with discreteℕ z x | discreteℕ z y
  ... | yes p | yes p₁ = help
    where
    help : swapFin (x , xp) (y , yp) (z , zp) ≡ (z , zp)
    help with discreteℕ z x | discreteℕ z y
    ... | yes p | yes p₁ = refl
    ... | yes p | no ¬p = Empty.rec (¬p p₁)
    ... | no ¬p | r = Empty.rec (¬p p)
  ... | yes p | no ¬q = help
    where
    help : swapFin (x , xp) (y , yp) (y , yp) ≡ (z , zp)
    help with discreteℕ y x | discreteℕ y y
    ... | yes p' | yes p₁ = Σ≡Prop (λ z → isProp<ᵗ {z} {n}) (p' ∙ sym p)
    ... | no ¬p | yes p₁ = Σ≡Prop (λ z → isProp<ᵗ {z} {n})  (sym p)
    ... | p | no ¬p = Empty.rec (¬p refl)
  ... | no ¬p | yes p = help
    where
    help : swapFin (x , xp) (y , yp) (x , xp) ≡ (z , zp)
    help with discreteℕ x y | discreteℕ x x
    ... | yes p₁ | yes _ = Σ≡Prop (λ z → isProp<ᵗ {z} {n}) (p₁ ∙ sym p)
    ... | no ¬p | yes _ = Σ≡Prop (λ z → isProp<ᵗ {z} {n})  (sym p)
    ... | s | no ¬p = Empty.rec (¬p refl)
  ... | no ¬p | no ¬q = help
    where
    help : swapFin (x , xp) (y , yp) (z , zp) ≡ (z , zp)
    help with discreteℕ z x | discreteℕ z y
    ... | yes p | yes p₁ = refl
    ... | yes p | no ¬b = Empty.rec (¬p p)
    ... | no ¬a | yes b = Empty.rec (¬q b)
    ... | no ¬a | no ¬b = refl

  swapFinIso : (x y : Fin n) → Iso (Fin n) (Fin n)
  Iso.fun (swapFinIso x y) = swapFin x y
  Iso.inv (swapFinIso x y) = swapFin x y
  Iso.rightInv (swapFinIso x y) = swapFin² x y
  Iso.leftInv (swapFinIso x y) = swapFin² x y

module _ {ℓ : Level} {n : ℕ} {A : Fin n → Type ℓ} (x₀ : Fin n)
  (pt : A x₀) (l : (x : Fin n) → ¬ x ≡ x₀ → A x) where
  private
    x = fst x₀
    p = snd x₀
  elimFinChoose : (x : _) → A x
  elimFinChoose (x' , q) with (discreteℕ x x')
  ... | yes p₁ = subst A (Σ≡Prop (λ z → isProp<ᵗ {z} {n}) p₁) pt
  ... | no ¬p = l (x' , q) λ r → ¬p (sym (cong fst r))

  elimFinChooseβ : (elimFinChoose x₀ ≡ pt)
                × ((x : _) (q : ¬ x ≡ x₀) → elimFinChoose x ≡ l x q)
  fst elimFinChooseβ with (discreteℕ x x)
  ... | yes p₁ = (λ j → subst A (isSetFin {n} x₀ x₀ (Σ≡Prop (λ z → isProp<ᵗ {z} {n}) p₁) refl j) pt)
                ∙ transportRefl pt
  ... | no ¬p = Empty.rec (¬p refl)
  snd elimFinChooseβ (x' , q) with (discreteℕ x x')
  ... | yes p₁ = λ q → Empty.rec (q (Σ≡Prop (λ z → isProp<ᵗ {z} {n}) (sym p₁)))
  ... | no ¬p = λ s → cong (l (x' , q)) (isPropΠ (λ _ → isProp⊥) _ _)

containsTwoFin : {n : ℕ} (x : Fin (suc (suc n))) → Σ[ y ∈ Fin (suc (suc n)) ] ¬ x ≡ y
containsTwoFin (zero , p) = (1 , p) , λ q → snotz (sym (cong fst q))
containsTwoFin (suc x , p) = fzero , λ q → snotz (cong fst q)

≠flast→<ᵗflast : {n : ℕ} → (x : Fin (suc n)) → ¬ x ≡ flast → fst x <ᵗ n
≠flast→<ᵗflast = elimFin (λ p → Empty.rec (p refl)) λ p _ → snd p

Fin≠Fin : {n m : ℕ} → ¬ (n ≡ m) → ¬ (Iso (Fin n) (Fin m))
Fin≠Fin {n = zero} {m = zero} p = Empty.rec (p refl)
Fin≠Fin {n = zero} {m = suc m} p q = Iso.inv q fzero .snd
Fin≠Fin {n = suc n} {m = zero} p q = Iso.fun q fzero .snd
Fin≠Fin {n = suc n} {m = suc m} p q =
  Fin≠Fin {n = n} {m = m} (p ∘ cong suc)
    (Iso⊎→Iso idIso help λ {(zero , tt)
      → cong (Iso.inv (Iso-Fin1⊎Fin-FinSuc {n = m})) (swapFinβₗ (Iso.fun q flast) flast)
       ∙ elimFinβ {m = m} (inl flast) inr .fst})
  where
  q^ : Iso (Fin (suc n)) (Fin (suc m))
  q^ = compIso q (swapFinIso {suc m} (Iso.fun q flast) flast)

  help : Iso (Fin 1 ⊎ Fin n) (Fin 1 ⊎ Fin m)
  help = compIso Iso-Fin1⊎Fin-FinSuc (compIso q^ (invIso Iso-Fin1⊎Fin-FinSuc))