{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.AbGroup.Instances.FreeAbGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_·_) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.FreeAbGroup

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Pi
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties


private variable
  ℓ : Level

module _ {A : Type ℓ} where

  FAGAbGroup : AbGroup ℓ
  FAGAbGroup = makeAbGroup {G = FreeAbGroup A} ε _·_ _⁻¹ trunc assoc identityᵣ invᵣ comm

-- Alternative definition of case when A = Fin n
ℤ[Fin_] : (n : ℕ) → AbGroup ℓ-zero
ℤ[Fin n ] = ΠℤAbGroup (Fin n)


--  generator of ℤ[Fin_]
ℤFinGenerator : {n : ℕ} (k : Fin n) → ℤ[Fin n ] .fst
ℤFinGenerator {n = n} k s with (fst k ≟ᵗ fst s)
... | lt x = 0
... | eq x = 1
... | gt x = 0

ℤFinGeneratorComm : {n : ℕ} (x y : Fin n) → ℤFinGenerator x y ≡ ℤFinGenerator y x
ℤFinGeneratorComm x y with (fst x ≟ᵗ fst y) | (fst y ≟ᵗ fst x)
... | lt x₁ | lt x₂ = refl
... | lt x₁ | eq x₂ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst y) (sym x₂) x₁))
... | lt x₁ | gt x₂ = refl
... | eq x₁ | lt x₂ = ⊥.rec (¬m<ᵗm (subst (fst y <ᵗ_) x₁ x₂))
... | eq x₁ | eq x₂ = refl
... | eq x₁ | gt x₂ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst y) x₁ x₂))
... | gt x₁ | lt x₂ = refl
... | gt x₁ | eq x₂ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst x) x₂ x₁))
... | gt x₁ | gt x₂ = refl

isGeneratorℤFinGenerator : {n : ℕ} (f : ℤ[Fin n ] .fst) (a : _)
  → f a ≡ sumFinℤ {n = n} λ s → f s ·ℤ (ℤFinGenerator s a)
isGeneratorℤFinGenerator {n = suc n} f =
  elimFin basec
          λ s → cong f (Σ≡Prop (λ _ → isProp<ᵗ) refl)
  ∙∙ isGeneratorℤFinGenerator {n = n} (f ∘ injectSuc) s
  ∙∙ (λ i → sumFinℤ (λ x → f (injectSuc x) ·ℤ lem₁ s x i))
  ∙∙ +Comm (F s) 0
  ∙∙ λ i → (sym (·Comm (f flast) 0)
    ∙ (cong (f flast ·ℤ_) (sym (lem₂ s flast refl)))) i
     + F s
  where
  basec : f flast ≡ sumFinℤ (λ s → f s ·ℤ ℤFinGenerator s flast)
  basec with (n ≟ᵗ n)
  ... | lt x = ⊥.rec (¬m<ᵗm x)
  ... | eq x = λ i → (·Comm (f flast) (pos 1) (~ i)) + lem₂ (~ i)
    where
    lem₁ : (s : _) → ℤFinGenerator (injectSuc {n = n} s) flast ≡ 0
    lem₁ s with (fst s ≟ᵗ n)
    ... | lt x = refl
    ... | eq w = ⊥.rec (¬m<ᵗm (subst (fst s <ᵗ_) (sym w) (snd s)))
    ... | gt x = refl

    lem₂ : sumFinℤ (λ s → f (injectSuc s) ·ℤ ℤFinGenerator (injectSuc s) flast) ≡ 0
    lem₂ = (λ i → sumFinℤ λ s → (cong (f (injectSuc s) ·ℤ_) (lem₁ s)
                              ∙ ·Comm (f (injectSuc s)) 0) i)
       ∙ (sumFinℤ0 n)
  ... | gt x = ⊥.rec (¬m<ᵗm x)

  module _ (a : Fin n) where
    F = sumFinGen _+_ (pos 0) (λ x → f (injectSuc x)
                      ·ℤ (ℤFinGenerator (injectSuc x) (injectSuc a)))

    lem₁ : (x : _)
      → ℤFinGenerator {n = n} x a -- (a , diff , cong predℕ p)
       ≡ ℤFinGenerator {n = suc n} (injectSuc x) (injectSuc a) -- (a , suc diff , p)
    lem₁ x with (fst x ≟ᵗ fst a)
    ... | lt x₁ = refl
    ... | eq x₁ = refl
    ... | gt x₁ = refl

    lem₂ : (k : Fin (suc n)) → fst k ≡ n
      → ℤFinGenerator {n = suc n} k (injectSuc a) ≡ 0
    lem₂ k q with (fst k ≟ᵗ fst a)
    ... | lt _ = refl
    ... | eq x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (sym x ∙ q) (snd a)))
    ... | gt _ = refl


isGeneratorℤFinGenerator' : {n : ℕ} (f : ℤ[Fin n ] .fst) (a : _)
  → f a ≡ sumFinℤ {n = n} λ s → (ℤFinGenerator a s) ·ℤ f s
isGeneratorℤFinGenerator' {n = n} f a =
  isGeneratorℤFinGenerator f a
  ∙ sumFinℤId n λ x → ·Comm (f x) (ℤFinGenerator x a)
                     ∙ cong (_·ℤ f x) (ℤFinGeneratorComm x a)

ℤFinGeneratorVanish : (n : ℕ) (x : _) → ℤFinGenerator {n = suc n} flast (injectSuc x) ≡ 0
ℤFinGeneratorVanish n x with (n ≟ᵗ (fst x))
... | lt x₁ = refl
... | eq x₁ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (sym x₁) (snd x)))
... | gt x₁ = refl

-- elimination principle
elimℤFin : ∀ {ℓ} {n : ℕ}
  → (P : ℤ[Fin (suc n) ] .fst → Type ℓ)
  → ((x : _) → P (ℤFinGenerator x))
  → ((f : _) → P f → P (λ x → -ℤ (f x)))
  → ((f g : _) → P f → P g → P (λ x → f x + g x))
  → (x : _) → P x
elimℤFin {n = n} P gen d ind f =
  subst P (sym (funExt (isGeneratorℤFinGenerator f)))
    (P-resp-sumFinℤ n P gen d ind (suc n) (λ x y → f y ·ℤ ℤFinGenerator y x)
      λ t → P-resp· n P gen d ind (f t) (ℤFinGenerator t) (gen t))
  where
  module _ {ℓ} (n : ℕ) (P : ℤ[Fin (suc n) ] .fst → Type ℓ)
           (gens : (x : _) → P (ℤFinGenerator x))
           (ind- : ((f : _) → P f → P (λ x → -ℤ (f x))))
           (ind+ : (f g : _) → P f → P g → P (λ x → f x + g x)) where
    P-resp·pos : (x : ℕ) (f : ℤ[Fin (suc n) ] .fst) → P f → P (λ x₁ → pos x ·ℤ f x₁)
    P-resp·pos zero f d =
      subst P  (funExt (λ x → -Cancel (ℤFinGenerator fzero x)))
      (ind+ (ℤFinGenerator fzero)
        (λ x → -ℤ (ℤFinGenerator fzero x))
          (gens fzero) (ind- _ (gens fzero)))
    P-resp·pos (suc zero) f d = d
    P-resp·pos (suc (suc x)) f d =
      ind+ f (λ a → pos (suc x) ·ℤ f a) d (P-resp·pos (suc x) f d)

    P-resp· : (x : _) (f : ℤ[Fin (suc n) ] .fst) → P f → P (λ x₁ → x ·ℤ f x₁)
    P-resp· (pos n) f d = P-resp·pos n f d
    P-resp· (negsuc n) f d =
      subst P (funExt (λ r → -DistL· (pos (suc n)) (f r)))
       (ind- (λ x → pos (suc n) ·ℤ f x) (P-resp·pos (suc n) _ d))

    P-resp-sumFinℤ : (m : ℕ) (f : Fin (suc n) → Fin m → ℤ)
                  → ((t : _) → P (λ x → f x t))
                  → P (λ t → sumFinℤ {n = m} (f t))
    P-resp-sumFinℤ zero f r = P-resp·pos zero (ℤFinGenerator fzero) (gens fzero)
    P-resp-sumFinℤ (suc m) f r =
      ind+ (λ t → f t flast) (λ t → sumFinℤ (λ x → f t (injectSuc x)))
        (r flast)
        (P-resp-sumFinℤ m (λ x y → f x (injectSuc y)) (r ∘ injectSuc))


-- multiplication
·posFree : {n : ℕ} (a : ℕ) (x : Fin n) → FreeAbGroup (Fin n)
·posFree {n = n} zero x = ε
·posFree {n = n} (suc a) x = ⟦ x ⟧ · (·posFree {n = n} a x)

·Free : {n : ℕ} (a : ℤ) (x : Fin n) → FreeAbGroup (Fin n)
·Free (pos n) x = ·posFree n x
·Free (negsuc n) x = ·posFree (suc n) x ⁻¹

·Free⁻¹ : {n : ℕ} (a : ℤ) (x : Fin n) → ·Free (-ℤ a) x ≡ (·Free a x) ⁻¹
·Free⁻¹ {n = n} (pos zero) x = sym (GroupTheory.inv1g (AbGroup→Group FAGAbGroup))
·Free⁻¹ {n = n} (pos (suc n₁)) x = refl
·Free⁻¹ {n = n} (negsuc n₁) x = sym (GroupTheory.invInv (AbGroup→Group FAGAbGroup) _)

·FreeSuc : {n : ℕ} (a : ℤ) (x : Fin n)
  → ·Free (sucℤ a) x ≡ ⟦ x ⟧ · ·Free a x
·FreeSuc (pos n) x = refl
·FreeSuc (negsuc zero) x =
  sym (cong (⟦ x ⟧ ·_) (cong (_⁻¹) (identityᵣ ⟦ x ⟧)) ∙ invᵣ ⟦ x ⟧)
·FreeSuc (negsuc (suc n)) x =
  sym (cong (⟦ x ⟧ ·_)
           (GroupTheory.invDistr (AbGroup→Group FAGAbGroup) ⟦ x ⟧ (⟦ x ⟧ · ·posFree n x)
          ∙ comm _ _)
  ∙∙ assoc _ _ _
  ∙∙ (cong (_· (⟦ x ⟧ · ·posFree n x) ⁻¹) (invᵣ ⟦ x ⟧)
  ∙ comm _ _
  ∙ identityᵣ ((⟦ x ⟧ · ·posFree n x) ⁻¹)))

·FreeHomPos : {n : ℕ} (a : ℕ) (b : ℤ) (x : Fin n)
             → ·Free (pos a) x · ·Free b x ≡ ·Free (pos a + b) x
·FreeHomPos zero b x = comm _ _ ∙ identityᵣ (·Free b x) ∙ cong (λ y → ·Free y x) (+Comm b 0)
·FreeHomPos (suc n) b x =
    sym (assoc ⟦ x ⟧ (·Free (pos n) x) (·Free b x))
  ∙ cong (⟦ x ⟧ ·_) (·FreeHomPos n b x)
  ∙ l b
  where
  l : (b : ℤ) → ⟦ x ⟧ · ·Free (pos n + b) x ≡ ·Free (pos (suc n) + b) x
  l (pos m) = cong (⟦ x ⟧ ·_) (λ i → ·Free (pos+ n m (~ i)) x)
                             ∙ λ i → ·Free (pos+ (suc n) m i) x
  l (negsuc m) = sym (·FreeSuc (pos n +negsuc m) x)
               ∙ λ j → ·Free (sucℤ+negsuc m (pos n) j) x

·FreeHom : {n : ℕ} (a b : ℤ) (x : Fin n) → ·Free a x · ·Free b x ≡ ·Free (a + b) x
·FreeHom (pos n) b x = ·FreeHomPos n b x
·FreeHom (negsuc n) b x =
     cong ((⟦ x ⟧ · ·posFree n x) ⁻¹ ·_)
       (sym (cong (_⁻¹) (·Free⁻¹ b x)
          ∙ GroupTheory.invInv (AbGroup→Group FAGAbGroup) (·Free b x)))
   ∙ comm _ _
  ∙∙ sym (GroupTheory.invDistr (AbGroup→Group FAGAbGroup) (·Free (pos (suc n)) x) (·Free (-ℤ b) x))
  ∙∙ cong (_⁻¹) (·FreeHomPos (suc n) (-ℤ b) x)
  ∙∙ sym (·Free⁻¹ (pos (suc n) + -ℤ b) x)
  ∙∙ λ i → ·Free (help (~ i)) x
  where
  help : negsuc n + b ≡ -ℤ (pos (suc n) + -ℤ b)
  help = cong (negsuc n +_) (sym (-Involutive b))
       ∙ sym (-Dist+ (pos (suc n)) (-ℤ b))

sumFinℤFinGenerator≡1 : (n : ℕ) (f : Fin n)
  → sumFinGen _·_ ε (λ x → ·Free (ℤFinGenerator f x) x) ≡ ⟦ f ⟧
sumFinℤFinGenerator≡1 (suc n) =
  elimFin (basec n)
          indstep
  where
  basec : (n : ℕ) → sumFinGen _·_ ε (λ x → ·Free (ℤFinGenerator (flast {m = n}) x) x) ≡ ⟦ flast ⟧
  basec n with (n ≟ᵗ n)
  ... | lt x = ⊥.rec (¬m<ᵗm x)
  ... | eq x = ((λ i → identityᵣ ⟦ flast ⟧ i
            · sumFinGen _·_ ε (λ x → ·Free (ℤFinGenerator flast (injectSuc x))
                                            (injectSuc x)))
              ∙ cong (⟦ flast ⟧ ·_) (sumFinGenId _ _ _ _
                  (funExt (λ s → cong₂ ·Free (ℤFinGeneratorVanish n s) refl))
                ∙ sumFinGen0 _·_ ε identityᵣ n
                   (λ x₁ → ·Free (pos 0) (injectSuc x₁)) (λ _ → refl)) )
              ∙ identityᵣ _
  ... | gt x = ⊥.rec (¬m<ᵗm x)
  module _ (x : Fin n) where
    FR = Free↑
    indstep :
      ·Free (ℤFinGenerator (injectSuc x) flast) flast · sumFinGen _·_ ε
            (λ x₁ → ·Free (ℤFinGenerator (injectSuc x) (injectSuc x₁)) (injectSuc x₁))
      ≡ ⟦ injectSuc x ⟧
    indstep with (fst x ≟ᵗ n)
    ... | lt a = comm _ _
               ∙ identityᵣ _
               ∙ (λ i → sumFinGen _·_ ε (λ x → lem x i))
               ∙ sym (Free↑sumFinℤ n n (λ x₁ → ·Free (ℤFinGenerator x x₁) x₁))
               ∙ cong (Free↑ n) (sumFinℤFinGenerator≡1 n x)
     where
     lem : (x₁ : Fin n)
       → ·Free (ℤFinGenerator (injectSuc x) (injectSuc x₁)) (injectSuc x₁)
        ≡ Free↑ n (·Free (ℤFinGenerator x x₁) x₁)
     lem x₁ with (fst x ≟ᵗ fst x₁)
     ... | lt x = refl
     ... | eq x = refl
     ... | gt x = refl
    ... | eq a = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) a (snd x)))
    ... | gt a = ⊥.rec (¬m<ᵗm (<ᵗ-trans a (snd x)))


-- equivalence between two versions of free ab group
ℤFin→Free : (n : ℕ) → ℤ[Fin n ] .fst → FreeAbGroup (Fin n)
ℤFin→Free n f = sumFinGen {A = FreeAbGroup (Fin n)} _·_ ε (λ x → ·Free (f x) x)

Free→ℤFin : (n : ℕ) → FreeAbGroup (Fin n) → ℤ[Fin n ] .fst
Free→ℤFin n ⟦ x ⟧ = ℤFinGenerator x
Free→ℤFin n ε _ = pos 0
Free→ℤFin n (a · a₁) x = Free→ℤFin n a x + Free→ℤFin n a₁ x
Free→ℤFin n (a ⁻¹) x = -ℤ Free→ℤFin n a x
Free→ℤFin n (assoc a a₁ a₂ i) x = +Assoc (Free→ℤFin n a x) (Free→ℤFin n a₁ x) (Free→ℤFin n a₂ x) i
Free→ℤFin n (comm a a₁ i) x = +Comm (Free→ℤFin n a x) (Free→ℤFin n a₁ x) i
Free→ℤFin n (identityᵣ a i) = Free→ℤFin n a
Free→ℤFin n (invᵣ a i) x = -Cancel (Free→ℤFin n a x) i
Free→ℤFin n (trunc a a₁ x y i j) k =
  isSet→isSet' isSetℤ
    (λ _ → Free→ℤFin n a k) (λ _ → Free→ℤFin n a₁ k)
    (λ j → Free→ℤFin n (x j) k) (λ j → Free→ℤFin n (y j) k) j i

ℤFin→Free-ℤFinGenerator : (n : ℕ) (x : _)
  → ℤFin→Free n (ℤFinGenerator x) ≡ ⟦ x ⟧
ℤFin→Free-ℤFinGenerator zero x = isContr→isProp isContr-FreeFin0 _ _
ℤFin→Free-ℤFinGenerator (suc n) f = sumFinℤFinGenerator≡1 _ f

ℤFin→FreeHom : (n : ℕ) → (f g : ℤ[Fin n ] .fst)
  → ℤFin→Free n (λ x → f x + g x) ≡ ℤFin→Free n f · ℤFin→Free n g
ℤFin→FreeHom n f g =
  (λ i → sumFinGen _·_ ε (λ x → ·FreeHom  (f x) (g x) x (~ i)))
  ∙ sumFinGenHom _·_ ε identityᵣ comm assoc n
      (λ x → ·Free (f x) x) λ x → ·Free (g x) x

ℤFin→FreeInv : (n : ℕ) (f : ℤ[Fin n ] .fst)
  → ℤFin→Free n (λ x → -ℤ (f x)) ≡ (ℤFin→Free n f) ⁻¹
ℤFin→FreeInv n f =
    (λ i → sumFinGen _·_ ε (λ x → ·Free⁻¹ (f x) x i))
  ∙ sumFinG-neg n {A = FAGAbGroup} (λ x → ·Free (f x) x)

ℤFin→Free→ℤFin : (n : ℕ) (x : FreeAbGroup (Fin n)) → ℤFin→Free n (Free→ℤFin n x) ≡ x
ℤFin→Free→ℤFin zero x = isContr→isProp (subst (isContr ∘ FreeAbGroup) (sym lem) isContr-Free⊥) _ _
  where
  lem : Fin 0 ≡ ⊥
  lem = isoToPath (iso ¬Fin0 (λ{()}) (λ{()}) λ p → ⊥.rec (¬Fin0 p))
ℤFin→Free→ℤFin (suc n) =
  ElimProp.f (trunc _ _)
    (ℤFin→Free-ℤFinGenerator (suc n))
    (comm _ _
    ∙∙ identityᵣ _
    ∙∙ sumFinGen0 _·_ ε identityᵣ n (λ _ → ε) (λ _ → refl))
    (λ {x = x} {y = y} p q
      → ℤFin→FreeHom (suc n) (Free→ℤFin (suc n) x) (Free→ℤFin (suc n) y) ∙ cong₂ _·_ p q)
    λ {x} p → ℤFin→FreeInv (suc n) (Free→ℤFin (suc n) x) ∙ cong (_⁻¹) p

Free→ℤFin→Free : (n : ℕ) (x : _) → Free→ℤFin n (ℤFin→Free n x) ≡ x
Free→ℤFin→Free zero f = funExt λ x → ⊥.rec (¬Fin0 x)
Free→ℤFin→Free (suc n) =
  elimℤFin _
   (λ x → cong (Free→ℤFin (suc n)) (ℤFin→Free-ℤFinGenerator (suc n) x))
   (λ f p → cong (Free→ℤFin (suc n))
              (ℤFin→FreeInv (suc n) f) ∙ λ i r → -ℤ (p i r))
   λ f g p q → cong (Free→ℤFin (suc n))
                 (ℤFin→FreeHom (suc n) f g) ∙ λ i r → p i r + q i r

Iso-ℤFin-FreeAbGroup : (n : ℕ) → Iso (ℤ[Fin n ] .fst) (FAGAbGroup {A = Fin n} .fst)
Iso.fun (Iso-ℤFin-FreeAbGroup n) = ℤFin→Free n
Iso.inv (Iso-ℤFin-FreeAbGroup n) = Free→ℤFin n
Iso.rightInv (Iso-ℤFin-FreeAbGroup n) = ℤFin→Free→ℤFin n
Iso.leftInv (Iso-ℤFin-FreeAbGroup n) = Free→ℤFin→Free n

ℤFin≅FreeAbGroup : (n : ℕ) → AbGroupIso (ℤ[Fin n ]) (FAGAbGroup {A = Fin n})
fst (ℤFin≅FreeAbGroup n) = Iso-ℤFin-FreeAbGroup n
snd (ℤFin≅FreeAbGroup n) = makeIsGroupHom (ℤFin→FreeHom n)

-- this iso implies that ℤFin inherits the prop elimination principle of FAGAbGroup
elimPropℤFin : ∀ {ℓ} (n : ℕ)
  (A : ℤ[Fin n ] .fst → Type ℓ)
  → ((x : _) → isProp (A x))
  → (A (λ _ → 0))
  → ((x : _) → A (ℤFinGenerator x))
  → ((f g : _) → A f → A g → A λ x → f x + g x)
  → ((f : _) → A f → A (-ℤ_ ∘ f))
  → (x : _) → A x
elimPropℤFin n A pr z t s u w =
  subst A (Iso.leftInv (Iso-ℤFin-FreeAbGroup n) w) (help (ℤFin→Free n w))
  where
  help : (x : _) → A (Free→ℤFin n x)
  help = ElimProp.f (pr _) t z
    (λ {x} {y} → s (Free→ℤFin n x) (Free→ℤFin n y))
    λ {x} → u (Free→ℤFin n x)

-- functoriality of ℤFin in n

ℤFinFunctGenerator : {n m : ℕ} (f : Fin n → Fin m) (g : ℤ[Fin n ] .fst)
  (x : Fin n) → ℤ[Fin m ] .fst
ℤFinFunctGenerator {n = n} {m} f g x y with ((f x .fst) ≟ᵗ y .fst)
... | lt _ = 0
... | eq _ = g x
... | gt _ = 0

ℤFinFunctGenerator≡ : {n m : ℕ} (f : Fin n → Fin m)
  (t : Fin n)  (y : Fin m)
  → ℤFinFunctGenerator f (ℤFinGenerator t) t y
   ≡ ℤFinGenerator (f t) y
ℤFinFunctGenerator≡ f t y with (f t .fst ≟ᵗ y .fst)
... | lt _ = refl
... | eq _ = lem
  where
  lem : _
  lem with (fst t ≟ᵗ fst t)
  ... | lt q = ⊥.rec (¬m<ᵗm q)
  ... | eq _ = refl
  ... | gt q = ⊥.rec (¬m<ᵗm q)
... | gt _ = refl

ℤFinFunctFun : {n m : ℕ} (f : Fin n → Fin m)
  → ℤ[Fin n ] .fst → ℤ[Fin m ] .fst
ℤFinFunctFun {n = n} {m} f g x =
  sumFinℤ {n = n} λ y → ℤFinFunctGenerator f g y x

ℤFinFunct : {n m : ℕ} (f : Fin n → Fin m)
  → AbGroupHom (ℤ[Fin n ]) (ℤ[Fin m ])
fst (ℤFinFunct {n = n} {m} f) = ℤFinFunctFun f
snd (ℤFinFunct {n = n} {m} f) =
  makeIsGroupHom λ g h
   → funExt λ x → sumFinGenId _+_ 0
              (λ y → ℤFinFunctGenerator f (λ x → g x + h x) y x)
              (λ y → ℤFinFunctGenerator f g y x + ℤFinFunctGenerator f h y x)
              (funExt (lem g h x))
          ∙ sumFinGenHom _+_ (pos 0) (λ _ → refl) +Comm +Assoc n _ _
  where
  lem : (g h : _) (x : _) (y : Fin n)
    → ℤFinFunctGenerator f (λ x → g x + h x) y x
     ≡ ℤFinFunctGenerator f g y x + ℤFinFunctGenerator f h y x
  lem g h x y with (f y . fst ≟ᵗ x .fst)
  ... | lt _ = refl
  ... | eq _ = refl
  ... | gt _ = refl

-- Homs are equal if they agree on generators
agreeOnℤFinGenerator→≡ : ∀ {n m : ℕ}
  → {ϕ ψ : AbGroupHom (ℤ[Fin n ]) (ℤ[Fin m ])}
  → ((x : _) → fst ϕ (ℤFinGenerator x) ≡ fst ψ (ℤFinGenerator x))
  → ϕ ≡ ψ
agreeOnℤFinGenerator→≡ {n} {m} {ϕ} {ψ} idr =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
   (funExt
    (elimPropℤFin _ _ (λ _ → isOfHLevelPath' 1 (isSetΠ (λ _ → isSetℤ)) _ _)
      (IsGroupHom.pres1 (snd ϕ) ∙ sym (IsGroupHom.pres1 (snd ψ)))
      idr
      (λ f g p q → IsGroupHom.pres· (snd ϕ) f g
                 ∙∙ (λ i x → p i x + q i x)
                 ∙∙ sym (IsGroupHom.pres· (snd ψ) f g ))
      λ f p → IsGroupHom.presinv (snd ϕ) f
           ∙∙ (λ i x → -ℤ (p i x))
           ∙∙ sym (IsGroupHom.presinv (snd ψ) f)))

--
sumCoefficients : (n : ℕ) → AbGroupHom (ℤ[Fin n ]) (ℤ[Fin 1 ])
fst (sumCoefficients n) v = λ _ → sumFinℤ v
snd (sumCoefficients n) = makeIsGroupHom (λ x y → funExt λ _ → sumFinℤHom x y)

ℤFinProductIso : (n m : ℕ) → Iso (ℤ[Fin (n +ℕ m) ] .fst) ((AbDirProd ℤ[Fin n ] ℤ[Fin m ]) .fst)
ℤFinProductIso n m = iso sum→product product→sum product→sum→product sum→product→sum
  where
    sum→product : (ℤ[Fin (n +ℕ m) ] .fst) → ((AbDirProd ℤ[Fin n ] ℤ[Fin m ]) .fst)
    sum→product x = ((λ (a , Ha) → x (a , <→<ᵗ (≤-trans (<ᵗ→< Ha) (≤SumLeft {n}{m}))))
                    , λ (a , Ha) → x (n +ℕ a , <→<ᵗ (<-k+ {a}{m}{n} (<ᵗ→< Ha))))

    product→sum : ((AbDirProd ℤ[Fin n ] ℤ[Fin m ]) .fst) → (ℤ[Fin (n +ℕ m) ] .fst)
    product→sum (x , y) (a , Ha) with (a ≟ᵗ n)
    ... | lt H = x (a , H)
    ... | eq H = y (a ∸ n , <→<ᵗ (subst (a ∸ n <_) (∸+ m n) (<-∸-< a (n +ℕ m) n (<ᵗ→< Ha) (subst (λ a → a < n +ℕ m) H (<ᵗ→< Ha)))))
    ... | gt H = y (a ∸ n , <→<ᵗ (subst (a ∸ n <_) (∸+ m n) (<-∸-< a (n +ℕ m) n (<ᵗ→< Ha) (<ᵗ→< (<ᵗ-trans {n}{a}{n +ℕ m} H Ha)))))

    product→sum→product : ∀ x → sum→product (product→sum x) ≡ x
    product→sum→product (x , y) = ≡-× (funExt (λ (a , Ha) → lemx a Ha)) (funExt (λ (a , Ha) → lemy a Ha))
      where
        lemx : (a : ℕ) (Ha : a <ᵗ n) → fst (sum→product (product→sum (x , y))) (a , Ha) ≡ x (a , Ha)
        lemx a Ha with (a ≟ᵗ n)
        ... | lt H = cong x (Fin≡ (a , H) (a , Ha) refl)
        ... | eq H = rec (¬m<ᵗm (subst (λ a → a <ᵗ n) H Ha))
        ... | gt H = rec (¬m<ᵗm (<ᵗ-trans Ha H))

        lemy : (a : ℕ) (Ha : a <ᵗ m) → snd (sum→product (product→sum (x , y))) (a , Ha) ≡ y (a , Ha)
        lemy a Ha with ((n +ℕ a) ≟ᵗ n)
        ... | lt H = rec (¬m<m (≤<-trans (≤SumLeft {n}{a}) (<ᵗ→< H)))
        ... | eq H = cong y (Fin≡ _ _ (∸+ a n))
        ... | gt H = cong y (Fin≡ _ _ (∸+ a n))

    sum→product→sum : ∀ x → product→sum (sum→product x) ≡ x
    sum→product→sum x = funExt (λ (a , Ha) → lem a Ha)
      where
        lem : (a : ℕ) (Ha : a <ᵗ (n +ℕ m)) → product→sum (sum→product x) (a , Ha) ≡ x (a , Ha)
        lem a Ha with (a ≟ᵗ n)
        ... | lt H = cong x (Fin≡ _ _ refl)
        ... | eq H = cong x (Fin≡ _ _ ((+-comm n (a ∸ n)) ∙ ≤-∸-+-cancel (subst (n ≤_) (sym H) ≤-refl)))
        ... | gt H = cong x (Fin≡ _ _ ((+-comm n (a ∸ n)) ∙ ≤-∸-+-cancel (<-weaken (<ᵗ→< H))))

ℤFinProduct : (n m : ℕ) → AbGroupIso ℤ[Fin (n +ℕ m) ] (AbDirProd ℤ[Fin n ] ℤ[Fin m ])
fst (ℤFinProduct n m) = ℤFinProductIso n m
snd (ℤFinProduct n m) = makeIsGroupHom (λ x y → refl)
