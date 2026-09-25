{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.LastMinuteLemmas.Smith where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.Int
open import Cubical.Data.Bool

open import Cubical.Data.Fin as FinAlt using (isContrFin1)
open import Cubical.Data.Fin renaming (Fin to FinInd)
open import Cubical.Data.FinData
open import Cubical.Data.List renaming (length to len)

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]')
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.IntegerMatrix.Smith
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.AbGroup.Instances.Pi
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.Properties
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.AbGroup.Instances.IntMod
open import Cubical.Algebra.AbGroup.FinitePresentation

open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.ZAction
open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.Homotopy.Serre.LastMinuteLemmas.AlgebraLemmas
open import Cubical.Homotopy.Serre.LastMinuteLemmas.FinLemmas

open Coefficient ℤCommRing renaming (_⋆_ to _✦_)

-- abbreviations
module _ (n m : ℕ) where
  Matℤ : Type
  Matℤ = Mat n m

  MatℤGr : AbGroup ℓ-zero
  MatℤGr = ΠAbGroup {X = Fin n} λ _ → ΠAbGroup {X = Fin m} λ _ → ℤAbGroup

  Matℤ'Gr : AbGroup ℓ-zero
  Matℤ'Gr =
    ΠAbGroup {X = FinInd n}
      λ _ → ΠAbGroup {X = FinInd m} λ _ → ℤAbGroup

  Matℤ' : Type
  Matℤ' = fst Matℤ'Gr

  -- todo: unify Matℤ' and matℤ when only one version of Fin is used in library
  -- for now, we need the following iso:

  Matℤ≅Matℤ' : AbGroupIso MatℤGr Matℤ'Gr
  fst Matℤ≅Matℤ' =
    compIso (domIso (Iso-Fin-FinInd n))
      (codomainIso (domIso (Iso-Fin-FinInd m)))
  snd Matℤ≅Matℤ' =
    makeIsGroupHom λ f g → refl

-- Hom(ℤ[Fin n],ℤ[Fin m]) ≅ matℤ' n m
module _ (n m : ℕ) where
  FreeHom→Matrix : (ℤ[Fin n ] .fst → ℤ[Fin m ] .fst) → Matℤ' n m
  FreeHom→Matrix F x y = F (ℤFinGenerator {n = n} x) y

  Matrix→FreeHom : Matℤ' n m → ((FinInd n → ℤ) → (FinInd m → ℤ))
  Matrix→FreeHom M F x = sumFinℤ {n = n} (λ y → F y · M y x)

  FreeHom→MatrixHom : AbGroupHom (HomGroup (AbGroup→Group ℤ[Fin n ]) ℤ[Fin m ])
                                  (Matℤ'Gr n m)
  fst FreeHom→MatrixHom F = FreeHom→Matrix (fst F)
  snd FreeHom→MatrixHom = makeIsGroupHom λ _ _ → refl

  Matrix→FreeHomHom : AbGroupHom (Matℤ'Gr n m)
                        (HomGroup (AbGroup→Group ℤ[Fin n ]) ℤ[Fin m ])
  fst (fst Matrix→FreeHomHom F) = Matrix→FreeHom F
  snd (fst Matrix→FreeHomHom F) =
    makeIsGroupHom λ f g
      → funExt λ r → cong (sumFinℤ {n = n})
           (funExt (λ y → CommRingStr.·DistL+ (snd ℤCommRing) (f y) (g y) (F y r)))
           ∙ sumFinℤHom {n = n} (λ y → f y · F y r) (λ y → g y · F y r)
  snd Matrix→FreeHomHom = makeIsGroupHom λ F G
    → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
        (funExt λ g → funExt λ x
          → cong (sumFinℤ {n = n})
             (funExt (λ y → CommRingStr.·DistR+ (snd ℤCommRing) (g y) (F y x) (G y x)))
               ∙ sumFinℤHom {n = n} (λ y → g y · F y x) (λ y → g y · G y x))

  FreeHom→Matrix→FreeHom :
       compGroupHom Matrix→FreeHomHom (FreeHom→MatrixHom) ≡ idGroupHom
  FreeHom→Matrix→FreeHom =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt λ F → funExt λ x → funExt λ y
        → sym (isGeneratorℤFinGenerator' {n = n} (λ w → F w y) x))

  Matrix→FreeHom→Matrix :
       compGroupHom FreeHom→MatrixHom Matrix→FreeHomHom
     ≡ idGroupHom
  Matrix→FreeHom→Matrix =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
     (funExt λ F → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
       (funExt λ g → funExt λ y
         → funExt⁻ (cong fst (lem F y)) g))
    where
    module _ (F : AbGroupHom (ℤ[Fin n ]) ℤ[Fin m ]) (y : FinInd m) where
      F' : AbGroupHom ℤ[Fin n ] ℤAbGroup
      fst F' r = F .fst r y
      snd F' = makeIsGroupHom λ f g
        → funExt⁻ (IsGroupHom.pres· (F .snd) f g) y

      G' : AbGroupHom ℤ[Fin n ] ℤAbGroup
      fst G' r = Matrix→FreeHom (FreeHom→Matrix (fst F)) r y
      snd G' = makeIsGroupHom λ f g
        → funExt⁻ (IsGroupHom.pres·
                  (Matrix→FreeHomHom .fst
                    (FreeHom→Matrix (fst F)) .snd) f g) y

      lem : G' ≡ F'
      lem = agreeOnℤFinGenerator→≡ {n = n}
        λ t → sym (isGeneratorℤFinGenerator' {n = n}
                    (λ s → fst F (ℤFinGenerator {n = n} s) y) t)

  Matℤ'≅HomGroup : AbGroupIso (Matℤ'Gr n m)
                              (HomGroup (AbGroup→Group ℤ[Fin n ]) ℤ[Fin m ])
  Iso.fun (fst Matℤ'≅HomGroup) = Matrix→FreeHomHom .fst
  Iso.inv (fst Matℤ'≅HomGroup) = FreeHom→MatrixHom .fst
  Iso.sec (fst Matℤ'≅HomGroup) f =
    funExt⁻ (cong fst Matrix→FreeHom→Matrix) f
  Iso.ret (fst Matℤ'≅HomGroup) f =
    funExt⁻ (cong fst FreeHom→Matrix→FreeHom) f
  snd Matℤ'≅HomGroup = Matrix→FreeHomHom .snd

  -- main iso
  Matℤ≅HomGroup : AbGroupIso (MatℤGr n m)
                             (HomGroup (AbGroup→Group ℤ[Fin n ]) ℤ[Fin m ])
  Matℤ≅HomGroup = compGroupIso (Matℤ≅Matℤ' n m) Matℤ'≅HomGroup

-- Iso sends matrix multiplication to composition of homomorphisms
Matℤ≅HomGroupPresMult : (n m k : ℕ) (G : MatℤGr n m .fst) (H : MatℤGr m k .fst)
  → Iso.fun (fst (Matℤ≅HomGroup n k)) (G ✦ H)
  ≡ compGroupHom (Iso.fun (fst (Matℤ≅HomGroup n m)) G)
                 (Iso.fun (fst (Matℤ≅HomGroup m k)) H)
Matℤ≅HomGroupPresMult n m k G H = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
  (funExt λ F → funExt λ x
  → cong (sumFinℤ {n = n})
     (funExt λ r →
        (cong (F r ·_)
          ((cong (foldrFin {n = m} _+_ (pos 0))
            (funExt λ s
            → cong₂ _·_ (cong (G (FinInd→Fin n r))
                          (sym (FinInd→Fin→FinInd m refl s)))
                         (cong (λ t → H t (FinInd→Fin k x))
                          (sym (FinInd→Fin→FinInd m refl s)))))
        ∙ (λ i → sumFinℤ≡foldrFin {n = m}
                        (λ j → G (FinInd→Fin n r) (FinInd→Fin m j)
                              · H (FinInd→Fin m j) (FinInd→Fin k x)) (~ i))))
       ∙ sumFinℤMult {n = m} (F r) ((λ j →
         G (FinInd→Fin n r) (FinInd→Fin m j) ·
         H (FinInd→Fin m j) (FinInd→Fin k x)))
      ∙ cong (sumFinℤ {n = m}) (funExt λ w →
         ·Assoc (F r)
                (G (FinInd→Fin n r) (FinInd→Fin m w))
                (H (FinInd→Fin m w) (FinInd→Fin k x))
         ∙ ·Comm (F r · G (FinInd→Fin n r) (FinInd→Fin m w))
                 (H (FinInd→Fin m w) (FinInd→Fin k x))))
  ∙ sumFinℤSwap {n = n} {m}
    (λ r y → H (FinInd→Fin m y) (FinInd→Fin k x)
           · (F r · G (FinInd→Fin n r) (FinInd→Fin m y)))
  ∙ cong (sumFinℤ {n = m}) (funExt λ w →
      sym (sumFinℤMult {n = n}
            (H (FinInd→Fin m w) (FinInd→Fin k x))
            (λ y → F y · G (FinInd→Fin n y) (FinInd→Fin m w)))
      ∙ ·Comm (H (FinInd→Fin m w) (FinInd→Fin k x))
              (sumFinℤ {n = n}
                (λ y → F y · G (FinInd→Fin n y) (FinInd→Fin m w)))))

-- Matℤ≅HomGroup sends 𝟙 to the identity map
Matℤ≅HomGroupPres𝟙 : (n : ℕ)
  → Iso.fun (fst (Matℤ≅HomGroup n n)) 𝟙 ≡ idGroupHom
Matℤ≅HomGroupPres𝟙 n = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
  (funExt λ g → funExt (λ a → cong (sumFinℤ {n = n})
    (funExt (λ y → cong (g y ·_)
      ((λ i → 𝟙 (FinInd→Fin n y) (FinInd→Fin n a))
      ∙ cong (if_then 1 else 0)
             (==-comm _ _
             ∙ sym (lem2 y a (fst y ≟ᵗ fst a))) ∙ lem n a y)))
    ∙ sym (isGeneratorℤFinGenerator {n = n} g a)))
  where
  ==-< : {n : ℕ} (a b : FinInd n)
    → fst a <ᵗ fst b → false ≡ (FinInd→Fin n b == FinInd→Fin n a)
  ==-< {n = (suc n)} (zero , q) (suc b , s) p = refl
  ==-< {n = suc n} (suc a , q) (suc b , s) p = ==-< (a , q) (b , s) p

  lem2 : (a y : FinInd n) (p : _)
    → Trichotomy→Bool (fst a) (fst y) p
     ≡ (FinInd→Fin n y == FinInd→Fin n a)
  lem2 a y (lt x) = ==-< a y x
  lem2 a y (eq x) = sym (==-diag (FinInd→Fin n y))
    ∙ cong₂ _==_ refl (cong (FinInd→Fin n) (sym (Fin≡ a y x)))
  lem2 a y (gt x) = ==-< y a x ∙ ==-comm _ _

  lem : (n : ℕ) (a y : FinInd n)
    → (if Trichotomy→Bool (fst y) (fst a) (fst y ≟ᵗ fst a) then 1 else 0)
     ≡ ℤFinGenerator y a
  lem n a y with (fst y ≟ᵗ fst a)
  ... | lt x = refl
  ... | eq x = refl
  ... | gt x = refl

-- Matℤ≅HomGroup sends invertible matrices to isomorphisms
Matℤ≅HomGroupInv : (n : ℕ) (M : Matℤ n n)
  → isInv M
  → isEquiv (Iso.fun (Matℤ≅HomGroup n n .fst) M .fst)
Matℤ≅HomGroupInv n M v =
  isoToIsEquiv
    (iso _ (Iso.fun (Matℤ≅HomGroup n n .fst) M⁻ .fst)
      (λ x → sym (funExt⁻ (cong fst (Matℤ≅HomGroupPresMult n n n M⁻ M)) x)
           ∙ cong (λ s → fst (Iso.fun (fst (Matℤ≅HomGroup n n)) s) x)
                  (v .snd .snd)
           ∙ funExt⁻ (cong fst (Matℤ≅HomGroupPres𝟙 n)) x)
      (λ x → sym (funExt⁻ (cong fst (Matℤ≅HomGroupPresMult n n n M M⁻)) x)
           ∙ cong (λ s → fst (Iso.fun (fst (Matℤ≅HomGroup n n)) s) x)
                  (v .snd .fst)
           ∙ funExt⁻ (cong fst (Matℤ≅HomGroupPres𝟙 n)) x))
  where
  M⁻ = v .fst

--------- Definition of a `Smith normal homomorphism' ---------
-- Definition of underlying function
smithFun : (n m : ℕ) (l : List ℤ)
  → ℤ[Fin (len l +ℕ n) ] .fst → ℤ[Fin (len l +ℕ m)] .fst
smithFun n m [] x _ = 0
smithFun n m (x ∷ xs) F =
  elimFin-alt {A = λ _ → ℤ}
    (x · F fzero)
    (smithFun n m xs (F ∘ fsuc))

-- Map as a homomorphism
smithHom : (n m : ℕ) (l : List ℤ)
  → AbGroupHom ℤ[Fin (len l +ℕ n) ] ℤ[Fin (len l +ℕ m) ]
fst (smithHom n m l) = smithFun n m l
snd (smithHom n m []) = trivGroupHom .snd
snd (smithHom n m (x ∷ xs)) =
  makeIsGroupHom λ f g → funExt
    (elimFin-alt
      (elimFin-altβ {m = len xs +ℕ m}
        (x · (f (0 , tt) + g (0 , tt)))
        (smithFun n m xs (λ x₁ → f (fsuc x₁) + g (fsuc x₁))) .fst
      ∙ ·DistR+ x (f fzero) (g fzero)
      ∙ cong₂ _+_ (sym (elimFin-altβ {m = len xs +ℕ m}
                        (x · f (0 , tt))
                        (smithFun n m xs (f ∘ fsuc)) .fst))
                  (sym (elimFin-altβ {m = len xs +ℕ m}
                        (x · g (0 , tt))
                        (smithFun n m xs (g ∘ fsuc)) .fst)))
    λ t → elimFin-altβ {m = len xs +ℕ m}
        (x · (f fzero + g fzero))
        (smithFun n m xs (λ x₁ → f (fsuc x₁) + g (fsuc x₁))) .snd t
         ∙ funExt⁻ (IsGroupHom.pres· (smithHom n m xs .snd)
                                     (f ∘ fsuc) (g ∘ fsuc)) t
         ∙ cong₂ _+_
             (sym (elimFin-altβ {m = len xs +ℕ m}
                        (x · f (0 , tt))
                        (smithFun n m xs (f ∘ fsuc)) .snd t))
             (sym (elimFin-altβ {m = len xs +ℕ m}
                        (x · g (0 , tt))
                        (smithFun n m xs (g ∘ fsuc)) .snd t)))

smithFunPres0 : (n m : ℕ) (xs : List ℤ) (t : _)
  → smithFun n m xs (λ _ → pos 0) t ≡ 0
smithFunPres0 n m [] (x , w) = refl
smithFunPres0 n m (x ∷ xs) (zero , s) =
  cong (λ G → elimFin-alt {m = len xs +ℕ m} {A = λ _ → ℤ}
                  (x · pos 0) G (zero , s))
       (funExt (smithFunPres0 n m xs))
  ∙ elimFin-altβ {m = len xs +ℕ m} {A = λ _ → ℤ}
                 (x · 0) (λ _ → 0) .fst
  ∙ ·Comm x (pos 0)
smithFunPres0 n m (x ∷ xs) (suc t , s) =
    cong (λ G → elimFin-alt {m = len xs +ℕ m} {A = λ _ → ℤ}
                  (x · pos 0) G (suc t , s))
      (funExt (smithFunPres0 n m xs))
  ∙ cong (elimFin-alt {m = len xs +ℕ m} {A = λ _ → ℤ}
           (x · 0) (λ _ → 0))
           (Fin≡ {m = suc (len xs +ℕ m)} (suc t , s) (fsuc (t , s)) refl)
  ∙ elimFin-altβ {m = len xs +ℕ m} {A = λ _ → ℤ}
                 (x · 0) (λ _ → 0) .snd (t , s)


-- Matℤ≅HomGroup⁻¹ takes Smith normal maps to to Smith normal matrices
Matℤ≅HomGroup⁻¹-presSmith : (n m : ℕ) (l : List ℤ)
  → Iso.inv (Matℤ≅HomGroup _ _ .fst) (smithHom n m l) ≡ smithMat l n m
Matℤ≅HomGroup⁻¹-presSmith n m [] = refl
Matℤ≅HomGroup⁻¹-presSmith n m (x ∷ xs) i zero zero =
  (elimFin-altβ {m = len xs +ℕ m} {A = λ _ → ℤ}
    (x · pos 1) (smithFun n m xs (λ x₁ → pos 0)) .fst
   ∙ ·Comm x (pos 1)) i
Matℤ≅HomGroup⁻¹-presSmith n m (x ∷ xs) i zero (suc b) =
  (elimFin-altβ {m = len xs +ℕ m} {A = λ _ → ℤ}
    (x · pos 1)
    (smithFun n m xs (λ x₁ → pos 0)) .snd (Fin→FinInd (len xs +ℕ m) b)
   ∙ smithFunPres0 n m xs (Fin→FinInd (len xs +ℕ m) b)) i
Matℤ≅HomGroup⁻¹-presSmith n m (x ∷ xs) i (suc a) zero =
   (elimFin-altβ {m = len xs +ℕ m} {A = λ _ → ℤ} (x · pos 0)
                 (smithFun n m xs
                 (ℤFinGenerator {n = suc (len xs +ℕ n)}
                   (fsuc (Fin→FinInd (len xs +ℕ n) a)) ∘ fsuc)) .fst
  ∙ ·Comm x (pos 0)) i
Matℤ≅HomGroup⁻¹-presSmith n m (x ∷ xs) i (suc a) (suc b) =
  (elimFin-altβ {m = len xs +ℕ m} {A = λ _ → ℤ} (x · pos 0)
                 (smithFun n m xs
                 (ℤFinGenerator {n = suc (len xs +ℕ n)}
                   (fsuc (Fin→FinInd (len xs +ℕ n) a)) ∘ fsuc)) .snd
                    (Fin→FinInd (len xs +ℕ m) b)
  ∙ cong (λ G → smithFun n m xs G (Fin→FinInd (len xs +ℕ m) b))
         (funExt (λ s →
           sym (ℤFinGenerator-fsuc
                (len xs +ℕ n) (Fin→FinInd (len xs +ℕ n) a) s)))
  ∙ funExt⁻ (funExt⁻ (Matℤ≅HomGroup⁻¹-presSmith n m xs) a) b) i

-- Other direction
Matℤ≅HomGroup-presSmith : (n m : ℕ) (l : List ℤ)
  → Iso.fun (Matℤ≅HomGroup _ _ .fst) (smithMat l n m) ≡ smithHom n m l
Matℤ≅HomGroup-presSmith n m l =
  sym (cong (Iso.fun (Matℤ≅HomGroup _ _ .fst) )
            (Matℤ≅HomGroup⁻¹-presSmith n m l))
  ∙ Iso.sec (Matℤ≅HomGroup _ _ .fst) (smithHom n m l)

-------- Goal : ℤ[Fin]/ImSmith ≅ ℤᵐ × ℤ/a₁ × ... × ℤ/aₙ --------
-- Definition of ℤᵐ × ℤ/a₁ × ... × ℤ/aₙ
FPGroupNormalForm : (m : ℤ) → List ℤ → AbGroup ℓ-zero
FPGroupNormalForm m [] = dirProdAbIt (abs m) ℤAbGroup
FPGroupNormalForm m (x ∷ xs) =
  dirProdAb (ℤAbGroup/' x) (FPGroupNormalForm m xs)

-- Alternative definition using other defintion of ℤ/ k
FPGroupNormalForm' : (m : ℤ) → List ℤ → AbGroup ℓ-zero
FPGroupNormalForm' m [] = dirProdAbIt (abs m) ℤAbGroup
FPGroupNormalForm' m (x ∷ xs) =
  dirProdAb (ℤAbGroup/ (abs x)) (FPGroupNormalForm' m xs)

-- The two definitions agree
FPGroupNormalForm≅FPGroupNormalForm' : (m : ℤ) (l : List ℤ)
  → AbGroupIso (FPGroupNormalForm m l) (FPGroupNormalForm' m l)
FPGroupNormalForm≅FPGroupNormalForm' m [] = idGroupIso
FPGroupNormalForm≅FPGroupNormalForm' m (x ∷ l) =
  GroupIsoDirProd (ℤAbGroup/≅ℤAbGroup/' x)
                  (FPGroupNormalForm≅FPGroupNormalForm' m l)

-- ℤ[Fin m+1] → ℤ/k × ℤ/Im(SmithHom)
ℤ[Fin]→ℤAbGroup/'×ℤ[Fin]/ImSmith : (n m : ℕ) (l : List ℤ) (x : ℤ)
  → AbGroupHom (ℤ[Fin suc (len l +ℕ m) ])
                (dirProdAb (ℤAbGroup/' x)
                           (ℤ[Fin (len l +ℕ m) ] /Im smithHom n m l))
fst (ℤ[Fin]→ℤAbGroup/'×ℤ[Fin]/ImSmith n m l x) F = [ F fzero ]' , [ F ∘ fsuc ]'
snd (ℤ[Fin]→ℤAbGroup/'×ℤ[Fin]/ImSmith n m l x) = makeIsGroupHom (λ F G → refl)

ℤ[Fin]/ImSmith→ℤAbGroup/'×ℤ[Fin]/ImSmith : (n m : ℕ) (l : List ℤ) (x : _)
  → AbGroupHom (ℤ[Fin suc (len l +ℕ m) ] /Im smithHom n m (x ∷ l))
      (dirProdAb (ℤAbGroup/' x)
                 (ℤ[Fin (len l +ℕ m) ] /Im smithHom n m l))
ℤ[Fin]/ImSmith→ℤAbGroup/'×ℤ[Fin]/ImSmith n m l x =
  /ImElim (smithHom n m (x ∷ l)) (ℤ[Fin]→ℤAbGroup/'×ℤ[Fin]/ImSmith n m l x)
    (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt λ F → ΣPathP (cong [_]' ((elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ}
        (x · F fzero) (smithFun n m l (F ∘ fsuc)) .fst))
        ∙ eq/ _ _ ∣ F fzero , sym (ℤ·≡· x (F fzero)) ∣₁
      , cong [_]' (funExt (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ}
        (x · F fzero) (smithFun n m l (F ∘ fsuc)) .snd))
      ∙ eq/ _ _ ∣ (F ∘ fsuc) , refl ∣₁)))

ℤ[Fin]/ImSmith→ℤ[Fin]/ImSmith : (n m : ℕ) (l : List ℤ) (x : _)
  → AbGroupHom (ℤ[Fin (len l +ℕ m) ] /Im smithHom n m l)
                (ℤ[Fin (suc (len l +ℕ m)) ] /Im smithHom n m (x ∷ l))
ℤ[Fin]/ImSmith→ℤ[Fin]/ImSmith n m l x = /ImElim _ ϕ main
  where
  ϕ : AbGroupHom ℤ[Fin len l +ℕ m ]
                   (ℤ[Fin suc (len l +ℕ m) ] /Im smithHom n m (x ∷ l))
  fst ϕ f = [ elimFin-alt 0 f ]'
  snd ϕ = makeIsGroupHom λ f g → cong [_]'
          (funExt (elimFin-alt
            (elimFin-altβ {m = len l +ℕ m} (pos 0) (λ x → f x + g x) .fst
          ∙ cong₂ _+_ (sym (elimFin-altβ {m = len l +ℕ m} (pos 0) f .fst))
                      (sym (elimFin-altβ {m = len l +ℕ m} (pos 0) g .fst)))
          λ r → elimFin-altβ {m = len l +ℕ m} (pos 0) (λ x → f x + g x) .snd r
              ∙ cong₂ _+_ (sym (elimFin-altβ {m = len l +ℕ m} (pos 0) f .snd r))
                          (sym (elimFin-altβ {m = len l +ℕ m} (pos 0) g .snd r))))

  main : compGroupHom (smithHom n m l) ϕ ≡ trivGroupHom
  main = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt λ t → eq/ _ _ ∣ (elimFin-alt 0 t)
     , (funExt (elimFin-alt
       (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ}
         (x · elimFin-alt {m = len l +ℕ n} {A = λ _ → ℤ} (pos 0) t (0 , tt))
         (smithFun n m l
           (λ x₁ → elimFin-alt {m = len l +ℕ n} {A = λ _ → ℤ}
                     (pos 0) t (fsuc x₁))) .fst
      ∙ cong (x ·_) (elimFin-altβ {m = len l +ℕ n} {A = λ _ → ℤ} (pos 0) t .fst)
      ∙ ·Comm x 0
      ∙ sym (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ}
               (pos 0) (smithFun n m l t) .fst))
     λ s → elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ}
           (x · elimFin-alt {m = len l +ℕ n} {A = λ _ → ℤ} (pos 0) t (0 , tt))
           (smithFun n m l (λ x₁ → elimFin-alt {m = len l +ℕ n} {A = λ _ → ℤ}
                                      (pos 0) t (fsuc x₁))) .snd s
          ∙ cong (λ w → smithFun n m l w s)
                 (funExt (elimFin-altβ {m = len l +ℕ n} {A = λ _ → ℤ}
                           (pos 0) t .snd))
          ∙ sym (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ}
                   (pos 0) (smithFun n m l t) .snd s))) ∣₁)

ℤAbGroup/'→ℤ[Fin]/ImSmith : (n m : ℕ) (l : List ℤ) (x : _)
  → AbGroupHom (ℤAbGroup/' x)
                (ℤ[Fin (suc (len l +ℕ m)) ] /Im smithHom n m (x ∷ l))
ℤAbGroup/'→ℤ[Fin]/ImSmith n m l x = /ImElim _ ϕ mainEq
  where
  ϕ : AbGroupHom ℤAbGroup (ℤ[Fin (suc (len l +ℕ m)) ] /Im smithHom n m (x ∷ l))
  fst ϕ x = [ elimFin-alt x (λ _ → 0) ]'
  snd ϕ = makeIsGroupHom λ x y →
    cong [_]' (funExt (elimFin-alt
    (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ} (x + y) (λ _ → pos 0) .fst
    ∙ cong₂ _+_
       (sym (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ} x (λ _ → 0) .fst))
       (sym (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ} y (λ _ → 0) .fst)))
       λ s → elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ} (x + y) (λ _ → pos 0)
            .snd s
           ∙ cong₂ _+_
       (sym (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ} x (λ _ → 0) .snd s))
       (sym (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ} y (λ _ → 0) .snd s))))

  mainEq : compGroupHom (multₗHom ℤAbGroup x) ϕ ≡ trivGroupHom
  mainEq = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt λ w → eq/ _ _ ∣ elimFin-alt w (λ _ → 0)
      , cong₂ elimFin-alt
         (cong (x ·_)
           (elimFin-altβ {m = len l +ℕ n} {A = λ _ → ℤ} w (λ _ → pos 0) .fst))
         (cong (smithFun n m l)
           (funExt
             (elimFin-altβ {m = len l +ℕ n} {A = λ _ → ℤ} w (λ _ → pos 0) .snd))
           ∙ funExt (smithFunPres0 n m l))
      ∙ cong₂ elimFin-alt (ℤ·≡· x w) refl ∣₁)

ℤAbGroup/'×ℤ[Fin]/ImSmith→ℤ[Fin]/ImSmith : (n m : ℕ) (l : List ℤ) (x : _)
  → AbGroupHom (dirProdAb (ℤAbGroup/' x) (ℤ[Fin (len l +ℕ m) ] /Im smithHom n m l))
                (ℤ[Fin (suc (len l +ℕ m)) ] /Im smithHom n m (x ∷ l))
fst (ℤAbGroup/'×ℤ[Fin]/ImSmith→ℤ[Fin]/ImSmith n m l x) (a , b) =
  AbGroupStr._+_ (snd ((ℤ[Fin (suc (len l +ℕ m)) ] /Im smithHom n m (x ∷ l))))
    (ℤAbGroup/'→ℤ[Fin]/ImSmith n m l x .fst a)
    (ℤ[Fin]/ImSmith→ℤ[Fin]/ImSmith n m l x .fst b)
snd (ℤAbGroup/'×ℤ[Fin]/ImSmith→ℤ[Fin]/ImSmith n m l x) = makeIsGroupHom
  (uncurry (SQ.elimProp2 (λ _ _ → isPropΠ λ _ → squash/ _ _)
    λ a b → uncurry (SQ.elimProp2 (λ _ _ → squash/ _ _)
      λ c d → cong [_]' (funExt λ s
        → elimFin-alt++ (len l +ℕ m) (a + c) 0 (λ _ → 0) (λ x → b x + d x) s
        ∙ cong (λ w → elimFin-alt {m = len l +ℕ m} {A = λ _ → ℤ}
                        (a + c) w s)
                        (funExt (λ s
                        → +Comm (pos 0) (b s + d s)
                        ∙ (λ _ → b s + d s)
                        ∙ cong₂ _+_ (+Comm (b s) 0) (+Comm (d s) 0)))
        ∙ sym (elimFin-alt++ (len l +ℕ m) a c (λ x → 0 + b x) (λ x → 0 + d x) s)
        ∙ sym (cong₂ _+_ (elimFin-alt++ (len l +ℕ m) a 0 (λ _ → 0) b s)
                         (elimFin-alt++ (len l +ℕ m) c 0 (λ _ → 0) d s))))))

ℤ[Fin]/ImSmith≅ℤAbGroup/'×ℤ[Fin]/ImSmith : (n m : ℕ) (l : List ℤ) (x : _)
  → AbGroupIso (ℤ[Fin suc (len l +ℕ m) ] /Im smithHom n m (x ∷ l))
                (dirProdAb (ℤAbGroup/' x)
                           (ℤ[Fin (len l +ℕ m) ] /Im smithHom n m l))
Iso.fun (fst (ℤ[Fin]/ImSmith≅ℤAbGroup/'×ℤ[Fin]/ImSmith n m l x)) =
  fst (ℤ[Fin]/ImSmith→ℤAbGroup/'×ℤ[Fin]/ImSmith n m l x)
Iso.inv (fst (ℤ[Fin]/ImSmith≅ℤAbGroup/'×ℤ[Fin]/ImSmith n m l x)) =
  fst (ℤAbGroup/'×ℤ[Fin]/ImSmith→ℤ[Fin]/ImSmith n m l x)
Iso.sec (fst (ℤ[Fin]/ImSmith≅ℤAbGroup/'×ℤ[Fin]/ImSmith n m l x)) =
  uncurry (SQ.elimProp (λ _ → isPropΠ λ _ → isSetΣ squash/ (λ _ → squash/) _ _)
    λ a → SQ.elimProp (λ _ → isSetΣ squash/ (λ _ → squash/) _ _)
      λ b → ΣPathP (cong [_]'
        (cong₂ _+_
         (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ} a (λ _ → pos 0) .fst)
         (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ} (pos 0) b .fst))
        , cong [_]' (funExt λ s → cong₂ _+_
            (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ} a (λ _ → pos 0) .snd s)
            (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ} (pos 0) b .snd s)
          ∙ +Comm 0 (b s))))
Iso.ret (fst (ℤ[Fin]/ImSmith≅ℤAbGroup/'×ℤ[Fin]/ImSmith n m l x)) =
  SQ.elimProp (λ _ → squash/ _ _)
  λ f → cong [_]' (funExt
    (elimFin-alt
      (cong₂ _+_ (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ}
                  (f fzero) (λ _ → pos 0) .fst)
                 (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ}
                  0 (f ∘ fsuc) .fst))
      λ s → cong₂ _+_
              (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ}
                  (f fzero) (λ _ → pos 0) .snd s)
              (elimFin-altβ {m = len l +ℕ m} {A = λ _ → ℤ}
                  0 (f ∘ fsuc) .snd s)
            ∙ +Comm 0 (f (fsuc s))))
snd (ℤ[Fin]/ImSmith≅ℤAbGroup/'×ℤ[Fin]/ImSmith n m l x) =
  ℤ[Fin]/ImSmith→ℤAbGroup/'×ℤ[Fin]/ImSmith n m l x .snd

-- ℤ[Fin]/ImSmith ≅ ℤᵐ × ℤ/a₁ × ... × ℤ/aₙ
FPGroupNormalFormIso : (n m : ℕ) (l : List ℤ)
  → AbGroupIso (ℤ[Fin (len l +ℕ m) ] /Im smithHom n m l)
                (FPGroupNormalForm (pos m) l)
FPGroupNormalFormIso n m [] = compGroupIso (invGroupIso (trivialRelIso _
    λ f g → PT.rec (isSetΠ (λ _ → isSetℤ) _ _)
    (uncurry λ s t → funExt λ x
      → sym (cong (g x +_) (+Comm (f x) (- g x))
      ∙ +Assoc (g x) (- g x) (f x)
      ∙ cong₂ _+_ (AbGroupStr.+InvR (snd ℤAbGroup) (g x)) refl
      ∙ +Comm 0 (f x))
      ∙ sym (cong (g x +_) (funExt⁻ t x))))) (ℤ[Fin]≅ℤᵐ m)
FPGroupNormalFormIso n m (x ∷ l) =
  compGroupIso (ℤ[Fin]/ImSmith≅ℤAbGroup/'×ℤ[Fin]/ImSmith n m l x)
               (GroupIsoDirProd idGroupIso (FPGroupNormalFormIso n m l))

-- G ≅ ℤᵐ × ℤ/a₁ × ... × ℤ/aₙ for any Finitely presented group
module _ {ℓ} {G : AbGroup ℓ} (fpG : FinitePresentation G) where
  private
    open FinitePresentation fpG
    S = smith (Iso.inv (fst (Matℤ≅HomGroup nRels nGens)) rels)
    M = Iso.inv (fst (Matℤ≅HomGroup nRels nGens)) rels
    open Smith S
    open Sim sim
    open SimRel simrel
    open isSmithNormal isnormal

    L = transMatL
    L⁻ = isInvTransL .fst

    R = transMatR
    R⁻ = isInvTransR .fst

    T = result

    LMR≡T : L ✦ M ✦ R ≡ T
    LMR≡T = sym transEq

    M≡L⁻TR⁻ : M ≡ L⁻ ✦ T ✦ R⁻
    M≡L⁻TR⁻ =
      M                          ≡⟨ sym (⋆lUnit M) ⟩
      𝟙 ✦ M                     ≡⟨ (λ i → ⋆rUnit (isInvTransL .snd .snd (~ i) ✦ M) (~ i)) ⟩
      (L⁻ ✦ L) ✦ M ✦ 𝟙          ≡⟨ cong₂ _✦_ (sym (⋆Assoc L⁻ L M)) (sym (isInvTransR .snd .fst)) ⟩
      L⁻ ✦ (L ✦ M) ✦ (R ✦ R⁻)   ≡⟨  (⋆Assoc (L⁻ ✦ (L ✦ M)) R R⁻)  ⟩
      L⁻ ✦ (L ✦ M) ✦ R ✦ R⁻     ≡⟨ cong (_✦ R⁻) (sym (⋆Assoc L⁻ (L ✦ M) R)) ⟩
      (L⁻ ✦ ((L ✦ M) ✦ R)) ✦ R⁻ ≡⟨ cong (λ X → (L⁻ ✦ X) ✦ R⁻) LMR≡T ⟩
      L⁻ ✦ T ✦ R⁻ ∎

    ϕₘ : AbGroupHom ℤ[Fin nRels ] ℤ[Fin nGens ]
    ϕₘ = Iso.fun (fst (Matℤ≅HomGroup nRels nGens)) T

    ϕₗ : AbGroupEquiv ℤ[Fin nRels ] ℤ[Fin nRels ]
    fst (fst ϕₗ) = fst (Iso.fun (fst (Matℤ≅HomGroup nRels nRels)) L⁻)
    snd (fst ϕₗ) =
      Matℤ≅HomGroupInv nRels L⁻
        (L , isInvTransL .snd .snd , isInvTransL .snd .fst)
    snd ϕₗ = snd (Iso.fun (fst (Matℤ≅HomGroup nRels nRels)) L⁻)

    ϕᵣ : AbGroupEquiv ℤ[Fin nGens ] ℤ[Fin nGens ]
    fst (fst ϕᵣ) = fst (Iso.fun (fst (Matℤ≅HomGroup nGens nGens)) R⁻)
    snd (fst ϕᵣ) =
      Matℤ≅HomGroupInv nGens R⁻
        (R , isInvTransR .snd .snd , isInvTransR .snd .fst)
    snd ϕᵣ = snd (Iso.fun (fst (Matℤ≅HomGroup nGens nGens)) R⁻)

    ϕₘ≡ : (ℤ[Fin nGens ] /Im ϕₘ)
        ≡ (ℤ[Fin (len (divs .fst) +ℕ colNull) ]
          /Im smithHom rowNull colNull (divs .fst))
    ϕₘ≡ = (λ i → ℤ[Fin colEq (~ i) ]
                 /Im Iso.fun (Matℤ≅HomGroup _ _ .fst) (matEq (~ i)))
        ∙ cong (ℤ[Fin (len (divs .fst) +ℕ colNull) ] /Im_)
               (Matℤ≅HomGroup-presSmith rowNull colNull (divs .fst))

    rels≡ : rels ≡ compGroupHom (GroupEquiv→GroupHom ϕₗ)
                   (compGroupHom ϕₘ (GroupEquiv→GroupHom ϕᵣ))
    rels≡ = sym (Iso.sec (fst (Matℤ≅HomGroup nRels nGens)) rels)
          ∙ cong (Iso.fun (fst (Matℤ≅HomGroup nRels nGens)))
                 M≡L⁻TR⁻
          ∙ Matℤ≅HomGroupPresMult nRels nGens nGens (L⁻ ✦ T) R⁻
          ∙ cong (λ F → compGroupHom F (GroupEquiv→GroupHom ϕᵣ))
                 (Matℤ≅HomGroupPresMult nRels nRels nGens L⁻ T)
          ∙ Σ≡Prop (λ _ → isPropIsGroupHom _ _) refl

  -- main
  isFP→isFPGroupNormalForm :
    Σ[ l ∈ List ℤ ] Σ[ n ∈ ℕ ] (AbGroupIso G (FPGroupNormalForm' (pos n) l))
  fst isFP→isFPGroupNormalForm = divs .fst
  fst (snd isFP→isFPGroupNormalForm) = colNull
  snd (snd isFP→isFPGroupNormalForm) =
    compGroupIso fpiso
      (compGroupIso {G = _} {H = AbGroup→Group (ℤ[Fin nGens ] /Im ϕₘ)}
        (Hom/ImIso rels ϕₘ
          (GroupEquiv→GroupIso ϕₗ) (GroupEquiv→GroupIso (invGroupEquiv ϕᵣ))
          λ t → sym (retEq (fst ϕᵣ) _)
                ∙ cong (fst (Iso.fun (fst (Matℤ≅HomGroup nGens nGens)) R))
                       (sym (funExt⁻ (cong fst rels≡) t)))
          (compGroupIso (GroupEquiv→GroupIso
            (invEq (AbGroupPath (ℤ[Fin nGens ] /Im ϕₘ)
              ((ℤ[Fin (len (divs .fst) +ℕ colNull) ]
              /Im smithHom rowNull colNull (divs .fst)))) ϕₘ≡))
              (compGroupIso (FPGroupNormalFormIso _ _ _)
                (FPGroupNormalForm≅FPGroupNormalForm' _ _))))
