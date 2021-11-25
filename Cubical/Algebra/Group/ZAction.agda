-- Left ℤ-multiplication on groups and some of its properties
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.Group.ZAction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Int
  renaming (_·_ to _*_ ; _+_ to _+ℤ_ ; _-_ to _-ℤ_)
open import Cubical.Data.Nat
  hiding (_·_) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sum

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int renaming (ℤ to ℤGroup)
open import Cubical.Algebra.Group.DirProd

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' : Level

open Iso
open GroupStr
open IsGroupHom

_ℤ[_]·_ : ℤ → (G : Group ℓ) → fst G → fst G
pos zero ℤ[ G' ]· g = 1g (snd G')
pos (suc n) ℤ[ G' ]· g = _·_ (snd G') g (pos n ℤ[ G' ]· g)
negsuc zero ℤ[ G' ]· g = inv (snd G') g
negsuc (suc n) ℤ[ G' ]· g =
  _·_ (snd G') (inv (snd G') g) (negsuc n ℤ[ G' ]· g)

homPresℤ· : {G : Group ℓ} {H : Group ℓ'}
         → (ϕ : GroupHom G H)
         → (x : fst G) (z : ℤ)
         → fst ϕ (z ℤ[ G ]· x) ≡ (z ℤ[ H ]· fst ϕ x)
homPresℤ· (ϕ , ϕhom) x (pos zero) = pres1 ϕhom
homPresℤ· {H = H} (ϕ , ϕhom) x (pos (suc n)) =
    pres· ϕhom _ _
  ∙ cong (_·_ (snd H) (ϕ x)) (homPresℤ· (ϕ , ϕhom) x (pos n))
homPresℤ· (ϕ , ϕhom) x (negsuc zero) = presinv ϕhom _
homPresℤ· {H = H} (ϕ , ϕhom) x (negsuc (suc n)) =
    pres· ϕhom _ _
  ∙ cong₂ (_·_ (snd H)) (presinv ϕhom x)
                        (homPresℤ· (ϕ , ϕhom) x (negsuc n))

rUnitℤ· : (G : Group ℓ) (x : ℤ) → (x ℤ[ G ]· 1g (snd G)) ≡ 1g (snd G)
rUnitℤ· G (pos zero) = refl
rUnitℤ· G (pos (suc n)) =
    cong (_·_ (snd G) (1g (snd G)))
      (rUnitℤ· G (pos n))
  ∙ lid (snd G) (1g (snd G))
rUnitℤ· G (negsuc zero) = GroupTheory.inv1g G
rUnitℤ· G (negsuc (suc n)) =
    cong₂ (_·_ (snd G)) (GroupTheory.inv1g G) (rUnitℤ· G (negsuc n))
  ∙ lid (snd G) (1g (snd G))

rUnitℤ·ℤ : (x : ℤ) → (x ℤ[ ℤGroup ]· 1) ≡ x
rUnitℤ·ℤ (pos zero) = refl
rUnitℤ·ℤ (pos (suc n)) = cong (pos 1 +ℤ_) (rUnitℤ·ℤ (pos n)) ∙ sym (pos+ 1 n)
rUnitℤ·ℤ (negsuc zero) = refl
rUnitℤ·ℤ (negsuc (suc n)) = cong (-1 +ℤ_) (rUnitℤ·ℤ (negsuc n))
                          ∙ +Comm (negsuc 0) (negsuc n)

private
  precommℤ : (G : Group ℓ) (g : fst G) (y : ℤ)
           → (snd G · (y ℤ[ G ]· g)) g ≡ (sucℤ y ℤ[ G ]· g)
  precommℤ G g (pos zero) = lid (snd G) g ∙ sym (rid (snd G) g)
  precommℤ G g (pos (suc n)) =
       sym (assoc (snd G) _ _ _)
     ∙ cong ((snd G · g)) (precommℤ G g (pos n))
  precommℤ G g (negsuc zero) = invl (snd G) g
  precommℤ G g (negsuc (suc n)) =
    sym (assoc (snd G) _ _ _)
    ∙ cong ((snd G · inv (snd G) g)) (precommℤ G g (negsuc n))
    ∙ negsucLem n
    where
    negsucLem : (n : ℕ) → (snd G · inv (snd G) g)
      (sucℤ (negsuc n) ℤ[ G ]· g)
      ≡ (sucℤ (negsuc (suc n)) ℤ[ G ]· g)
    negsucLem zero = (rid (snd G) _)
    negsucLem (suc n) = refl

module _ (G : Group ℓ) (g : fst G) where
  private
    lem : (y : ℤ) → (predℤ y ℤ[ G ]· g)
                   ≡ (snd G · inv (snd G) g) (y ℤ[ G ]· g)
    lem (pos zero) = sym (rid (snd G) _)
    lem (pos (suc n)) =
         sym (lid (snd G) ((pos n ℤ[ G ]· g)))
      ∙∙ cong (λ x → _·_ (snd G) x (pos n ℤ[ G ]· g))
              (sym (invl (snd G) g))
      ∙∙ sym (assoc (snd G) _ _ _)
    lem (negsuc n) = refl

  distrℤ· : (x y : ℤ) → ((x +ℤ y) ℤ[ G ]· g)
           ≡ _·_ (snd G) (x ℤ[ G ]· g) (y ℤ[ G ]· g)
  distrℤ· (pos zero) y = cong (_ℤ[ G ]· g) (+Comm 0 y)
                            ∙ sym (lid (snd G) _)
  distrℤ· (pos (suc n)) (pos n₁) =
      cong (_ℤ[ G ]· g) (sym (pos+ (suc n) n₁))
    ∙ cong (_·_ (snd G) g)
           (cong (_ℤ[ G ]· g) (pos+ n n₁) ∙ distrℤ· (pos n) (pos n₁))
    ∙ assoc (snd G) _ _ _
  distrℤ· (pos (suc n)) (negsuc zero) =
      distrℤ· (pos n) 0
    ∙ ((rid (snd G) (pos n ℤ[ G ]· g) ∙ sym (lid (snd G) (pos n ℤ[ G ]· g)))
    ∙ cong (λ x → _·_ (snd G) x (pos n ℤ[ G ]· g))
           (sym (invl (snd G) g)) ∙ sym (assoc (snd G) _ _ _))
    ∙ (assoc (snd G) _ _ _)
    ∙ cong (λ x → _·_ (snd G)  x (pos n ℤ[ G ]· g)) (invl (snd G) g)
    ∙ lid (snd G) _
    ∙ sym (rid (snd G) _)
    ∙ (cong (_·_ (snd G) (pos n ℤ[ G ]· g)) (sym (invr (snd G) g))
    ∙ assoc (snd G) _ _ _)
    ∙ cong (λ x → _·_ (snd G)  x (inv (snd G) g))
           (precommℤ G g (pos n))
  distrℤ· (pos (suc n)) (negsuc (suc n₁)) =
       cong (_ℤ[ G ]· g) (predℤ+negsuc n₁ (pos (suc n)))
    ∙∙ distrℤ· (pos n) (negsuc n₁)
    ∙∙ (cong (λ x → _·_ (snd G) x (negsuc n₁ ℤ[ G ]· g))
             ((sym (rid (snd G) (pos n ℤ[ G ]· g))
             ∙ cong (_·_ (snd G) (pos n ℤ[ G ]· g)) (sym (invr (snd G) g)))
           ∙∙ assoc (snd G) _ _ _
           ∙∙ cong (λ x → _·_ (snd G) x (inv (snd G) g)) (precommℤ G g (pos n)))
      ∙ sym (assoc (snd G) _ _ _))
  distrℤ· (negsuc zero) y =
      cong (_ℤ[ G ]· g) (+Comm -1 y) ∙ lem y
  distrℤ· (negsuc (suc n)) y =
       cong (_ℤ[ G ]· g) (+Comm (negsuc (suc n)) y)
    ∙∙ lem (y +negsuc n)
    ∙∙ cong (snd G · inv (snd G) g)
            (cong (_ℤ[ G ]· g) (+Comm y (negsuc n)) ∙ distrℤ· (negsuc n) y)
     ∙ (assoc (snd G) _ _ _)

GroupHomℤ→ℤpres- : (e : GroupHom ℤGroup ℤGroup) (a : ℤ)
                  → fst e (- a) ≡ - fst e a
GroupHomℤ→ℤpres- e a =
  cong (fst e) (minus≡0- a) ∙∙ presinv (snd e) a ∙∙ sym (minus≡0- _)

ℤ·≡· : (a b : ℤ) → a * b ≡ (a ℤ[ ℤGroup ]· b)
ℤ·≡· (pos zero) b = refl
ℤ·≡· (pos (suc n)) b = cong (b +ℤ_) (ℤ·≡· (pos n) b)
ℤ·≡· (negsuc zero) b = minus≡0- b
ℤ·≡· (negsuc (suc n)) b = cong₂ _+ℤ_ (minus≡0- b) (ℤ·≡· (negsuc n) b)

GroupHomℤ→ℤPres· : (e : GroupHom ℤGroup ℤGroup) (a b : ℤ)
                  → fst e (a * b) ≡ a * fst e b
GroupHomℤ→ℤPres· e a b =
  cong (fst e) (ℤ·≡· a b) ∙∙ homPresℤ· e b a ∙∙ sym (ℤ·≡· a (fst e b))

-- Generators in terms of ℤ-multiplication
-- Todo : generalise
gen₁-by : (G : Group ℓ) → (g : fst G) → Type _
gen₁-by G g = (h : fst G)
          → Σ[ a ∈ ℤ ] h ≡ (a ℤ[ G ]· g)

gen₂-by : ∀ {ℓ} (G : Group ℓ) → (g₁ g₂ : fst G) → Type _
gen₂-by G g₁ g₂ =
  (h : fst G) → Σ[ a ∈ ℤ × ℤ ] h ≡ _·_ (snd G) ((fst a) ℤ[ G ]· g₁) ((snd a) ℤ[ G ]· g₂)

Iso-pres-gen₁ : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') (g : fst G)
  → gen₁-by G g → (e : GroupIso G H)
  → gen₁-by H (Iso.fun (fst e) g)
Iso-pres-gen₁ G H g genG is h =
    (fst (genG (Iso.inv (fst is) h)))
  , (sym (Iso.rightInv (fst is) h)
    ∙∙ cong (Iso.fun (fst is)) (snd (genG (Iso.inv (fst is) h)))
    ∙∙ (homPresℤ· (_ , snd is) g (fst (genG (Iso.inv (fst is) h)))))

Iso-pres-gen₂ : (G : Group ℓ) (H : Group ℓ') (g₁ g₂ : fst G)
  → gen₂-by G g₁ g₂ → (e : GroupIso G H)
  → gen₂-by H (Iso.fun (fst e) g₁) (Iso.fun (fst e) g₂)
fst (Iso-pres-gen₂ G H g₁ g₂ genG is h) = genG (Iso.inv (fst is) h) .fst
snd (Iso-pres-gen₂ G H g₁ g₂ genG is h) =
     sym (Iso.rightInv (fst is) h)
  ∙∙ cong (fun (fst is)) (snd (genG (Iso.inv (fst is) h)))
  ∙∙ (pres· (snd is) _ _
  ∙ cong₂ (_·_ (snd H))
          (homPresℤ· (_ , snd is) g₁ (fst (fst (genG (inv (fst is) h)))))
          (homPresℤ· (_ , snd is) g₂ (snd (fst (genG (inv (fst is) h))))))


private
  intLem₁ : (n m : ℕ) → Σ[ a ∈ ℕ ] (negsuc n * pos (suc m)) ≡ negsuc a
  intLem₁ n zero = n , ·Comm  (negsuc n) (pos 1)
  intLem₁ n (suc m) = lem _ _ .fst ,
       (·Comm (negsuc n) (pos (suc (suc m)))
    ∙∙ cong (negsuc n +ℤ_) (·Comm (pos (suc m)) (negsuc n) ∙ (intLem₁ n m .snd))
    ∙∙ lem _ _ .snd)
    where
    lem : (x y : ℕ) → Σ[ a ∈ ℕ ] negsuc x +ℤ negsuc y ≡ negsuc a
    lem zero zero = 1 , refl
    lem zero (suc y) = (suc (suc y)) , +Comm (negsuc zero) (negsuc (suc y))
    lem (suc x) zero = (suc (suc x)) , refl
    lem (suc x) (suc y) =
       (lem (suc (suc x)) y .fst)
     , (predℤ+negsuc y (negsuc (suc x)) ∙ snd ((lem (suc (suc x))) y))

  intLem₂ : (n x : ℕ)
    → Σ[ a ∈ ℕ ] ((pos (suc x)) * pos (suc (suc n)) ≡ pos (suc (suc a)))
  intLem₂ n zero = n , refl
  intLem₂ n (suc x) = lem _ _ (intLem₂ n x)
    where
    lem : (x : ℤ) (n : ℕ) → Σ[ a ∈ ℕ ] (x ≡ pos (suc (suc a)))
                  → Σ[ a ∈ ℕ ] pos n +ℤ x ≡ pos (suc (suc a))
    lem x n (a , p) = n +ℕ a
      , cong (pos n +ℤ_) p ∙ cong sucℤ (sucℤ+pos a (pos n))
         ∙ sucℤ+pos a (pos (suc n)) ∙ (sym (pos+ (suc (suc n)) a))

  ¬1=x·suc-suc : (n : ℕ) (x : ℤ) → ¬ pos 1 ≡ x * pos (suc (suc n))
  ¬1=x·suc-suc n (pos zero) p = snotz (injPos p)
  ¬1=x·suc-suc n (pos (suc n₁)) p =
    snotz (injPos (sym (cong predℤ (snd (intLem₂ n n₁))) ∙ sym (cong predℤ p)))
  ¬1=x·suc-suc n (negsuc n₁) p = posNotnegsuc _ _ (p ∙ intLem₁ _ _ .snd)

GroupEquivℤ-pres1 : (e : GroupEquiv ℤGroup ℤGroup) (x : ℤ)
  → (fst (fst e) 1) ≡ x → abs (fst (fst e) 1) ≡ 1
GroupEquivℤ-pres1 e (pos zero) p =
  ⊥-rec (snotz (injPos (sym (retEq (fst e) 1)
            ∙∙ (cong (fst (fst (invGroupEquiv e))) p)
            ∙∙ IsGroupHom.pres1 (snd (invGroupEquiv e)))))
GroupEquivℤ-pres1 e (pos (suc zero)) p = cong abs p
GroupEquivℤ-pres1 e (pos (suc (suc n))) p =
  ⊥-rec (¬1=x·suc-suc _ _ (h3 ∙ ·Comm (pos (suc (suc n))) (invEq (fst e) 1)))
  where
  h3 : pos 1 ≡ _
  h3 = sym (retEq (fst e) 1)
    ∙∙ cong (fst (fst (invGroupEquiv e)))
            (p ∙ ·Comm 1 (pos (suc (suc n))))
    ∙∙ GroupHomℤ→ℤPres· (_ , snd (invGroupEquiv e)) (pos (suc (suc n))) 1
GroupEquivℤ-pres1 e (negsuc zero) p = cong abs p
GroupEquivℤ-pres1 e (negsuc (suc n)) p = ⊥-rec (¬1=x·suc-suc _ _ lem₂)
  where
  lem₁ : fst (fst e) (negsuc zero) ≡ pos (suc (suc n))
  lem₁ = GroupHomℤ→ℤpres- (_ , snd e) (pos 1) ∙ cong -_ p

  compGroup : GroupEquiv ℤGroup ℤGroup
  fst compGroup = isoToEquiv (iso -_ -_ -Involutive -Involutive)
  snd compGroup = makeIsGroupHom -Dist+

  compHom : GroupEquiv ℤGroup ℤGroup
  compHom = compGroupEquiv compGroup e

  lem₂ : pos 1 ≡ invEq (fst compHom) (pos 1) * pos (suc (suc n))
  lem₂ = sym (retEq (fst compHom) (pos 1))
     ∙∙ cong (invEq (fst compHom)) lem₁
     ∙∙ (cong (invEq (fst compHom)) (·Comm (pos 1) (pos (suc (suc n))))
       ∙ GroupHomℤ→ℤPres· (_ , (snd (invGroupEquiv compHom)))
                           (pos (suc (suc n))) (pos 1)
       ∙ ·Comm (pos (suc (suc n))) (invEq (fst compHom) (pos 1)))

groupEquivPresGen : ∀ {ℓ} (G : Group ℓ) (ϕ : GroupEquiv G ℤGroup) (x : fst G)
              → (fst (fst ϕ) x ≡ 1) ⊎ (fst (fst ϕ) x ≡ - 1)
              → (ψ : GroupEquiv G ℤGroup)
              → (fst (fst ψ) x ≡ 1) ⊎ (fst (fst ψ) x ≡ - 1)
groupEquivPresGen G (ϕeq , ϕhom) x (inl r) (ψeq , ψhom) =
     abs→⊎ _ _ (cong abs (cong (fst ψeq) (sym (retEq ϕeq x)
               ∙ cong (invEq ϕeq) r))
   ∙ GroupEquivℤ-pres1 (compGroupEquiv
                         (invGroupEquiv (ϕeq , ϕhom)) (ψeq , ψhom)) _ refl)
groupEquivPresGen G (ϕeq , ϕhom) x (inr r) (ψeq , ψhom) =
  abs→⊎ _ _
    (cong abs (cong (fst ψeq) (sym (retEq ϕeq x) ∙ cong (invEq ϕeq) r))
    ∙ cong abs (IsGroupHom.presinv
                (snd (compGroupEquiv (invGroupEquiv (ϕeq , ϕhom))
                       (ψeq , ψhom))) 1)
    ∙ absLem _ (GroupEquivℤ-pres1
                (compGroupEquiv (invGroupEquiv (ϕeq , ϕhom)) (ψeq , ψhom))
                 _ refl))
  where
  absLem : ∀ x → abs x ≡ 1 → abs (pos 0 -ℤ x) ≡ 1
  absLem (pos zero) p = ⊥-rec (snotz (sym p))
  absLem (pos (suc zero)) p = refl
  absLem (pos (suc (suc n))) p = ⊥-rec (snotz (cong predℕ p))
  absLem (negsuc zero) p = refl
  absLem (negsuc (suc n)) p = ⊥-rec (snotz (cong predℕ p))

gen₂ℤ×ℤ : gen₂-by (DirProd ℤGroup ℤGroup) (1 , 0) (0 , 1)
fst (gen₂ℤ×ℤ (x , y)) = x , y
snd (gen₂ℤ×ℤ (x , y)) =
  ΣPathP ((cong₂ _+ℤ_ ((·Comm 1 x) ∙ cong fst (sym (distrLem 1 0 x)))
                     ((·Comm 0 y) ∙ cong fst (sym (distrLem 0 1 y))))
        , +Comm y 0
         ∙ cong₂ _+ℤ_ (·Comm 0 x ∙ cong snd (sym (distrLem 1 0 x)))
                     (·Comm 1 y ∙ cong snd (sym (distrLem 0 1 y))))
  where
  ℤ×ℤ = DirProd ℤGroup ℤGroup
  _+''_ = GroupStr._·_ (snd ℤ×ℤ)

  -lem : (x : ℤ) → - x ≡ 0 -ℤ x
  -lem (pos zero) = refl
  -lem (pos (suc zero)) = refl
  -lem (pos (suc (suc n))) =
    cong predℤ (-lem (pos (suc n)))
  -lem (negsuc zero) = refl
  -lem (negsuc (suc n)) = cong sucℤ (-lem (negsuc n))

  distrLem : (x y : ℤ) (z : ℤ)
         → Path (ℤ × ℤ) (z ℤ[ ℤ×ℤ ]· (x , y)) (z * x , z * y)
  distrLem x y (pos zero) = refl
  distrLem x y (pos (suc n)) =
    (cong ((x , y) +''_) (distrLem x y (pos n)))
  distrLem x y (negsuc zero) = ΣPathP (sym (-lem x) , sym (-lem y))
  distrLem x y (negsuc (suc n)) =
    cong₂ _+''_ (ΣPathP (sym (-lem x) , sym (-lem y)))
                (distrLem x y (negsuc n))
