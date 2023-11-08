-- Left ℤ-multiplication on groups and some of its properties

-- TODO: lots of the content here should be moved elsewhere
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.Group.ZAction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Int as ℤ
  renaming
    (_·_ to _*_ ; _+_ to _+ℤ_ ; _-_ to _-ℤ_ ; pos·pos to pos·) hiding (·Assoc; ·IdL; ·IdR)
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sum renaming (rec to ⊎-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Fin hiding (_/_)
open import Cubical.Data.Fin.Arithmetic

open import Cubical.HITs.SetQuotients renaming (_/_ to _/s_ ; rec to sRec ; elim to sElim)
open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.IsomorphismTheorems
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.Exact

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' : Level

open Iso
open GroupStr
open IsGroupHom
open Exact4

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
  ∙ ·IdL (snd G) (1g (snd G))
rUnitℤ· G (negsuc zero) = GroupTheory.inv1g G
rUnitℤ· G (negsuc (suc n)) =
    cong₂ (_·_ (snd G)) (GroupTheory.inv1g G) (rUnitℤ· G (negsuc n))
  ∙ ·IdL (snd G) (1g (snd G))

rUnitℤ·ℤ : (x : ℤ) → (x ℤ[ ℤGroup ]· 1) ≡ x
rUnitℤ·ℤ (pos zero) = refl
rUnitℤ·ℤ (pos (suc n)) = cong (pos 1 +ℤ_) (rUnitℤ·ℤ (pos n)) ∙ sym (pos+ 1 n)
rUnitℤ·ℤ (negsuc zero) = refl
rUnitℤ·ℤ (negsuc (suc n)) = cong (-1 +ℤ_) (rUnitℤ·ℤ (negsuc n))
                          ∙ +Comm (negsuc 0) (negsuc n)

private
  precommℤ : (G : Group ℓ) (g : fst G) (y : ℤ)
           → (snd G · (y ℤ[ G ]· g)) g ≡ (sucℤ y ℤ[ G ]· g)
  precommℤ G g (pos zero) = ·IdL (snd G) g ∙ sym (·IdR (snd G) g)
  precommℤ G g (pos (suc n)) =
       sym (·Assoc (snd G) _ _ _)
     ∙ cong ((snd G · g)) (precommℤ G g (pos n))
  precommℤ G g (negsuc zero) = ·InvL (snd G) g
  precommℤ G g (negsuc (suc n)) =
    sym (·Assoc (snd G) _ _ _)
    ∙ cong ((snd G · inv (snd G) g)) (precommℤ G g (negsuc n))
    ∙ negsucLem n
    where
    negsucLem : (n : ℕ) → (snd G · inv (snd G) g)
      (sucℤ (negsuc n) ℤ[ G ]· g)
      ≡ (sucℤ (negsuc (suc n)) ℤ[ G ]· g)
    negsucLem zero = (·IdR (snd G) _)
    negsucLem (suc n) = refl

module _ (G : Group ℓ) (g : fst G) where
  private
    lem : (y : ℤ) → (predℤ y ℤ[ G ]· g)
                   ≡ (snd G · inv (snd G) g) (y ℤ[ G ]· g)
    lem (pos zero) = sym (·IdR (snd G) _)
    lem (pos (suc n)) =
         sym (·IdL (snd G) ((pos n ℤ[ G ]· g)))
      ∙∙ cong (λ x → _·_ (snd G) x (pos n ℤ[ G ]· g))
              (sym (·InvL (snd G) g))
      ∙∙ sym (·Assoc (snd G) _ _ _)
    lem (negsuc n) = refl

  distrℤ· : (x y : ℤ) → ((x +ℤ y) ℤ[ G ]· g)
           ≡ _·_ (snd G) (x ℤ[ G ]· g) (y ℤ[ G ]· g)
  distrℤ· (pos zero) y = cong (_ℤ[ G ]· g) (+Comm 0 y)
                            ∙ sym (·IdL (snd G) _)
  distrℤ· (pos (suc n)) (pos n₁) =
      cong (_ℤ[ G ]· g) (sym (pos+ (suc n) n₁))
    ∙ cong (_·_ (snd G) g)
           (cong (_ℤ[ G ]· g) (pos+ n n₁) ∙ distrℤ· (pos n) (pos n₁))
    ∙ ·Assoc (snd G) _ _ _
  distrℤ· (pos (suc n)) (negsuc zero) =
      distrℤ· (pos n) 0
    ∙ ((·IdR (snd G) (pos n ℤ[ G ]· g) ∙ sym (·IdL (snd G) (pos n ℤ[ G ]· g)))
    ∙ cong (λ x → _·_ (snd G) x (pos n ℤ[ G ]· g))
           (sym (·InvL (snd G) g)) ∙ sym (·Assoc (snd G) _ _ _))
    ∙ (·Assoc (snd G) _ _ _)
    ∙ cong (λ x → _·_ (snd G)  x (pos n ℤ[ G ]· g)) (·InvL (snd G) g)
    ∙ ·IdL (snd G) _
    ∙ sym (·IdR (snd G) _)
    ∙ (cong (_·_ (snd G) (pos n ℤ[ G ]· g)) (sym (·InvR (snd G) g))
    ∙ ·Assoc (snd G) _ _ _)
    ∙ cong (λ x → _·_ (snd G)  x (inv (snd G) g))
           (precommℤ G g (pos n))
  distrℤ· (pos (suc n)) (negsuc (suc n₁)) =
       cong (_ℤ[ G ]· g) (predℤ+negsuc n₁ (pos (suc n)))
    ∙∙ distrℤ· (pos n) (negsuc n₁)
    ∙∙ (cong (λ x → _·_ (snd G) x (negsuc n₁ ℤ[ G ]· g))
             ((sym (·IdR (snd G) (pos n ℤ[ G ]· g))
             ∙ cong (_·_ (snd G) (pos n ℤ[ G ]· g)) (sym (·InvR (snd G) g)))
           ∙∙ ·Assoc (snd G) _ _ _
           ∙∙ cong (λ x → _·_ (snd G) x (inv (snd G) g)) (precommℤ G g (pos n)))
      ∙ sym (·Assoc (snd G) _ _ _))
  distrℤ· (negsuc zero) y =
      cong (_ℤ[ G ]· g) (+Comm -1 y) ∙ lem y
  distrℤ· (negsuc (suc n)) y =
       cong (_ℤ[ G ]· g) (+Comm (negsuc (suc n)) y)
    ∙∙ lem (y +negsuc n)
    ∙∙ cong (snd G · inv (snd G) g)
            (cong (_ℤ[ G ]· g) (+Comm y (negsuc n)) ∙ distrℤ· (negsuc n) y)
     ∙ (·Assoc (snd G) _ _ _)

GroupHomℤ→ℤpres- : (e : GroupHom ℤGroup ℤGroup) (a : ℤ)
                  → fst e (- a) ≡ - fst e a
GroupHomℤ→ℤpres- e a = presinv (snd e) a

ℤ·≡· : (a b : ℤ) → a * b ≡ (a ℤ[ ℤGroup ]· b)
ℤ·≡· (pos zero) b = refl
ℤ·≡· (pos (suc n)) b = cong (b +ℤ_) (ℤ·≡· (pos n) b)
ℤ·≡· (negsuc zero) b = refl
ℤ·≡· (negsuc (suc n)) b = cong (λ X → - b +ℤ X) (ℤ·≡· (negsuc n) b)

GroupHomℤ→ℤPres· : (e : GroupHom ℤGroup ℤGroup) (a b : ℤ)
                  → fst e (a * b) ≡ a * fst e b
GroupHomℤ→ℤPres· e a b =
  cong (fst e) (ℤ·≡· a b) ∙∙ homPresℤ· e b a ∙∙ sym (ℤ·≡· a (fst e b))

-- Generators in terms of ℤ-multiplication

-- TODO : generalise and develop theory of cyclic groups
gen₁-by : (G : Group ℓ) → (g : fst G) → Type _
gen₁-by G g = (h : fst G)
            → Σ[ a ∈ ℤ ] h ≡ (a ℤ[ G ]· g)

gen₂-by : ∀ {ℓ} (G : Group ℓ) → (g₁ g₂ : fst G) → Type _
gen₂-by G g₁ g₂ =
  (h : fst G) → Σ[ a ∈ ℤ × ℤ ] h ≡ _·_ (snd G) ((fst a) ℤ[ G ]· g₁) ((snd a) ℤ[ G ]· g₂)

Iso-pres-gen₁ : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') (g : fst G)
  → gen₁-by G g → (e : GroupIso G H)
  → gen₁-by H (fun (fst e) g)
Iso-pres-gen₁ G H g genG is h =
    (fst (genG (inv (fst is) h)))
  , (sym (rightInv (fst is) h)
    ∙∙ cong (fun (fst is)) (snd (genG (inv (fst is) h)))
    ∙∙ (homPresℤ· (_ , snd is) g (fst (genG (inv (fst is) h)))))

Iso-pres-gen₂ : (G : Group ℓ) (H : Group ℓ') (g₁ g₂ : fst G)
  → gen₂-by G g₁ g₂ → (e : GroupIso G H)
  → gen₂-by H (fun (fst e) g₁) (fun (fst e) g₂)
fst (Iso-pres-gen₂ G H g₁ g₂ genG is h) = genG (inv (fst is) h) .fst
snd (Iso-pres-gen₂ G H g₁ g₂ genG is h) =
     sym (rightInv (fst is) h)
  ∙∙ cong (fun (fst is)) (snd (genG (inv (fst is) h)))
  ∙∙ (pres· (snd is) _ _
  ∙ cong₂ (_·_ (snd H))
          (homPresℤ· (_ , snd is) g₁ (fst (fst (genG (inv (fst is) h)))))
          (homPresℤ· (_ , snd is) g₂ (snd (fst (genG (inv (fst is) h))))))

-- TODO: upstream and express using divisibility?
¬1=x·suc-suc : (n : ℕ) (x : ℤ) → ¬ pos 1 ≡ x * pos (suc (suc n))
¬1=x·suc-suc n (pos zero) p = snotz (injPos p)
¬1=x·suc-suc n (pos (suc n₁)) p =
  snotz (injPos (sym (cong predℤ (snd (intLem₂ n n₁))) ∙ sym (cong predℤ p)))
  where
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
¬1=x·suc-suc n (negsuc n₁) p = posNotnegsuc _ _ (p ∙ intLem₁ _ _ .snd)
  where
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

GroupEquivℤ-pres1 : (e : GroupEquiv ℤGroup ℤGroup) (x : ℤ)
  → (fst (fst e) 1) ≡ x → abs (fst (fst e) 1) ≡ 1
GroupEquivℤ-pres1 e (pos zero) p =
  ⊥-rec (snotz (injPos (sym (retEq (fst e) 1)
            ∙∙ (cong (fst (fst (invGroupEquiv e))) p)
            ∙∙ pres1 (snd (invGroupEquiv e)))))
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
    ∙ cong abs (presinv
                (snd (compGroupEquiv (invGroupEquiv (ϕeq , ϕhom))
                       (ψeq , ψhom))) 1)
    ∙ absLem _ (GroupEquivℤ-pres1
                (compGroupEquiv (invGroupEquiv (ϕeq , ϕhom)) (ψeq , ψhom))
                 _ refl))
  where
  absLem : ∀ x → abs x ≡ 1 → abs (- x) ≡ 1
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

  distrLem : (x y : ℤ) (z : ℤ)
         → Path (ℤ × ℤ) (z ℤ[ ℤ×ℤ ]· (x , y)) (z * x , z * y)
  distrLem x y (pos zero) = refl
  distrLem x y (pos (suc n)) =
    (cong ((x , y) +''_) (distrLem x y (pos n)))
  distrLem x y (negsuc zero) = refl
  distrLem x y (negsuc (suc n)) = cong₂ _+''_ refl ((distrLem x y (negsuc n)))

gen₁ℤGroup-⊎ : (g : ℤ) → gen₁-by ℤGroup g → (g ≡ 1) ⊎ (g ≡ -1)
gen₁ℤGroup-⊎ (pos zero) h = ⊥-rec (negsucNotpos 0 0 (h (negsuc 0) .snd ∙ rUnitℤ· ℤGroup _))
gen₁ℤGroup-⊎ (pos (suc zero)) h = inl refl
gen₁ℤGroup-⊎ (pos (suc (suc n))) h = ⊥-rec (¬1=x·suc-suc n _ (rem (pos 1)))
  where
  rem : (x : ℤ) → x ≡ fst (h x) * pos (suc (suc n))
  rem x = h x .snd ∙ sym (ℤ·≡· (fst (h x)) (pos (suc (suc n))))
gen₁ℤGroup-⊎ (negsuc zero) h = inr refl
gen₁ℤGroup-⊎ (negsuc (suc n)) h = ⊥-rec (¬1=x·suc-suc n _ (rem (pos 1) ∙ ℤ·negsuc (fst (h (pos 1))) (suc n) ∙ -DistL· _ _))
  where
  rem : (x : ℤ) → x ≡ fst (h x) * negsuc (suc n)
  rem x = h x .snd ∙ sym (ℤ·≡· (fst (h x)) (negsuc (suc n)))

-- Properties of homomorphisms of ℤ wrt generators (should be moved)
module _ (ϕ : GroupHom ℤGroup ℤGroup) where
  ℤHomId : fst ϕ 1 ≡ 1 → fst ϕ ≡ idfun _
  ℤHomId p = funExt rem
    where
    remPos : (x : ℕ) → fst ϕ (pos x) ≡ idfun ℤ (pos x)
    remPos zero = pres1 (snd ϕ)
    remPos (suc zero) = p
    remPos (suc (suc n)) =
      pres· (snd ϕ) (pos (suc n)) 1 ∙ cong₂ _+ℤ_ (remPos (suc n)) p

    rem : (x : ℤ) → fst ϕ x ≡ idfun ℤ x
    rem (pos n) = remPos n
    rem (negsuc zero) =
        presinv (snd ϕ) 1 ∙ cong -_ p
    rem (negsuc (suc n)) =
        presinv (snd ϕ) (pos (suc (suc n)))
        ∙ cong -_ (remPos (suc (suc n)))

  ℤHomId- : fst ϕ -1 ≡ -1 → fst ϕ ≡ idfun _
  ℤHomId- p = ℤHomId (presinv (snd ϕ) (negsuc 0) ∙ cong -_ p)

  ℤHom1- : fst ϕ 1 ≡ -1 → fst ϕ ≡ -_
  ℤHom1- p = funExt rem
    where
    rem-1 : fst ϕ (negsuc zero) ≡ pos 1
    rem-1 = presinv (snd ϕ) (pos 1) ∙ cong -_ p

    rem : (n : ℤ) → fst ϕ n ≡ - n
    rem (pos zero) = pres1 (snd ϕ)
    rem (pos (suc zero)) = p
    rem (pos (suc (suc n))) = pres· (snd ϕ) (pos (suc n)) (pos 1) ∙ cong₂ _+ℤ_ (rem (pos (suc n))) p
    rem (negsuc zero) = rem-1
    rem (negsuc (suc n)) = pres· (snd ϕ) (negsuc n) -1 ∙ cong₂ _+ℤ_ (rem (negsuc n)) rem-1

  ℤHom-1 : fst ϕ -1 ≡ 1 → fst ϕ ≡ -_
  ℤHom-1 p = ℤHom1- (presinv (snd ϕ) -1 ∙ cong -_ p)


-- Properties of equivalences of ℤ wrt generators (should be moved)
module _ (ϕ : GroupEquiv ℤGroup ℤGroup) where
  ℤEquiv1 : (groupEquivFun ϕ 1 ≡ 1) ⊎ (groupEquivFun ϕ 1 ≡ -1)
  ℤEquiv1 =
    groupEquivPresGen ℤGroup (compGroupEquiv ϕ (invGroupEquiv ϕ))
                     (pos 1) (inl (funExt⁻ (cong fst (invEquiv-is-rinv (ϕ .fst))) (pos 1))) ϕ

  ℤEquivIsIdOr- : (g : ℤ) → (groupEquivFun ϕ g ≡ g) ⊎ (groupEquivFun ϕ g ≡ - g)
  ℤEquivIsIdOr- g =
    ⊎-rec (λ h → inl (funExt⁻ (ℤHomId (_ , ϕ .snd) h) g))
          (λ h → inr (funExt⁻ (ℤHom1- (_ , ϕ .snd) h) g))
          ℤEquiv1

  absℤEquiv : (g : ℤ) → abs g ≡ abs (fst (fst ϕ) g)
  absℤEquiv g =
    ⊎-rec (λ h → sym (cong abs h))
          (λ h → sym (abs- _) ∙ sym (cong abs h))
          (ℤEquivIsIdOr- g)

-- A few consequences of the above lemmas
characℤ≅ℤ : (e : GroupEquiv ℤGroup ℤGroup)
          → (e ≡ idGroupEquiv) ⊎ (e ≡ negEquivℤ)
characℤ≅ℤ e =
  ⊎-rec
    (λ p → inl (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                 (Σ≡Prop (λ _ → isPropIsEquiv _)
                   (funExt λ x →
                     cong (e .fst .fst) (·Comm 1 x)
                   ∙ GroupHomℤ→ℤPres· (fst (fst e) , snd e) x 1
                   ∙ cong (x *_) p
                   ∙ ·Comm x 1))))
    (λ p → inr (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                  (Σ≡Prop (λ _ → isPropIsEquiv _)
                    (funExt λ x →
                      cong (fst (fst e)) (sym (ℤ.·IdR x))
                      ∙ GroupHomℤ→ℤPres· ((fst (fst e)) , (snd e)) x 1
                      ∙ cong (x *_) p
                      ∙ ·Comm x -1 ))))

    (ℤEquiv1 e)

absGroupEquivℤGroup : {G : Group₀} (ϕ ψ : GroupEquiv ℤGroup G) (g : fst G)
                    → abs (invEq (fst ϕ) g) ≡ abs (invEq (fst ψ) g)
absGroupEquivℤGroup =
  GroupEquivJ (λ G ϕ → (ψ : GroupEquiv ℤGroup G) (g : fst G)
                     → abs (invEq (fst ϕ) g) ≡ abs (invEq (fst ψ) g))
              (λ ψ → absℤEquiv (invGroupEquiv ψ))

GroupEquivℤ-isEquiv : {G : Group₀}
         → GroupEquiv ℤGroup G
         → (g : fst G)
         → gen₁-by G g
         → (ϕ : GroupHom G ℤGroup)
         → (fst ϕ g ≡ 1) ⊎ (fst ϕ g ≡ -1)
         → isEquiv (fst ϕ)
GroupEquivℤ-isEquiv {G = G} =
  GroupEquivJ
    (λ G _ → (g : fst G)
         → gen₁-by G g
         → (ϕ : GroupHom G ℤGroup)
         → (fst ϕ g ≡ 1) ⊎ (fst ϕ g ≡ -1)
         → isEquiv (fst ϕ))
    rem
  where
  rem : (g : ℤ)
      → gen₁-by ℤGroup g
      → (ϕ : GroupHom ℤGroup ℤGroup)
      → (fst ϕ g ≡ 1) ⊎ (fst ϕ g ≡ -1)
      → isEquiv (fst ϕ)
  rem g gen ϕ (inl h₁) =
    ⊎-rec (λ h₂ → subst isEquiv (sym (ℤHomId ϕ (sym (cong (fst ϕ) h₂) ∙ h₁))) (idIsEquiv _))
          (λ h₂ → subst isEquiv (sym (ℤHom-1 ϕ (sym (cong (fst ϕ) h₂) ∙ h₁))) isEquiv-)
          (gen₁ℤGroup-⊎ g gen)
  rem g gen ϕ (inr h₁) =
   ⊎-rec (λ h₂ → subst isEquiv (sym (ℤHom1- ϕ (sym (cong (fst ϕ) h₂) ∙ h₁))) isEquiv-)
         (λ h₂ → subst isEquiv (sym (ℤHomId- ϕ (sym (cong (fst ϕ) h₂) ∙ h₁))) (idIsEquiv _))
         (gen₁ℤGroup-⊎ g gen)

-- Characterisation of ℤ→ℤ
characGroupHomℤ : (e : GroupHom ℤGroup ℤGroup) → e ≡ ℤHom (fst e (pos 1))
characGroupHomℤ e =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt λ { (pos n) → lem n
               ; (negsuc n)
                  → presinv (snd e) (pos (suc n))
                  ∙ cong -_ (lem (suc n))
                  ∙ sym (ℤ·negsuc (fst e 1) n) })
  where
  lem : (n : ℕ) → fst e (pos n) ≡ fst e 1 * (pos n)
  lem zero = pres1 (snd e) ∙ ·Comm 0 (fst e 1)
  lem (suc zero) = ·Comm 1 (fst e 1)
  lem (suc (suc n)) =
      pres· (snd e) (pos (suc n)) 1
    ∙ cong (_+ℤ fst e 1) (lem (suc n))
    ∙ cong (fst e (pos 1) * pos (suc n) +ℤ_) (·Comm 1 (fst e 1))
    ∙ sym (·DistR+ (fst e 1) (pos (suc n)) 1)

imℤHomSubGroup : (f : GroupHom ℤGroup ℤGroup) → NormalSubgroup ℤGroup
imℤHomSubGroup f = imNormalSubgroup f +Comm

-- Equivalence between ℤ/ (abs (f 1)) and ℤ/ (im f) using the two different
-- definitions of ℤ quotients. We start with the case f 1 ≥ 0.
module _ (f : GroupHom ℤGroup ℤGroup) where
  trivHom→ℤ≅ℤ/im : fst f 1 ≡ 0
    → GroupIso ℤGroup (ℤGroup / imℤHomSubGroup f)
  trivHom→ℤ≅ℤ/im q =
    trivialRelIso
      (imℤHomSubGroup f)
      λ x y →  Prop.rec (isSetℤ _ _)
        λ {(c , p) →
          GroupTheory.invUniqueL ℤGroup
             {g = x} {h = (GroupStr.inv (snd ℤGroup) y)}
            (sym p ∙ (funExt⁻ (cong fst (characGroupHomℤ f ∙ cong ℤHom q)) c))
        ∙ GroupTheory.invInv ℤGroup y}

  ℤHom→ℤ/im≅ℤ/im1 : (n : ℕ) →  fst f 1 ≡ pos (suc n)
    → BijectionIso (ℤGroup / imℤHomSubGroup f) (ℤGroup/ (suc n))
  fst (BijectionIso.fun (ℤHom→ℤ/im≅ℤ/im1 n p)) =
      sRec isSetFin (ℤ→Fin n) λ a b
      → rec (isSetFin _ _) (uncurry λ x q
        → (cong (ℤ→Fin n) (cancel-lem a b _
                            (sym q ∙ funExt⁻ (cong fst (characGroupHomℤ f ∙ cong ℤHom p)) x)))

            ∙ pres· (isHomℤ→Fin n) (pos (suc n) * x) b
            ∙ cong (_+ₘ ℤ→Fin n b) (lem x)
            ∙ GroupStr.·IdL (snd (ℤGroup/ (suc n))) (ℤ→Fin n b))
    where
    lem : (x : ℤ) → ℤ→Fin n (pos (suc n) * x) ≡ 0
    lem (pos x) = cong (ℤ→Fin n) (sym (pos· (suc n) x))
                 ∙ Σ≡Prop (λ _ → isProp≤)
                    (cong (_mod (suc n)) (·-comm (suc n) x)
                    ∙ zero-charac-gen (suc n) x)
    lem (negsuc x) =
         cong (ℤ→Fin n) (pos·negsuc (suc n) x
                        ∙ cong -_ (sym (pos· (suc n) (suc x))))
      ∙∙ cong -ₘ_ (Σ≡Prop (λ _ → isProp≤)
                    (cong (_mod (suc n)) (·-comm (suc n) (suc x))
                    ∙ zero-charac-gen (suc n) (suc x)))
      ∙∙ GroupTheory.inv1g (ℤGroup/ (suc n))

    cancel-lem : (a b x : ℤ) → a +ℤ (- b) ≡ x → a ≡ x +ℤ b
    cancel-lem a b x p = sym (minusPlus b a) ∙ cong (_+ℤ b) p

  snd (BijectionIso.fun (ℤHom→ℤ/im≅ℤ/im1 n p)) =
    makeIsGroupHom (elimProp2 (λ _ _ → isSetFin _ _) (pres· (isHomℤ→Fin n)))
  BijectionIso.inj (ℤHom→ℤ/im≅ℤ/im1 n p) =
    elimProp (λ _ → isPropΠ λ _ → squash/ _ _)
      (λ { (pos x) q → eq/ (pos x) 0
                        ∣ (((pos (quotient x / (suc n)))) ,
                          (funExt⁻ (cong fst (characGroupHomℤ f ∙ cong ℤHom p)) ((pos (quotient x / (suc n))))
                          ∙ sym (pos· (suc n) (quotient x / (suc n)))
                          ∙ cong pos ((λ i → q (~ i) .fst +ℕ suc n ·ℕ (quotient x / suc n)))
                          ∙ cong pos (≡remainder+quotient (suc n) x))) ∣₁ ;
           (negsuc x) q → eq/ (negsuc x) 0
                          ∣ (((- pos (quotient suc x / (suc n)))) ,
                          presinv (snd f) (pos (quotient suc x / (suc n)))
                          ∙ (cong -_ (funExt⁻ (cong fst (characGroupHomℤ f ∙ cong ℤHom p))
                                       (pos (quotient (suc x) / (suc n))))
                          ∙∙ cong -_ (sym (pos· (suc n) (quotient suc x / (suc n)))
                                    ∙ (λ i → pos (fst ((sym (GroupTheory.invInv
                                                              (ℤGroup/ (suc n))
                                                  ((suc x mod suc n) , mod< n (suc x)))
                                                 ∙ cong -ₘ_ q
                                                 ∙ GroupTheory.inv1g (ℤGroup/ (suc n))) (~ i))
                                                 +ℕ suc n ·ℕ quotient (suc x) / suc n)))
                          ∙∙ cong -_ (cong pos (≡remainder+quotient (suc n) (suc x))))) ∣₁})
  BijectionIso.surj (ℤHom→ℤ/im≅ℤ/im1 n p) x =
      ∣ [ pos (fst x) ]
    , (Σ≡Prop (λ _ → isProp≤) (modIndBase n (fst x) (snd x))) ∣₁

-- main result
ℤ/imIso : (f : GroupHom ℤGroup ℤGroup)
  → GroupIso (ℤGroup / imℤHomSubGroup f) (ℤGroup/ abs (fst f 1))
ℤ/imIso f = helpIso _ refl
  where
  helpIso : (a : ℤ)
       → fst f 1 ≡ a → GroupIso (ℤGroup / imℤHomSubGroup f) (ℤGroup/ abs a)
  helpIso (pos zero) p = invGroupIso (trivHom→ℤ≅ℤ/im f p)
  helpIso (pos (suc n)) p = BijectionIso→GroupIso (ℤHom→ℤ/im≅ℤ/im1 f n p)
  helpIso (negsuc n) p =
    subst ((λ x → GroupIso (ℤGroup / x) (ℤGroup/ abs (negsuc n))))
          (sym lem1)
          (BijectionIso→GroupIso
            (ℤHom→ℤ/im≅ℤ/im1 extendHom n (cong -_ p)))
    where
    extendHom : GroupHom ℤGroup ℤGroup
    extendHom = compGroupHom f (fst (fst negEquivℤ) , snd negEquivℤ)

    lem1 : imℤHomSubGroup f ≡ imℤHomSubGroup extendHom
    lem1 = Σ≡Prop (λ _ → isPropIsNormal _)
             (Σ≡Prop (λ _ → isPropIsSubgroup _ _)
             (funExt λ x → Σ≡Prop (λ _ → isPropIsProp)
               (isoToPath (iso
                 (Prop.map (λ { (x , q) → (- x) , cong -_ (presinv (snd f) x)
                                                   ∙ GroupTheory.invInv ℤGroup (fst f x)
                                                   ∙ q }))
                 (Prop.map (λ { (x , q) → (- x) , (presinv (snd f) x ∙ q) }))
                 ((λ _ → squash₁ _ _))
                 (λ _ → squash₁ _ _)))))

-- Goal: given G -ᶠ→ H → L → Unit exact, with G ≅ H ≅ ℤ, we get
-- an iso ℤ/abs (f 1) ≅ H, where f 1 and 1 are viewed as integers
-- via the isomorphisms. We start with the case when G = H = ℤ
module _ (f : GroupHom ℤGroup ℤGroup) (G : Group₀)
         (g : GroupHom ℤGroup G)
         (ex : Exact4 ℤGroup ℤGroup G UnitGroup₀ f g (→UnitHom G)) where

  private
    imf≡kerg : imℤHomSubGroup f ≡ kerNormalSubgroup g
    imf≡kerg =
      Σ≡Prop (λ _ → isPropIsNormal _)
        (Σ≡Prop (λ _ → isPropIsSubgroup _ _)
          (funExt λ x → Σ≡Prop (λ _ → isPropIsProp)
            (isoToPath
              (isProp→Iso
                (isPropIsInIm _ _)
                (isPropIsInKer _ _)
                (ImG→H⊂KerH→L ex x)
                (KerH→L⊂ImG→H ex x)))))

  ℤ/im≅ℤ/ker : GroupIso (ℤGroup / imℤHomSubGroup f) (ℤGroup / kerNormalSubgroup g)
  ℤ/im≅ℤ/ker =
    GroupEquiv→GroupIso (invEq (GroupPath _ _) (cong (ℤGroup /_) imf≡kerg))

  GroupIsoℤ/abs : GroupIso (ℤGroup/ abs (fst f (pos 1))) G
  GroupIsoℤ/abs =
    compGroupIso
      (invGroupIso (ℤ/imIso f))
      (compGroupIso
        ℤ/im≅ℤ/ker
        (compGroupIso
          (invGroupIso (isoThm1 g))
          (surjImIso g λ a → KerL→R⊂ImH→L ex a refl)))

-- The general case
GroupEquivℤ/abs-gen : (G H L : Group₀)
  → (e : GroupEquiv ℤGroup G)
  → (r : GroupEquiv ℤGroup H)
  → (f : GroupHom G H) (g : GroupHom H L)
  → Exact4 G H L UnitGroup₀ f g (→UnitHom L)
  → GroupEquiv (ℤGroup/ abs (invEq (fst r) (fst f (fst (fst e) 1)))) L
GroupEquivℤ/abs-gen G H L =
  GroupEquivJ (λ G e
    → (r : GroupEquiv ℤGroup H)
     → (f : GroupHom G H) (g : GroupHom H L)
     → Exact4 G H L UnitGroup₀ f g (→UnitHom L)
     → GroupEquiv (ℤGroup/ abs (invEq (fst r) (fst f (fst (fst e) 1)))) L)
    (GroupEquivJ (λ H r
      → (f : GroupHom ℤGroup H) (g : GroupHom H L) →
      Exact4 ℤGroup H L UnitGroup₀ f g (→UnitHom L) →
      GroupEquiv
      (ℤGroup/ abs (invEq (fst r) (fst f 1))) L)
      λ f g ex → GroupIso→GroupEquiv (GroupIsoℤ/abs f L g ex))

-- for type checking reasons, let's also do it with an abstract type
abstract
  abstractℤGroup/_ : ℕ → Group₀
  abstractℤGroup/_ n = ℤGroup/ n

  abstractℤ/≡ℤ : abstractℤGroup/_ ≡ ℤGroup/_
  abstractℤ/≡ℤ = refl

  abstractℤ/≅ℤ : (n : ℕ) → GroupEquiv (abstractℤGroup/_ n) (ℤGroup/ n)
  abstractℤ/≅ℤ n = idGroupEquiv

GroupEquiv-abstractℤ/abs-gen : (G H L : Group₀)
  → (e : GroupEquiv ℤGroup G)
  → (r : GroupEquiv ℤGroup H)
  → (f : GroupHom G H) (g : GroupHom H L)
  → Exact4 G H L UnitGroup₀ f g (→UnitHom L)
  → (n : ℕ)
  → abs (invEq (fst r) (fst f (fst (fst e) 1))) ≡ n
  → GroupEquiv (abstractℤGroup/_ n) L
GroupEquiv-abstractℤ/abs-gen G H L e r f g ex n p = main
  where
  abstract
    main : GroupEquiv (abstractℤGroup/_ n) L
    main =
      transport (λ i
               → GroupEquiv (abstractℤ/≡ℤ (~ i) (p i)) L)
             (GroupEquivℤ/abs-gen G H L e r f g ex)

1∈Im→isEquivℤ : (h : GroupHom ℤGroup ℤGroup) → isInIm h (pos 1) → isEquiv (fst h)
1∈Im→isEquivℤ h = Prop.rec (isPropIsEquiv _)
         λ p → GroupEquivℤ-isEquiv idGroupEquiv 1
                 (λ r → r , (·Comm 1 r ∙ ℤ·≡· r 1)) h (main p)
   where
   main : Σ[ x ∈ ℤ ] fst h x ≡ 1 → (fst h 1 ≡ 1) ⊎ (fst h 1 ≡ -1)
   main (n , p) =
     ≡±1-id n
      (fst h (pos 1))
      h1-id
      (λ q → snotz (injPos (sym p
                 ∙∙ cong (fst h) q
                 ∙∙ IsGroupHom.pres1 (snd h))))
       λ q → snotz (injPos (sym p
                   ∙∙ cong (fst h) (·Comm 1 n ∙ ℤ·≡· n 1)
                   ∙∙ homPresℤ· h 1 n ∙ (cong (n ℤ[ ℤGroup ]·_) q)
                   ∙∙ sym (ℤ·≡· n 0)
                   ∙∙ ·Comm n 0))
     where
     h1-id : pos 1 ≡ n * fst h (pos 1)
     h1-id =
         sym p
       ∙ cong (fst h) (sym (ℤ·≡· 1 n)
       ∙∙ ·Comm 1 n ∙∙ ℤ·≡· n 1)
       ∙ (homPresℤ· h 1 n)
       ∙ sym (ℤ·≡· n (fst h 1))

     ≡±1-id : (a b : ℤ) → 1 ≡ a * b
       → ¬ (a ≡ 0) → ¬ (b ≡ 0)
       → (b ≡ 1) ⊎ (b ≡ -1)
     ≡±1-id a (pos zero) p a≠0 b≠0 = ⊥-rec (b≠0 refl)
     ≡±1-id a (pos (suc zero)) p a≠0 b≠0 = inl refl
     ≡±1-id (pos zero) (pos (suc (suc n))) p a≠0 b≠0 = ⊥-rec (a≠0 refl)
     ≡±1-id (pos (suc n₁)) (pos (suc (suc n))) p a≠0 b≠0 =
       ⊥-rec (snotz
         (cong predℕ (injPos ((pos· (suc n₁) (suc (suc n)) ∙ sym p)))))
     ≡±1-id (negsuc n₁) (pos (suc (suc n))) p a≠0 b≠0 =
       ⊥-rec (snotz (sym (injNegsuc (cong (predℤ ∘ predℤ)
               (p ∙ negsuc·pos n₁ (suc (suc n))
               ∙ cong (-_) (sym (pos· (suc n₁) (suc (suc n)))))))))
     ≡±1-id a (negsuc zero) p a≠0 b≠0 = inr refl
     ≡±1-id (pos zero) (negsuc (suc n)) p a≠0 b≠0 = ⊥-rec (a≠0 refl)
     ≡±1-id (pos (suc n₁)) (negsuc (suc n)) p a≠0 b≠0 =
       ⊥-rec (snotz (sym (injNegsuc
           (cong (predℤ ∘ predℤ) (p ∙ pos·negsuc (suc n₁) (suc n)
         ∙ cong (-_) (sym (pos· (suc n₁) (suc (suc n)))))))))
     ≡±1-id (negsuc n₁) (negsuc (suc n)) p a≠0 b≠0 =
       ⊥-rec (snotz (injPos
           (sym (cong predℤ (p ∙ negsuc·negsuc n₁ (suc n)
          ∙ sym (pos· (suc n₁) (suc (suc n))))))))

1∈Im→isEquiv : ∀ (G : Group₀) (e : GroupEquiv ℤGroup G)
       → (h : GroupHom G ℤGroup)
       → isInIm (_ , snd h) 1
       → isEquiv (fst h)
1∈Im→isEquiv G =
  GroupEquivJ
    (λ H _ → (h : GroupHom H ℤGroup)
       → isInIm (_ , snd h) 1
       → isEquiv (fst h))
    1∈Im→isEquivℤ
