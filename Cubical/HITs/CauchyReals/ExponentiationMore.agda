{-# OPTIONS --lossy-unification --safe #-}

module Cubical.HITs.CauchyReals.ExponentiationMore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos; ℤ)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Bisect
-- open import Cubical.HITs.CauchyReals.BisectApprox
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Derivative

open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationDer

import Cubical.Algebra.CommRing.Instances.Int as ℤCRing
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.Algebra.CommRing as CR

open import Cubical.Algebra.Group.DirProd


fromLipschitz'-rat : ∀ f isL q →
  fst (fromLipschitz' (f ∘S rat) isL) (rat q) ≡ f (rat q)
fromLipschitz'-rat f = PT.elim
 (λ _ → isPropΠ λ _ → isSetℝ _ _)
 λ _ _ → refl

x+n·x≡sn·x : ∀ n x → x +ᵣ fromNat n ·ᵣ x ≡ fromNat (suc n) ·ᵣ x
x+n·x≡sn·x n x = cong₂ _+ᵣ_
  (sym (·IdL _)) refl ∙ sym (·DistR+ _ _ _)
   ∙ cong (_·ᵣ x) (fromNat+ᵣ 1 n)


+Groupℝ : Group₀
+Groupℝ = Ring→Group Rℝ

Is·₊Groupℝ : IsGroup 1 _₊·ᵣ_ invℝ₊
Is·₊Groupℝ = makeIsGroup
   isSetℝ₊
   (λ _ _ _ → ℝ₊≡ (·ᵣAssoc _ _ _ ))
   (λ _ → ℝ₊≡ (·IdR _)) (λ _ → ℝ₊≡ (·IdL _))
   (λ (x , 0<x) → ℝ₊≡ (·invℝ' x 0<x))
   (λ (x , 0<x) → ℝ₊≡ (·ᵣComm _ _ ∙ ·invℝ' x 0<x))

ℝ₋₊ : Type
ℝ₋₊ = Σ ℝ (0 ＃_)

_·ᵣ₋₊_ : ℝ₋₊ → ℝ₋₊ → ℝ₋₊
x ·ᵣ₋₊ x₁ = (fst x ·ᵣ fst x₁) , 0＃· _ _ (snd x) (snd x₁)

ℝ₋₊≡ : ∀ {x y : ℝ₋₊} → fst x ≡ fst y → x ≡ y
ℝ₋₊≡ = Σ≡Prop (isProp＃ 0)

ℝ₋₊→ℝ₊×Bool : ℝ₋₊ → (ℝ₊ × Bool)
ℝ₋₊→ℝ₊×Bool x = (absᵣ (fst x) , 0＃→0<abs _ (snd x)) ,
  ⊎.rec (const true) (const false) (snd x)

ℝ₊×Bool→ℝ₋₊ : (ℝ₊ × Bool) → ℝ₋₊
ℝ₊×Bool→ℝ₋₊ x = (if (snd x) then (1 , inl decℚ<ᵣ?) else (-1 , inr decℚ<ᵣ?))
  ·ᵣ₋₊ (fst (fst x) , inl (snd (fst x)))

opaque
 unfolding 0＃· absᵣ
 sec-ℝ₋₊→ℝ₊×Bool : section ℝ₋₊→ℝ₊×Bool ℝ₊×Bool→ℝ₋₊
 sec-ℝ₋₊→ℝ₊×Bool (x , false) =
   cong₂ _,_
   (ℝ₊≡ (·absᵣ _ _ ∙ ·IdL _ ∙ absᵣPos _ (snd x)))
   refl
 sec-ℝ₋₊→ℝ₊×Bool (x , true) =
  cong₂ _,_
   (ℝ₊≡ (·absᵣ _ _ ∙ ·IdL _ ∙ absᵣPos _ (snd x)))
   refl

ret-ℝ₋₊→ℝ₊×Bool : retract ℝ₋₊→ℝ₊×Bool ℝ₊×Bool→ℝ₋₊
ret-ℝ₋₊→ℝ₊×Bool (fst₁ , inl x) =
  ℝ₋₊≡ (·IdL _ ∙ absᵣPos _ x)
ret-ℝ₋₊→ℝ₊×Bool (fst₁ , inr x) =
  ℝ₋₊≡ (sym (-ᵣ≡[-1·ᵣ] _)
    ∙∙ cong (-ᵣ_) (absᵣNeg _ x)
    ∙∙ -ᵣInvol _)

Iso-ℝ₋₊-ℝ₊×𝟚 : Iso ℝ₋₊ (ℝ₊ × Bool)
Iso-ℝ₋₊-ℝ₊×𝟚 .Iso.fun  = ℝ₋₊→ℝ₊×Bool
Iso-ℝ₋₊-ℝ₊×𝟚 .Iso.inv = ℝ₊×Bool→ℝ₋₊
Iso-ℝ₋₊-ℝ₊×𝟚 .Iso.rightInv = sec-ℝ₋₊→ℝ₊×Bool
Iso-ℝ₋₊-ℝ₊×𝟚 .Iso.leftInv = ret-ℝ₋₊→ℝ₊×Bool

IsGroupℝˣ : IsGroup {G = ℝ₋₊}
  (1 , inl decℚ<ᵣ?)
  _·ᵣ₋₊_
  λ (x , 0＃x) → invℝ x 0＃x , invℝ0＃ x 0＃x
IsGroupℝˣ = makeIsGroup
  (isSetΣ isSetℝ (isProp→isSet ∘ isProp＃ 0))
  (λ _ _ _ → ℝ₋₊≡ (·ᵣAssoc _ _ _))
  (λ _ → ℝ₋₊≡ (·IdR _)) (λ _ → ℝ₋₊≡ (·IdL _))
  (λ _ → ℝ₋₊≡ (x·invℝ[x] _ _))
  (λ _ → ℝ₋₊≡ (·ᵣComm _ _ ∙ x·invℝ[x] _ _))

·₊Groupℝ : Group₀
·₊Groupℝ = group _ _ _ _ Is·₊Groupℝ

·Groupℝ : Group₀
·Groupℝ = group _ _ _ _ IsGroupℝˣ


-- GroupIso-ℝˣ-ℝˣ₊×𝟚 : GroupIso ·Groupℝ (DirProd ·₊Groupℝ BoolGroup)
-- GroupIso-ℝˣ-ℝˣ₊×𝟚 = Iso-ℝ₋₊-ℝ₊×𝟚 , makeIsGroupHom {!!}


module AutCont (Gstr : GroupStr ℝ) where

 open GroupStr Gstr
 Ĝ : Group₀
 Ĝ = ℝ , Gstr

 contGroupIso : Type
 contGroupIso = Σ (GroupIso Ĝ Ĝ) λ x → (IsContinuous (Iso.fun (fst x))
                                        × IsContinuous (Iso.inv (fst x)))
 i≡ : ∀ {x₀ x₁ : contGroupIso} → Iso.fun (fst (fst x₀)) ≡ Iso.fun (fst (fst x₁)) → x₀ ≡ x₁
 i≡ {x₀} {x₁} = Σ≡Prop (λ _ → isProp× (isPropIsContinuous _) (isPropIsContinuous _))
  ∘ GroupIso≡ ∘ SetsIso≡fun isSetℝ isSetℝ


 Aut[_]ᵣ : Group₀
 Aut[_]ᵣ =
   makeGroup {G = contGroupIso}
     (idGroupIso , IsContinuousId , IsContinuousId)
     (λ (a , b , c) (a' , b' , c') →
       compGroupIso a a' , IsContinuous∘ _ _ b' b , IsContinuous∘ _ _ c c')
     (λ (a , b , c) → invGroupIso a , c , b)
     (isSetΣ (isSetΣ (isSet-SetsIso isSetℝ isSetℝ)
        (λ _ → isProp→isSet (isPropIsGroupHom _ _)))
         (λ _ → isProp→isSet (isProp× (isPropIsContinuous _) (isPropIsContinuous _))))
     (λ _ _ _ → i≡ refl)
          (λ _ → i≡ refl)
          (λ _ → i≡ refl)
          (λ ((x , _) , _) → i≡ (funExt (Iso.leftInv x)))
          (λ ((x , _) , _) → i≡ (funExt (Iso.rightInv x)))



open AutCont public using (Aut[_]ᵣ)

module +GrAutomorphism (A : ⟨ (Aut[ +Groupℝ ]) ⟩) where

 open IsGroupHom (snd A)
 open Iso (fst A)

 f-linℚ : ∀ x q → rat q ·ᵣ fun x ≡ fun (rat q ·ᵣ x)
 f-linℚ x = SQ.ElimProp.go w
  where

  w'' : ∀ x n → fromNat n ·ᵣ fun x ≡ fun (fromNat n ·ᵣ x)
  w'' x zero = 𝐑'.0LeftAnnihilates _ ∙∙
    sym pres1 ∙∙ cong fun (sym (𝐑'.0LeftAnnihilates _))
  w'' x (suc n) = sym (x+n·x≡sn·x n (fun x)) ∙∙
     cong (fun x +ᵣ_) (w'' x n) ∙∙
      (sym (pres· _ _) ∙ cong fun (x+n·x≡sn·x n x))


  w' : ∀ n m → rat [ ℤ.pos m , (1+ n) ] ·ᵣ fun x ≡ fun (rat [ ℤ.pos m , (1+ n) ] ·ᵣ x)
  w' n m = cong₂ _·ᵣ_ (cong rat (ℚ.[/]≡· (ℤ.pos m) (1+ n))
      ∙ rat·ᵣrat _ _ ∙ ·ᵣComm  _ _)
    refl ∙
    (sym (·ᵣAssoc _ _ _) ∙
     cong (rat [ pos 1 / 1+ n ] ·ᵣ_)
       (w'' _ _)) ∙
        cong (rat [ pos 1 / 1+ n ] ·ᵣ_)
          (cong fun (cong (_·ᵣ x)
           (cong rat (sym (m·n/m n m)) ∙ rat·ᵣrat _ _)
           ∙ sym (·ᵣAssoc _ _ _)) ∙ sym (w'' _ _)) ∙ ·ᵣAssoc _ _ _
          ∙ cong₂ _·ᵣ_ (sym (rat·ᵣrat _ _)
           ∙ cong rat (ℚ.·Comm _ _
            ∙ sym (ℚ.[/]≡· (pos (suc n)) (1+ n)) ∙
            eq/ _ _ (ℤ.·Comm _ _))) refl ∙ ·IdL _


  w : ElimProp (λ z → rat z ·ᵣ fun x ≡ fun (rat z ·ᵣ x))
  w .ElimProp.isPropB _ = isSetℝ _ _
  w .ElimProp.f (pos m , (1+ n)) = w' n m
  w .ElimProp.f (ℤ.negsuc m , (1+ n)) =
    cong₂ _·ᵣ_ (cong rat (ℚ.-[/] _ _) ∙ sym (-ᵣ-rat _)) refl  ∙ (-ᵣ· _ _)
    ∙ cong -ᵣ_ (w' n (suc m)) ∙ sym (presinv _) ∙
     cong fun (sym (-ᵣ· _ _) ∙
       cong₂ _·ᵣ_ (-ᵣ-rat _ ∙ cong rat (sym (ℚ.-[/] _ _) )) refl)

 α = fun 1

 fun-rat : ∀ q → fun (rat q) ≡ rat q ·ᵣ α
 fun-rat q = cong fun (sym (·IdR _)) ∙ sym (f-linℚ 1 q)

 -- _ : {!!}
 -- _ = {!fun-rat 1!}

 Σfun' : Σ[ f' ∈ (ℝ → ℝ) ] ∃[ L ∈ ℚ₊ ] (Lipschitz-ℝ→ℝ L f')
 Σfun' = fromLipschitz' (fun ∘ rat)
  (PT.map
     (λ (δ , <δ , δ<) →
      let δ₊ = δ , ℚ.<→0< _
             (<ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _
              (0≤absᵣ _) <δ))
      in δ₊ , λ q r ε x x₁ →
          let u = ℚ.absFrom<×< (fst ε) (q ℚ.- r) x x₁
          in invEq (∼≃abs<ε _ _ _)
                (isTrans≡<ᵣ _ _ _
                  (cong absᵣ (cong₂ _-ᵣ_ (fun-rat q) (fun-rat r)
                   ∙ sym (𝐑'.·DistL- _ _ _))
                    ∙ ·absᵣ _ _ ∙
                     ·ᵣComm _ _ ∙
                      cong (absᵣ α ·ᵣ_)
                      (cong absᵣ (-ᵣ-rat₂ _ _) ∙ absᵣ-rat _ ) )
                  (isTrans≤<ᵣ _ _ _
                    (isTrans≤≡ᵣ _ _ _
                      (≤ᵣ-·ᵣo _ _ _
                        (≤ℚ→≤ᵣ _ _ (ℚ.0≤abs _) )
                        (<ᵣWeaken≤ᵣ _ _ <δ))
                      (sym (rat·ᵣrat _ _)))
                    (<ℚ→<ᵣ _ _ (ℚ.<-o· _ _ _ (ℚ.0<ℚ₊ δ₊) u))))
         )
     (denseℚinℝ (absᵣ α) ((absᵣ α) +ᵣ 1)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR (absᵣ α)))
         (<ᵣ-o+ 0 1 _ decℚ<ᵣ?))))


 fun' = fst Σfun'

 fun'-cont : IsContinuous fun'
 fun'-cont = PT.rec
  (isPropIsContinuous _)
  (λ x → Lipschitz→IsContinuous _ _ (snd x))
  (snd Σfun')

 fun'· : ∀ x → fun' x ≡ x ·ᵣ α
 fun'· = ≡Continuous _ _ fun'-cont
   (IsContinuous·ᵣR α)
    λ q → fromLipschitz'-rat fun _ _ ∙ fun-rat q

 fun'-rat : ∀ x → fun' (rat x) ≡ fun (rat x)
 fun'-rat x = fun'· (rat x) ∙ sym (fun-rat x)



-- .Elimℝ-Prop2Sym.rat-ratA r q p =
--     let z = sym (fun'-rat r) ∙∙ p ∙∙ fun'-rat q
--     in isoFunInjective (fst A) _ _ z
--   w .Elimℝ-Prop2Sym.rat-limA = {!!}
--   w .Elimℝ-Prop2.lim-limA = {!!}
--   w .Elimℝ-Prop2.isPropA _ _ = isPropΠ λ _ → isSetℝ _ _

 -- fun'·-equiv : isEquiv fun'
 -- fun'·-equiv = isEmbedding×isSurjection→isEquiv {f = fun'}
 --  (fun-emb , {!!})

-- module +GrAutomorphism-Cont (A : ⟨ (Aut[ +Groupℝ ]) ⟩) where

--  module F = +GrAutomorphism A
--  module F' = +GrAutomorphism (invGroupIso A)

--  isom' : Iso ℝ ℝ
--  isom' .Iso.fun = F.fun'
--  isom' .Iso.inv = F'.fun'
--  isom' .Iso.rightInv = {!!}
--  -- ≡Continuous _ _
--  --   (IsContinuous∘ _ _ F.fun'-cont F'.fun'-cont) IsContinuousId
--  --     λ r → {!!}
--  isom' .Iso.leftInv = {!!}

--  α·α'≡1 : F'.α ·ᵣ F.α ≡ 1
--  α·α'≡1 = sym (F.fun'· _)
--   ∙  cong F.fun' (sym (·IdL _) ∙ sym (F'.fun'· _)) ∙ isom' .Iso.rightInv 1

--  g-linℚ : ∀ x q → rat q ·ᵣ g x ≡ g (rat q ·ᵣ x)
--  g-linℚ = {!!}


--  β = g 1


--  g-rat : ∀ q → g (rat q) ≡ rat q ·ᵣ β
--  g-rat q = cong g (sym (·IdR _)) ∙ sym (g-linℚ 1 q)


--  α·β=1 : α ·ᵣ β ≡ 1
--  α·β=1 =
--    let q : ℚ
--        q = {!!}
--        pp : {!!}
--        pp =     cong g {!f
--        !}
--                ∙ Iso.leftInv (fst A) (rat q)
--    in {!!}

--  -- f≠1 : f 1 ≡ 0 → ⊥
--  -- f≠1 p = {!inj-rat _ _
--  --   (isoFunInjective (fst A) _ _ (p ∙ sym (pres1)))!}

--  0<∣α∣ : 0 <ᵣ absᵣ α
--  0<∣α∣ = {! !}


-- --  _ : {!!}
-- --  _ = {!g (absᵣ α)!}


-- --  f-cont : IsContinuous f
-- --  f-cont u ε =
-- --   PT.map
-- --     {!!}
-- --     {!!}


Invlipschitz-ℝ→ℝ→injective-interval : ∀ K a b f →
 Invlipschitz-ℝ→ℝℙ K (intervalℙ a b) f
    → ∀ x x∈ y y∈ → f x x∈ ≡ f y y∈ → x ≡ y
Invlipschitz-ℝ→ℝ→injective-interval K a b f il x x∈ y y∈ =
 fst (∼≃≡ _ _) ∘
   (λ p ε → subst∼ (ℚ.y·[x/y] K (fst ε))
     (il x x∈ y  y∈ ((invℚ₊ K) ℚ₊· ε) (p (invℚ₊ K ℚ₊· ε))))
   ∘S invEq (∼≃≡ _ _)


intervalℙ→dist< : ∀ a b x y → x ∈ intervalℙ a b → y ∈ intervalℙ a b
                   → absᵣ (x -ᵣ y) ≤ᵣ b -ᵣ a
intervalℙ→dist< a b x y (a≤x , x≤b) (a≤y , y≤b) =
  isTrans≡≤ᵣ _ _ _ (abs-max _ ∙ cong (maxᵣ _) (-[x-y]≡y-x _ _) )
    (max≤-lem _ _ _ (≤ᵣMonotone+ᵣ _ _ _ _ x≤b (-ᵣ≤ᵣ _ _ a≤y))
                    ((≤ᵣMonotone+ᵣ _ _ _ _ y≤b (-ᵣ≤ᵣ _ _ a≤x))))



ℚ1≤x⊔1/x : ∀ x → 1 ℚ.≤ ℚ.max (fst x) (fst (invℚ₊ x))
ℚ1≤x⊔1/x x =
  ⊎.rec
     (λ 1≤x →
       ℚ.isTrans≤ _ _ _ 1≤x (ℚ.≤max (fst x) (fst (invℚ₊ x))) )
     (λ x<1 →
       ℚ.isTrans≤ _ _ _ (ℚ.invℚ≤invℚ 1 _
         (ℚ.<Weaken≤ _ _ x<1))
         (ℚ.≤max' (fst x) (fst (invℚ₊ x))))
   (ℚ.Dichotomyℚ 1 (fst x))


opaque
 unfolding maxᵣ
 1≤x⊔1/x : ∀ x → 1 ≤ᵣ maxᵣ (fst x) (fst (invℝ₊ x))
 1≤x⊔1/x =
   uncurry (<→≤ContPos'pred {0}
     (AsContinuousWithPred _ _
       (IsContinuousConst _))
        (contDiagNE₂WP maxR _ _ _
          (AsContinuousWithPred _ _
            IsContinuousId) (snd invℝ'))
              λ u 0<u →
                subst (1 ≤ᵣ_) (cong (maxᵣ (rat u))
                  (sym (invℝ'-rat _ _ _)))
                  (≤ℚ→≤ᵣ _ _ (
                   (ℚ1≤x⊔1/x (u , ℚ.<→0< u (<ᵣ→<ℚ _ _ 0<u))))))


0<pos[sucN]² : ∀ n → 0 ℤ.< (ℤ.pos (suc n)) ℤ.· (ℤ.pos (suc n))
0<pos[sucN]² n = ℤ.<-·o {0} {ℤ.pos (suc n)} {n} (ℤ.suc-≤-suc ℤ.zero-≤pos)

0<x² : ∀ n → ¬ (n ≡ 0) → 0 ℤ.< n ℤ.· n
0<x² (pos zero) x = ⊥.elim (x refl)
0<x² (pos (suc n)) _ = 0<pos[sucN]² n
0<x² (ℤ.negsuc n) _ = subst (0 ℤ.<_) (sym (ℤ.negsuc·negsuc n n))
  (0<pos[sucN]² n)

mn<m²+n² : (a b : ℕ) → pos (suc a) ℤ.· pos (suc b) ℤ.<
                    (pos (suc a) ℤ.· pos (suc a))
                      ℤ.+ (pos (suc b) ℤ.· pos (suc b))
mn<m²+n² a b =
  ℤ.<-+pos-trans {k = a ℕ.· suc b} h'
 where
 a' = pos (suc a)
 b' = pos (suc b)
 h : ((a' ℤ.· b') ℤ.+ (a' ℤ.· b')) ℤ.≤
         (a' ℤ.· a' ℤ.+ b' ℤ.· b')
 h = subst2 (ℤ._≤_)
       (𝐙'.+IdL' _ _ refl)
       (cong (ℤ._+ ((a' ℤ.· b') ℤ.+ (a' ℤ.· b'))) (L𝐙.lem--073 {a'} {b'})
        ∙ 𝐙'.minusPlus _ _)
       (ℤ.≤-+o {o = ((a' ℤ.· b') ℤ.+ (a' ℤ.· b'))} (ℤ.0≤x² (a' ℤ.- b')))

 h' = ℤ.<≤-trans (ℤ.<-o+ (subst (ℤ._< a' ℤ.· b')
     (sym (ℤ.pos·pos _ _)) (ℤ.<-·o {k = b}
       ℤ.isRefl≤))) h


ℚ1<x+1/x : ∀ x → 1 ℚ.< fst x ℚ.+ fst (invℚ₊ x)
ℚ1<x+1/x = uncurry (SQ.ElimProp.go w)
 where
 w : ElimProp (λ z → (y : 0< z) → 1 ℚ.< z ℚ.+ fst (invℚ₊ (z , y)))
 w .ElimProp.isPropB _ = isPropΠ λ _ → ℚ.isProp< _ _
 w .ElimProp.f (pos (suc n) , (1+ m)) y =
    subst2 ℤ._<_
      (sym (ℤ.pos·pos  _ _)) (ℤ.+Comm _ _ ∙ sym (ℤ.·IdR _))
     (mn<m²+n² m n)
opaque
 unfolding _+ᵣ_
 1≤x+1/x : ∀ x → 1 ≤ᵣ fst x +ᵣ fst (invℝ₊ x)
 1≤x+1/x =
   uncurry (<→≤ContPos'pred {0}
     (AsContinuousWithPred _ _
       (IsContinuousConst _))
        (contDiagNE₂WP sumR _ _ _
          (AsContinuousWithPred _ _
            IsContinuousId) (snd invℝ'))
              λ u 0<u →
                subst (1 ≤ᵣ_) (cong (rat u +ᵣ_)
                  (sym (invℝ'-rat _ _ _)))
                  (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ 1 _
                   (ℚ1<x+1/x (u , ℚ.<→0< u (<ᵣ→<ℚ _ _ 0<u))))))

-- pasting : (x₀ : ℝ) → (f< : ∀ x → x ≤ᵣ x₀ → ℝ)
--                   → (<f : ∀ x → x₀ ≤ᵣ x → ℝ)
--                   → f< x₀ (≤ᵣ-refl x₀) ≡ <f x₀ (≤ᵣ-refl x₀)
--                   → Σ[ f ∈ (ℝ → ℝ) ]
--                         (∀ x x≤x₀ → f x ≡ f< x x≤x₀)
--                          × (∀ x x₀≤x → f x ≡ <f x x₀≤x)
-- pasting x₀ f< <f p =
--   (λ x → (<f (maxᵣ x₀ x) (≤maxᵣ _ _)
--       +ᵣ f< (minᵣ x₀ x) (min≤ᵣ _ _))
--        -ᵣ f< x₀ (≤ᵣ-refl x₀))
--   , (λ x x≤x₀ →
--       let z = minᵣComm _ _ ∙ ≤→minᵣ _ _ x≤x₀
--       in cong₂ _-ᵣ_ (cong₂ _+ᵣ_
--              (cong (uncurry <f) (Σ≡Prop (λ _ → isProp≤ᵣ _ _)
--                (maxᵣComm _ _ ∙ ?))) -- x≤x₀
--              (cong (uncurry f<) (Σ≡Prop (λ _ → isProp≤ᵣ _ _) z)) ) p ∙
--           L𝐑.lem--063)
--   , λ x x₀≤x →
--        𝐑'.plusMinus' _ _ _ (cong (uncurry f<)
--         (Σ≡Prop (λ _ → isProp≤ᵣ _ _) (≤→minᵣ _ _ x₀≤x))) ∙
--         (cong (uncurry <f)
--         (Σ≡Prop (λ _ → isProp≤ᵣ _ _) ?)) -- x₀≤x


-- pasting< : ∀ b x₀ b<x₀
--                   → (f< : ∀ x → b <ᵣ x → x ≤ᵣ x₀ → ℝ)
--                   → (<f : ∀ x → x₀ ≤ᵣ x → ℝ)
--                   → f< x₀ b<x₀ (≤ᵣ-refl x₀) ≡ <f x₀ (≤ᵣ-refl x₀)
--                   → Σ[ f ∈ (∀ x → b <ᵣ x → ℝ) ]
--                         (∀ x b<x x≤x₀ → f x b<x ≡ f< x b<x x≤x₀)
--                          × (∀ x b<x x₀≤x → f x b<x ≡ <f x x₀≤x)
-- pasting< b x₀ b<x₀ f< <f p =
--    ((λ x x< → (<f (maxᵣ x₀ x) (≤maxᵣ _ _)
--       +ᵣ f< (minᵣ x₀ x) (<min-lem _ _ _ b<x₀ x<) (min≤ᵣ _ _))
--        -ᵣ f< x₀ b<x₀ (≤ᵣ-refl x₀)))
--   , (λ x b<x x≤x₀ →
--       let z = minᵣComm _ _ ∙ ≤→minᵣ _ _ x≤x₀
--       in cong₂ _-ᵣ_ (cong₂ _+ᵣ_
--              (cong (uncurry <f) (Σ≡Prop (λ _ → isSetℝ _ _)
--                (maxᵣComm _ _ ∙ x≤x₀)))
--              (cong (uncurry (uncurry f<))
--                (Σ≡Prop (flip isProp≤ᵣ _ ∘ fst) (Σ≡Prop (isProp<ᵣ _) z)))
--              ) p ∙
--           L𝐑.lem--063)
--    , λ x b<x x₀≤x →
--      𝐑'.plusMinus' _ _ _ (cong (uncurry (uncurry f<))
--         (Σ≡Prop (λ (x , _) → isProp≤ᵣ x _) (Σ≡Prop (isProp<ᵣ _) (≤→minᵣ _ _ x₀≤x))) ) ∙
--        cong (uncurry <f) ((Σ≡Prop (λ _ → isSetℝ _ _) x₀≤x))



-- pasting≤ : ∀ b x₀ b≤x₀
--                   → (f< : ∀ x → b ≤ᵣ x → x ≤ᵣ x₀ → ℝ)
--                   → (<f : ∀ x → x₀ ≤ᵣ x → ℝ)
--                   → f< x₀ b≤x₀ (≤ᵣ-refl x₀) ≡ <f x₀ (≤ᵣ-refl x₀)
--                   → Σ[ f ∈ (∀ x → b ≤ᵣ x → ℝ) ]
--                         (∀ x b≤x x≤x₀ → f x b≤x ≡ f< x b≤x x≤x₀)
--                          × (∀ x b≤x x₀≤x → f x b≤x ≡ <f x x₀≤x)
-- pasting≤ b x₀ b≤x₀ f< <f p =
--   (λ x _ → (fst h) x)
--   , (λ x b≤x x≤x₀ → fst (snd h) x x≤x₀ ∙ q b≤x)
--   ,  const ∘ snd (snd h)
--  where

--  q : ∀ {y y' : Σ[ x ∈ ℝ ] (b ≤ᵣ x) × (x ≤ᵣ x₀)}
--          → (a : (fst y) ≡ (fst y')) → _ ≡ _
--  q {y} {y'} = cong {x = y} {y = y'} (uncurry $ uncurry ∘ f<) ∘
--          (Σ≡Prop (λ _ → isProp× (isSetℝ _ _) (isSetℝ _ _)))

--  h = pasting x₀
--        (λ x x≤x₀ → f< (maxᵣ b x) (≤maxᵣ _ _)
--          (max≤-lem _ _ _ b≤x₀ x≤x₀))
--        <f (q b≤x₀ ∙ p)


opaque
 unfolding _+ᵣ_
 slope-lower-bound : (z : ℝ₊) (B : ℚ₊) (1<z : 1 <ᵣ fst z) → (y₀ y₁ : ℚ )
   → (y₀<y₁ : y₀ ℚ.< y₁)
   → (y₀∈ : y₀ ∈ ℚintervalℙ (ℚ.- (fst B)) (fst B))
   → (y₁∈ : y₁ ∈ ℚintervalℙ (ℚ.- (fst B)) (fst B)) →
   fst (z ^ℚ (ℚ.- fst B)) ·ᵣ
        ((fst z -ᵣ 1) ／ᵣ₊ z)
       <ᵣ
   ((fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  y₀<y₁ ))
 slope-lower-bound z B 1<z y₀ y₁ y₀<y₁ (-B≤y₀ , y₀≤B) (-B≤y₁ , y₁≤B) =
   isTrans<≡ᵣ _ _ _
     (≤<ᵣ₊Monotone·ᵣ
       ((z ^ℚ (ℚ.- (fst B)))) (fst (z ^ℚ y₀))
       (_ ,
         isTrans≡≤ᵣ _ _ _ (sym (𝐑'.0LeftAnnihilates _))
            (≤ᵣ-·ᵣo 0 _ _
             (<ᵣWeaken≤ᵣ _ _ (snd (invℝ₊ (fst z , z .snd))))
              (<ᵣWeaken≤ᵣ _ _ (x<y→0<y-x _ _ 1<z))))
               ((fst (z ^ℚ (fst h₊)) -ᵣ 1) ／ᵣ₊ ℚ₊→ℝ₊ h₊)

       (^ℚ-MonotoneR {z} (ℚ.- (fst B)) y₀ -B≤y₀ (<ᵣWeaken≤ᵣ _ _ 1<z))

        (invEq (z/y'<x/y≃y₊·z<y'₊·x _ _ _ _)
           brn )
        )
       (·ᵣAssoc _ _ _
        ∙ cong (_·ᵣ
         fst (invℝ₊ (ℚ₊→ℝ₊ h₊)))
          (sym (factor-xᵃ-xᵇ z _ _) ))

  where
   h₊ : ℚ₊
   h₊ = ℚ.<→ℚ₊ _ _ y₀<y₁

   brn : fst (ℚ₊→ℝ₊ h₊) ·ᵣ (fst z -ᵣ 1)   <ᵣ
         fst z ·ᵣ (fst (z ^ℚ fst h₊) -ᵣ rat [ pos 1 / 1+ 0 ])

   brn = isTrans<≡ᵣ _ _ _ (a+c<b⇒a<b-c _ _ _ (isTrans≡<ᵣ _ _ _ (sym (·DistR+ (fst (ℚ₊→ℝ₊ h₊)) 1 _))
          (a+c<b⇒a<b-c _ _ 1
           (isTrans≡<ᵣ _ _ _
            (+ᵣComm (rat (fst h₊ ℚ.+ [ pos 1 / 1+ 0 ]) ·ᵣ
       (fst z -ᵣ rat [ pos 1 / 1+ 0 ])) 1) (bernoulli's-ineq-^ℚ z (fst h₊ ℚ.+ 1)
             1<z (subst (1 ℚ.<_) (ℚ.+Comm 1 (fst h₊))
              (ℚ.<+ℚ₊' _ _ h₊ (ℚ.isRefl≤ 1))) )))))
             (sym (+ᵣAssoc (fst (z ^ℚ (fst h₊ ℚ.+ 1))) _ _) ∙
              cong₂ _+ᵣ_
                (cong fst (sym (^ℚ-+ z (fst h₊) 1))
                  ∙ ·ᵣComm _ _ ∙
                    cong (_·ᵣ (z ^ℚ fst h₊) .fst) (cong fst (^ℚ-1 _) ))
                ((sym (-ᵣDistr _ _) ∙
                  cong (-ᵣ_) (cong (1 +ᵣ_) (·IdL _)
                   ∙ L𝐑.lem--05 ∙ sym (·IdL _))
                  ) ∙ sym (-ᵣ· _ _) ∙ ·ᵣComm _ _)
               ∙ sym (·DistL+ _ _ _) )


slope-upper-bound : (z : ℝ₊) (B : ℚ₊) → (y₀ y₁ : ℚ )
  → (y₀<y₁ : y₀ ℚ.< y₁)
  → (y₀∈ : y₀ ∈ ℚintervalℙ (ℚ.- (fst B)) (fst B))
  → (y₁∈ : y₁ ∈ ℚintervalℙ (ℚ.- (fst B)) (fst B)) →
  ((fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  y₀<y₁ ))
     ≤ᵣ fst (z ^ℚ (fst B)) ·ᵣ (fst z -ᵣ 1)
slope-upper-bound z B y₀ y₁ y₀<y₁ (-B≤y₀ , y₀≤B) (-B≤y₁ , y₁≤B) =
  isTrans≤≡ᵣ _ _ _
    (slope-monotone z
      y₀ y₁ (fst B) (fst B ℚ.+ 1)
       y₀<y₁ B<B+1 y₀≤B
         (ℚ.isTrans≤ _ _ _ y₁≤B (ℚ.<Weaken≤ _ _ B<B+1))
         )
    (𝐑'.·IdR' _ _ (cong (fst ∘ invℝ₊)
      (ℝ₊≡ (cong rat lem--063)) ∙ cong fst invℝ₊1) ∙
       factor-xᵃ-xᵇ z (fst B ℚ.+ 1) (fst B) ∙
         cong (λ u → fst (z ^ℚ fst B) ·ᵣ (fst u -ᵣ 1))
           (cong (z ^ℚ_) lem--063 ∙ ^ℚ-1 z))

 where
  h₊ = ℚ.<→ℚ₊ _ _ y₀<y₁
  B<B+1 = ℚ.<+ℚ₊' _ _ 1 (ℚ.isRefl≤ (fst B))


-- -- lowBnd-1/ℕ : (ε : ℝ₊) → ∃[ k ∈ ℕ₊₁ ] rat [ 1 / k ] <ᵣ fst ε
-- -- lowBnd-1/ℕ = {!!}


-- -- ceilℚ₊ q = 1+ (fst (fst (floor-fracℚ₊ q))) ,
-- --    subst2 (_<_) --  (fromNat (suc (fst (fst (floor-fracℚ₊ q)))))
-- --       (ℚ.+Comm _ _ ∙ fst (snd (floor-fracℚ₊ q)))
-- --       (ℚ.ℕ+→ℚ+ _ _)
-- --        (<-+o _ _ (fromNat (fst (fst (floor-fracℚ₊ q))))
-- --          (snd (snd (snd (floor-fracℚ₊ q)))))


slUpBd : ℕ → ℕ → ℚ₊
slUpBd Z m = (fromNat (suc (suc Z)) ℚ₊^ⁿ (suc m)) ℚ₊· fromNat (suc Z)



monotone^ℚ' : ∀ q q' q''
 → q ℚ.≤ q'
 → q' ℚ.≤ q''
 → ∀ u 0<u
 → minᵣ (fst ((rat u , 0<u) ^ℚ q)) (fst ((rat u , 0<u) ^ℚ q'')) ≤ᵣ
   fst ((rat u , 0<u) ^ℚ q')
monotone^ℚ' q q' q'' q≤q' q'≤q'' u 0<u =
 ⊎.rec
   (λ 1≤u →
     isTrans≤ᵣ _ _ _ (min≤ᵣ (fst ((rat u , 0<u) ^ℚ q))
            (fst ((rat u , 0<u) ^ℚ q'')))
        (^ℚ-MonotoneR {(rat u , 0<u)} q q'
           q≤q'
        (≤ℚ→≤ᵣ _ _ 1≤u)))
   (λ u<1 → isTrans≤ᵣ _ _ _
     (min≤ᵣ' (fst ((rat u , 0<u) ^ℚ q))
            (fst ((rat u , 0<u) ^ℚ q'')))
       let xx = (^ℚ-MonotoneR {invℝ₊ (rat u , 0<u)}
               _ _  (ℚ.minus-≤ _ _ q'≤q'')
                   (isTrans≤≡ᵣ _ _ _
                    (invEq (z≤x/y₊≃y₊·z≤x 1 1 (rat u , 0<u))
                      (isTrans≡≤ᵣ _ _ _ (·IdR _)
                        (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ u<1))))
                    (·IdL _)))
       in subst2 _≤ᵣ_
            (cong fst (sym (^ℚ-minus _ _)))
            (cong fst (sym (^ℚ-minus _ _)))
            xx)
   (ℚ.Dichotomyℚ 1 u)


opaque
 unfolding minᵣ
 monotone^ℚ : ∀ q q' q''
  → q ℚ.≤ q'
  → q' ℚ.≤ q''
  → ∀ z
  → minᵣ (fst (z ^ℚ q)) (fst (z ^ℚ q'')) ≤ᵣ fst (z ^ℚ q')
 monotone^ℚ q q' q'' q≤q' q'≤q'' =
   uncurry (<→≤ContPos'pred {0}
     (contDiagNE₂WP minR _ _ _
       (IsContinuous^ℚ q)
       (IsContinuous^ℚ q''))
     (IsContinuous^ℚ q')
     λ u 0<u → monotone^ℚ' q q' q'' q≤q' q'≤q'' u 0<u)

-- module BDL (z : ℝ₊) (Z : ℕ)
--           (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
--           (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ]  ≤ᵣ fst z)
--           -- (1+1/Z<z : rat (1 ℚ.+ [ 1 / 1+ (suc Z) ]) ≤ᵣ fst z )
--            where


-- bdl' : 1 ≤ᵣ fst z → boundedLipschitz (fst ∘ z ^ℚ_) (slUpBd Z)
-- bdl' 1≤z n = ℚ.elimBy≡⊎<
--  (λ x y X y∈ x∈ → subst2 _≤ᵣ_
--       (minusComm-absᵣ _ _)
--       (cong (rat ∘ (fst (slUpBd Z n) ℚ.·_)) (ℚ.absComm- _ _))
--       (X x∈ y∈)  )
--  (λ x _ _ → subst2 _≤ᵣ_
--     (cong absᵣ (sym (+-ᵣ _)))
--     (cong rat (sym (𝐐'.0RightAnnihilates' _ _ (cong ℚ.abs (ℚ.+InvR x)))))
--     (≤ᵣ-refl 0))
--  λ y₀ y₁ y₀<y₁ y₀∈ y₁∈ →
--   isTrans≡≤ᵣ _ _ _ (absᵣNonNeg _ (x≤y→0≤y-x _ _
--         (^ℚ-MonotoneR _ _ (ℚ.<Weaken≤ _ _ y₀<y₁) 1≤z )))
--     (isTrans≤≡ᵣ _ _ _ (isTrans≤ᵣ _ _ _ (
--    (fst (z/y≤x₊≃z≤y₊·x _ _ _) (slope-upper-bound z (fromNat (suc n))
--    y₀ y₁ y₀<y₁
--     (ℚ.absTo≤×≤ (fromNat (suc n)) y₀ y₀∈)
--     (ℚ.absTo≤×≤ (fromNat (suc n)) y₁ y₁∈))))
--      (≤ᵣ-o· _ _ _ (ℚ.<Weaken≤ 0 _ (ℚ.-< _ _ y₀<y₁))
--       (≤ᵣ₊Monotone·ᵣ _ _ _ _
--         (<ᵣWeaken≤ᵣ _ _ $ snd (fromNat (suc (suc Z)) ^ℚ fst (fromNat (suc n))))
--         (x≤y→0≤y-x _ _ 1≤z)
--         (^ℚ-Monotone {y = fromNat (suc (suc Z))}
--          (fromNat (suc n)) z≤Z)
--         (≤ᵣ-+o _ _ (-1) z≤Z))))
--      (·ᵣComm _ _ ∙
--       cong₂ (_·ᵣ_)
--         (cong₂ (_·ᵣ_) (^ⁿ-ℚ^ⁿ _ _) (cong rat (ℚ.ℤ+→ℚ+ _ _))
--          ∙ sym (rat·ᵣrat _ _) )
--         (cong rat (sym (ℚ.absPos _ (ℚ.-< _ _ y₀<y₁))))
--        ∙ sym (rat·ᵣrat _ _)))



-- --  slUpBdInv : ℕ → ℚ₊
-- --  slUpBdInv m = (fromNat (suc (suc Z))) ℚ₊^ⁿ (suc (suc (suc m)))
-- --      -- ℚ₊· ((invℚ₊ (fromNat (suc (suc Z)))) ℚ₊· invℚ₊ (fromNat (suc (suc Z))))
-- -- -- ((fst z -ᵣ 1) ／ᵣ₊ z)

--  -- slpBdIneq : ∀ n → fst (invℚ₊ (slUpBdInv n)) ℚ.≤
--  --    fst (slUpBd n)
--  -- slpBdIneq n = ℚ.isTrans≤ _ 1 _
--  --   (fst (ℚ.invℚ₊-≤-invℚ₊ 1 _)
--  --     (ℚ.1≤x^ⁿ (fromNat (suc (suc Z)))
--  --          (suc (suc (suc n)))
--  --          (ℚ.≤ℤ→≤ℚ 1 (pos (suc (suc Z)))
--  --            (ℤ.suc-≤-suc {0} {pos (suc Z)}
--  --             (ℤ.zero-≤pos {suc Z})))))
--  --   (ℚ.≤Monotone·-onNonNeg 1 _ 1 _
--  --    ((ℚ.1≤x^ⁿ (fromNat (suc (suc Z)))
--  --          ((suc n))
--  --          (ℚ.≤ℤ→≤ℚ 1 (pos (suc (suc Z)))
--  --            (ℤ.suc-≤-suc {0} {pos (suc Z)}
--  --             (ℤ.zero-≤pos {suc Z})))))
--  --    ((ℚ.≤ℤ→≤ℚ 1 (pos (suc Z))
--  --            (ℤ.suc-≤-suc {0} {pos Z}
--  --             (ℤ.zero-≤pos {Z}))))
--  --    (ℚ.decℚ≤? {0} {1})
--  --    (ℚ.decℚ≤? {0} {1}))

-- --  1<z : 1 <ᵣ (fst z)
-- --  1<z = isTrans<ᵣ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' _ _ _ (ℚ.isRefl≤ 1))) 1+1/Z<z


-- clampᵣ₊ : ℝ₊ → ℝ₊ → ℝ₊ → ℝ₊
-- clampᵣ₊ d u x = minᵣ₊ (maxᵣ₊ d x) u

isIncrasingℙᵣ : (P : ℙ ℝ) → (∀ (x : ℝ) → x ∈ P → ℝ) → Type
isIncrasingℙᵣ P f =
 ∀ (x : ℝ) (x∈ : x ∈ P) (y : ℝ) (y∈ : y ∈ P) → x <ᵣ y → f x x∈ <ᵣ f y y∈


isNondecrasingℙᵣ : (P : ℙ ℝ) → (∀ (x : ℝ) → x ∈ P → ℝ) → Type
isNondecrasingℙᵣ P f =
 ∀ (x : ℝ) (x∈ : x ∈ P) (y : ℝ) (y∈ : y ∈ P) → x ≤ᵣ y → f x x∈ ≤ᵣ f y y∈

opaque
 unfolding minᵣ maxᵣ
 ∈interval→≤ContPos'pred : {x₀ x₁ : ℚ} → (x₀ ℚ.≤ x₁)
          → {f₀ f₁ : ∀ x → x ∈ intervalℙ (rat x₀) (rat x₁)   → ℝ}
          → IsContinuousWithPred (intervalℙ (rat x₀) (rat x₁)) f₀
          → IsContinuousWithPred (intervalℙ (rat x₀) (rat x₁)) f₁
          → (∀ u x₀<u<x₁ → f₀ (rat u) x₀<u<x₁
                     ≤ᵣ f₁ (rat u) x₀<u<x₁ )
              → ∀ x x₀<x<x₁ → f₀ x x₀<x<x₁ ≤ᵣ f₁ x x₀<x<x₁
 ∈interval→≤ContPos'pred {x₀} {x₁} x₀≤x₁ {f₀} {f₁} f₀C f₁C X x (≤x , x≤) =
   subst (λ (u , u∈) → f₀ u u∈ ≤ᵣ f₁ u u∈)
    (Σ≡Prop (∈-isProp ((intervalℙ (rat x₀) (rat x₁))))
      (sym (∈ℚintervalℙ→clampᵣ≡ _ _ _ (≤x , x≤))))
    $ ≤Cont
      {λ x → f₀ (clampᵣ (rat x₀) (rat x₁) x)
        (clampᵣ∈ℚintervalℙ _ _ (≤ℚ→≤ᵣ _ _ x₀≤x₁) _)}
      {λ x → f₁ (clampᵣ (rat x₀) (rat x₁) x)
       ((clampᵣ∈ℚintervalℙ _ _ (≤ℚ→≤ᵣ _ _ x₀≤x₁) _))}
      (IsContinuousWithPred∘IsContinuous _ _ _
          _ f₀C (IsContinuousClamp (rat x₀) (rat x₁)))
      (IsContinuousWithPred∘IsContinuous _ _ _
          _ f₁C (IsContinuousClamp (rat x₀) (rat x₁)))
      (λ u →
         X (ℚ.clamp x₀ x₁ u) (clampᵣ∈ℚintervalℙ (rat x₀) (rat x₁) (≤ℚ→≤ᵣ x₀ x₁ x₀≤x₁) (rat u)))
      x

module BDL (z : ℝ₊) (Z : ℕ)
          (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
          (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ]  ≤ᵣ fst z)
          -- (1+1/Z<z : rat (1 ℚ.+ [ 1 / 1+ (suc Z) ]) ≤ᵣ fst z )
           where

 opaque
  unfolding _+ᵣ_
  bdl' : (z : ℝ₊) (Z : ℕ)
           (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
           (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ]  ≤ᵣ fst z)
           → 1 ≤ᵣ fst z → boundedLipschitz (fst ∘ z ^ℚ_) (slUpBd Z)
  bdl' z Z z≤Z 1/Z≤z 1≤z n = ℚ.elimBy≡⊎<
   (λ x y X y∈ x∈ → subst2 _≤ᵣ_
        (minusComm-absᵣ _ _)
        (cong (rat ∘ (fst (slUpBd Z n) ℚ.·_)) (ℚ.absComm- _ _))
        (X x∈ y∈)  )
   (λ x _ _ → subst2 _≤ᵣ_
      (cong absᵣ (sym (+-ᵣ _)))
      (cong rat (sym (𝐐'.0RightAnnihilates' _ _ (cong ℚ.abs (ℚ.+InvR x)))))
      (≡ᵣWeaken≤ᵣ _ _ (absᵣ-rat 0))) -- (≤ᵣ-refl 0)
   λ y₀ y₁ y₀<y₁ y₀∈ y₁∈ →
    isTrans≡≤ᵣ _ _ _ (absᵣNonNeg _ (x≤y→0≤y-x _ _
          (^ℚ-MonotoneR _ _ (ℚ.<Weaken≤ _ _ y₀<y₁) 1≤z )))
      (isTrans≤≡ᵣ _ _ _ (isTrans≤ᵣ _ _ _ (
     (fst (z/y≤x₊≃z≤y₊·x _ _ _) (slope-upper-bound z (fromNat (suc n))
     y₀ y₁ y₀<y₁
      (ℚ.absTo≤×≤ (fromNat (suc n)) y₀ y₀∈)
      (ℚ.absTo≤×≤ (fromNat (suc n)) y₁ y₁∈))))
       (≤ᵣ-o· _ _ _ (ℚ.<Weaken≤ 0 _ (ℚ.-< _ _ y₀<y₁))
        (≤ᵣ₊Monotone·ᵣ _ _ _ _
          (<ᵣWeaken≤ᵣ _ _ $ snd (fromNat (suc (suc Z)) ^ℚ fst (fromNat (suc n))))
          (x≤y→0≤y-x _ _ 1≤z)
          (^ℚ-Monotone {y = fromNat (suc (suc Z))}
           (fromNat (suc n)) z≤Z)
          (isTrans≡≤ᵣ _ _ _ (cong (fst z +ᵣ_) (-ᵣ-rat 1)) (≤ᵣ-+o _ _ (-1) z≤Z)))))
       (·ᵣComm _ _ ∙
        cong₂ (_·ᵣ_)
          (cong₂ (_·ᵣ_) (^ⁿ-ℚ^ⁿ _ _) (cong rat (ℚ.ℤ+→ℚ+ _ _))
           ∙ sym (rat·ᵣrat _ _) )
          (cong rat (sym (ℚ.absPos _ (ℚ.-< _ _ y₀<y₁))))
         ∙ sym (rat·ᵣrat _ _)))


  bdl : boundedLipschitz (fst ∘ z ^ℚ_) (slUpBd Z)
  bdl n x y x< y< = isTrans≡≤ᵣ _ _ _
     (cong (λ z → absᵣ
       (fst (z ^ℚ  y) -ᵣ fst (z ^ℚ x)))
       (ℝ₊≡ refl))
    (∈interval→≤ContPos'pred {[ 1 / fromNat (suc (suc Z)) ]}
         {fromNat (suc (suc Z)) }
         (ℚ.isTrans≤ [ 1 / (fromNat (suc (suc Z))) ] 1 (fromNat (suc (suc Z)))
          (fst (ℚ.invℚ₊-≤-invℚ₊ 1 ((fromNat (suc (suc Z)))))
            ((ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos 1 (suc (suc Z))
            (ℕ.suc-≤-suc (ℕ.zero-≤ {suc Z})))))  )
           ((ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos 1 (suc (suc Z))
            (ℕ.suc-≤-suc (ℕ.zero-≤ {suc Z}))))))
         {λ x₁ z₁ →
             absᵣ (fst (_ ^ℚ  y) -ᵣ fst (_ ^ℚ x))}
         (IsContinuousWP∘' _ _ _ IsContinuousAbsᵣ (IsContinuousWithPred⊆ pred0< _ _
          (λ z z∈ → isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _))
           (fst z∈))
          ((contDiagNE₂WP sumR _ _ _
         (⊆IsContinuousWithPred _ _ (λ x 0<x → 0<x) _
           (IsContinuous^ℚ y))
            (IsContinuousWP∘' _ _ _ IsContinuous-ᵣ
              ((⊆IsContinuousWithPred _ _ (λ x 0<x → 0<x) _
           (IsContinuous^ℚ x))))))))
         ((AsContinuousWithPred _ _ (IsContinuousConst
           (rat (fst (slUpBd Z n) ℚ.· ℚ.abs (y ℚ.- x))))))
           www
         (fst z) (1/Z≤z , z≤Z))

      where
      www : (u : ℚ)
             (x₀<u<x₁
              : rat u ∈
                intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
                (rat (fromNat (suc (suc Z))))) →
             absᵣ
             (fst
              ((rat u ,
                isTrans<≤ᵣ (rat [ pos 0 / 1 ]) (rat [ 1 / fromNat (suc (suc Z)) ])
                (rat u)
                (<ℚ→<ᵣ [ pos 0 / 1 ] [ 1 / fromNat (suc (suc Z)) ]
                 (ℚ.0<pos 0 (fromNat (suc (suc Z)))))
                (fst x₀<u<x₁))
               ^ℚ y)
              -ᵣ
              fst
              ((rat u ,
                isTrans<≤ᵣ (rat [ pos 0 / 1 ]) (rat [ 1 / fromNat (suc (suc Z)) ])
                (rat u)
                (<ℚ→<ᵣ [ pos 0 / 1 ] [ 1 / fromNat (suc (suc Z)) ]
                 (ℚ.0<pos 0 (fromNat (suc (suc Z)))))
                (fst x₀<u<x₁))
               ^ℚ x))
             ≤ᵣ rat (fst (slUpBd Z n) ℚ.· ℚ.abs (y ℚ.- x))
      www u (≤u , u≤) =
        ⊎.rec
          wwwL
          wwwR
          (ℚ.≤cases 1 u)
       where
       u₊ : ℝ₊
       u₊ = (rat u ,
                  isTrans<≤ᵣ (rat [ pos 0 / 1 ]) (rat [ 1 / fromNat (suc (suc Z)) ])
                  (rat u)
                  (<ℚ→<ᵣ [ pos 0 / 1 ] [ 1 / fromNat (suc (suc Z)) ]
                   (ℚ.0<pos 0 (fromNat (suc (suc Z)))))
                  ≤u)
       wwwL : 1 ℚ.≤ u →
               absᵣ (fst (u₊ ^ℚ y) -ᵣ fst (u₊ ^ℚ x))
               ≤ᵣ rat (fst (slUpBd Z n) ℚ.· ℚ.abs (y ℚ.- x))
       wwwL 1≤u = bdl' u₊
          Z u≤ ≤u (≤ℚ→≤ᵣ _ _ 1≤u) n x y x< y<

       wwwR : u ℚ.≤ 1 →
                absᵣ (fst (u₊ ^ℚ y) -ᵣ fst (u₊ ^ℚ x))
               ≤ᵣ rat (fst (slUpBd Z n) ℚ.· ℚ.abs (y ℚ.- x))
       wwwR u≤1 = subst2 _≤ᵣ_
              (cong absᵣ (cong₂ _-ᵣ_ (cong fst (sym (^ℚ-minus _ _)))
                                     (cong fst (sym (^ℚ-minus _ _)))))
              (cong (λ uu → rat (fst (slUpBd Z n) ℚ.· uu))
                (cong ℚ.abs (sym lem--083) ∙ ℚ.absComm- _ _))
            wwwR'
        where
         wwwR' : absᵣ (fst ((invℝ₊ u₊) ^ℚ (ℚ.- y)) -ᵣ fst ((invℝ₊ u₊) ^ℚ (ℚ.- x)))
                ≤ᵣ rat (fst (slUpBd Z n) ℚ.· ℚ.abs ((ℚ.- y) ℚ.- (ℚ.- x)))
         wwwR' = bdl' (invℝ₊ u₊) Z
          (isTrans≤≡ᵣ _ _ _ (invEq (invℝ₊-≤-invℝ₊ _ _) ≤u) (invℝ₊-rat _)  )
          (isTrans≡≤ᵣ _ _ _ (sym (invℝ₊-rat _)) (invEq (invℝ₊-≤-invℝ₊ _ _) u≤))
          (isTrans≡≤ᵣ _ _ _ (sym (invℝ₊-rat _)) (invEq (invℝ₊-≤-invℝ₊ 1 u₊)
            (≤ℚ→≤ᵣ _ _ u≤1)))

          n (ℚ.- x) (ℚ.- y)
           (subst (ℚ._≤ (fromNat (suc n))) (ℚ.-abs x) x<)
           (subst (ℚ._≤ (fromNat (suc n))) (ℚ.-abs y) y<)

 open BoundedLipsch (fst ∘ z ^ℚ_) (slUpBd Z) bdl public

-- --  bdlInv-lem : ( fst (fromNat (suc (suc Z))
-- --                    ^ℚ -2)) ≤ᵣ ((fst z -ᵣ 1) ／ᵣ₊ z)
-- --  bdlInv-lem = isTrans≡≤ᵣ _ _ _
-- --    (cong fst (^ℚ-minus' _ 2 ∙ sym (^ℚ-+ _ 1 1)) ∙
-- --     cong₂ _·ᵣ_ (
-- --         cong fst (^ℚ-1 (invℝ₊ (fromNat (suc (suc Z)))))
-- --       ∙ cong (fst ∘ invℝ₊) (fromNatℝ≡fromNatℚ _)
-- --      ∙ invℝ₊-rat (fromNat (suc (suc Z))))
-- --         (cong fst (^ℚ-1 (invℝ₊ (fromNat (suc (suc Z)))))
-- --       ∙ cong (fst ∘ invℝ₊) (fromNatℝ≡fromNatℚ _)) )
-- --    (≤ᵣ₊Monotone·ᵣ (rat _) _ _ _
-- --     (<ᵣWeaken≤ᵣ _ _ (x<y→0<y-x _ _ 1<z))
-- --     (<ᵣWeaken≤ᵣ _ _ $
-- --      snd (invℝ₊ (ℚ₊→ℝ₊ ([ pos (suc (suc Z)) , 1 ] , tt)))) (
-- --     <ᵣWeaken≤ᵣ _ _
-- --      (a+c<b⇒a<b-c _ _ _
-- --        (isTrans≡<ᵣ _ _ _ (+ᵣComm (rat [ 1 / 1+ (suc Z) ]) 1) 1+1/Z<z)))
-- --      (invEq (invℝ₊-≤-invℝ₊ (ℚ₊→ℝ₊ _) _) (<ᵣWeaken≤ᵣ _ _ z<Z)))

-- --  bdlInv : boundedInvLipschitz slUpBdInv
-- --  bdlInv n = ℚ.elimBy≡⊎<
-- --   (λ x y X y∈ x∈ → subst2 _≤ᵣ_
-- --        (cong rat (ℚ.absComm- _ _))
-- --        (cong (rat (fst (slUpBdInv n)) ·ᵣ_) (minusComm-absᵣ _ _))
-- --        (X x∈ y∈)  )
-- --   ((λ x _ _ → subst2 _≤ᵣ_
-- --      (cong rat (sym (cong ℚ.abs (ℚ.+InvR x))))
-- --      (sym (𝐑'.0RightAnnihilates' _ _ (cong absᵣ (+-ᵣ _))))
-- --      (≤ᵣ-refl 0)))
-- --   λ y₀ y₁ y₀<y₁ y₀∈ y₁∈ →
-- --    subst2 _≤ᵣ_
-- --      (cong rat (sym (ℚ.absPos _ (ℚ.-< _ _ y₀<y₁))))
-- --      (cong (rat (fst (slUpBdInv n)) ·ᵣ_)
-- --       (sym (absᵣNonNeg _ (x≤y→0≤y-x _ _
-- --          (^ℚ-MonotoneR _ _ (ℚ.<Weaken≤ _ _ y₀<y₁) (<ᵣWeaken≤ᵣ _ _ 1<z) )))))
-- --      (isTrans≡≤ᵣ _ _ _ (sym (·IdR _))
-- --       (fst (z/y'≤x/y≃y₊·z≤y'₊·x _ _ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ y₀<y₁))
-- --             (ℚ₊→ℝ₊ (slUpBdInv n)))
-- --         (isTrans≡≤ᵣ _ _ _ (·IdL _)
-- --          (isTrans≤ᵣ _ _ _
-- --            (isTrans≡≤ᵣ _ _ _
-- --              (invℝ₊-rat _ ∙ cong fst (
-- --                ( (sym (^ℤ-rat (fromNat (suc (suc Z)))
-- --                    (ℤ.negsuc (1 ℕ.+ suc n)))
-- --                    ∙ cong (_^ℚ [ ℤ.negsuc (1 ℕ.+ suc n) / 1 ])
-- --                     (ℝ₊≡ refl))
-- --            ∙ cong (fromNat (suc (suc Z)) ^ℚ_)
-- --             (cong [_/ 1 ] (ℤ.negsuc+ _ _) ∙ sym (ℚ.ℤ+→ℚ+ _ _)))
-- --                ∙ sym (^ℚ-+ _ _ _)) ∙ ·ᵣComm _ _)
-- --              (≤ᵣ₊Monotone·ᵣ
-- --                (fst (fromNat (suc (suc Z))
-- --                    ^ℚ (ℚ.- [ pos (suc n) , (1+ 0) ])))
-- --                _
-- --                _
-- --                _
-- --                (<ᵣWeaken≤ᵣ _ _
-- --                  $ snd (z ^ℚ (ℚ.- [ pos (suc n) , (1+ 0) ])))
-- --                (<ᵣWeaken≤ᵣ _ _
-- --                  $ snd (fromNat (fromNat (suc (suc Z))) ^ℚ -2))
-- --                (subst2 _≤ᵣ_
-- --                  (cong fst (sym (^ℚ-minus' _ _)))
-- --                  (cong fst (sym (^ℚ-minus' _ _)))
-- --                  (^ℚ-Monotone (fromNat (suc n))
-- --                   (invEq (invℝ₊-≤-invℝ₊ _ _)
-- --                    (<ᵣWeaken≤ᵣ _ _ z<Z))))
-- --                bdlInv-lem))
-- --           (<ᵣWeaken≤ᵣ _ _
-- --            (slope-lower-bound z (fromNat (suc n)) 1<z
-- --             _ _ y₀<y₁
-- --             (ℚ.absTo≤×≤ (fromNat (suc n)) y₀ y₀∈)
-- --             (ℚ.absTo≤×≤ (fromNat (suc n)) y₁ y₁∈))
-- --      )))))

-- --  open BoundedInvLipsch slUpBdInv bdlInv public

 mid-𝒇 : ∀ q q' q'' → q ℚ.≤ q' → q' ℚ.≤ q'' →
    minᵣ (𝒇 (rat q))
         (𝒇 (rat q'')) ≤ᵣ 𝒇 (rat q')
 mid-𝒇 q q' q'' q≤q' q'≤q'' =
   subst2 _≤ᵣ_
     (cong₂ minᵣ (sym (𝒇-rat q)) (sym (𝒇-rat q'')))
     (sym (𝒇-rat q'))
     (monotone^ℚ q q' q'' q≤q' q'≤q'' _)

 opaque
  unfolding minᵣ maxᵣ
  0<𝒇 : ∀ x → 0 <ᵣ 𝒇 x
  0<𝒇 x = PT.rec (isProp<ᵣ _ _)
   (λ ((q , q') , q'-q<1 , q<x , x<q') →
     let q⊓q' = (minᵣ₊ (z ^ℚ q) (z ^ℚ q'))
     in PT.rec (isProp<ᵣ _ _)
        (λ (ε , 0<ε , ε<q⊓q') →
          PT.rec (isProp<ᵣ _ _)
          (λ (δ , X) →
           PT.rec (isProp<ᵣ _ _)
             (λ (r , r-x≤δ , x≤r) →
                let r' = ℚ.clamp q q' r
                    r'-x≤δ = isTrans≤ᵣ _ _ _
                              (≤ᵣ-+o _ _ (-ᵣ x)
                                (≤ℚ→≤ᵣ _ _
                             (ℚ.clamped≤ q q' r
                               (ℚ.<Weaken≤ _ _
                                 (<ᵣ→<ℚ _ _ (isTrans<≤ᵣ _ _ _ q<x x≤r))))) ) r-x≤δ
                    x≤r' = ≤min-lem _ (rat (ℚ.max q r)) (rat q')
                             (isTrans≤ᵣ _ _ _ x≤r
                              (≤ℚ→≤ᵣ _ _ (ℚ.≤max' q r)))
                             (<ᵣWeaken≤ᵣ _ _ x<q')
                    |fx-fr|<ε = fst (∼≃abs<ε _ _ _)
                        (sym∼ _ _ _ (X (rat r') (sym∼ _ _ _
                          ((invEq (∼≃abs<ε _ _ _)
                         (isTrans≡<ᵣ _ _ _
                           (absᵣNonNeg _ (x≤y→0≤y-x _ _ x≤r'))
                            (isTrans≤<ᵣ _ _ _
                                r'-x≤δ (<ℚ→<ᵣ _ _ (x/2<x δ))))))) ))
                    zzz =
                         mid-𝒇 q r' q'
                          (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _
                           (<ᵣWeaken≤ᵣ _ _ q<x) x≤r'))
                          (ℚ.clamp≤ q q' r)
                    zzz' = isTrans<≤ᵣ _ _ _
                             (isTrans<≡ᵣ _ _ _ ε<q⊓q'
                               (cong₂ minᵣ
                                 (sym (𝒇-rat _)) (sym (𝒇-rat _))))
                              zzz
                in isTrans≡<ᵣ _ _ _ (sym (CRℝ.+InvR _)) (a-b<c⇒a-c<b _ _ _
                      (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                     (isTrans<ᵣ _ _ _ |fx-fr|<ε zzz')))
               ) (∃rationalApprox≤ x (/2₊ δ)))

          (𝒇-cont x (ε , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<ε)))
          )
       (denseℚinℝ 0 _ (snd q⊓q')) )
    (∃rationalApprox x 1)

 𝒇₊ : ℝ → ℝ₊
 𝒇₊ x = 𝒇 x , 0<𝒇 x

 opaque
  unfolding minᵣ maxᵣ
  flₙ≡𝒇 : ∀ x n → (x ∈ intervalℙ (fromNeg (suc n)) (fromNat (suc n)))
            →  fst (fst (flₙ n)) x ≡ 𝒇 x
  flₙ≡𝒇 x n x∈ = ≡Continuous (fst (fst (flₙ n)))
            (𝒇 ∘ clampᵣ (fromNeg (suc n)) (fromNat (suc n)))
      (snd (flₙ n)) (IsContinuous∘ _ _ 𝒇-cont
           (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n))))
        (λ r → sym (𝒇-rat _))
        x
    ∙ cong 𝒇 (sym (∈ℚintervalℙ→clampᵣ≡ _ _ x x∈))


  𝒇-monotone : 1 ≤ᵣ fst z → ∀ x y → x ≤ᵣ y → 𝒇 x ≤ᵣ 𝒇 y
  𝒇-monotone 1≤z x y x≤y =
   ≡→≤ᵣ ((≡Cont₂ (cont₂∘ (contNE₂ maxR) 𝒇-cont 𝒇-cont)
     (cont∘₂ 𝒇-cont (contNE₂ maxR) )
     (ℚ.elimBy≤
        (λ u u' X → maxᵣComm _ _ ∙∙ X ∙∙ cong 𝒇 (maxᵣComm (rat u) (rat u')))
        λ u u' u≤u' →
          cong₂ maxᵣ (𝒇-rat _) (𝒇-rat _)
           ∙∙ ≤ᵣ→≡ (^ℚ-MonotoneR u u' u≤u' 1≤z) ∙
            cong (fst ∘ (z ^ℚ_)) (sym (ℚ.≤→max u u' u≤u')) ∙∙
           sym (𝒇-rat _))
         x y)
    ∙ cong 𝒇 (≤ᵣ→≡ x≤y))


 opaque
  unfolding _<ᵣ_
  𝒇-monotone-str : 1 <ᵣ fst z → ∀ x y → x <ᵣ y → 𝒇 x <ᵣ 𝒇 y
  𝒇-monotone-str 1<z x y = PT.rec (isProp<ᵣ _ _)
     λ ((q , q') , (≤q , q<q' , q'≤)) →
       isTrans≤<ᵣ _ _ _ (𝒇-monotone (<ᵣWeaken≤ᵣ _ _ 1<z) x (rat q) ≤q)
         (isTrans<≤ᵣ _ _ _ (
            subst2 _<ᵣ_ (sym (𝒇-rat _)) (sym (𝒇-rat _))
             (^ℚ-StrictMonotoneR 1<z q q' q<q'))
           (𝒇-monotone (<ᵣWeaken≤ᵣ _ _ 1<z) (rat q') y q'≤))

 module _ (n : ℕ) where


  incr^ : 1 <ᵣ fst z → isIncrasingℙᵣ
            (intervalℙ (rat (ℚ.- fromNat (suc n))) (rat (fromNat (suc n))))
            (λ x _ → fst (fst (flₙ n)) x)
  incr^ 1<z x x∈ y y∈ x<y =
    subst2 _<ᵣ_
      (sym (flₙ≡𝒇 x n x∈))
      (sym (flₙ≡𝒇 y n y∈))
      (𝒇-monotone-str 1<z  x y x<y)


  nondecr^ : 1 ≤ᵣ fst z → isNondecrasingℙᵣ
      (intervalℙ (rat (ℚ.- [ pos (suc n) / 1+ 0 ]))
       (rat [ pos (suc n) / 1+ 0 ]))
      (λ x _ → fst (fst (flₙ n)) x)
  nondecr^ 1≤z x x∈ y y∈ x≤y =
    subst2 _≤ᵣ_
      (sym (flₙ≡𝒇 x n x∈))
      (sym (flₙ≡𝒇 y n y∈))
      (𝒇-monotone 1≤z x y x≤y)



 open expPreDer Z public
 open expPreDer' z z≤Z 1/Z≤z public

 opaque
  unfolding _+ᵣ_
  expDerAt0 : derivativeOf 𝒇 at 0 is preLn
  expDerAt0 ε =
   PT.rec
     squash₁
     (λ (ε' , 0<ε' , <ε) →
       let ε'₊ = (ε' , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<ε'))
           N = fst (seqΔ-δ Z ε'₊)
           X =  seqΔ ε'₊
       in  ∣ ℚ₊→ℝ₊ ([ 1 / 2+ (suc N) ] , _) ,
              (λ r 0＃r ∣r∣<1/N →
                let d≤lnSeq : differenceAt 𝒇 0 r 0＃r ≤ᵣ lnSeq z (suc N)
                    d≤lnSeq = ≤ContWP＃≤ [ 1 / 2+ suc N ] (ℚ.0<pos 0 (2+ (suc N)))
                              (IsContinuousWithPred-differenceAt 0 _ 𝒇-cont)
                              ((AsContinuousWithPred _ _
                               (IsContinuousConst (lnSeq z (suc N)))))
                              (λ u u∈ u≤ →
                                subst2 _≤ᵣ_
                                 ((cong₂ _·ᵣ_ (cong₂ _-ᵣ_
                              (cong (fst ∘ (z ^ℚ_)) (sym (ℚ.+IdL _)) ∙ sym (𝒇-rat _))
                              (sym (𝒇-rat _)))
                                 ((cong₂ invℝ (𝐑'.+IdR' _ _ (-ᵣ-rat 0)) (toPathP (isProp＃ _ _ _ _))))))
                                 (cong₂ _·ᵣ_
                                   refl ((invℝ₊-rat _ ∙ cong rat
                               (cong (fst ∘ invℚ₊) (ℚ₊≡ {y = [ 1 / 2+ (suc N) ] , _ }
                                  (ℚ.+IdR _))))))
                                 ( (slope-monotone＃ ((z)) 0 u
                                   0 [ 1 / 2+ (suc N) ]
                                   u∈ (ℚ.0<pos 0 _) (ℚ.isRefl≤ 0) u≤))

                                   )
                              r 0＃r
                              (isTrans≤ᵣ _ _ _ (≤absᵣ r)
                                 (isTrans≡≤ᵣ _ _ _ (cong absᵣ (sym (𝐑'.+IdR' _ _ (-ᵣ-rat 0)))
                                  ∙ minusComm-absᵣ _ _) (<ᵣWeaken≤ᵣ (absᵣ (0 -ᵣ r)) _ ∣r∣<1/N)))


                    lnSeq'≤d : lnSeq' z (suc N) ≤ᵣ differenceAt 𝒇 0 r 0＃r
                    lnSeq'≤d = ≤ContWP＃≤' (ℚ.- [ 1 / 2+ suc N ])
                                   ((ℚ.minus-< 0 [ 1 / 2+ suc N ] (ℚ.0<pos 0 (2+ (suc N)))))
                               ((AsContinuousWithPred _ _
                               (IsContinuousConst (lnSeq' z (suc N)))))
                               (IsContinuousWithPred-differenceAt 0 _ 𝒇-cont)
                                (λ u u∈ u≤ → subst2 _≤ᵣ_
                                   ((cong₂ _·ᵣ_ refl ((invℝ₊-rat _ ∙ cong rat
                                     (cong (fst ∘ invℚ₊)
                                       (ℚ₊≡ {x = (0 ℚ.- (ℚ.- [ 1 / 2+ suc N ])) , _}
                                            {y = [ 1 / 2+ (suc N) ] , _ }
                                         (ℚ.+IdL _ ∙ ℚ.-Invol _)))))))
                                   (sym (-ᵣ·-ᵣ _ _) ∙ cong₂ _·ᵣ_
                                     (-[x-y]≡y-x _ _ ∙
                                       cong₂ _-ᵣ_ (sym (𝒇-rat _) ∙ cong 𝒇 (sym (+IdL _)))
                                         (sym (𝒇-rat _)))
                                     (-invℝ _ _ ∙ cong₂ invℝ (cong -ᵣ_ (+IdL _) ∙ -ᵣInvol _)
                                       (toPathP (isProp＃ _ _ _ _))))

                                   (slope-monotone＃' z
                                     (ℚ.- [ 1 / 2+ (suc N) ]) 0 u 0
                                     ((ℚ.minus-< 0 [ 1 / 2+ suc N ] (ℚ.0<pos 0 (2+ (suc N)))))
                                     (isSym＃ _ _ u∈) u≤ (ℚ.isRefl≤ 0))
                                     )
                                r 0＃r
                              (isTrans≤ᵣ _ _ _
                                (isTrans≡≤ᵣ _ _ _
                                 (sym (-ᵣ-rat _))
                                 (-ᵣ≤ᵣ _ _ (<ᵣWeaken≤ᵣ (absᵣ (0 -ᵣ r)) _ ∣r∣<1/N)))
                                (≤ᵣ-ᵣ _ _ (isTrans≤≡ᵣ _ _ _ (≤absᵣ (-ᵣ r))
                                  (cong absᵣ (sym (+IdL _)) ∙ sym (-ᵣInvol _)))))


                in isTrans≤<ᵣ _ _ _
                     (intervalℙ→dist< _ _ _ _
                        ((lnSeq'≤preLn _) , (preLn≤lnSeq _))
                        (lnSeq'≤d , d≤lnSeq))
                     (isTrans<ᵣ _ _ _ (X (suc N) ℕ.≤-refl) <ε)

                 ) ∣₁ )
     (denseℚinℝ 0 _ (snd ε))

  𝒇· : ∀ x y → 𝒇 x ·ᵣ 𝒇 y ≡ 𝒇 (x +ᵣ y)
  𝒇· = ≡Cont₂
       (cont₂∘ IsContinuous₂·ᵣ 𝒇-cont 𝒇-cont )
       (cont∘₂ 𝒇-cont (contNE₂ sumR))
       λ u u' → cong₂ _·ᵣ_ (𝒇-rat _) (𝒇-rat _)
          ∙ cong fst (^ℚ-+ _ _ _) ∙ sym (𝒇-rat _)


 differenceAt𝒇-Δ : ∀ x r 0＃r → 𝒇 x ·ᵣ differenceAt 𝒇 0 r 0＃r ≡ (differenceAt 𝒇 x r 0＃r)
 differenceAt𝒇-Δ x r 0＃r = ·ᵣAssoc _ _ _ ∙
   cong (_／ᵣ[ r , 0＃r ]) (𝐑'.·DistR- _ _ _ ∙
     cong₂ _-ᵣ_
       (𝒇· _ (0 +ᵣ r) ∙ cong 𝒇 (cong (x +ᵣ_) (+IdL r)))
       (𝒇· _ _ ∙ cong 𝒇 (+IdR x)))


 expDerA : ∀ x → derivativeOf 𝒇 at x is (𝒇 x ·ᵣ preLn)
 expDerA x =
  subst (at (rat [ pos zero / 1+ zero ]) limitOf_is (𝒇 x ·ᵣ preLn))
   (funExt₂ λ r 0＃r → differenceAt𝒇-Δ _ _ _ )
   (·-lim _ _ _ _ _ (const-lim (𝒇 x) 0) expDerAt0)


seq-^-intervals : Seq⊆
seq-^-intervals .Seq⊆.𝕡 Z = intervalℙ (rat [ 1 / (fromNat (suc (suc Z))) ]) (fromNat (suc (suc Z)))

seq-^-intervals .Seq⊆.𝕡⊆ Z x (≤x , x≤) =
  isTrans≤ᵣ _ _ _  (≤ℚ→≤ᵣ _ _ ((invEq (ℚ.invℚ₊-≤-invℚ₊
     ([ 1 / (2+ (suc Z)) ] , _) _) w))) ≤x
  , isTrans≤ᵣ _ _ _ x≤ (≤ℚ→≤ᵣ _ _ w)

 where
  w = (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-suc (ℕ.≤-refl {suc (suc Z)}))))

seq-^-intervals∈Pos : seq-^-intervals Seq⊆.s⊇ pred0<
seq-^-intervals∈Pos x 0<x =
  PT.map2 (λ (1+ n , N) (1+ n' , N') →
        ℕ.max n n'
            ,
              fst (invℝ₊-≤-invℝ₊ (x , 0<x) (_ , <ℚ→<ᵣ _ _ (ℚ.0<pos _ _)))
              (isTrans≤ᵣ _ _ _
               (isTrans≤ᵣ _ _ _                 (≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ N'))
               (isTrans≤≡ᵣ _ _ _
                 (((≤ℚ→≤ᵣ (fromNat (suc n')) (fromNat (suc (suc (ℕ.max n n'))))
                      ((ℚ.≤ℤ→≤ℚ _ _
                       (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.suc-≤-suc (ℕ.≤-suc (ℕ.right-≤-max {n'} {n})))))))))
                        (sym (invℝ₊-rat _))))

              ,
                isTrans≤ᵣ _ _ _
             (isTrans≤ᵣ _ _ _
                 (≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ N))

                 (((≤ℚ→≤ᵣ (fromNat (suc n)) _
                      (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-suc $ ℕ.suc-≤-suc (ℕ.left-≤-max {n} {n'})))))))

               )
    (getClamps x) (getClamps (fst (invℝ₊ (x , 0<x))))



-- -- -- -- -- -- -- FnWith


Seq-^ : Seq⊆→ ((ℝ → ℝ₊) × ℝ) seq-^-intervals
Seq-^ .Seq⊆→.fun x Z (≤x , x≤) = F.𝒇₊ , F.preLn
 where
 module F = BDL (x , isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)) ≤x) Z x≤ ≤x
Seq-^ .Seq⊆→.fun⊆ x n m (≤x , x≤) (≤x' , x≤') n<m = cong₂ _,_
  (funExt (ℝ₊≡ ∘ (≡Continuous _ _ F.𝒇-cont F'.𝒇-cont
       λ r → F.𝒇-rat r ∙∙ cong (fst ∘ (_^ℚ r)) (ℝ₊≡ refl) ∙∙ sym (F'.𝒇-rat r))))
        λ i → fromCauchySequence'-≡-lem (lnSeq (x , xp i))
              (icP i) (icP' i) i

 where
 module F = BDL _ n x≤ ≤x
 module F' = BDL _ m x≤' ≤x'

 0<x = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)) ≤x
 0<x' = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)) ≤x'
 xp : 0<x ≡ 0<x'
 xp = isProp<ᵣ 0 x 0<x 0<x'

 icP : PathP (λ i → IsCauchySequence' (lnSeq (x , xp i))) F.ca-lnSeq _
 icP = toPathP refl

 icP' : PathP (λ i → IsCauchySequence' (lnSeq (x , xp i))) _ F'.ca-lnSeq
 icP' = symP (toPathP refl)








open ℚ.HLP

module Seq-^-FI = Seq⊆→.FromIntersection Seq-^
   (isSet× (isSet→ isSetℝ₊) isSetℝ) pred0< seq-^-intervals∈Pos

module Pos^ where
 open Seq-^-FI


 ^-c : ∀ x → 0 <ᵣ x  → ℝ → ℝ₊
 ^-c x 0<x = fst (∩$ x 0<x)

 _^ᵣ_ : ℝ₊ → ℝ → ℝ₊
 (x , 0<x) ^ᵣ y = fst (∩$ x 0<x) y


 ^ᵣ-mon-str : ∀ x
   → 1 <ᵣ fst x
   → ∀ y y'
   → y <ᵣ y'
   → fst (x ^ᵣ y) <ᵣ fst (x ^ᵣ y')
 ^ᵣ-mon-str x 1<x y y'  y<y' =
  ∩$-elimProp (fst x) (snd x)
    {λ (f , _) → fst (f y) <ᵣ fst (f y')}
    (λ _ → isProp<ᵣ _ _)
    (λ n x∈ₙ → BDL.𝒇-monotone-str (fst x , _) n (snd x∈ₙ) (fst x∈ₙ)
         1<x y y' y<y')

 ln-c : ∀ x → 0 <ᵣ x → ℝ
 ln-c x 0<x = snd (∩$ x 0<x)

 ln : ℝ₊ → ℝ
 ln (x , 0<x) = snd (∩$ x 0<x)

 ln-1≡0 : ln 1 ≡ 0
 ln-1≡0 =
   let 1r : ℝ₊
       1r = fromNat 1
   in ∩$-elimProp (fst 1r) (snd 1r)
             {λ (_ , lnx) → lnx ≡ 0}
             (λ _ → isSetℝ _ _)
             λ Z x∈ →
                 congS (λ 0<1 → BDL.preLn (rat [ pos (suc zero) / 1+ zero ] , 0<1)
                        Z (snd x∈) (fst x∈))
                         (isProp<ᵣ _ _ _ _)
                ∙ sym (expPreDer.0=preLn Z (snd x∈) (fst x∈))

 ln-cont : IsContinuousWithPred pred0< (curry ln)
 ln-cont x ε 0<x = w
  where
  ww : (Z : ℕ) (x∈ : x ∈ Seq⊆.𝕡 seq-^-intervals Z) →
        ∃-syntax ℚ₊
        (λ δ →
           (v : ℝ) (v∈P : 0 <ᵣ v) →
           x ∼[ δ ] v → Seq⊆→.fun Seq-^ x Z x∈ .snd ∼[ ε ] curry ln v v∈P)
  ww Z x∈ =
    let (N , X) = seqΔ-δ (suc Z) (/4₊ ε)
        uuu = seq-^-intervals .Seq⊆.𝕡⊆ Z x x∈
        δZ : ℚ₊
        δZ = ℚ.<→ℚ₊ [ 1 / fromNat (suc (suc (suc Z))) ] [ 1 / fromNat (suc (suc Z)) ]
              (fst (ℚ.invℚ₊-<-invℚ₊ (fromNat (suc (suc Z))) (fromNat (suc (suc (suc Z)))))
                (ℚ.<ℤ→<ℚ _ _ ((invEq (ℤ.pos-<-pos≃ℕ< _ _) ℕ.≤-refl ))))
    in PT.map
        (λ (δ , D) →
          (ℚ.min₊ δ δZ) ,
            (λ v 0<v x∼v →
               let ca' = expPreDer.expPreDer'.preLn∼ (suc Z)
                   uvu = isTrans≡≤ᵣ (rat [ pos 1 / 2+ suc Z ]) _ _
                           (sym (L𝐑.lem--079 {rat [ pos 1 / 2+ Z ]}) ∙
                             cong₂ _-ᵣ_ refl (-ᵣ-rat₂ _ _)
                            ) (≤ᵣMonotone+ᵣ _ _ _ _
                          (fst x∈) (-ᵣ≤ᵣ _ _ (isTrans≤ᵣ _ _ _ (isTrans≤ᵣ _ _ _
                            (≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ (fst (∼≃abs<ε _ _ _)
                                   x∼v))) (≤ℚ→≤ᵣ _ _ (ℚ.min≤' _ _)))))
                   uuuV : v ∈ seq-^-intervals .Seq⊆.𝕡 (suc Z)
                   uuuV = isTrans≤≡ᵣ _ _ _ uvu L𝐑.lem--079
                        , (isTrans≤≡ᵣ _ _ _
                            (isTrans≤ᵣ _ _ _
                             (a-b≤c⇒a≤c+b _ _ _
                               (isTrans≤ᵣ _ _ _ (≤absᵣ _)
                                (isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ (fst (∼≃abs<ε _ _ _)
                                   (sym∼ _ _ _ x∼v)))
                                    (≤ℚ→≤ᵣ _ _
                                      (ℚ.isTrans≤ _ _ _ (ℚ.min≤' _ _)
                                       (ℚ.≤-ℚ₊ [ 1 / fromNat (suc (suc Z)) ]
                                        1 ([ 1 / fromNat (suc (suc (suc Z))) ] , _)
                                         (fst (ℚ.invℚ₊-≤-invℚ₊ 1 (fromNat (suc (suc Z))))
                                           (ℚ.≤ℤ→≤ℚ _ _
                                              (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _)
                                                (ℕ.suc-≤-suc ℕ.zero-≤))))))))))
                             (≤ᵣ-o+ _ _ 1 (snd x∈)))
                            (+ᵣ-rat _ _ ∙  cong rat (ℚ.ℕ+→ℚ+ _ _)))
                   ≡ε = distℚ! (fst ε) ·[ ((ge[ ℚ.[ 1 / 4 ] ]
                               +ge ge[ ℚ.[ 1 / 2 ] ])
                            +ge  ge[ ℚ.[ 1 / 4 ] ]
                            ) ≡ ge1 ]
                   qqq : BDL.preLn (x , _) (suc Z) (snd (Seq⊆.𝕡⊆ seq-^-intervals Z x x∈))
                          (fst (Seq⊆.𝕡⊆ seq-^-intervals Z x x∈))
                          ∼[ ((/4₊ ε) ℚ₊+ /2₊ ε) ℚ₊+ (/4₊ ε) ]
                          BDL.preLn (v , _) (suc Z) _ _
                   qqq = (triangle∼ (triangle∼ (sym∼ _ _ _
                             (ca' (x , isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)) (fst uuu))
                              (snd uuu) (fst uuu) _ _ ℕ.≤-refl))
                         ((D v (isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)) (fst uuuV))
                            (∼-monotone≤ (ℚ.min≤ _ _) x∼v))))
                          ((ca' (v , _) (snd uuuV) (fst uuuV) _ _ ℕ.≤-refl)))
               in ((cong snd (2c x (suc Z) Z uuu _))
                    subst∼[ ℚ₊≡ ≡ε ]
                      (cong snd (sym (∩$-∈ₙ v _ (suc Z) uuuV)))
                      )
                      qqq))
        (lnSeqCont (suc N) x (/2₊ ε) _)

  w : _
  w = ∩$-elimProp x 0<x
    {λ (_ , lnx) → ∃-syntax ℚ₊
      (λ δ → (v : ℝ) (v∈P : 0 <ᵣ v) →
        x ∼[ δ ] v → lnx ∼[ ε ] curry ln v v∈P)}
    (λ _ → squash₁)
    ww



 ^-rat : ∀ x y → fst (x ^ᵣ (rat y)) ≡ fst (x ^ℚ y)
 ^-rat x =
   ∩$-elimProp (fst x) (snd x)
    {λ (f , _) → ∀ y → fst (f (rat y)) ≡ fst (x ^ℚ y)}
     (λ _ → isPropΠ λ _ → isSetℝ _ _)
     (λ n (≤x , x≤) q →
          BDL.𝒇-rat _ n x≤ ≤x q ∙ cong (λ x → fst (x ^ℚ q)) (ℝ₊≡ refl))


 ln-inv : ∀ x → ln (invℝ₊ x) ≡ -ᵣ (ln x)
 ln-inv (x , 0<x) =
   let (1/x , 0<1/x) = invℝ₊ (x , 0<x)
   in ∩$-elimProp2 1/x 0<1/x x 0<x
        {λ (_ , ln1/x) (_ , lnx) → ln1/x ≡ -ᵣ lnx}
        (λ _ _ → isSetℝ _ _)
        λ Z x∈ y∈ →
          congS (λ zz → BDL.preLn (1/x , zz) Z (snd x∈) (fst x∈))
            (isProp<ᵣ 0 _ _ _)  ∙ expPreDer.preLn-inv Z _
            (snd y∈) (fst y∈) (snd x∈) (fst x∈)
           ∙ congS (λ zz → -ᵣ (BDL.preLn (x , zz) Z (snd y∈) (fst y∈)))
            (isProp<ᵣ 0 _ _ _)

 cont-^ : ∀ (x : ℝ₊) → IsContinuous (fst ∘ x ^ᵣ_)
 cont-^ (x , 0<x) =
    ∩$-elimProp x 0<x  {λ (f , _) → IsContinuous (fst ∘ f)}
      (λ _ → isPropIsContinuous _)
      λ Z (≤x , x≤) → BDL.𝒇-cont _ Z x≤ ≤x



 -- slope-monotone-^ᵣ :   (a b a' b' : ℝ₊)
 --  → (a<b : fst a <ᵣ fst b) → (a'<b' : fst a' <ᵣ fst b')
 --  → (a≤a' : fst a ≤ᵣ fst a') →  (b≤b' : fst b ≤ᵣ fst b') →
 --  ∀ y → 1 ≤ᵣ y →
 --  (((fst (b ^ᵣ y)) -ᵣ (fst (a ^ᵣ y)))
 --    ／ᵣ₊ (_ , x<y→0<y-x _ _ a<b ))
 --      ≤ᵣ
 --  (((fst (b' ^ᵣ y)) -ᵣ (fst (a' ^ᵣ y)))
 --    ／ᵣ₊ (_ , x<y→0<y-x _ _ a'<b' ))
 -- slope-monotone-^ᵣ a b a' b' a<b a'<b' a≤a' b≤b' =
 --   (≤ContPos' {1}
 --    (IsContinuous∘ _ _ (IsContinuous·ᵣR _)
 --      (cont₂+ᵣ _ _
 --        (cont-^ _)
 --        (IsContinuous∘ _ _
 --          IsContinuous-ᵣ
 --           (cont-^ _))))
 --    (IsContinuous∘ _ _ (IsContinuous·ᵣR _)
 --      (cont₂+ᵣ _ _
 --        (cont-^ _)
 --        (IsContinuous∘ _ _
 --          IsContinuous-ᵣ
 --           (cont-^ _))))
 --    λ q 1≤q →
 --      subst2 _≤ᵣ_
 --        (cong₂ (λ u v → ((u -ᵣ v) ／ᵣ₊
 --         (fst b +ᵣ -ᵣ fst a , x<y→0<y-x (fst a) (fst b) a<b)))
 --        (sym (^-rat _ _)) (sym (^-rat _ _)))
 --        ((cong₂ (λ u v → ((u -ᵣ v) ／ᵣ₊
 --         (fst b' +ᵣ -ᵣ fst a' , x<y→0<y-x (fst a') (fst b') a'<b')))
 --        (sym (^-rat _ _)) (sym (^-rat _ _))))
 --        (slope-monotone-^ℚ a b a' b' a<b a'<b' a≤a' b≤b' q 1≤q))

 -- ^-cont : ∀ (y : ℝ) → IsContinuousWithPred pred0< (curry (fst ∘ (_^ᵣ y)))
 -- ^-cont  y = {! !}

 -- factor-xᵃ-xᵇ'ᵣ : ∀ x a b → fst (x ^ᵣ a) -ᵣ fst (x ^ᵣ b) ≡
 --                         fst (x ^ᵣ a) ·ᵣ (1 -ᵣ fst (x ^ᵣ (b -ᵣ a)))
 -- factor-xᵃ-xᵇ'ᵣ x a b = {!!}

 -- ^-monotone-lemmaℚ : ∀ (x : ℚ₊) y (δ : ℚ₊) → fst ((ℚ₊→ℝ₊ x) ^ℚ y) ∈
 --                        intervalℙ (minᵣ (fst ((ℚ₊→ℝ₊ x) ^ℚ (y ℚ.+ (fst δ))))
 --                                      (fst ((ℚ₊→ℝ₊ x) ^ℚ (y ℚ.+ (fst δ)))))
 --                                  (maxᵣ (fst ((ℚ₊→ℝ₊ x) ^ℚ (y ℚ.+ (fst δ))))
 --                                      (fst ((ℚ₊→ℝ₊ x) ^ℚ (y ℚ.+ (fst δ)))))
 -- ^-monotone-lemmaℚ = {!!}

 -- ^-monotone-lemma : ∀ x y δ → fst (x ^ᵣ y) ∈
 --                        intervalℙ (minᵣ (fst (x ^ᵣ (y -ᵣ δ)))
 --                                      (fst (x ^ᵣ (y +ᵣ δ))))
 --                                  (maxᵣ (fst (x ^ᵣ (y -ᵣ δ)))
 --                                      (fst (x ^ᵣ (y +ᵣ δ))))
 -- ^-monotone-lemma = {!!}
 -- -- ^-strictMonotone : ∀ x x' y → 0 <ᵣ y → fst x <ᵣ fst x'
 -- --   → fst (x ^ᵣ y) <ᵣ fst (x' ^ᵣ y)
 -- -- ^-strictMonotone = {!!}

--  ^-cont : ∀ (y : ℝ) → IsContinuousWithPred pred0< (curry (fst ∘ (_^ᵣ y)))
--  ^-cont y u ε 0<u =
--    PT.rec
--      squash₁
--       (λ (δy , Xy) →
--         PT.rec2 squash₁
--           (λ (δy- , (<δy- , δy-< )) (δy+ , <δy+ , δy+< )
--              → PT.map2
--               (λ (δx- , Xx-) (δx+ , Xx+ ) →
--                 let δ₊ = ℚ.min₊ (ℚ.min₊ δx- δx+) δy
--                     Xy- = subst ((fst ((u , 0<u) ^ᵣ y))  ∼[ /4₊ ε ]_)
--                             (^-rat _ _)
--                              (Xy (rat δy-)
--                              {!!})
--                     Xy+ = subst ((fst ((u , 0<u) ^ᵣ y))  ∼[ /4₊ ε ]_)
--                             (^-rat _ _)
--                              (Xy (rat δy+) {!!})
--                 in δ₊ ,
--                   λ v 0<v u∼v →
--                    let Y : fst ((u , 0<u) ^ᵣ y) ∼[ _ ]
--                             fst ((v , 0<v) ^ᵣ rat δy-)
--                        Y = triangle∼ Xy-
--                           (subst ((fst ((u , 0<u) ^ℚ δy-))  ∼[ /4₊ ε ]_)
--                             (sym (^-rat _ _))
--                              ((Xx- v 0<v {!!})) )
--                    in {!!}
--                  )
--               (IsContinuous^ℚ δy- u (/4₊ ε) 0<u)
--               (IsContinuous^ℚ δy+ u (/4₊ ε) 0<u)
--              )
--           (denseℚinℝ (y -ᵣ rat (fst δy)) y {!!})
--           (denseℚinℝ y (y +ᵣ rat (fst δy)) {!!}))
--       (cont-^ (u , 0<u) y (/4₊ ε))
-- --     PT.map
-- --       {!!}
-- --       (denseℚinℝ 0 (fst δᵣ) (snd δᵣ))


   -- Seq⊆.elimProp-∩ Seq⊆-abs<N
   --    ⊤Pred y tt Seq⊆-abs<N-s⊇-⊤Pred
   --    (λ (y : ℝ) → IsContinuousWithPred pred0< (curry (fst ∘ (_^ᵣ y))))
   --    (λ _ → isPropΠ3 λ _ _ _ → squash₁)
   --    λ n y∈ u ε u∈P → PT.map2
   --     (λ (δ , X) (δ' , X') →
   --       ℚ.min₊ δ δ' ,
   --        λ v 0<v u∼v →
   --          let B  = fst (∼≃abs<ε _ _ _)
   --                     $ X  v 0<v (∼-monotone≤ (ℚ.min≤ _ _ ) u∼v)
   --              B' = fst (∼≃abs<ε _ _ _)
   --                     $ X' v 0<v (∼-monotone≤ (ℚ.min≤' _ _) u∼v)
   --          in invEq (∼≃abs<ε _ _ _)
   --               (isTrans≤<ᵣ _ _ _
   --                 (^B-δ-lemma n y (u , _) (v , 0<v)
   --                  (ointervalℙ⊆intervalℙ _ _ _ y∈))
   --                 (max<-lem _ _ _
   --                   B
   --                   B')))
   --     (IsContinuous^ℚ (fromNat (suc n)) u ε u∈P)
   --     (IsContinuous^ℚ (fromNeg (suc n)) u ε u∈P)



 ^-der : ∀ x → ∀ y → derivativeOf (fst ∘ x ^ᵣ_) at y
               is (fst (x ^ᵣ y) ·ᵣ ln x)
 ^-der (x , 0<x) = ∩$-elimProp x 0<x
       {λ (g , d) → (y : ℝ) →
         derivativeOf (fst ∘ g) at y is (fst (g y) ·ᵣ d)}
      (λ _ → isPropΠ2 λ _ _ → squash₁)
       (λ n (a , b) → BDL.expDerA (x , _) n b a)

 ^ᵣ0 : ∀ x → fst (x ^ᵣ 0) ≡ 1
 ^ᵣ0 x = ^-rat x 0

 ^ᵣ1 : ∀ x → fst (x ^ᵣ 1) ≡ fst x
 ^ᵣ1 x = ^-rat x 1 ∙ ^ⁿ-1 _

 ^ᵣ[1/n] : ∀ x n₊ → fst (x ^ᵣ rat [ 1 / n₊ ]) ≡ fst (root n₊ x)
 ^ᵣ[1/n] x n₊ =  ^-rat x [ 1 / n₊ ] ∙ ^ⁿ-1 _

 1<a→0<ln[a] : ∀ a → (1 <ᵣ fst a) → 0 <ᵣ ln a
 1<a→0<ln[a] (a , 0<a) 1<a =
    ∩$-elimProp a 0<a
             {λ (_ , lna) → 0 <ᵣ lna}
               (λ _ → isProp<ᵣ _ _)
               λ _ _ → BDL.0<preLn _ _ _ _ 1<a

 ^ᵣ+ : ∀ x y y' → x ^ᵣ (y +ᵣ y') ≡ (x ^ᵣ y) ₊·ᵣ (x ^ᵣ y')
 ^ᵣ+ (x , 0<x) y y' =
   ∩$-elimProp x 0<x
    {λ (f , _) → f (y +ᵣ y') ≡ f y ₊·ᵣ f y'}
    (λ _ → isSetℝ₊ _ _ )
    λ n x∈ → ℝ₊≡ (sym (BDL.𝒇· _ _ _  _ y y'))

open Pos^ public


rootₙ→1 : ∀ x (α : ℝ) → 1 <ᵣ α →
         ∃[ N ∈ ℕ ]
           (∀ n → N ℕ.< n → fst (root (1+ n) x) <ᵣ α)
rootₙ→1 x α 1<α =
  PT.rec squash₁ w
    (IsContinuousLim _ 0 (cont-^ x) (α -ᵣ 1 , x<y→0<y-x _ _ 1<α))
 where
 w : Σ ℝ₊
      (λ δ →
         (r : ℝ) (x＃r : 0 ＃ r) →
         absᵣ (0 -ᵣ r) <ᵣ fst δ →
         absᵣ (fst (x ^ᵣ 0) -ᵣ fst (x ^ᵣ r))
         <ᵣ α -ᵣ 1) →
      ∃ ℕ (λ N → (n : ℕ) → N ℕ.< n → fst (root (1+ n) x) <ᵣ α)
 w ((δᵣ , 0<δᵣ) , X) =
    PT.map
      (λ (δ , 0<δ , δ<δᵣ) →
        let 1/δ = (invℚ₊ (δ , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<δ)))
            ((1+ k) , Y) = ℚ.boundℕ (fst 1/δ)
        in suc k , λ n <n →
            <-+o-cancel _ _ (-ᵣ 1)
              (isTrans≤<ᵣ _ _ _
                (≤absᵣ _) (isTrans≡<ᵣ _ _ _
               (cong absᵣ (cong₂ _-ᵣ_
                (sym (^ᵣ[1/n] x (1+ n)))
                (sym (^ᵣ0 x)))
                ∙ minusComm-absᵣ _ _) (X (rat [ 1 / 1+ n ])
            (inl (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)))
             (isTrans≡<ᵣ _ _ _ (
              cong absᵣ (+IdL _) ∙ sym (-absᵣ _)
                ∙ absᵣPos _ (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _))) (isTrans<ᵣ _ _ _
              (<ℚ→<ᵣ [ 1 / 1+ n ] δ
                (subst2 ℚ._<_
                  refl
                  (ℚ.invℚ₊-invol _)
                  (fst (ℚ.invℚ₊-<-invℚ₊ 1/δ (fromNat (suc n)) )
                   (ℚ.isTrans< _ _ _
                     (ℚ.isTrans≤< _ _ _ (ℚ.≤abs (fst 1/δ)) Y)
                     (ℚ.<ℤ→<ℚ _ _ (invEq (ℤ.pos-<-pos≃ℕ< _ _)
                      (ℕ.≤-suc <n) )))))) δ<δᵣ)))))
        )
      (denseℚinℝ 0 δᵣ 0<δᵣ)

-- clamp : ℚ → ℚ → ℚ → ℚ
-- clamp d u x = ℚ.min (ℚ.max d x) u


opaque
 unfolding maxᵣ
 ℚ-clamp-<-cases : ∀ L L' x y → L ℚ.< L' → x ℚ.< y →
                     (ℚ.clamp L L' x ≡ ℚ.clamp L L' y) ⊎
                        (ℚ.clamp L L' x ℚ.< ℚ.clamp L L' y)
 ℚ-clamp-<-cases L L' x y L<L' x<y =
   w (ℚ.Dichotomyℚ y L) (ℚ.Dichotomyℚ L' x)
  where
  w : (y ℚ.≤ L) ⊎ (L ℚ.< y) → (L' ℚ.≤ x) ⊎ (x ℚ.< L') → (ℚ.clamp L L' x ≡ ℚ.clamp L L' y) ⊎
                        (ℚ.clamp L L' x ℚ.< ℚ.clamp L L' y)
  w _ (inl L'≤x) = inl (ℚ.minComm _ _ ∙ ℚ.≤→min _ _ (ℚ.isTrans≤ _ _ _ L'≤x (ℚ.≤max' _ _))
       ∙ sym ((ℚ.minComm _ _ ∙ ℚ.≤→min _ _
        (ℚ.isTrans≤ _ _ _ (ℚ.isTrans≤ _ _ _ L'≤x (ℚ.<Weaken≤ _ _ x<y)) (ℚ.≤max' _ _)))))
  w (inl y≤L) _ = inl
    (cong (flip ℚ.min _) (ℚ.maxComm _ _ ∙
     (ℚ.≤→max _ _ (ℚ.isTrans≤ _ _ _  (ℚ.<Weaken≤ _ _ x<y) y≤L)))
      ∙ cong (flip ℚ.min _) (sym (ℚ.≤→max _ _ y≤L) ∙ ℚ.maxComm _ _))

  w (inr L<y) (inr x<L') = inr
   (ℚ.isTrans≤< _ _ _
     (ℚ.min≤ _ _)
       (ℚ.isTrans<≤ (ℚ.max L x) (ℚ.min y L') _
         (<ᵣ→<ℚ _ _ (<min-lem (rat y) (rat L') (maxᵣ (rat L) (rat x))
              (max<-lem _ _ _ (<ℚ→<ᵣ _ _ L<y) (<ℚ→<ᵣ _ _ x<y))
              (max<-lem _ _ _ ((<ℚ→<ᵣ _ _ L<L')) (<ℚ→<ᵣ _ _ x<L'))))
         (ℚ.≡Weaken≤ _ _ (cong (flip ℚ.min L') (sym (ℚ.≤→max L y (ℚ.<Weaken≤ _ _ L<y)))))))

 ℚ-clamp-<-casesᵣ : ∀ L L' x y → L ℚ.< L' →  x ℚ.< y →
                     (clampᵣ (rat L) (rat L') (rat x)
                       ≡ clampᵣ (rat L) (rat L') (rat y)) ⊎
                        (clampᵣ (rat L) (rat L') (rat x)
                         <ᵣ clampᵣ (rat L) (rat L') (rat y))
 ℚ-clamp-<-casesᵣ L L' x y L<L' x<y =
  (⊎.map (cong rat) (<ℚ→<ᵣ _ _)
     (ℚ-clamp-<-cases L L' x y L<L' x<y))

eventually-lnSeq[x]<lnSeq'[x+Δ] : ∀ (x Δ : ℝ₊) → 1 <ᵣ fst x →
  ∃[ k ∈ ℕ ] lnSeq x k <ᵣ lnSeq' (x ₊+ᵣ Δ) k
eventually-lnSeq[x]<lnSeq'[x+Δ] x Δ 1<x =
   PT.map w
     (rootₙ→1 x α 1<α)

 where


 0<1-1/[x+Δ] = (isTrans<≡ᵣ _ _ _
          (invEq (invℝ₊-<-invℝ₊ _ 1)
            (isTrans≡<ᵣ _ _ _
              (sym (+IdR _))
              (<ᵣMonotone+ᵣ _ _ _ _ 1<x (snd Δ)))) (cong fst invℝ₊1) )


 0<1-1/x = (isTrans<≡ᵣ _ _ _
          (invEq (invℝ₊-<-invℝ₊ _ 1)
            (isTrans≡<ᵣ _ _ _
              (sym (+IdR _) ∙ (+ᵣ-rat _ _))
              1<x)) (cong fst invℝ₊1) )


 α : ℝ
 α = (1 -ᵣ fst (invℝ₊ (x ₊+ᵣ Δ)))
      ／ᵣ₊ (_ , x<y→0<y-x _ _ 0<1-1/x)

 1<α : 1 <ᵣ α
 1<α = invEq (1<x/y≃y<x _ _)
   (<ᵣ-o+ _ _ 1
     (-ᵣ<ᵣ _ _ (invEq (invℝ₊-<-invℝ₊ _ _)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR _))
         (<ᵣ-o+ _ _ (fst x) (snd Δ))))))



 w : Σ ℕ
      (λ N → (n : ℕ) → N ℕ.< n → fst (root (1+ n) x) <ᵣ α) →
      Σ ℕ (λ k → lnSeq x k <ᵣ lnSeq' (x ₊+ᵣ Δ) k)
 w (K , X) =
   K , <ᵣ-·ᵣo _ _ (_ , <ℚ→<ᵣ _ _ (ℚ.0<pos _ _))
     (isTrans<≤ᵣ _ _ _
       (isTrans≡<ᵣ _ _ _
         (cong₂ _-ᵣ_
           (^ⁿ-1 _ ∙ sym (·IdL _))
           (cong fst (sym (ₙ√1 _) ∙∙
             cong (root _) (ℝ₊≡ (sym (x·invℝ₊[x] _) ∙ ·ᵣComm _ _))
              ∙∙ sym (·DistRoot _ _ _)))
           ∙ sym (𝐑'.·DistL- _ _ _))
         (<ᵣ-o·ᵣ _ _
           (_ , x<y→0<y-x (fst (root (1+ (suc K)) (invℝ₊ x))) 1
              (isTrans<≡ᵣ _ _ _
               (ₙ√-StrictMonotone {invℝ₊ x} {1}  (1+ suc K)
                 (invEq (1/x<1≃1<x x) 1<x))
               (cong fst (ₙ√1 _))))
           (X (suc K) (ℕ.≤-refl {suc K}))))
       from-concave)

  where

  from-concave :
    (1 -ᵣ fst (root (2+ K) (invℝ₊ x))) ·ᵣ α ≤ᵣ
     1 -ᵣ fst ((x ₊+ᵣ Δ) ^ℚ (ℚ.- [ 1 / 2+ K ]))
  from-concave = isTrans≡≤ᵣ (_ ·ᵣ α) _ _
        (cong₂ (_·ᵣ_) (cong₂ _-ᵣ_ (cong fst (sym (ₙ√1 _)))
         refl) (·ᵣComm _ _) ∙ ·ᵣAssoc _ _ _ ∙ ·ᵣComm _ _ )
        (isTrans≤≡ᵣ _ _ _ (fst (z≤x/y₊≃y₊·z≤x _ _ _) (slope-monotone-ₙ√ (suc K)
         (invℝ₊ (x ₊+ᵣ Δ)) 1
         (invℝ₊ x) 1
         0<1-1/[x+Δ]
         0<1-1/x
         (invEq (invℝ₊-≤-invℝ₊ _ _)
           (isTrans≡≤ᵣ _ _ _ (sym (+IdR _))
            (≤ᵣ-o+ _ _ (fst x) (<ᵣWeaken≤ᵣ _ _ (snd Δ)))))
            (≤ᵣ-refl 1)))
            (cong₂ _-ᵣ_ (cong fst (ₙ√1 _))
            (sym (^ⁿ-1 _) ∙
             cong fst (sym (^ℚ-minus' _ _)))))




monotoneStrictPreLn : ∀ Z → (z z' : ℝ₊) → 1 <ᵣ fst z →
         (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
         (1/Z≤z :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z)
         (z'≤Z : fst z' ≤ᵣ fromNat (suc (suc Z)))
         (1/Z≤z' :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z')
         → fst z <ᵣ fst z'
         → expPreDer.expPreDer'.preLn Z z z≤Z 1/Z≤z  <ᵣ
           expPreDer.expPreDer'.preLn Z z' z'≤Z 1/Z≤z'
monotoneStrictPreLn Z z z' 1<z z≤Z 1/Z≤z z'≤Z 1/Z≤z' z<z' =
  PT.rec (isProp<ᵣ _ _)
    (λ (K , X) →
       isTrans<≤ᵣ _ _ _
         (isTrans≤<ᵣ _ _ _
           (BDL.preLn≤lnSeq z Z z≤Z 1/Z≤z K) X)

         ((isTrans≡≤ᵣ _ _ _
          (cong (λ zz → lnSeq' zz K) (ℝ₊≡ L𝐑.lem--05) )
          (BDL.lnSeq'≤preLn z' Z z'≤Z 1/Z≤z' K)))
          )
    (eventually-lnSeq[x]<lnSeq'[x+Δ]
      z (fst z' +ᵣ -ᵣ fst z , x<y→0<y-x _ _ z<z' )
      1<z)


ln-mon-str-1< :
   ∀ (y y' : ℝ₊)
   → 1 <ᵣ fst y
   → fst y <ᵣ fst y'
   → ln y <ᵣ ln y'
ln-mon-str-1< y y' 1<y y<y' =
 Seq-^-FI.∩$-elimProp2  (fst y) (snd y) (fst y') (snd y')
  {B = λ (_ , ln-y) (_ , ln-y') → ln-y <ᵣ ln-y'}
  (λ _ _ → isProp<ᵣ _ _)
  λ Z x∈ y∈ → monotoneStrictPreLn Z (fst y , _) (fst y' , _)
    1<y (snd x∈) (fst x∈) (snd y∈) (fst y∈) y<y'


-- opaque
--  unfolding _+ᵣ_
invLipPreLn : ∀ Z → ∃[ K ∈ _ ]
              Invlipschitz-ℝ→ℝℙ K
               ((intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
              (fromNat (suc (suc Z)))))
              λ x (≤x , x≤) →
                expPreDer.expPreDer'.preLn Z
                  (x , isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)) ≤x)
                 x≤ ≤x
invLipPreLn Z =
   PT.map
     ww
     (denseℚinℝ _ _ (snd Kᵣ))

  where


   Z<SZ : fst (fromNat (suc (suc Z))) ℚ.<
       fst (fromNat (suc (suc (suc Z))))
   Z<SZ =
                (ℚ.<ℤ→<ℚ (pos (suc (suc Z))) (pos (suc (suc (suc Z))))
                (invEq (ℤ.pos-<-pos≃ℕ< _ _)
                  (ℕ.≤-refl {(suc (suc (suc Z)))})))
   1<Z : [ pos 1 / 1+ 0 ] ℚ.< [ pos (suc (suc Z)) / 1+ 0 ]
   1<Z =
                (ℚ.<ℤ→<ℚ (pos (suc zero)) (pos (suc (suc Z)))
                (invEq (ℤ.pos-<-pos≃ℕ< _ _)
                  (ℕ.suc-≤-suc (ℕ.suc-≤-suc ℕ.zero-≤))))

   [1/3+Z]≤[2+Z] : rat [ pos 1 / 2+ suc Z ] ≤ᵣ rat [ pos (suc (suc Z)) / 1+ 0 ]
   [1/3+Z]≤[2+Z] = isTrans≤ᵣ _ 1 _
     (≤ℚ→≤ᵣ _ _ (fst (ℚ.invℚ₊-≤-invℚ₊ 1 (fromNat (suc (suc (suc Z)))))
       ((ℚ.<Weaken≤ _ _
        (ℚ.isTrans< 1 (fst (fromNat (suc (suc Z)))) _ 1<Z (Z<SZ))))
       ))
     (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ 1<Z))

   2+Z∈ : (fromNat (suc (suc Z))) ∈
            ((intervalℙ (rat [ 1 / fromNat (suc (suc (suc Z))) ])
               (fromNat (suc (suc (suc Z))))))
   2+Z∈ = [1/3+Z]≤[2+Z] , (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ Z<SZ))


   3+Z∈ : rat ([ (pos (suc (suc (suc Z)))) / 1 ]) ∈
            ((intervalℙ (rat [ 1 / fromNat (suc (suc (suc Z))) ])
               (fromNat (suc (suc (suc Z))))))
   3+Z∈ =
             (≤ℚ→≤ᵣ _ _
                (ℚ.isTrans≤ _ 1 [ pos (suc (suc (suc Z))) / (1+ 0) ]
                  (fst (ℚ.invℚ₊-≤-invℚ₊ 1 (fromNat (suc (suc (suc Z)))))
                   ((ℚ.≤ℤ→≤ℚ _ (pos _) (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _)
                (ℕ.suc-≤-suc ℕ.zero-≤)))))
                  ((ℚ.≤ℤ→≤ℚ _ (pos (suc (suc (suc Z)))) (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _)
                (ℕ.suc-≤-suc ℕ.zero-≤)))))) , (≤ᵣ-refl _)



   SSSZ₊ SSZ₊ : ℝ₊
   SSSZ₊ = (ℚ₊→ℝ₊ ([ (pos (suc (suc (suc Z)))) / 1 ] , _))
   SSZ₊ = (ℚ₊→ℝ₊ ([ (pos (suc (suc Z))) / 1 ] , _))

   Kᵣ : ℝ₊
   Kᵣ =
         BDL.preLn SSSZ₊ (suc Z) (snd 3+Z∈) (fst 3+Z∈)
          +ᵣ -ᵣ

          BDL.preLn SSZ₊ (suc Z) (snd 2+Z∈) (fst 2+Z∈)
          ,
          x<y→0<y-x
           (BDL.preLn (ℚ₊→ℝ₊ ([ (pos (suc (suc Z))) / 1 ] , _)) (suc Z) (snd 2+Z∈) (fst 2+Z∈))
           (BDL.preLn (ℚ₊→ℝ₊ ([ (pos (suc (suc (suc Z)))) / 1 ] , _))  (suc Z) (snd 3+Z∈)
         (fst 3+Z∈))
           (monotoneStrictPreLn (suc Z)
             (ℚ₊→ℝ₊ ([ (pos (suc (suc Z))) / 1 ] , _))
             (ℚ₊→ℝ₊ ([ (pos (suc (suc (suc Z)))) / 1 ] , _))
             (<ℚ→<ᵣ _ _ 1<Z)
             (snd 2+Z∈) (fst 2+Z∈)
             (snd 3+Z∈) (fst 3+Z∈)
             (<ℚ→<ᵣ _ _ Z<SZ))

   ww : Σ ℚ (λ q → (rat [ pos 0 / 1+ 0 ] <ᵣ rat q) × (rat q <ᵣ Kᵣ .fst)) →
         Σ ℚ₊
         (λ K →
            Invlipschitz-ℝ→ℝℙ K
            (intervalℙ (rat [ pos 1 / 2+ Z ])
             (rat [ pos (suc (suc Z)) / 1+ 0 ]))
            λ x (x≤ , ≤x) → expPreDer.expPreDer'.preLn Z
                  (x , isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)) x≤)
                 ≤x x≤)
   ww (K , 0<K , K<Kᵣ) =  (invℚ₊ K₊) , zzz

    where
    K₊ : ℚ₊
    K₊ = (K , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<K))
    zzz : Invlipschitz-ℝ→ℝℙ (invℚ₊ K₊)
      (intervalℙ (rat [ pos 1 / 2+ Z ])
       (rat [ pos (suc (suc Z)) / 1+ 0 ]))
      (λ x (≤x , x≤) →
         BDL.preLn
         (x ,
          isTrans<≤ᵣ (rat [ pos 0 / 1+ 0 ]) (rat [ pos 1 / 2+ Z ]) x
          (<ℚ→<ᵣ [ pos 0 / 1+ 0 ] [ pos 1 / 2+ Z ] (ℚ.0<pos 0 (2+ Z)))
          ≤x)
         Z x≤ ≤x )
    zzz u u∈ v v∈ ε lnU∼lnV =
     invEq (∼≃abs<ε _ _ _)
              (isTrans<≡ᵣ _ _ _
               (isTrans≤<ᵣ _ _ _
                 zzzz
                 (isTrans<≡ᵣ _ _ _
                  (<ᵣ₊Monotone·ᵣ _ _ _ _
                  (<ᵣWeaken≤ᵣ _ _ (snd (invℝ₊ Kᵣ)))
                  (0≤absᵣ _)
                  (invEq (invℝ₊-<-invℝ₊ Kᵣ _)
                    K<Kᵣ) lnuv<)
                     (cong₂ _·ᵣ_
                      (invℝ₊-rat _)
                      refl))
                 )
               (sym (rat·ᵣrat _ _)))
     where
      u₊ = _
      v₊ = _

      lnU = BDL.preLn u₊ Z (snd u∈) (fst u∈)
      lnV = BDL.preLn v₊ Z (snd v∈) (fst v∈)




      clp : ℝ → ℝ
      clp = clampᵣ (rat [ 1 / (1+  (suc Z)) ])
                   (rat [ pos (suc (suc Z)) / 1 ])

      1/SSZ<SSZ = (ℚ.isTrans< _ 1 _
                ((fst (ℚ.invℚ₊-<-invℚ₊ 1
                   (([ pos (suc (suc Z)) / 1 ] , _))
                   )
                  (1<Z)))
                ((1<Z)))


      1/SSZ≤SSZ = ≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ 1/SSZ<SSZ)

      0<clp : ∀ x → 0 <ᵣ clp x
      0<clp x = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _))
         (≤clampᵣ (rat [ 1 / (1+  (suc Z)) ]) _ x 1/SSZ≤SSZ)

      clpCount : IsContinuous clp
      clpCount = IsContinuousClamp
         (rat [ 1 / (1+  (suc Z)) ])
                   (rat [ pos (suc (suc Z)) / 1 ])

      -- lnX : ℝ → ℝ
      -- lnX x = BDL.preLn (clp x , 0<clp x) Z
      --    (clamp≤ᵣ (rat [ 1 / fromNat (suc (suc Z)) ]) _ x)

      --    (≤clampᵣ (rat [ 1 / fromNat (suc (suc Z)) ]) _ x
      --       (isTrans≤ᵣ _ 1 _
      --           (≤ℚ→≤ᵣ _ _ (fst (ℚ.invℚ₊-≤-invℚ₊ 1 (fromNat (suc (suc Z))))
      --             (ℚ.<Weaken≤ _ _ 1<Z)))
      --           (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ 1<Z))))

      lnX' : ℝ → ℝ
      lnX' x = ln (clp x , 0<clp x)

      lnX'ₙ : ∀ (x : ℝ₊) 0<x
              (x∈ : fst x ∈ (intervalℙ (rat [ 1 /  (2+ (suc Z)) ])
                        (rat [ pos (suc (suc (suc Z))) / 1 ]))) →
                ln x ≡ BDL.preLn
                         (fst x , 0<x) (suc Z) (snd x∈) (fst x∈)
      lnX'ₙ x 0<x x∈ =
        cong snd (Seq-^-FI.∩$-∈ₙ (fst x) (snd x) (suc Z) x∈)
        ∙ cong (λ 0<x → BDL.preLn
                         (fst x , 0<x) (suc Z) (snd x∈) (fst x∈))
                         (isProp<ᵣ _ _ _ _)

      clp≡ : ∀ u → u ∈ ((intervalℙ (rat [ 1 /  (1+ (suc Z)) ])
               (rat [ pos (suc (suc Z)) / 1 ]))) → clp u ≡ u
      clp≡ u u∈ = sym (∈ℚintervalℙ→clampᵣ≡ _ _ u u∈)

      lnX'Cont : IsContinuous lnX'
      lnX'Cont = IsContinuousWithPred∘IsContinuous
       _ _ _ 0<clp
       ln-cont clpCount

      lnuv< = fst (∼≃abs<ε _ _ _) lnU∼lnV

      zzzz= : ∀ x y → clampᵣ (rat [ pos 1 / 2+ Z ])
       (rat [ pos (suc (suc Z)) / 1+ 0 ]) (rat x)
       ≡
       clampᵣ (rat [ pos 1 / 2+ Z ]) (rat [ pos (suc (suc Z)) / 1+ 0 ])
       (rat y) →
       fst Kᵣ ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)) ≤ᵣ
       absᵣ (lnX' (rat x) -ᵣ lnX' (rat y))
      zzzz= x y p =
       ≡ᵣWeaken≤ᵣ _ _
                 (𝐑'.0RightAnnihilates' _ _
                   (cong absᵣ (𝐑'.+InvR' _ _ p) ∙ absᵣ-rat 0)
                   ∙ sym (absᵣ-rat 0) ∙
                   cong absᵣ (sym (𝐑'.+InvR' _ _
                     (ll))))

         where

         ll : ln (clp (rat x) , 0<clp (rat x))  ≡ ln (clp (rat y) , 0<clp (rat y))
         ll = cong ln (ℝ₊≡ p)

      zzzz< : ∀ x y → clampᵣ (rat [ pos 1 / 2+ Z ])
       (rat [ pos (suc (suc Z)) / 1+ 0 ]) (rat x)
       <ᵣ
       clampᵣ (rat [ pos 1 / 2+ Z ]) (rat [ pos (suc (suc Z)) / 1+ 0 ])
       (rat y) →
       fst Kᵣ ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)) ≤ᵣ
       absᵣ (lnX' (rat x) -ᵣ lnX' (rat y))
      zzzz< x y x<y =
       isTrans≡≤ᵣ
         (fst Kᵣ ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)))
         (absᵣ (clp (rat x) -ᵣ clp (rat y)) ·ᵣ fst Kᵣ)
         (absᵣ (lnX' (rat x) -ᵣ lnX' (rat y)))
        (·ᵣComm _ _) (fst (z≤x/y₊≃y₊·z≤x _ _ _)
          (subst2  _≤ᵣ_
           (cong₂ _·ᵣ_ refl
             (cong (fst ∘ invℝ₊)
              (ℝ₊≡ {_ , _} {_ , isTrans<≡ᵣ _ _ _ decℚ<ᵣ?
               (sym (cong (rat ∘ [_/ 1 ]) hhhh))} (-ᵣ-rat₂ _ _ ∙ cong rat (ℚ.ℤ-→ℚ- _ _
               ∙ cong ([_/ 1 ]) (cong₂ ℤ._+_ (ℤ.pos+ _ _) refl ∙ sym (ℤ.+Assoc 1 (pos ((suc (suc Z))))
                    (ℤ.- (pos (suc (suc Z)))))
                ∙ 𝐙'.+IdR' _ _ refl )) ))
             ∙ cong (fst ∘ invℝ₊) (ℝ₊≡ (cong rat (cong [_/ 1 ] hhhh))) ∙ cong fst invℝ₊1 )
             ∙ (·IdR _) )
           (cong₂ {y = absᵣ (lnX' (rat x) +ᵣ -ᵣ lnX' (rat y))} _·ᵣ_
             ( sym (absᵣNonNeg _ (x≤y→0≤y-x _ _
              (expPreDer.monotonePreLn (suc Z)
               (clp (rat x) , 0<clp (rat x))
               (clp (rat y) , 0<clp (rat y))
                (snd x*∈) (fst x*∈) (snd y*∈) (fst y*∈) (<ᵣWeaken≤ᵣ _ _ x<y))))
               ∙ cong absᵣ (cong₂ (λ u v → u +ᵣ -ᵣ v)
               (sym (lnX'ₙ ((clp (rat y)) , 0<clp (rat y)) _ _)) --(sym (lnX'ₙ _ _ _))
               ((sym (lnX'ₙ (clp (rat x) , 0<clp (rat x)) _ _))) --
                )
                 ∙ minusComm-absᵣ (lnX' (rat y)) (lnX' (rat x)))

             (cong (fst ∘ invℝ₊)
               (ℝ₊≡ {_} {_ , isTrans<≤ᵣ _ _ _ (x<y→0<y-x _ _ x<y)
                     (isTrans≤≡ᵣ _ _ _ (≤absᵣ _) (minusComm-absᵣ _ _))}
                  (sym (absᵣPos _ (x<y→0<y-x _ _ x<y))
                 ∙ minusComm-absᵣ _ _))))
           zzWW)) --
         where

         hhhh : 1 ℤ.+ ℤ.predℤ (pos (suc (suc Z)) ℤ.+negsuc Z) ≡ pos 1
         hhhh = 𝐙'.+IdR' _ _ (cong {y = 1} ℤ.predℤ
          ((cong (ℤ._+ ℤ.negsuc Z) (ℤ.pos+ _ _) ∙
           sym (ℤ.+Assoc 1 (pos (suc Z)) (ℤ.negsuc Z))) ∙
            𝐙'.+IdR' _ _ (ℤ.-Cancel (pos (suc Z))) ))

         SSZ≤SSSZ : [ pos (suc (suc Z)) / 1 ] ℚ.≤ [ pos (suc (suc (suc Z))) / 1 ]
         SSZ≤SSSZ = (ℚ.<Weaken≤ [ pos (suc (suc Z)) / 1 ] [ pos (suc (suc (suc Z))) / 1 ] Z<SZ)

         1/SSSZ≤1/SSZ : rat [ pos 1 / 2+ suc Z ] ≤ᵣ rat [ pos 1 / 2+ Z ]
         1/SSSZ≤1/SSZ = ≤ℚ→≤ᵣ _ _
           (ℚ.invℚ≤invℚ ([ pos (suc (suc (suc Z))) / 1 ] , _)
            ([ pos (suc (suc Z)) / 1 ] , _) SSZ≤SSSZ)

         x*∈ : clp (rat x) ∈  (intervalℙ (rat [ 1 /  (2+ (suc Z)) ])
                        (rat [ pos (suc (suc (suc Z))) / 1 ]))
         x*∈ =
          let (≤x , x≤) = ((clampᵣ∈ℚintervalℙ _ _ 1/SSZ≤SSZ (rat x)))
          in isTrans≤ᵣ _ _ _ 1/SSSZ≤1/SSZ ≤x , isTrans≤ᵣ _ _ _ x≤
            (≤ℚ→≤ᵣ _ _ SSZ≤SSSZ)

         y*∈ : clp (rat y) ∈ (intervalℙ (rat [ 1 /  (2+ (suc Z)) ])
                        (rat [ pos (suc (suc (suc Z))) / 1 ]))
         y*∈ =
          let (≤y , y≤) = ((clampᵣ∈ℚintervalℙ _ _ 1/SSZ≤SSZ (rat y)))
          in (isTrans≤ᵣ _ _ _ 1/SSSZ≤1/SSZ ≤y) ,
               isTrans≤ᵣ _ _ _ y≤ ((≤ℚ→≤ᵣ _ _ SSZ≤SSSZ))



         zzWW : _ ≤ᵣ _
         zzWW =
          (expPreDer.slope-monotone-preLn
             (suc Z) (clp (rat x) , 0<clp (rat x)) (clp (rat y) , 0<clp (rat y))
              SSZ₊ SSSZ₊
              (snd x*∈) (fst x*∈)
              (snd y*∈) (fst y*∈)
              (snd 2+Z∈) (fst 2+Z∈)
              (snd 3+Z∈) (fst 3+Z∈)
              x<y (<ℚ→<ᵣ _ _ Z<SZ) (snd ((clampᵣ∈ℚintervalℙ _ _ 1/SSZ≤SSZ (rat x)))) (snd y*∈))

      opaque
       unfolding _+ᵣ_
       zzzz* : fst Kᵣ ·ᵣ absᵣ (clp u -ᵣ clp v) ≤ᵣ absᵣ (lnX' u -ᵣ lnX' v)
       zzzz* =
         ≤Cont₂
            {λ u v → fst Kᵣ ·ᵣ absᵣ (clp u -ᵣ clp v)}
            {λ u v → absᵣ (lnX' u -ᵣ lnX' v)}
            (cont∘₂ (IsContinuous∘ _ _
               (IsContinuous·ᵣL (fst Kᵣ))
               IsContinuousAbsᵣ)
              (cont₂∘  (contNE₂ sumR)
                clpCount
                (IsContinuous∘ _ _
                  IsContinuous-ᵣ clpCount)) )
            (cont∘₂ IsContinuousAbsᵣ
              (cont₂∘  (contNE₂ sumR)
                lnX'Cont
                (IsContinuous∘ _ _
                  IsContinuous-ᵣ lnX'Cont)
                ))
            (ℚ.elimBy≡⊎<
               (λ x y X →
                 subst2 (_≤ᵣ_ ∘ (fst Kᵣ ·ᵣ_))
                   ((minusComm-absᵣ (clp (rat x)) (clp (rat y))))
                   (minusComm-absᵣ (lnX' (rat x)) (lnX' (rat y)))
                   X)
               (λ x → ≡ᵣWeaken≤ᵣ _ _
                    (𝐑'.0RightAnnihilates' _ _ (cong absᵣ (+-ᵣ _)
                      ∙ absᵣ-rat 0)
                     ∙∙ sym (absᵣ-rat 0)
                     ∙∙ cong absᵣ ((sym (+-ᵣ (lnX' (rat x)))))))
               λ x y →
                  ⊎.rec
                   (zzzz= x y)
                   (zzzz< x y)
                   ∘ ℚ-clamp-<-casesᵣ ([ 1 /  (1+ (suc Z)) ])
                          ([ pos (suc (suc Z)) / 1 ])
                          x y 1/SSZ<SSZ)
            u v

      zzzz : absᵣ (u -ᵣ v) ≤ᵣ
             invℝ₊ Kᵣ .fst ·ᵣ absᵣ (lnU -ᵣ lnV)
      zzzz =
        isTrans≤≡ᵣ _ _ _
          (invEq (z≤x/y₊≃y₊·z≤x _ _ _)
            (isTrans≤≡ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _
                (cong₂ (λ u v → fst Kᵣ ·ᵣ absᵣ (u -ᵣ v))
                  (∈ℚintervalℙ→clampᵣ≡ _ _ u u∈)
                  (∈ℚintervalℙ→clampᵣ≡ _ _ v v∈))
                zzzz*)
              (cong absᵣ
                (cong₂ _-ᵣ_
                  (cong ln
                      ((ℝ₊≡
                         {clp u , 0<clp u} {u , snd u₊}
                        (sym (∈ℚintervalℙ→clampᵣ≡ _ _ u u∈))))
         ∙∙ cong snd (Seq-^-FI.∩$-∈ₙ u (snd u₊) Z u∈)
         ∙∙ cong (λ 0<u → BDL.preLn (u , 0<u) Z (snd u∈) (fst u∈))
               (isProp<ᵣ 0 u _ _))

                  (cong ln
                      ((ℝ₊≡
                         {clp v , 0<clp v} {v , snd v₊}
                        (sym (∈ℚintervalℙ→clampᵣ≡ _ _ v v∈))))
         ∙∙ cong snd (Seq-^-FI.∩$-∈ₙ v (snd v₊) Z v∈)
         ∙∙ cong (λ 0<v → BDL.preLn (v , 0<v) Z (snd v∈) (fst v∈))
               (isProp<ᵣ 0 v _ _))
                  ))))
          (·ᵣComm _ _)

^ᵣ· : (x : ℝ₊) (a b : ℝ) →
      fst ((x ^ᵣ a) ^ᵣ b) ≡ fst (x ^ᵣ (a ·ᵣ b))
^ᵣ· x a  =
   ≡Continuous _ _
      (cont-^ _)
       (IsContinuous∘ _ _ (cont-^ x)
         (IsContinuous·ᵣL a))
     λ b' →
      ^-rat _ _ ∙
         ≡Continuous _ _
           (IsContinuousWithPred∘IsContinuous _ _
             _ (λ v → snd (x ^ᵣ v)) (IsContinuous^ℚ b') (cont-^ x))
           (IsContinuous∘ _ _ (cont-^ x)
         (IsContinuous·ᵣR (rat b')))
           (λ a' →
           (cong (fst ∘ _^ℚ b') (ℝ₊≡ (^-rat x a')))
             ∙ cong fst (^ℚ-· x a' b') ∙
             sym (^-rat _ _) ∙ cong (fst ∘ (x ^ᵣ_)) (rat·ᵣrat _ _))
           a

inj-ln : ∀ x y → ln x ≡ ln y → x ≡ y
inj-ln (x , 0<x) (y , 0<y) =
  Seq-^-FI.∩$-elimProp2 x 0<x y 0<y
   {λ (_ , ln-x) (_ , ln-y) → ln-x ≡ ln-y → (x , 0<x) ≡ (y , 0<y) }
   (λ _ _ → isPropΠ λ _ → isSetℝ₊ _ _)
   λ Z x∈ y∈ p →
     PT.rec (isSetℝ₊ _ _)
       (λ (_ , isLip) →
         ℝ₊≡ (Invlipschitz-ℝ→ℝ→injective-interval _ _ _ _ isLip x x∈ y y∈
          p))
      (invLipPreLn Z)

ln[a^b₊]≡b₊·ln[a] : ∀ a (b : ℝ₊) → ln (a ^ᵣ (fst b)) ≡ fst b ·ᵣ ln a
ln[a^b₊]≡b₊·ln[a] a (b , 0<b) =
   limitUniq _ _ _ _ (zz b) (zz' b 0<b) ∙ ·ᵣComm _ _
  where
  zz : ∀ b → derivativeOf (fst ∘ a ^ᵣ_  ∘ (b ·ᵣ_)) at 0 is
        (ln (a ^ᵣ b))
  zz b = substDer
     (λ r → ^ᵣ· _ _ _)
     (subst (derivativeOf (fst ∘ (a ^ᵣ b) ^ᵣ_ ) at 0 is_)
     ((𝐑'.·IdL' _ _ (^ᵣ0 _))) (^-der (a ^ᵣ b) 0))

  zz'' : ∀ b (0<b : 0 <ᵣ b) → derivativeOf (fst ∘ a ^ᵣ_  ∘ (b ·ᵣ_))
                at 0 ／ᵣ₊ (b , 0<b) is (b ·ᵣ (fst (a ^ᵣ 0) ·ᵣ ln a))
  zz'' b 0<b = derivative-∘· _ _ _ (b , 0<b) (^-der a 0)

  zz' : ∀ b (0<b : 0 <ᵣ b) → derivativeOf (fst ∘ a ^ᵣ_  ∘ (b ·ᵣ_)) at 0 is (ln a ·ᵣ b)
  zz' b 0<b = subst2 (derivativeOf (fst ∘ a ^ᵣ_  ∘ (b ·ᵣ_)) at_is_)
         (𝐑'.0LeftAnnihilates _) (cong (b ·ᵣ_) (𝐑'.·IdL' _ _ (^ᵣ0 a)) ∙ ·ᵣComm _ _) (zz'' b 0<b)

ln[a^b]≡b·ln[a] : ∀ a b → ln (a ^ᵣ b) ≡ b ·ᵣ ln a
ln[a^b]≡b·ln[a] a =
  ≡Continuous _ _
    (IsContinuousWithPred∘IsContinuous
     _ _ _
      (λ x → snd (a ^ᵣ x))
      ln-cont
      (cont-^ a)) (IsContinuous·ᵣR _)
    (ℚ.byTrichotomy 0 ww)

  where
  ww : ℚ.TrichotomyRec 0 (λ z → ln (a ^ᵣ rat z) ≡ rat z ·ᵣ ln a)
  ww .ℚ.TrichotomyRec.lt-case b b<0 =
    cong ln (ℝ₊≡ (^-rat _ _ ∙∙ cong fst (^ℚ-minus _ _) ∙∙ sym (^-rat _ _)))
     ∙∙ ln[a^b₊]≡b₊·ln[a] (invℝ₊ a) (rat (ℚ.- b) ,
      <ℚ→<ᵣ _ _ (ℚ.minus-< _ _ b<0) ) ∙∙
       (cong₂ _·ᵣ_ (sym (-ᵣ-rat b)) (ln-inv a) ∙  -ᵣ·-ᵣ _ _)
  ww .ℚ.TrichotomyRec.eq-case = (cong ln (ℝ₊≡ (^ᵣ0 _)) ∙ ln-1≡0)
    ∙ sym (𝐑'.0LeftAnnihilates (ln a))
  ww .ℚ.TrichotomyRec.gt-case b 0<b =
    ln[a^b₊]≡b₊·ln[a] a (rat b , <ℚ→<ᵣ _ _ 0<b)
