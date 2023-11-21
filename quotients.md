---
title: Quotients 
layout: default
nav_order: 12
--- 

# Quotients

By using type-theoretic quotients it is relatively easy to model quotients of algebraic objects in lean.
We can do this for groups using normal subgroups and rings using two-sided ideals by doing the following steps (focusing on normal subgroups):

1. Given a normal subgroup `N` in a group `G`, define an equivalence relation (a setoid) on `G` in the usual way.
2. Take the type-theoretic quotient of this setoid.
3. Construct the group structure on this quotient.
4. Construct the quotient map, the universal map out of the quotient, etc., showing its universal property.

Type-theoretically this is quite similar to what we do in every day mathematics, so I won't say much more about this.
Instead, I'll focus on quotients in algebra which aren't so familiar and don't correspond to some "subobject".
Let's use monoids as out example.

# Quotients of Monoids

Let `M` be a monoid.
An equivalence relation `r` on `M` is said to be "compatible with multiplication" provided that whenever `r x x'` and `r y y'` then `r (x * y) (x' * y')`.
This is exactly the kind of equivalence relation whose quotient inherits a monoid structure from the ambiant monoid.

Let's model this as a class in lean:
```lean
class MulCompat {X : Type*} [Mul X] (S : Setoid X) : Prop where
  cond : ∀ x x' y y', S.rel x x' → S.rel y y' → S.rel (x * y) (x' * y')
```

Now, given such a setoid, we'll construct a monoid structure on its quotient:
```lean
instance (X : Type*) [Mul X] (S : Setoid X) [MulCompat S] : Mul (Quotient S) where
  mul := Quotient.lift₂ (fun x y => Quotient.mk _ (x * y)) <|
    fun _ _ _ _ h₁ h₂ => Quotient.sound <| MulCompat.compat _ _ _ _ h₁ h₂

instance (X : Type*) [Monoid X] (S : Setoid X) [MulCompat S] : Monoid (Quotient S) where
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ; apply Quotient.sound ; simp [mul_assoc, Setoid.refl]
  one := Quotient.mk _ 1
  one_mul := by
    rintro ⟨a⟩ ; apply Quotient.sound ; simp [Setoid.refl]
  mul_one := by
    rintro ⟨a⟩ ; apply Quotient.sound ; simp [Setoid.refl]
  npow n := Quotient.lift (fun x => Quotient.mk _ <| x^n) <| by
    intro x y h
    dsimp
    induction n with
    | zero => simp
    | succ n ih =>
      simp at ih ⊢
      simp_rw [show Nat.succ n = (n+1) from rfl, pow_succ]
      apply MulCompat.compat
      assumption'
  npow_zero := by
    rintro ⟨x⟩
    apply Quotient.sound
    simp [Setoid.refl]
  npow_succ := by
    rintro n ⟨x⟩
    apply Quotient.sound
    rw [pow_succ]
```

We can then proceed to prove the universal property of quotients with this construction (details omitted).

# Saturation 
What happens when we have a relation which is not compatible with multiplication?
In this case, we can "saturate" it to get a compatible relation using an inductive construction.

```lean
variable {M : Type*} [Monoid M] (r : M → M → Prop)

inductive saturate : M → M → Prop
  | of (a b : M) : r a b → saturate a b
  | mul_compat (a a' b b' : M) : saturate a a' → saturate b b' → saturate (a * b) (a' * b')
  | refl (a : M) : saturate a a
  | symm {a b : M} : saturate a b → saturate b a
  | trans {a b c : M} : saturate a b → saturate b c → saturate a c

def mulSetoid : Setoid M where
  r := saturate r
  iseqv := ⟨saturate.refl, saturate.symm, saturate.trans⟩

```

This will allow us to construct a monoid structure on `Quotient (mulSetoid r)` for an *arbitrary* relation `r`.
Stating and poving the universal property of this quotient will be left as an exercise (hint: state it in terms of `r`, not in terms of the saturation! (WHY?)).