module

public import Tseitin.Defs
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation

namespace Tseitin

public section negative

@[simp, expose] def liftAux {α : Type*} [Mul α] (a b A B X : α) : TseitinGen → α
  | .a' => a
  | .b' => b
  | .A' => A
  | .B' => B
  | .X' => X
  | .mul x y => liftAux a b A B X x * liftAux a b A B X y

def lift {α : Type*} [Semigroup α] (a b A B X : α)
    (h1 : A * a = a * A) (h2 : A * b = b * A) (h3 : B * a = a * B) (h4 : B * b = b * B)
    (h5 : (X * a) * A = A * X) (h6 : (X * b) * B = B * X) (h7 : ((a * A) * A) * X = (a * A) * A) :
    Tseitin → α := Quot.lift (liftAux a b A B X) fun x y h ↦ by
  induction h with try simpa
  | assoc x y z => simp [_root_.mul_assoc]
  | lcongr x y z _ ih => simp [ih]
  | rcongr x y z _ ih => simp [ih]

def heavies : Tseitin → FreeMonoid Bool :=
  lift 1 1 (.of true) (.of false) 1
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

lemma A_ne_B : A ≠ B := by
  intro h
  have := congr(heavies $h)
  simp [heavies, lift, A, B] at this
  grind [FreeMonoid.of_injective]

def leftMost : Tseitin → Matrix (Fin 2) (Fin 2) ℤ :=
  lift !![1, 0; 0, 0] !![1, 0; 0, 0] 1 1 !![1, 0; 1, 0]
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by decide)

lemma AAX_ne_AAa : A A X ≠ A A a := ne_of_apply_ne leftMost (by decide)
lemma AAaX_ne_AAXa : A A a X ≠ A A X a := ne_of_apply_ne leftMost (by decide)

def signed : Tseitin → Matrix (Fin 3) (Fin 3) ℤ :=
  lift (-1) (-1) !![0, 1, 0; 0, 0, 1; 0, 0, 0] !![0, 1, 0; 0, 0, 1; 0, 0, 0]
    !![1, 0, 0; 0, -1, 0; 0, 0, 1]
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by decide)

lemma aaA_ne_aA : a a A A ≠ a A A := ne_of_apply_ne signed (by decide)
lemma aaAA_ne_aAA : a a A A ≠ a A A := ne_of_apply_ne signed (by decide)
lemma aaX_ne_aX : a a A A X ≠ a A A X := ne_of_apply_ne signed (by decide)
lemma AAX_ne_AXA : A A X ≠ A X A := ne_of_apply_ne signed (by decide)

end negative

end Tseitin
