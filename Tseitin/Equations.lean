module

public import Tseitin.Defs

open Tseitin

public section positive

variable {x : Tseitin}

@[simp] private lemma ac_comm' : x A a = x a A := by simp only [← Tseitin.mul_assoc, ac_comm]
@[simp] private lemma ad_comm' : x B a = x a B := by simp only [← Tseitin.mul_assoc, ad_comm]
@[simp] private lemma bc_comm' : x A b = x b A := by simp only [← Tseitin.mul_assoc, bc_comm]
@[simp] private lemma bd_comm' : x B b = x b B := by simp only [← Tseitin.mul_assoc, bd_comm]
lemma ea_swap' : x X a A = x A X := by simp only [← Tseitin.mul_assoc x, ea_swap]
lemma eb_swap' : x X b B = x B X := by simp only [← Tseitin.mul_assoc x, eb_swap]
lemma acce' : x a A A X = x a A A := by simp only [← Tseitin.mul_assoc x, acce]

macro "comm" : tactic =>
  `(tactic| simp only [ac_comm, ad_comm, bc_comm, bd_comm, ac_comm', ad_comm', bc_comm', bd_comm'])

macro "create" : tactic => `(tactic| simp only [acce, acce'])
macro "move_a" : tactic => `(tactic| simp only [ea_swap, ea_swap'])
macro "move_b" : tactic => `(tactic| simp only [eb_swap, eb_swap'])
macro "move" : tactic =>   `(tactic| simp only [ea_swap, ea_swap', eb_swap, eb_swap'])

-- flipped from the website's problem 1
lemma problem1 : a a A A A = a A A A := calc
  _ = a A A a A   := by comm
  _ = a A A X a A := by create
  _ = a A A A X   := by move_a
  _ = A a A A X   := by comm
  _ = A a A A     := by create
  _ = a A A A     := by comm

private lemma problem1' : x a a A A A = x a A A A := by simp only [← Tseitin.mul_assoc x, problem1]

macro "problem1" : tactic => `(tactic| simp only [problem1, problem1'])

lemma problem3 : a a A A A = a A A A := calc
  _ = a A A a A   := by comm
  _ = a A A X a A := by create
  _ = a A A A X   := by move_a
  _ = A a A A X   := by comm
  _ = A a A A     := by create
  _ = a A A A     := by comm

private lemma problem3' : x a a A A A = x a A A A := by simp only [← Tseitin.mul_assoc x, problem3]

macro "problem3" : tactic => `(tactic| simp only [problem3, problem3'])

lemma problem2 : A A A X a = A A A X := calc
  _ = A A X a A a       := by move_a
  _ = A X a A a A a     := by move_a
  _ = X a A a A a A a   := by move_a
  _ = X a a a a A A A   := by comm
  _ = X a a a A A A     := by problem3
  _ = X a A a A a A     := by comm
  _ = A X a A a A       := by move_a
  _ = A A X a A         := by move_a
  _ = A A A X           := by move_a

private lemma problem2' : x A A A X a = x A A A X := by simp only [← Tseitin.mul_assoc x, problem2]

macro "problem2" : tactic => `(tactic| simp only [problem2, problem2'])

lemma problem4 : a b a a A A B A A = a A A B A A := calc
  _ = a A A b B a A a A   := by comm
  _ = a A A X b B a A a A := by create
  _ = a A A B X a A a A   := by move
  _ = a A A B A X a A     := by move
  _ = a A A B A A X       := by move
  _ = A A B a A A X       := by comm
  _ = A A B a A A         := by create
  _ = a A A B A A         := by comm

private lemma problem4' : x a b a a A A B A A = x a A A B A A := by
  simp only [← Tseitin.mul_assoc x, problem4]

macro "problem4" : tactic => `(tactic| simp only [problem4, problem4'])

lemma problem5 : A A X A = A A A X := calc
  _ = A X a A A     := by move
  _ = X a A a A A   := by move
  _ = X a a A A A   := by comm
  _ = X a a a A A A := by problem3
  _ = X a A a A a A := by comm
  _ = A X a A a A   := by move
  _ = A A X a A     := by move
  _ = A A A X       := by move

private lemma problem5' : x A A X A = x A A A X := by
  simp only [← Tseitin.mul_assoc x, problem5]

macro "problem5" : tactic => `(tactic| simp only [problem5, problem5'])

lemma my_problem6 : A A X A = A X A A := calc
  _ = A X a A A   := by move
  _ = X a A a A A := by move
  _ = X a a A A A := by comm
  _ = X a A A A   := by problem3
  _ = A X A A     := by move

lemma example1 : A A X X = A A X := calc
  _ = A X a A X   := by move
  _ = X a A a A X := by move
  _ = X a a A A X := by comm
  _ = X a a A A   := by create
  _ = X a A a A   := by comm
  _ = A X a A     := by move
  _ = A A X       := by move

end positive
