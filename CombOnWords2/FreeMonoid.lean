import CombOnWords2.simp_attr
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.List.Join

namespace FreeMonoid

@[freemonoid_to_list]
def toList' (w : FreeMonoid α) : List α := w

@[freemonoid_to_list]
def one_eq_list_nil : (1 : FreeMonoid α) = ([] : List α) := rfl

@[freemonoid_to_list]
theorem mul_eq_list_append (v w : FreeMonoid α)
    : v * w = v.toList' ++ w.toList' :=
  rfl

def length' : FreeMonoid α →* Multiplicative ℕ where
  toFun    := List.length
  map_one' := List.length_nil
  map_mul' := List.length_append

def length (w : FreeMonoid α) : ℕ := length' w

-- Macro for length w as |w|
macro:max atomic("|" noWs) a:term noWs "|" : term => `(length $a)
def FreeMonoid.length.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()

@[freemonoid_to_list]
theorem length_eq_list_length (w : FreeMonoid α) : w.length = List.length w :=
  rfl

def join' : FreeMonoid (FreeMonoid α) →* FreeMonoid α where
  toFun    := List.join
  map_one' := List.join_nil
  map_mul' := List.join_append

def join (w : FreeMonoid (FreeMonoid α)) : FreeMonoid α := FreeMonoid.join' w

@[freemonoid_to_list]
theorem join_eq_list_join (w : FreeMonoid (FreeMonoid α)) : w.join = List.join w :=
  rfl

def take (a : ℕ) (w : FreeMonoid α) : FreeMonoid α := List.take a w

@[freemonoid_to_list]
theorem take_eq_list_take (a : ℕ) (w : FreeMonoid α) : w.take a = List.take a w :=
  rfl

def drop (a : ℕ) (w : FreeMonoid α) : FreeMonoid α := List.drop a w

@[freemonoid_to_list]
theorem drop_eq_list_drop (a : ℕ) (w : FreeMonoid α) : w.drop a = List.drop a w :=
  rfl

