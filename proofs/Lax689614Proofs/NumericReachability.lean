import Lax689614Proofs.NumericQuantifiers

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified.NumericReach

open Lax429075
open Lax434930Proofs.SavitchDefinitions.Reachability
open Lax434930Proofs.SavitchProofs (within_one path_splitting)

abbrev VectorFunction (n : ℕ) := CNF.Assignment → Vector n

def width (n : ℕ) : ℕ := 3 * n + 1
def leftBase (n start : ℕ) : ℕ := start + n + 1
def rightBase (n start : ℕ) : ℕ := start + 2 * n + 1

def readVector (n base : ℕ) : VectorFunction n := fun a i => a (base + i.val)

def ReadsBefore {n : ℕ} (bound : ℕ) (f : VectorFunction n) : Prop :=
  ∀ a b, AgreesBefore bound a b → f a = f b

theorem readVector_before (n base bound : ℕ) (h : base + n ≤ bound) :
    ReadsBefore bound (readVector n base) := by
  intro a b hab
  funext i
  exact hab (base + i.val) (by have := i.isLt; omega)

theorem ReadsBefore.mono {n bound bound' : ℕ} {f : VectorFunction n}
    (h : ReadsBefore bound f) (hb : bound ≤ bound') : ReadsBefore bound' f := by
  intro a b hab
  exact h a b (fun i hi => hab i (hi.trans_le hb))

def roundAssign (n start : ℕ) (a : CNF.Assignment) (mid : Vector n) (side : Vector 1)
    (left right : Vector n) : CNF.Assignment :=
  assignBlock (rightBase n start) n right
    (assignBlock (leftBase n start) n left (assignBlock (start + n) 1 side (assignBlock start n mid a)))

theorem roundAssign_before (n start : ℕ) (a : CNF.Assignment) (mid : Vector n) (side : Vector 1)
    (left right : Vector n) : AgreesBefore start (roundAssign n start a mid side left right) a := by
  intro i hi
  simp only [roundAssign]
  rw [assignBlock_before _ _ _ _ i (by unfold rightBase; omega),
    assignBlock_before _ _ _ _ i (by unfold leftBase; omega),
    assignBlock_before _ _ _ _ i (by omega), assignBlock_before _ _ _ _ i hi]

theorem roundAssign_mid (n start : ℕ) (a : CNF.Assignment) (mid : Vector n) (side : Vector 1)
    (left right : Vector n) : readVector n start (roundAssign n start a mid side left right) = mid := by
  funext i
  have hi := i.isLt
  simp only [readVector, roundAssign]
  rw [assignBlock_before _ _ _ _ (start + i.val) (by unfold rightBase; omega),
    assignBlock_before _ _ _ _ (start + i.val) (by unfold leftBase; omega),
    assignBlock_before _ _ _ _ (start + i.val) (by omega), assignBlock_inside]

theorem roundAssign_side (n start : ℕ) (a : CNF.Assignment) (mid : Vector n) (side : Vector 1)
    (left right : Vector n) : (roundAssign n start a mid side left right) (start + n) = side 0 := by
  simp only [roundAssign]
  rw [assignBlock_before _ _ _ _ (start + n) (by unfold rightBase; omega),
    assignBlock_before _ _ _ _ (start + n) (by unfold leftBase; omega)]
  simpa using assignBlock_inside (start + n) 1 side (assignBlock start n mid a) 0

theorem roundAssign_left (n start : ℕ) (a : CNF.Assignment) (mid : Vector n) (side : Vector 1)
    (left right : Vector n) : readVector n (leftBase n start) (roundAssign n start a mid side left right) = left := by
  funext i
  have hi := i.isLt
  simp only [readVector, roundAssign]
  rw [assignBlock_before _ _ _ _ (leftBase n start + i.val) (by unfold leftBase rightBase; omega),
    assignBlock_inside]

theorem roundAssign_right (n start : ℕ) (a : CNF.Assignment) (mid : Vector n) (side : Vector 1)
    (left right : Vector n) : readVector n (rightBase n start) (roundAssign n start a mid side left right) = right := by
  funext i
  exact assignBlock_inside _ _ _ _ i

def aligned (n start : ℕ) (x y : VectorFunction n) (a : CNF.Assignment) : Prop :=
  readVector n (leftBase n start) a = (if a (start + n) then x a else readVector n start a) ∧
    readVector n (rightBase n start) a = (if a (start + n) then readVector n start a else y a)

theorem aligned_round (n start : ℕ) (x y : VectorFunction n)
    (hx : ReadsBefore start x) (hy : ReadsBefore start y)
    (a : CNF.Assignment) (mid : Vector n) (side : Vector 1) (left right : Vector n) :
    aligned n start x y (roundAssign n start a mid side left right) ↔
      left = (if side 0 then x a else mid) ∧ right = (if side 0 then mid else y a) := by
  simp only [aligned, roundAssign_left, roundAssign_right, roundAssign_mid, roundAssign_side,
    hx _ _ (roundAssign_before n start a mid side left right),
    hy _ _ (roundAssign_before n start a mid side left right)]

theorem aligned_depends (n start : ℕ) (x y : VectorFunction n)
    (hx : ReadsBefore start x) (hy : ReadsBefore start y) :
    DependsBefore (start + width n) (aligned n start x y) := by
  intro a b hab
  have hx' := hx.mono (Nat.le_add_right start (width n)) a b hab
  have hy' := hy.mono (Nat.le_add_right start (width n)) a b hab
  have hm := readVector_before n start (start + width n) (by unfold width; omega) a b hab
  have hl := readVector_before n (leftBase n start) (start + width n) (by unfold width leftBase; omega) a b hab
  have hr := readVector_before n (rightBase n start) (start + width n) (by unfold width rightBase; omega) a b hab
  have hs := hab (start + n) (by unfold width; omega)
  simp only [aligned, hx', hy', hm, hl, hr, hs]

def roundPrefix (n : ℕ) : Prefix := [(false, n), (true, 1), (false, n), (false, n)]

def reachPrefix (n : ℕ) : ℕ → Prefix
  | 0 => []
  | d + 1 => roundPrefix n ++ reachPrefix n d

def condition (n : ℕ) (E : Vector n → Vector n → Prop) :
    ℕ → ℕ → VectorFunction n → VectorFunction n → CNF.Assignment → Prop
  | 0, _, x, y, a => x a = y a ∨ E (x a) (y a)
  | d + 1, start, x, y, a => aligned n start x y a ∧
      condition n E d (start + width n) (readVector n (leftBase n start)) (readVector n (rightBase n start)) a

theorem truth_round (n start : ℕ) (qs : Prefix) (P : CNF.Assignment → Prop) (a : CNF.Assignment) :
    Prefix.Truth P (roundPrefix n ++ qs) start a ↔
      ∃ mid : Vector n, ∀ side : Vector 1, ∃ left right : Vector n,
        Prefix.Truth P qs (start + width n) (roundAssign n start a mid side left right) := by
  simp only [roundPrefix, List.cons_append, List.nil_append, Prefix.Truth, quantify,
    Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
  have he1 : start + n + 1 + n = rightBase n start := by unfold rightBase; omega
  have he2 : rightBase n start + n = start + width n := by unfold width rightBase; omega
  simp only [roundAssign, leftBase, he1, he2]

theorem truth_condition (n d start : ℕ) (E : Vector n → Vector n → Prop)
    (x y : VectorFunction n) (hx : ReadsBefore start x) (hy : ReadsBefore start y) (a : CNF.Assignment) :
    Prefix.Truth (condition n E d start x y) (reachPrefix n d) start a ↔ Within E (2 ^ d) (x a) (y a) := by
  induction d generalizing start x y a with
  | zero => simp [reachPrefix, Prefix.Truth, condition, within_one]
  | succ d ih =>
    rw [reachPrefix, truth_round]
    have hleft : ReadsBefore (start + width n) (readVector n (leftBase n start)) :=
      readVector_before _ _ _ (by unfold width leftBase; omega)
    have hright : ReadsBefore (start + width n) (readVector n (rightBase n start)) :=
      readVector_before _ _ _ (by unfold width rightBase; omega)
    simp only [condition]
    simp_rw [Prefix.truth_guard _ _ _ _ _ (aligned_depends n start x y hx hy),
      aligned_round n start x y hx hy, ih _ _ _ hleft hright, roundAssign_left, roundAssign_right]
    rw [split_quantifiers, pow_succ, Nat.mul_two, path_splitting]

end Lax689614Proofs.Quantified.NumericReach
