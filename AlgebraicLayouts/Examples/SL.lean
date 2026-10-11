/-
  A semantic separation-logic backend and the β-law for `sll`.

  Checked against the repo at commit aa790de ("Abs") plus the uncommitted
  Abs.lean (Lean 4.35.0-rc4, relaxedAutoImplicit = false), by concatenating
  the modules. `#print axioms SL.sll_beta`: propext, Quot.sound.

  Design (design-decisions entries 14 and 17):
  - assertions are predicates over an owned heap and the global memory
    (`Asn := Heap → Mem → Prop`); `*` is the lifted disjoint union, so `Asn`
    with `sep`/`emp` is a total commutative monoid (a degenerate PCM);
  - `pointsTo` owns one cell, never at null, and agrees with memory;
  - `read` is a pure fact about memory (empty owned heap);
  - `≡` is "same models".
  Semantic `P` means every continuation is extensional automatically.
-/

import AlgebraicLayouts.Abs

/-! ## A semantic separation-logic backend -/

namespace SL

abbrev Loc := Nat            -- 0 is null

inductive HVal where
  | int (v : Int)
  | loc (l : Loc)

abbrev Heap := Loc → Option HVal
abbrev Mem := Loc → Option HVal

def Heap.empty : Heap := fun _ => none
def Heap.single (l : Loc) (v : HVal) : Heap := fun l' => if l' = l then some v else none
def Heap.Disjoint (h₁ h₂ : Heap) : Prop := ∀ l, h₁ l = none ∨ h₂ l = none
def Heap.union (h₁ h₂ : Heap) : Heap := fun l => (h₁ l).or (h₂ l)

/-- Assertions: predicates over an owned heap and the global memory. -/
abbrev Asn := Heap → Mem → Prop

def sep (p q : Asn) : Asn := fun h m =>
  ∃ h₁ h₂, Heap.Disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ p h₁ m ∧ q h₂ m
def emp : Asn := fun h _ => h = Heap.empty
def pure (φ : Prop) : Asn := fun h _ => φ ∧ h = Heap.empty
/-- Owned cell; never at null; agrees with the global memory. -/
def pointsTo (l : Loc) (v : HVal) : Asn := fun h m =>
  l ≠ 0 ∧ h = Heap.single l v ∧ m l = some v
/-- Pure read of the global memory. -/
def read (l : Loc) (v : HVal) : Asn := fun h m => m l = some v ∧ h = Heap.empty
def ex {α : Type} (f : α → Asn) : Asn := fun h m => ∃ a, f a h m
def or (p q : Asn) : Asn := fun h m => p h m ∨ q h m

/-- Same models. -/
def Equiv (p q : Asn) : Prop := ∀ h m, p h m ↔ q h m
infix:50 " ≡ " => Equiv

instance : Backend Asn where
  Val b := b.interp
  const v := v
  add x y := (x + y : Int)
  eq x y := decide ((x : Int) = y)
  cond b p q := if (b : Bool) then p else q
  unit := emp
  op := sep

theorem Heap.union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by
  funext l; simp [Heap.union, Heap.empty]

/-- A pure fact on the left of `*` is just a conjunct. -/
theorem sep_pure (φ : Prop) (q : Asn) (h : Heap) (m : Mem) :
    sep (pure φ) q h m ↔ φ ∧ q h m := by
  constructor
  · rintro ⟨h₁, h₂, -, rfl, ⟨hφ, rfl⟩, hq⟩
    exact ⟨hφ, by rwa [Heap.union_empty_left]⟩
  · rintro ⟨hφ, hq⟩
    exact ⟨Heap.empty, h, fun _ => Or.inl rfl, (Heap.union_empty_left h).symm, ⟨hφ, rfl⟩, hq⟩

/-! ## The `sll` layout in this backend -/

abbrev Layer := intList.layer Asn (ULift Loc)

def sllClose (u : Layer) (k : Loc → Asn) : Asn :=
  match u with
  | .inl _ => ex fun d => sep (pure (d = 0)) (k d)
  | .inr (hd, tl) => ex fun d =>
      sep (sep (pointsTo d (.int hd.down)) (pointsTo (d + 1) (.loc tl.down))) (k d)

def sllOpen (k : Layer → Asn) (d : Loc) : Asn :=
  or (sep (pure (d = 0)) (k (.inl ⟨()⟩)))
     (ex fun (v : Int) => ex fun (t : Loc) =>
        sep (pure (d ≠ 0)) (sep (read d (.int v)) (sep (read (d + 1) (.loc t))
          (k (.inr (⟨v⟩, ⟨t⟩))))))

def sll : SemLayout Asn intList where
  Rep := Loc
  dict := { close_ := sllClose, open_ := sllOpen }


/-- A read on the left of `*` is a fact about memory. -/
theorem sep_read (l : Loc) (v : HVal) (q : Asn) (h : Heap) (m : Mem) :
    sep (read l v) q h m ↔ m l = some v ∧ q h m := by
  constructor
  · rintro ⟨h₁, h₂, -, rfl, ⟨hv, rfl⟩, hq⟩
    exact ⟨hv, by rwa [Heap.union_empty_left]⟩
  · rintro ⟨hv, hq⟩
    exact ⟨Heap.empty, h, fun _ => Or.inl rfl, (Heap.union_empty_left h).symm, ⟨hv, rfl⟩, hq⟩

/-- Opening a handle whose cells (in memory) hold `hd` and `tl`. -/
theorem sllOpen_cons {k : Layer → Asn} {d : Loc} {hd : Int} {tl : Loc} {h : Heap} {m : Mem}
    (hd0 : d ≠ 0) (hm₁ : m d = some (.int hd)) (hm₂ : m (d + 1) = some (.loc tl)) :
    sllOpen k d h m ↔ k (.inr (⟨hd⟩, ⟨tl⟩)) h m := by
  simp only [sllOpen, or, ex, sep_pure, sep_read]
  constructor
  · rintro (⟨h0, -⟩ | ⟨v, t, -, hv, ht, hk⟩)
    · exact absurd h0 hd0
    · rw [hm₁] at hv; rw [hm₂] at ht
      cases hv; cases ht; exact hk
  · intro hk
    exact Or.inr ⟨hd, tl, hd0, hm₁, hm₂, hk⟩

/-- **β for `sll`**: opening what you just built gives back the layer
(the footprint is kept on both sides). -/
theorem sll_beta (u : Layer) (k : Layer → Asn) :
    sllClose u (sllOpen k) ≡ sllClose u (fun _ => k u) := by
  intro h m
  match u with
  | .inl x =>
    cases x with | up x =>
    cases x
    simp only [sllClose, ex, sep_pure]
    constructor
    · rintro ⟨d, rfl, ho⟩
      refine ⟨0, rfl, ?_⟩
      simp only [sllOpen, or, ex, sep_pure] at ho
      rcases ho with ⟨-, hk⟩ | ⟨_, _, hne, -⟩
      · exact hk
      · exact absurd rfl hne
    · rintro ⟨d, rfl, hk⟩
      refine ⟨0, rfl, ?_⟩
      simp only [sllOpen, or, sep_pure]
      exact Or.inl ⟨trivial, hk⟩
  | .inr (hd, tl) =>
    simp only [sllClose, ex]
    apply exists_congr; intro d
    constructor
    · rintro ⟨h₁, h₂, hdisj, rfl, hA, ho⟩
      obtain ⟨-, -, -, -, ⟨hd0, -, hm₁⟩, ⟨-, -, hm₂⟩⟩ := id hA
      exact ⟨h₁, h₂, hdisj, rfl, hA, (sllOpen_cons hd0 hm₁ hm₂).1 ho⟩
    · rintro ⟨h₁, h₂, hdisj, rfl, hA, hk⟩
      obtain ⟨-, -, -, -, ⟨hd0, -, hm₁⟩, ⟨-, -, hm₂⟩⟩ := id hA
      exact ⟨h₁, h₂, hdisj, rfl, hA, (sllOpen_cons hd0 hm₁ hm₂).2 hk⟩

end SL
