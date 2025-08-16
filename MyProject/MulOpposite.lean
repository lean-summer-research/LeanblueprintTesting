import MyProject.GreensRelations

/-!
# Duality lemmas for Green's relations

This file develops `MulOpposite` duality for Green’s preorders, equivalences,
and equivalence classes. It also defines two *named simp sets*:

* `toOpp` — lemmas oriented to push statements **into** `MulOpposite`,
* `fromOpp` — lemmas oriented to pull statements **out of** `MulOpposite`.

Use them via `simp (attr := toOpp)` and `simp (attr := fromOpp)`.
-/

/-! ## Registration of simp sets -/

/-
ERROR: `toOpp` cannot be mutated, only variables declared using `let mut` can be mutated. If you did not intend to mutate but define `toOpp`, consider using `let toOpp` instead
We also see errors every time that a lemma is tagged with `toOpp` or `fromOpp`.
ALso, there is no longer a Green namespace so remove every `Green` prefixl.
-/
initialize toOpp : SimpAttr :=
  registerSimpAttr `toOpp "Rewrite lemmas that push into `MulOpposite`."
initialize fromOpp : SimpAttr :=
  registerSimpAttr `fromOpp "Rewrite lemmas that pull out of `MulOpposite`."

/-! ## Raw `op` arithmetic helpers -/

section RawMul

open MulOpposite

variable {M : Type*} [Monoid M] (x y z u : M)

theorem mul_eq_op_iff : op x * op y = op z ↔ y * x = z := by simp [← op_mul]

theorem op_eq_mul_iff : op x = op y * op z ↔ x = z * y := by simp [← op_mul]

theorem mul_mul_eq_op_iff : op x * op y * op z = op u ↔ z * y * x = u :=
  by simp [← op_mul, ← mul_assoc]

theorem op_eq_mul_mul_iff : op x = op y * op z * op u ↔ x = u * z * y :=
  by simp [← op_mul, ← mul_assoc]

end RawMul

/-! ## Duality for preorders and equivalences -/

section Duality

open MulOpposite

variable {M : Type*} [Monoid M] (x y : M)

/-! ### Iff lemmas (default orientation is “out of `op`”) -/

lemma RRel.op_iff : op x ≤𝓡 op y ↔ x ≤𝓛 y := by
  simp [RRel, LRel]

lemma LRel.op_iff : op x ≤𝓛 op y ↔ x ≤𝓡 y := by
  simp [Green.LRel, Green.RRel]

lemma JRel.op_iff : op x ≤𝓙 op y ↔ x ≤𝓙 y := by
  simp [Green.JRel, mul_assoc]

lemma HRel.op_iff : op x ≤𝓗 op y ↔ x ≤𝓗 y := by
  simp [Green.HRel, RRel.op_iff, LRel.op_iff, and_comm]

lemma REquiv.op_iff : op x 𝓡 op y ↔ x 𝓛 y := by
  simp [Green.REquiv, Green.LEquiv, RRel.op_iff]

lemma LEquiv.op_iff : op x 𝓛 op y ↔ x 𝓡 y := by
  simp [Green.LEquiv, Green.REquiv, LRel.op_iff]

lemma JEquiv.op_iff : op x 𝓙 op y ↔ x 𝓙 y := by
  simp [Green.JEquiv]

lemma HEquiv.op_iff : op x 𝓗 op y ↔ x 𝓗 y := by
  simp [Green.HEquiv]

/-! ### Orientation-specific copies in simp sets -/

-- preorders
@[toOpp] lemma toOpp_RRel : (x ≤𝓛 y) ↔ (op x ≤𝓡 op y) := (RRel.op_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_RRel : (op x ≤𝓡 op y) ↔ (x ≤𝓛 y) := RRel.op_iff (x:=x) (y:=y)

@[toOpp] lemma toOpp_LRel : (x ≤𝓡 y) ↔ (op x ≤𝓛 op y) := (LRel.op_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_LRel : (op x ≤𝓛 op y) ↔ (x ≤𝓡 y) := LRel.op_iff (x:=x) (y:=y)

@[toOpp] lemma toOpp_JRel : (x ≤𝓙 y) ↔ (op x ≤𝓙 op y) := (JRel.op_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_JRel : (op x ≤𝓙 op y) ↔ (x ≤𝓙 y) := JRel.op_iff (x:=x) (y:=y)

@[toOpp] lemma toOpp_HRel : (x ≤𝓗 y) ↔ (op x ≤𝓗 op y) := (HRel.op_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_HRel : (op x ≤𝓗 op y) ↔ (x ≤𝓗 y) := HRel.op_iff (x:=x) (y:=y)

-- equivalences
@[toOpp] lemma toOpp_REquiv : (x 𝓛 y) ↔ (op x 𝓡 op y) := (REquiv.op_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_REquiv : (op x 𝓡 op y) ↔ (x 𝓛 y) := REquiv.op_iff (x:=x) (y:=y)

@[toOpp] lemma toOpp_LEquiv : (x 𝓡 y) ↔ (op x 𝓛 op y) := (LEquiv.op_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_LEquiv : (op x 𝓛 op y) ↔ (x 𝓡 y) := LEquiv.op_iff (x:=x) (y:=y)

@[toOpp] lemma toOpp_JEquiv : (x 𝓙 y) ↔ (op x 𝓙 op y) := (JEquiv.op_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_JEquiv : (op x 𝓙 op y) ↔ (x 𝓙 y) := JEquiv.op_iff (x:=x) (y:=y)

@[toOpp] lemma toOpp_HEquiv : (x 𝓗 y) ↔ (op x 𝓗 op y) := (HEquiv.op_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_HEquiv : (op x 𝓗 op y) ↔ (x 𝓗 y) := HEquiv.op_iff (x:=x) (y:=y)

end Duality

/-! ## Duality for equivalence classes and `𝓓` -/

section ClassesAndD

open MulOpposite
variable {M : Type*} [Monoid M] (x y : M)

/-- Class membership duality for `𝓡`. -/
theorem REquiv.op_mem_set_iff :
    op x ∈ ⟦op y⟧𝓡 ↔ x ∈ ⟦y⟧𝓛 := by
  simp [Green.REquiv.set, Green.LEquiv.set, REquiv.op_iff]

/-- Class membership duality for `𝓛`. -/
theorem LEquiv.op_mem_set_iff :
    op x ∈ ⟦op y⟧𝓛 ↔ x ∈ ⟦y⟧𝓡 := by
  simp [Green.LEquiv.set, Green.REquiv.set, LEquiv.op_iff]

/-- Class membership duality for `𝓙`. -/
theorem JEquiv.op_mem_set_iff :
    op x ∈ ⟦op y⟧𝓙 ↔ x ∈ ⟦y⟧𝓙 := by
  simp [Green.JEquiv.set, JEquiv.op_iff]

/-- Class membership duality for `𝓗`. -/
theorem HEquiv.op_mem_set_iff :
    op x ∈ ⟦op y⟧𝓗 ↔ x ∈ ⟦y⟧𝓗 := by
  simp [Green.HEquiv.set, HEquiv.op_iff]

/-- `𝓓` duality. -/
theorem DEquiv.op_iff :
    op x 𝓓 op y ↔ x 𝓓 y := by
  constructor
  · intro h
    rcases h with ⟨z, hR, hL⟩
    -- hR : op x 𝓡 op z  ≃  x 𝓛 z ;  hL : op z 𝓛 op y  ≃  z 𝓡 y
    have hxz : x 𝓛 z := (REquiv.op_iff (x:=x) (y:=z)).1 hR
    have hzy : z 𝓡 y := (LEquiv.op_iff (x:=z) (y:=y)).1 hL
    -- reorder to witness `x 𝓡 ?` and `? 𝓛 y` using symmetry
    exact ⟨z, LEquiv.symm hxz, REquiv.symm hzy⟩
  · intro h
    rcases h with ⟨z, hR, hL⟩
    have hxz : op x 𝓡 op z := (REquiv.op_iff (x:=x) (y:=z)).2 (LEquiv.symm hL)
    have hzy : op z 𝓛 op y := (LEquiv.op_iff (x:=z) (y:=y)).2 (REquiv.symm hR)
    exact ⟨z, hxz, hzy⟩

/-! ### Orientation-specific copies for the simp sets -/

@[toOpp] lemma toOpp_RClass :
    (x ∈ ⟦y⟧𝓛) ↔ (op x ∈ ⟦op y⟧𝓡) := (REquiv.op_mem_set_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_RClass :
    (op x ∈ ⟦op y⟧𝓡) ↔ (x ∈ ⟦y⟧𝓛) := REquiv.op_mem_set_iff (x:=x) (y:=y)

@[toOpp] lemma toOpp_LClass :
    (x ∈ ⟦y⟧𝓡) ↔ (op x ∈ ⟦op y⟧𝓛) := (LEquiv.op_mem_set_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_LClass :
    (op x ∈ ⟦op y⟧𝓛) ↔ (x ∈ ⟦y⟧𝓡) := LEquiv.op_mem_set_iff (x:=x) (y:=y)

@[toOpp] lemma toOpp_JClass :
    (x ∈ ⟦y⟧𝓙) ↔ (op x ∈ ⟦op y⟧𝓙) := (JEquiv.op_mem_set_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_JClass :
    (op x ∈ ⟦op y⟧𝓙) ↔ (x ∈ ⟦y⟧𝓙) := JEquiv.op_mem_set_iff (x:=x) (y:=y)

@[toOpp] lemma toOpp_HClass :
    (x ∈ ⟦y⟧𝓗) ↔ (op x ∈ ⟦op y⟧𝓗) := (HEquiv.op_mem_set_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_HClass :
    (op x ∈ ⟦op y⟧𝓗) ↔ (x ∈ ⟦y⟧𝓗) := HEquiv.op_mem_set_iff (x:=x) (y:=y)

@[toOpp] lemma toOpp_DEquiv : (x 𝓓 y) ↔ (op x 𝓓 op y) := (DEquiv.op_iff (x:=x) (y:=y)).symm
@[fromOpp] lemma fromOpp_DEquiv : (op x 𝓓 op y) ↔ (x 𝓓 y) := DEquiv.op_iff (x:=x) (y:=y)

end ClassesAndD

end Green
