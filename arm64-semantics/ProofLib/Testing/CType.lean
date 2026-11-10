/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.CType

/-!
# `c_type_spec` Regression Tests

Positive and negative (`#guard_msgs`) tests for `c_type_spec` lowering (`Arm64/Trusted/Surface/CType.lean`)
and the `#c_type_report` summary command (`ProofLib/CType.lean`), checking definitional (`rfl`)
equality between each valid `c_type_spec` and its hand-written `c_spec`.
-/

@[expose] public section

namespace Testing.CType

open Arm64 ProofLib Arm64.CType

structure Pair where
  a : BitVec 32
  b : BitVec 32

def pairAt (p : BitVec 64) (st : Pair) : SepProp := (p ↦₃₂ st.a) ∗ ((p + 4#64) ↦₃₂ st.b)

/-- Semantic type for a two-field `struct pair` with invariant `a ≤ b`. -/
def PairT : SemType Pair := { tyName := "struct pair", interp := pairAt, pureWf := fun _ st => st.a ≤ st.b }

/-! ## Lowering equivalence with hand-written `c_spec` -/

c_type_spec fooSpec (p : ptr) (s : ptr) (ghost bs : List (BitVec 8)) (n : u64) (ghost st : Pair) :
    (ret : u32) where
  c_arg p : MutRef PairT st ⇝ { st with a := st.b }
  c_arg s : ShrRef CStr bs
  c_arg n : Val SizeT
  c_ret : Val (StatusCode [0#32, 1#32])
  caveat [C_ARITH_BOUND] "len fits in int" : bs.length < 2 ^ 31
  caveat [API_RESTRICTION] "n must be nonzero" : n ≠ 0#64
  stack16

c_spec fooSpecRaw (p : ptr) (s : ptr) (ghost bs : List (BitVec 8)) (n : u64) (ghost st : Pair) :
    (ret : u32) where
  requires_cond PairT.pureWf p st ∧ CStr.pureWf s bs ∧ SizeT.valWf n ∧ bs.length < 2 ^ 31 ∧ n ≠ 0#64
  requires PairT.interp p st ∗ CStr.interp s bs
  ensures_pure PairT.pureWf p { st with a := st.b } ∧ (StatusCode [0#32, 1#32]).valWf ret
  ensures PairT.interp p { st with a := st.b } ∗ CStr.interp s bs
  stack16

example : fooSpec = fooSpecRaw := rfl

c_type_spec barSpec (p : ptr) (ghost st : Pair) : (ret : u32) where
  c_exists (st' : Pair)
  c_arg p : MutRef PairT st ⇝ st'
  ensures_pure ret = st'.a

c_spec barSpecRaw (p : ptr) (ghost st : Pair) : (ret : u32) where
  requires_cond PairT.pureWf p st
  requires PairT.interp p st
  ensures ∃∗ st' : Pair, ⌜PairT.pureWf p st' ∧ ret = st'.a⌝ ∗ PairT.interp p st'

example : barSpec = barSpecRaw := rfl

c_type_spec newSpec (ghost om : Option Pair) : (ret : u64) where
  c_ret : Own (OptOwn PairT) om
  caveat [PARTIAL_SPEC] "only the success path" : om.isSome

c_spec newSpecRaw (ghost om : Option Pair) : (ret : u64) where
  requires_cond om.isSome
  ensures_pure (OptOwn PairT).pureWf ret om
  ensures (OptOwn PairT).interp ret om

example : newSpec = newSpecRaw := rfl

c_type_spec initSpec (ctx R : SepProp) (p : ptr) (ghost st : Pair) where
  c_arg p : UninitSlot 8 ⇝ PairT st
  c_env R

c_spec initSpecRaw (ctx R : SepProp) (p : ptr) (ghost st : Pair) where
  requires memRegion p 8
  ensures_pure PairT.pureWf p st
  ensures PairT.interp p st
  preserves R

example : initSpec = initSpecRaw := rfl

c_type_spec freeSpec (p : ptr) (out : ptr) (ghost st : Pair) where
  c_arg p : Own PairT st
  c_arg out : OutPtr U32Cell st.a

c_spec freeSpecRaw (p : ptr) (out : ptr) (ghost st : Pair) where
  requires_cond PairT.pureWf p st
  requires PairT.interp p st ∗ memRegion out 8
  ensures outPtrPost U32Cell out st.a

example : freeSpec = freeSpecRaw := rfl

c_type_spec stackSpec (p : ptr) (ghost st : Pair) : (ret : u32) where
  c_exists (st' : Pair)
  c_arg p : MutRef PairT st ⇝ st'
  c_stack 48

c_spec stackSpecRaw (p : ptr) (ghost st : Pair) : (ret : u32) where
  requires_cond PairT.pureWf p st
  requires PairT.interp p st ∗ stackFrameAt s0.sp 48
  ensures ∃∗ st' : Pair, ⌜PairT.pureWf p st'⌝ ∗ PairT.interp p st' ∗ stackFrameAt sf.sp 48

example : stackSpec = stackSpecRaw := rfl

c_type_spec borrowRetSpec (p : ptr) (ghost st : Pair) : (ret : u64) where
  c_arg p : ShrRef PairT st
  c_ret : ShrRef (InteriorPtr "const uint32_t *") p

c_spec borrowRetSpecRaw (p : ptr) (ghost st : Pair) : (ret : u64) where
  requires_cond PairT.pureWf p st
  preserves PairT.interp p st
  ensures_pure (InteriorPtr "const uint32_t *").pureWf ret p

example : borrowRetSpec = borrowRetSpecRaw := rfl

c_type_spec fallibleSpec (p out slot : ptr) (ghost st : Pair) : (ret : u32) where
  c_arg p : MutRef (CondOwn PairT) (some st) ⇝ (if ret = 0#32 then none else some st)
  c_arg out : OutPtr (OutPtrOnOk PairT (ret = 0#32)) st
  c_arg slot : MutRef (OptOutPtr PairT) none ⇝ (if ret = 0#32 then some st else none)
  c_ret : Val (StatusCode [0#32, 1#32])

c_spec fallibleSpecRaw (p out slot : ptr) (ghost st : Pair) : (ret : u32) where
  requires_cond (CondOwn PairT).pureWf p (some st) ∧ (OptOutPtr PairT).pureWf slot none
  requires (CondOwn PairT).interp p (some st) ∗ memRegion out 8 ∗ (OptOutPtr PairT).interp slot none
  ensures_pure (CondOwn PairT).pureWf p (if ret = 0#32 then none else some st) ∧
               (OptOutPtr PairT).pureWf slot (if ret = 0#32 then some st else none) ∧
               (StatusCode [0#32, 1#32]).valWf ret
  ensures (CondOwn PairT).interp p (if ret = 0#32 then none else some st) ∗
          outPtrPost (OutPtrOnOk PairT (ret = 0#32)) out st ∗
          (OptOutPtr PairT).interp slot (if ret = 0#32 then some st else none)

example : fallibleSpec = fallibleSpecRaw := rfl

/-! ## Metadata and `#c_type_report` -/

/--
info: 8 c_type_spec(s); caveats — API_RESTRICTION: 1, CALLER_TYPESTATE: 0, C_ARITH_BOUND: 1, PARTIAL_SPEC: 1

| Spec | Typed parameters | Return | Caveats |
| :--- | :--- | :--- | :--- |
| `barSpec` | `p : MutRef PairT` | — | none |
| `borrowRetSpec` | `p : ShrRef PairT` | `ShrRef (InteriorPtr "const uint32_t *")` | none |
| `fallibleSpec` | `p : MutRef (CondOwn PairT)`, `out : OutPtr (OutPtrOnOk PairT (ret = 0#32))`, `slot : MutRef (OptOutPtr PairT)` | `Val (StatusCode [0#32, 1#32])` | none |
| `fooSpec` | `p : MutRef PairT`, `s : ShrRef CStr`, `n : Val SizeT` | `Val (StatusCode [0#32, 1#32])` | [C_ARITH_BOUND] len fits in int (`bs.length < 2 ^ 31`)<br>[API_RESTRICTION] n must be nonzero (`n ≠ 0#64`) |
| `freeSpec` | `p : Own PairT`, `out : OutPtr U32Cell` | — | none |
| `initSpec` | `p : UninitSlot 8 bytes ⇝ PairT` | — | none<br>env `R` |
| `newSpec` |  | `Own (OptOwn PairT)` | [PARTIAL_SPEC] only the success path (`om.isSome`) |
| `stackSpec` | `p : MutRef PairT` | — | none<br>env `stack frame: 48 bytes below sp` |
-/
#guard_msgs in
#c_type_report Testing.CType

/-! ## Rejected surface forms -/

/-- error: c_type_spec: register parameter 'n' has no `c_arg n : <Mode> <Type> ...` clause -/
#guard_msgs in
c_type_spec missingArg (p : ptr) (n : u64) (ghost st : Pair) where
  c_arg p : ShrRef PairT st

/--
error: c_type_spec: extra pure preconditions must be tagged `caveat [API_RESTRICTION|CALLER_TYPESTATE|C_ARITH_BOUND|PARTIAL_SPEC] "why" : P`
-/
#guard_msgs in
c_type_spec rawCond (p : ptr) (ghost st : Pair) where
  c_arg p : ShrRef PairT st
  requires_cond st.a = 0#32

/--
error: c_type_spec: use `c_arg x : ShrRef T m` for typed arguments or `c_env R` for environment resources instead of `preserves`
-/
#guard_msgs in
c_type_spec rawPreserves (p : ptr) (ghost st : Pair) where
  c_arg p : ShrRef PairT st
  preserves pairAt p st

/--
error: unknown caveat tag 'SOUNDNESS'; expected API_RESTRICTION, CALLER_TYPESTATE, C_ARITH_BOUND, or PARTIAL_SPEC
-/
#guard_msgs in
c_type_spec badTag (p : ptr) (ghost st : Pair) where
  c_arg p : ShrRef PairT st
  caveat [SOUNDNESS] "nope" : True

/-- error: c_ret requires a named return in the header, e.g. `: (ret : u64)` -/
#guard_msgs in
c_type_spec unnamedRet (ghost st : Pair) : u64 where
  c_ret : Val U64

/-- error: c_ret supports only `Own T m`, `ShrRef T m`, `MutRef T m`, and `Val T` (got 'OutPtr') -/
#guard_msgs in
c_type_spec badRetMode (ghost st : Pair) : (ret : u64) where
  c_ret : OutPtr PairT st

/-- error: c_type_spec: `c_arg q` does not name a register parameter of the header -/
#guard_msgs in
c_type_spec strayArg (p : ptr) (ghost st : Pair) where
  c_arg p : ShrRef PairT st
  c_arg q : ShrRef PairT st

/--
error: c_type_spec: value-only scalar type 'U64' has an empty spatial footprint (`emp`) and cannot be used with pointer mode 'MutRef'; use 'U64Cell' (e.g. `U32Cell`, `U64Cell`, `SizeTCell`) for memory cells or `Val U64` for register values
-/
#guard_msgs in
c_type_spec badScalarPtr (p : ptr) (ghost v0 v1 : BitVec 64) where
  c_arg p : MutRef U64 v0 ⇝ v1

/--
error: c_type_spec: value-only scalar type 'U32' has an empty spatial footprint (`emp`) and cannot be used with pointer mode 'OutPtr'; use 'U32Cell' (e.g. `U32Cell`, `U64Cell`, `SizeTCell`) for memory cells or `Val U32` for register values
-/
#guard_msgs in
c_type_spec badScalarOutPtr (out : ptr) (ghost v : BitVec 32) where
  c_arg out : OutPtr U32 v

c_type_spec cellMutSpec (p : ptr) (ghost v0 : BitVec 64) : (ok : bool) where
  c_exists (v1 : BitVec 64)
  c_arg p : MutRef U64Cell v0 ⇝ v1
  ensures_pure ok = true → v1 = v0 + 1#64

c_spec cellMutSpecRaw (p : ptr) (ghost v0 : BitVec 64) : (ok : bool) where
  requires_cond U64Cell.pureWf p v0
  requires U64Cell.interp p v0
  ensures ∃∗ v1 : BitVec 64, ⌜U64Cell.pureWf p v1 ∧ (ok = true → v1 = v0 + 1#64)⌝ ∗ U64Cell.interp p v1

example : cellMutSpec = cellMutSpecRaw := rfl

-- Under AAPCS64 a C `_Bool` return (`: (ok : bool)` / `: bool`) constrains the low 8 bits of `W0`
-- to the canonical values `{0#8, 1#8}` (`(sf.readReg32 .x0).truncate 8`), whereas `: (ok : bool32)` /
-- `: bool32` constrains all 32 bits of `W0` to `{0#32, 1#32}`.
c_spec bool8RetSpec : (ok : bool) where
  ensures_pure ok = true

c_spec bool32RetSpec : (ok : bool32) where
  ensures_pure ok = true

rust_spec rustBoolRetSpec : (ok : rust_bool) where
  ensures_pure ok = true

example : rustBoolRetSpec = bool32RetSpec := rfl

c_spec bool64RetSpec : (ok : bool64) where
  ensures_pure ok = true

example (s0 sf : State) :
    bool8RetSpec.post () s0 sf =
      ⌜(sf.readReg32 .x0).truncate 8 = (if (sf.readReg32 .x0).truncate 8 != 0#8 then 1#8 else 0#8) ∧
       ((sf.readReg32 .x0).truncate 8 != 0#8) = true⌝ := rfl

example (s0 sf : State) :
    bool32RetSpec.post () s0 sf =
      ⌜sf.readReg32 .x0 = (if sf.readReg32 .x0 != 0#32 then 1#32 else 0#32) ∧
       (sf.readReg32 .x0 != 0#32) = true⌝ := rfl

example (s0 sf : State) :
    bool64RetSpec.post () s0 sf =
      ⌜sf.readReg64 .x0 = (if sf.readReg64 .x0 != 0#64 then 1 else 0) ∧
       (sf.readReg64 .x0 != 0#64) = true⌝ := rfl

-- Non-canonical boolean return (`W0 = 2`) does not satisfy a `true` bool return
-- (`bool8RetSpec`, `bool32RetSpec`, or `bool64RetSpec`), reducing the postcondition to `⌜False⌝`.
example (s0 sf : State) (h : sf.readReg32 .x0 = 2#32) :
    bool8RetSpec.post () s0 sf = ⌜False⌝ := by
  simp [bool8RetSpec, h]

example (s0 sf : State) (h : sf.readReg32 .x0 = 2#32) :
    bool32RetSpec.post () s0 sf = ⌜False⌝ := by
  simp [bool32RetSpec, h]

-- Named `(ok : bool)` + `ensures_pure ok = b` and unnamed `: bool` + `returns b` are equivalent:
c_spec bool8NamedParamRetSpec (flag : bool) : (ok : bool) where
  ensures_pure ok = flag

c_spec bool8UnnamedParamRetSpec (flag : bool) : bool where
  returns flag

example (flag : Bool) (s0 : State) :
    bool8NamedParamRetSpec.pre flag s0 =
      ⌜(s0.readReg32 .x0).truncate 8 = if flag then 1#8 else 0#8⌝ := rfl

example (flag : Bool) (s0 sf : State) :
    bool8NamedParamRetSpec.post flag s0 sf =
      bool8UnnamedParamRetSpec.post flag s0 sf := by
  simp only [bool8NamedParamRetSpec, bool8UnnamedParamRetSpec]
  congr 1
  apply propext
  constructor
  · rintro ⟨hCanon, hEq⟩
    rw [hEq] at hCanon
    exact hCanon
  · intro hRet
    rw [hRet]
    cases flag <;> decide

-- When a callee returns `w0 = 0x100` (low 8 bits zero, bit 8 set), C `_Bool` (`bool`) reads
-- canonical `0#8` (`false`), while `bool32` rejects `0x100#32` as non-canonical:
#guard (((0x100#32).truncate 8 == 0#8) == true) && ((0x100#32 == 0#32 || 0x100#32 == 1#32) == false)

/--
error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  bool8RetSpec = bool32RetSpec

Note: The following definitions were not unfolded because their definition is not exposed:
  SepProp.pure ↦ 4
-/
#guard_msgs in
example : bool8RetSpec = bool32RetSpec := rfl

/-! ## `oom_when` and `on_oom` clauses -/

c_spec oomWhenCSpec (p : ptr) (ghost st : Pair)
  preserves pairAt p st
  oom_when  True

example (p : BitVec 64) (st : Pair) (s0 sf : State) :
    oomWhenCSpec.onOom (p, st) s0 sf = ⌜True⌝ := rfl

c_type_spec oomWhenTypeSpec (p : ptr) (ghost st : Pair) where
  c_arg p : ShrRef PairT st
  oom_when True

example (p : BitVec 64) (st : Pair) (s0 sf : State) :
    oomWhenTypeSpec.onOom (p, st) s0 sf = ⌜True⌝ := rfl

end Testing.CType
