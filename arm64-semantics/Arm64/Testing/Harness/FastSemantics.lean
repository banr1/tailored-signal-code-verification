/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.ISA.Eval
public import Arm64.Trusted.Process
public import ProofLib.Process

/-!
# Verified Unboxed Fast Semantics

Defines unboxed `UInt64`/`UInt32` register and architectural state representations (`FastRegs`,
`FastVRegs`, `FastState`) and an instruction evaluator with `@[simp]` refinement theorems to
`Arm64.State` and `execInst`.
-/

@[expose] public section

namespace Arm64.Fast

open Arm64

/-! ## Finite `BitVec 5` Exhaustion -/

/-- Exhaustive case analysis over all 32 values of `BitVec 5`, proved once via `omega` so
    subsequent register-file theorems close by 32-way `rfl`. -/
theorem forall_bv5 {P : BitVec 5 → Prop}
    (h0  : P 0#5)  (h1  : P 1#5)  (h2  : P 2#5)  (h3  : P 3#5)
    (h4  : P 4#5)  (h5  : P 5#5)  (h6  : P 6#5)  (h7  : P 7#5)
    (h8  : P 8#5)  (h9  : P 9#5)  (h10 : P 10#5) (h11 : P 11#5)
    (h12 : P 12#5) (h13 : P 13#5) (h14 : P 14#5) (h15 : P 15#5)
    (h16 : P 16#5) (h17 : P 17#5) (h18 : P 18#5) (h19 : P 19#5)
    (h20 : P 20#5) (h21 : P 21#5) (h22 : P 22#5) (h23 : P 23#5)
    (h24 : P 24#5) (h25 : P 25#5) (h26 : P 26#5) (h27 : P 27#5)
    (h28 : P 28#5) (h29 : P 29#5) (h30 : P 30#5) (h31 : P 31#5) :
    ∀ (i : BitVec 5), P i := by
  intro ⟨⟨i, hi⟩⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
         i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
         i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
         i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h24
  · exact h25
  · exact h26
  · exact h27
  · exact h28
  · exact h29
  · exact h30
  · exact h31

/-! ## Unboxed General-Purpose Register File -/

/-- Unboxed 32-slot general-purpose register file (256 scalar bytes, 0 pointer fields). -/
structure FastRegs where
  r0  : UInt64 := 0
  r1  : UInt64 := 0
  r2  : UInt64 := 0
  r3  : UInt64 := 0
  r4  : UInt64 := 0
  r5  : UInt64 := 0
  r6  : UInt64 := 0
  r7  : UInt64 := 0
  r8  : UInt64 := 0
  r9  : UInt64 := 0
  r10 : UInt64 := 0
  r11 : UInt64 := 0
  r12 : UInt64 := 0
  r13 : UInt64 := 0
  r14 : UInt64 := 0
  r15 : UInt64 := 0
  r16 : UInt64 := 0
  r17 : UInt64 := 0
  r18 : UInt64 := 0
  r19 : UInt64 := 0
  r20 : UInt64 := 0
  r21 : UInt64 := 0
  r22 : UInt64 := 0
  r23 : UInt64 := 0
  r24 : UInt64 := 0
  r25 : UInt64 := 0
  r26 : UInt64 := 0
  r27 : UInt64 := 0
  r28 : UInt64 := 0
  r29 : UInt64 := 0
  r30 : UInt64 := 0
  r31 : UInt64 := 0
  deriving Inhabited, DecidableEq, Repr

namespace FastRegs

/-- Read slot `idx` via a balanced 5-level binary tree (5 scalar comparisons at runtime). -/
def read (fr : FastRegs) (idx : BitVec 5) : UInt64 :=
  if idx.ult 16#5 then
    if idx.ult 8#5 then
      if idx.ult 4#5 then
        if idx.ult 2#5 then
          if idx.ult 1#5 then fr.r0 else fr.r1
        else
          if idx == 2#5 then fr.r2 else fr.r3
      else
        if idx.ult 6#5 then
          if idx == 4#5 then fr.r4 else fr.r5
        else
          if idx == 6#5 then fr.r6 else fr.r7
    else
      if idx.ult 12#5 then
        if idx.ult 10#5 then
          if idx == 8#5 then fr.r8 else fr.r9
        else
          if idx == 10#5 then fr.r10 else fr.r11
      else
        if idx.ult 14#5 then
          if idx == 12#5 then fr.r12 else fr.r13
        else
          if idx == 14#5 then fr.r14 else fr.r15
  else
    if idx.ult 24#5 then
      if idx.ult 20#5 then
        if idx.ult 18#5 then
          if idx == 16#5 then fr.r16 else fr.r17
        else
          if idx == 18#5 then fr.r18 else fr.r19
      else
        if idx.ult 22#5 then
          if idx == 20#5 then fr.r20 else fr.r21
        else
          if idx == 22#5 then fr.r22 else fr.r23
    else
      if idx.ult 28#5 then
        if idx.ult 26#5 then
          if idx == 24#5 then fr.r24 else fr.r25
        else
          if idx == 26#5 then fr.r26 else fr.r27
      else
        if idx.ult 30#5 then
          if idx == 28#5 then fr.r28 else fr.r29
        else
          if idx == 30#5 then fr.r30 else fr.r31

/-- Write slot `idx` via a balanced 5-level binary tree (in-place when `fr` has RC=1). -/
def write (fr : FastRegs) (idx : BitVec 5) (v : UInt64) : FastRegs :=
  if idx.ult 16#5 then
    if idx.ult 8#5 then
      if idx.ult 4#5 then
        if idx.ult 2#5 then
          if idx.ult 1#5 then { fr with r0 := v } else { fr with r1 := v }
        else
          if idx == 2#5 then { fr with r2 := v } else { fr with r3 := v }
      else
        if idx.ult 6#5 then
          if idx == 4#5 then { fr with r4 := v } else { fr with r5 := v }
        else
          if idx == 6#5 then { fr with r6 := v } else { fr with r7 := v }
    else
      if idx.ult 12#5 then
        if idx.ult 10#5 then
          if idx == 8#5 then { fr with r8 := v } else { fr with r9 := v }
        else
          if idx == 10#5 then { fr with r10 := v } else { fr with r11 := v }
      else
        if idx.ult 14#5 then
          if idx == 12#5 then { fr with r12 := v } else { fr with r13 := v }
        else
          if idx == 14#5 then { fr with r14 := v } else { fr with r15 := v }
  else
    if idx.ult 24#5 then
      if idx.ult 20#5 then
        if idx.ult 18#5 then
          if idx == 16#5 then { fr with r16 := v } else { fr with r17 := v }
        else
          if idx == 18#5 then { fr with r18 := v } else { fr with r19 := v }
      else
        if idx.ult 22#5 then
          if idx == 20#5 then { fr with r20 := v } else { fr with r21 := v }
        else
          if idx == 22#5 then { fr with r22 := v } else { fr with r23 := v }
    else
      if idx.ult 28#5 then
        if idx.ult 26#5 then
          if idx == 24#5 then { fr with r24 := v } else { fr with r25 := v }
        else
          if idx == 26#5 then { fr with r26 := v } else { fr with r27 := v }
      else
        if idx.ult 30#5 then
          if idx == 28#5 then { fr with r28 := v } else { fr with r29 := v }
        else
          if idx == 30#5 then { fr with r30 := v } else { fr with r31 := v }

/-- Lift a trusted `RegFile` into `FastRegs` (unboxing each `BitVec 64` via `UInt64.ofBitVec`). -/
@[inline] def ofRegFile (rf : RegFile) : FastRegs :=
  { r0  := ⟨rf.regs 0#5⟩,  r1  := ⟨rf.regs 1#5⟩,  r2  := ⟨rf.regs 2#5⟩,  r3  := ⟨rf.regs 3#5⟩
    r4  := ⟨rf.regs 4#5⟩,  r5  := ⟨rf.regs 5#5⟩,  r6  := ⟨rf.regs 6#5⟩,  r7  := ⟨rf.regs 7#5⟩
    r8  := ⟨rf.regs 8#5⟩,  r9  := ⟨rf.regs 9#5⟩,  r10 := ⟨rf.regs 10#5⟩, r11 := ⟨rf.regs 11#5⟩
    r12 := ⟨rf.regs 12#5⟩, r13 := ⟨rf.regs 13#5⟩, r14 := ⟨rf.regs 14#5⟩, r15 := ⟨rf.regs 15#5⟩
    r16 := ⟨rf.regs 16#5⟩, r17 := ⟨rf.regs 17#5⟩, r18 := ⟨rf.regs 18#5⟩, r19 := ⟨rf.regs 19#5⟩
    r20 := ⟨rf.regs 20#5⟩, r21 := ⟨rf.regs 21#5⟩, r22 := ⟨rf.regs 22#5⟩, r23 := ⟨rf.regs 23#5⟩
    r24 := ⟨rf.regs 24#5⟩, r25 := ⟨rf.regs 25#5⟩, r26 := ⟨rf.regs 26#5⟩, r27 := ⟨rf.regs 27#5⟩
    r28 := ⟨rf.regs 28#5⟩, r29 := ⟨rf.regs 29#5⟩, r30 := ⟨rf.regs 30#5⟩, r31 := ⟨rf.regs 31#5⟩ }

/-- Project `FastRegs` back to the trusted `RegFile`. -/
def toRegFile (fr : FastRegs) : RegFile :=
  ⟨fun idx => (fr.read idx).toBitVec⟩

@[simp] theorem toRegFile_read (fr : FastRegs) (idx : BitVec 5) :
    fr.toRegFile.read idx = (fr.read idx).toBitVec := rfl

@[simp] theorem toRegFile_regs (fr : FastRegs) (idx : BitVec 5) :
    fr.toRegFile.regs idx = (fr.read idx).toBitVec := rfl

@[simp] theorem toRegFile_ofRegFile (rf : RegFile) :
    (ofRegFile rf).toRegFile = rf := by
  apply RegFile.ext
  funext idx
  revert idx
  exact forall_bv5 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                   rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

@[simp] theorem read_write (fr : FastRegs) (idx i : BitVec 5) (v : UInt64) :
    (fr.write idx v).read i = if i = idx then v else fr.read i := by
  revert i idx
  refine forall_bv5 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact forall_bv5 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                     rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

@[simp] theorem toRegFile_write (fr : FastRegs) (idx : BitVec 5) (v : UInt64) :
    (fr.write idx v).toRegFile = fr.toRegFile.write idx v.toBitVec := by
  apply RegFile.ext
  funext i
  simp only [toRegFile_regs, RegFile.write, read_write]
  split <;> rfl

end FastRegs

/-! ## Flat Vector Register File -/

/-- Flat 32-slot 128-bit vector register file (in-place mutation when RC=1, zero closures). -/
structure FastVRegs where
  v0  : BitVec 128 := 0#128
  v1  : BitVec 128 := 0#128
  v2  : BitVec 128 := 0#128
  v3  : BitVec 128 := 0#128
  v4  : BitVec 128 := 0#128
  v5  : BitVec 128 := 0#128
  v6  : BitVec 128 := 0#128
  v7  : BitVec 128 := 0#128
  v8  : BitVec 128 := 0#128
  v9  : BitVec 128 := 0#128
  v10 : BitVec 128 := 0#128
  v11 : BitVec 128 := 0#128
  v12 : BitVec 128 := 0#128
  v13 : BitVec 128 := 0#128
  v14 : BitVec 128 := 0#128
  v15 : BitVec 128 := 0#128
  v16 : BitVec 128 := 0#128
  v17 : BitVec 128 := 0#128
  v18 : BitVec 128 := 0#128
  v19 : BitVec 128 := 0#128
  v20 : BitVec 128 := 0#128
  v21 : BitVec 128 := 0#128
  v22 : BitVec 128 := 0#128
  v23 : BitVec 128 := 0#128
  v24 : BitVec 128 := 0#128
  v25 : BitVec 128 := 0#128
  v26 : BitVec 128 := 0#128
  v27 : BitVec 128 := 0#128
  v28 : BitVec 128 := 0#128
  v29 : BitVec 128 := 0#128
  v30 : BitVec 128 := 0#128
  v31 : BitVec 128 := 0#128
  deriving Inhabited, DecidableEq, Repr

namespace FastVRegs

/-- Read vector slot `idx` via a balanced 5-level binary tree. -/
def read (fv : FastVRegs) (idx : BitVec 5) : BitVec 128 :=
  if idx.ult 16#5 then
    if idx.ult 8#5 then
      if idx.ult 4#5 then
        if idx.ult 2#5 then
          if idx.ult 1#5 then fv.v0 else fv.v1
        else
          if idx == 2#5 then fv.v2 else fv.v3
      else
        if idx.ult 6#5 then
          if idx == 4#5 then fv.v4 else fv.v5
        else
          if idx == 6#5 then fv.v6 else fv.v7
    else
      if idx.ult 12#5 then
        if idx.ult 10#5 then
          if idx == 8#5 then fv.v8 else fv.v9
        else
          if idx == 10#5 then fv.v10 else fv.v11
      else
        if idx.ult 14#5 then
          if idx == 12#5 then fv.v12 else fv.v13
        else
          if idx == 14#5 then fv.v14 else fv.v15
  else
    if idx.ult 24#5 then
      if idx.ult 20#5 then
        if idx.ult 18#5 then
          if idx == 16#5 then fv.v16 else fv.v17
        else
          if idx == 18#5 then fv.v18 else fv.v19
      else
        if idx.ult 22#5 then
          if idx == 20#5 then fv.v20 else fv.v21
        else
          if idx == 22#5 then fv.v22 else fv.v23
    else
      if idx.ult 28#5 then
        if idx.ult 26#5 then
          if idx == 24#5 then fv.v24 else fv.v25
        else
          if idx == 26#5 then fv.v26 else fv.v27
      else
        if idx.ult 30#5 then
          if idx == 28#5 then fv.v28 else fv.v29
        else
          if idx == 30#5 then fv.v30 else fv.v31

/-- Write vector slot `idx` via a balanced 5-level binary tree (in-place when `fv` has RC=1). -/
def write (fv : FastVRegs) (idx : BitVec 5) (v : BitVec 128) : FastVRegs :=
  if idx.ult 16#5 then
    if idx.ult 8#5 then
      if idx.ult 4#5 then
        if idx.ult 2#5 then
          if idx.ult 1#5 then { fv with v0 := v } else { fv with v1 := v }
        else
          if idx == 2#5 then { fv with v2 := v } else { fv with v3 := v }
      else
        if idx.ult 6#5 then
          if idx == 4#5 then { fv with v4 := v } else { fv with v5 := v }
        else
          if idx == 6#5 then { fv with v6 := v } else { fv with v7 := v }
    else
      if idx.ult 12#5 then
        if idx.ult 10#5 then
          if idx == 8#5 then { fv with v8 := v } else { fv with v9 := v }
        else
          if idx == 10#5 then { fv with v10 := v } else { fv with v11 := v }
      else
        if idx.ult 14#5 then
          if idx == 12#5 then { fv with v12 := v } else { fv with v13 := v }
        else
          if idx == 14#5 then { fv with v14 := v } else { fv with v15 := v }
  else
    if idx.ult 24#5 then
      if idx.ult 20#5 then
        if idx.ult 18#5 then
          if idx == 16#5 then { fv with v16 := v } else { fv with v17 := v }
        else
          if idx == 18#5 then { fv with v18 := v } else { fv with v19 := v }
      else
        if idx.ult 22#5 then
          if idx == 20#5 then { fv with v20 := v } else { fv with v21 := v }
        else
          if idx == 22#5 then { fv with v22 := v } else { fv with v23 := v }
    else
      if idx.ult 28#5 then
        if idx.ult 26#5 then
          if idx == 24#5 then { fv with v24 := v } else { fv with v25 := v }
        else
          if idx == 26#5 then { fv with v26 := v } else { fv with v27 := v }
      else
        if idx.ult 30#5 then
          if idx == 28#5 then { fv with v28 := v } else { fv with v29 := v }
        else
          if idx == 30#5 then { fv with v30 := v } else { fv with v31 := v }

/-- Lift a trusted `VRegFile` into `FastVRegs`. -/
@[inline] def ofVRegFile (vf : VRegFile) : FastVRegs :=
  { v0  := vf.regs 0#5,  v1  := vf.regs 1#5,  v2  := vf.regs 2#5,  v3  := vf.regs 3#5
    v4  := vf.regs 4#5,  v5  := vf.regs 5#5,  v6  := vf.regs 6#5,  v7  := vf.regs 7#5
    v8  := vf.regs 8#5,  v9  := vf.regs 9#5,  v10 := vf.regs 10#5, v11 := vf.regs 11#5
    v12 := vf.regs 12#5, v13 := vf.regs 13#5, v14 := vf.regs 14#5, v15 := vf.regs 15#5
    v16 := vf.regs 16#5, v17 := vf.regs 17#5, v18 := vf.regs 18#5, v19 := vf.regs 19#5
    v20 := vf.regs 20#5, v21 := vf.regs 21#5, v22 := vf.regs 22#5, v23 := vf.regs 23#5
    v24 := vf.regs 24#5, v25 := vf.regs 25#5, v26 := vf.regs 26#5, v27 := vf.regs 27#5
    v28 := vf.regs 28#5, v29 := vf.regs 29#5, v30 := vf.regs 30#5, v31 := vf.regs 31#5 }

/-- Project `FastVRegs` back to the trusted `VRegFile`. -/
def toVRegFile (fv : FastVRegs) : VRegFile :=
  ⟨fun idx => fv.read idx⟩

@[simp] theorem toVRegFile_read (fv : FastVRegs) (idx : BitVec 5) :
    fv.toVRegFile.read idx = fv.read idx := rfl

@[simp] theorem toVRegFile_regs (fv : FastVRegs) (idx : BitVec 5) :
    fv.toVRegFile.regs idx = fv.read idx := rfl

@[simp] theorem toVRegFile_ofVRegFile (vf : VRegFile) :
    (ofVRegFile vf).toVRegFile = vf := by
  apply VRegFile.ext
  funext idx
  revert idx
  exact forall_bv5 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                   rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

@[simp] theorem read_write (fv : FastVRegs) (idx i : BitVec 5) (v : BitVec 128) :
    (fv.write idx v).read i = if i = idx then v else fv.read i := by
  revert i idx
  refine forall_bv5 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact forall_bv5 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                     rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

@[simp] theorem toVRegFile_write (fv : FastVRegs) (idx : BitVec 5) (v : BitVec 128) :
    (fv.write idx v).toVRegFile = fv.toVRegFile.write idx v := by
  apply VRegFile.ext
  funext i
  simp only [toVRegFile_regs, VRegFile.write, read_write]

end FastVRegs

/-! ## `UInt64` and `UInt32` Bit-Vector Bridges -/

@[simp] theorem UInt64.toBitVec_ofBitVec (b : BitVec 64) :
    (UInt64.ofBitVec b).toBitVec = b := rfl

@[simp] theorem UInt32.toBitVec_ofBitVec (b : BitVec 32) :
    (UInt32.ofBitVec b).toBitVec = b := rfl

@[simp] theorem UInt64.toBitVec_toUInt32 (x : UInt64) :
    x.toUInt32.toBitVec = x.toBitVec.truncate 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [UInt64.toUInt32, UInt32.ofNat]

@[simp] theorem UInt32.toBitVec_toUInt64 (x : UInt32) :
    x.toUInt64.toBitVec = x.toBitVec.zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

@[simp] theorem BitVec.mask32_eq_zeroExtend_truncate (b : BitVec 64) :
    (b &&& 0xffffffff#64) = (b.truncate 32).zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and, BitVec.toNat_setWidth, Nat.and_two_pow_sub_one_eq_mod _ 32]
  omega

@[simp] theorem UInt64.beq_toBitVec (a b : UInt64) :
    (a.toBitVec == b.toBitVec) = (a == b) := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  simp [BEq.beq]

@[simp] theorem UInt32.beq_toBitVec (a b : UInt32) :
    (a.toBitVec == b.toBitVec) = (a == b) := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  simp [BEq.beq]

@[inline] def uint64Msb (x : UInt64) : Bool :=
  decide (0x8000000000000000 ≤ x)

@[inline] def uint32Msb (x : UInt32) : Bool :=
  decide (0x80000000 ≤ x)

@[simp] theorem uint64Msb_eq (x : UInt64) :
    uint64Msb x = x.toBitVec.msb := by
  simp [uint64Msb, BitVec.msb_eq_toNat, UInt64.le_iff_toNat_le]

@[simp] theorem uint32Msb_eq (x : UInt32) :
    uint32Msb x = x.toBitVec.msb := by
  simp [uint32Msb, BitVec.msb_eq_toNat, UInt32.le_iff_toNat_le]

@[inline] def fastAddWithCarry64 (x y : UInt64) (carryIn : Bool) : UInt64 × PState :=
  let cin : UInt64 := if carryIn then 1 else 0
  let res : UInt64 := x + y + cin
  let n := uint64Msb res
  let z := res == 0
  let c := if carryIn then decide (res ≤ x) else decide (res < x)
  let v := (uint64Msb x == uint64Msb y) && (n != uint64Msb x)
  (res, { n, z, c, v })

@[inline] def fastAddWithCarry32 (x y : UInt32) (carryIn : Bool) : UInt32 × PState :=
  let cin : UInt32 := if carryIn then 1 else 0
  let res : UInt32 := x + y + cin
  let n := uint32Msb res
  let z := res == 0
  let c := if carryIn then decide (res ≤ x) else decide (res < x)
  let v := (uint32Msb x == uint32Msb y) && (n != uint32Msb x)
  (res, { n, z, c, v })

theorem fastAddWithCarry64_fst (x y : UInt64) (carryIn : Bool) :
    (fastAddWithCarry64 x y carryIn).1.toBitVec = (AddWithCarry64 x.toBitVec y.toBitVec carryIn).1 := by
  apply BitVec.eq_of_toNat_eq
  cases carryIn <;>
    simp [fastAddWithCarry64, AddWithCarry64, BitVec.toNat_add, BitVec.toNat_setWidth] <;>
    omega

theorem fastAddWithCarry64_snd (x y : UInt64) (carryIn : Bool) :
    (fastAddWithCarry64 x y carryIn).2 = (AddWithCarry64 x.toBitVec y.toBitVec carryIn).2 := by
  have h1 : x.toNat < 18446744073709551616 := x.toBitVec.isLt
  have h2 : y.toNat < 18446744073709551616 := y.toBitVec.isLt
  have hfst := fastAddWithCarry64_fst x y carryIn
  simp only [fastAddWithCarry64, AddWithCarry64] at hfst ⊢
  ext
  · rw [uint64Msb_eq, hfst]
  · rw [← UInt64.beq_toBitVec, hfst]
    rfl
  · cases carryIn <;>
      simp [BitVec.msb_eq_toNat, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt,
            UInt64.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth] <;>
      omega
  · cases carryIn <;>
    { simp only [uint64Msb, BitVec.msb_eq_toNat, UInt64.le_iff_toNat_le,
                 UInt64.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
                 BitVec.toNat_signExtend, UInt64.toNat_toBitVec]
      by_cases hx : 9223372036854775808 ≤ x.toNat <;>
      by_cases hy : 9223372036854775808 ≤ y.toNat <;>
      by_cases hr : 9223372036854775808 ≤ (x.toNat + y.toNat) % 18446744073709551616 <;>
      by_cases hr1 : 9223372036854775808 ≤ (x.toNat + y.toNat + 1) % 18446744073709551616 <;>
      simp [hx, hy, hr, hr1, Nat.add_comm y.toNat x.toNat, Nat.add_comm 1 (x.toNat + y.toNat)] <;>
      omega }

theorem fastAddWithCarry32_fst (x y : UInt32) (carryIn : Bool) :
    (fastAddWithCarry32 x y carryIn).1.toBitVec = (AddWithCarry32 x.toBitVec y.toBitVec carryIn).1 := by
  apply BitVec.eq_of_toNat_eq
  cases carryIn <;>
    simp [fastAddWithCarry32, AddWithCarry32, BitVec.toNat_add, BitVec.toNat_setWidth] <;>
    omega

theorem fastAddWithCarry32_snd (x y : UInt32) (carryIn : Bool) :
    (fastAddWithCarry32 x y carryIn).2 = (AddWithCarry32 x.toBitVec y.toBitVec carryIn).2 := by
  have h1 : x.toNat < 4294967296 := x.toBitVec.isLt
  have h2 : y.toNat < 4294967296 := y.toBitVec.isLt
  have hfst := fastAddWithCarry32_fst x y carryIn
  simp only [fastAddWithCarry32, AddWithCarry32] at hfst ⊢
  ext
  · rw [uint32Msb_eq, hfst]
  · rw [← UInt32.beq_toBitVec, hfst]
    rfl
  · cases carryIn <;>
      simp [BitVec.msb_eq_toNat, UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt,
            UInt32.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth] <;>
      omega
  · cases carryIn <;>
    { simp only [uint32Msb, BitVec.msb_eq_toNat, UInt32.le_iff_toNat_le,
                 UInt32.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
                 BitVec.toNat_signExtend, UInt32.toNat_toBitVec]
      by_cases hx : 2147483648 ≤ x.toNat <;>
      by_cases hy : 2147483648 ≤ y.toNat <;>
      by_cases hr : 2147483648 ≤ (x.toNat + y.toNat) % 4294967296 <;>
      by_cases hr1 : 2147483648 ≤ (x.toNat + y.toNat + 1) % 4294967296 <;>
      simp [hx, hy, hr, hr1, Nat.add_comm y.toNat x.toNat, Nat.add_comm 1 (x.toNat + y.toNat)] <;>
      omega }

@[inline] def signExtend32To64 (x : UInt32) : UInt64 :=
  if uint32Msb x then x.toUInt64 + 0xffffffff00000000 else x.toUInt64

@[simp] theorem toBitVec_signExtend32To64 (x : UInt32) :
    (signExtend32To64 x).toBitVec = x.toBitVec.signExtend 64 := by
  have hx : x.toNat < 4294967296 := x.toBitVec.isLt
  apply BitVec.eq_of_toNat_eq
  dsimp [signExtend32To64]
  rw [uint32Msb_eq, BitVec.toNat_signExtend]
  cases h : x.toBitVec.msb
  · simp only [Bool.false_eq_true, ↓reduceIte, UInt32.toBitVec_toUInt64, BitVec.toNat_setWidth,
               UInt32.toNat_toBitVec]
    omega
  · simp only [↓reduceIte, UInt64.toNat_toBitVec, UInt64.toNat_add, UInt32.toNat_toUInt64,
               BitVec.toNat_setWidth, UInt32.toNat_toBitVec]
    change (x.toNat + 18446744069414584320) % 18446744073709551616 =
      x.toNat % 18446744073709551616 + 18446744069414584320
    omega

/-- Unboxed 64x64 -> high-64-bit unsigned multiply (`UMULH`), computed via four 32x32 -> 64
    products without `BitVec 128` allocation. -/
@[inline] def fastUmulh (x y : UInt64) : UInt64 :=
  let x0 := x &&& 0xffffffff
  let x1 := x >>> 32
  let y0 := y &&& 0xffffffff
  let y1 := y >>> 32
  let p00 := x0 * y0
  let p01 := x0 * y1
  let p10 := x1 * y0
  let p11 := x1 * y1
  let mid := (p00 >>> 32) + (p01 &&& 0xffffffff) + (p10 &&& 0xffffffff)
  p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32)

private theorem mul_u32_lt {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) :
    a * b ≤ 18446744065119617025 := by
  have ha' : a ≤ 4294967295 := by omega
  have hb' : b ≤ 4294967295 := by omega
  exact Nat.mul_le_mul ha' hb'

private theorem foil_32 (a b c d : Nat) :
    (4294967296 * a + b) * (4294967296 * c + d) =
      18446744073709551616 * (a * c) + 4294967296 * (b * c + a * d) + b * d := by
  have h1 : (4294967296 * a) * (4294967296 * c) = 18446744073709551616 * (a * c) := by
    calc (4294967296 * a) * (4294967296 * c)
      _ = 4294967296 * (a * (4294967296 * c)) := Nat.mul_assoc _ _ _
      _ = 4294967296 * (4294967296 * (a * c)) := by rw [Nat.mul_left_comm a 4294967296 c]
      _ = 18446744073709551616 * (a * c) := (Nat.mul_assoc 4294967296 4294967296 (a * c)).symm
  have h2 : (4294967296 * a) * d = 4294967296 * (a * d) := Nat.mul_assoc _ _ _
  have h3 : b * (4294967296 * c) = 4294967296 * (b * c) := Nat.mul_left_comm b 4294967296 c
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, h1, h2, h3, Nat.mul_add]
  omega

private theorem mul_decomp_32 (x y : Nat) :
    x * y =
      18446744073709551616 * ((x / 4294967296) * (y / 4294967296)) +
      4294967296 * ((x % 4294967296) * (y / 4294967296) + (x / 4294967296) * (y % 4294967296)) +
      (x % 4294967296) * (y % 4294967296) := by
  have hx : x = 4294967296 * (x / 4294967296) + x % 4294967296 := (Nat.div_add_mod x 4294967296).symm
  have hy : y = 4294967296 * (y / 4294967296) + y % 4294967296 := (Nat.div_add_mod y 4294967296).symm
  conv => lhs; rw [hx, hy]
  exact foil_32 (x / 4294967296) (x % 4294967296) (y / 4294967296) (y % 4294967296)

private theorem uint64_toNat_and_mask32 (a : UInt64) :
    (a &&& 0xffffffff).toNat = a.toNat % 4294967296 := by
  change a.toNat &&& 4294967295 = a.toNat % 4294967296
  exact Nat.and_two_pow_sub_one_eq_mod a.toNat 32

private theorem uint64_toNat_shr32 (a : UInt64) :
    (a >>> 32).toNat = a.toNat / 4294967296 := by
  change a.toNat >>> 32 = a.toNat / 4294967296
  exact Nat.shiftRight_eq_div_pow a.toNat 32

private theorem umulh_limbs (p00 p01 p10 p11 xy : Nat)
    (hp00 : p00 ≤ 18446744065119617025)
    (hp01 : p01 ≤ 18446744065119617025)
    (hp10 : p10 ≤ 18446744065119617025)
    (hp11 : p11 ≤ 18446744065119617025)
    (hxy : xy = 18446744073709551616 * p11 + 4294967296 * (p01 + p10) + p00) :
    ((((p11 % 18446744073709551616 + (p01 % 18446744073709551616) / 4294967296) % 18446744073709551616 +
      (p10 % 18446744073709551616) / 4294967296) % 18446744073709551616 +
      ((((p00 % 18446744073709551616) / 4294967296 + (p01 % 18446744073709551616) % 4294967296) % 18446744073709551616 +
        (p10 % 18446744073709551616) % 4294967296) %
        18446744073709551616) / 4294967296) % 18446744073709551616) =
      (xy / 18446744073709551616) % 18446744073709551616 := by
  have hp00m : p00 % 18446744073709551616 = p00 := Nat.mod_eq_of_lt (by omega)
  have hp01m : p01 % 18446744073709551616 = p01 := Nat.mod_eq_of_lt (by omega)
  have hp10m : p10 % 18446744073709551616 = p10 := Nat.mod_eq_of_lt (by omega)
  have hp11m : p11 % 18446744073709551616 = p11 := Nat.mod_eq_of_lt (by omega)
  rw [hp00m, hp01m, hp10m, hp11m]
  let q00 := p00 / 4294967296; let r00 := p00 % 4294967296
  let q01 := p01 / 4294967296; let r01 := p01 % 4294967296
  let q10 := p10 / 4294967296; let r10 := p10 % 4294967296
  let mid := q00 + r01 + r10
  let qm := mid / 4294967296; let rm := mid % 4294967296
  have hr00 : r00 < 4294967296 := Nat.mod_lt _ (by decide)
  have hr01 : r01 < 4294967296 := Nat.mod_lt _ (by decide)
  have hr10 : r10 < 4294967296 := Nat.mod_lt _ (by decide)
  have hrm  : rm < 4294967296 := Nat.mod_lt _ (by decide)
  have hq00 : q00 < 4294967296 := by omega
  have hq01 : q01 < 4294967296 := by omega
  have hq10 : q10 < 4294967296 := by omega
  have hd00 : p00 = 4294967296 * q00 + r00 := (Nat.div_add_mod p00 4294967296).symm
  have hd01 : p01 = 4294967296 * q01 + r01 := (Nat.div_add_mod p01 4294967296).symm
  have hd10 : p10 = 4294967296 * q10 + r10 := (Nat.div_add_mod p10 4294967296).symm
  have hdm  : mid = 4294967296 * qm + rm := (Nat.div_add_mod mid 4294967296).symm
  have hqm  : qm ≤ 2 := by omega
  have hxy' : xy = 18446744073709551616 * (p11 + q01 + q10 + qm) + (4294967296 * rm + r00) := by
    have hp01' : 4294967296 * p01 = 18446744073709551616 * q01 + 4294967296 * r01 := by
      rw [hd01, Nat.mul_add, ← Nat.mul_assoc]
    have hp10' : 4294967296 * p10 = 18446744073709551616 * q10 + 4294967296 * r10 := by
      rw [hd10, Nat.mul_add, ← Nat.mul_assoc]
    have hmid' : 4294967296 * mid = 18446744073709551616 * qm + 4294967296 * rm := by
      rw [hdm, Nat.mul_add, ← Nat.mul_assoc]
    have hmid_def : 4294967296 * mid = 4294967296 * q00 + 4294967296 * r01 + 4294967296 * r10 := by
      change 4294967296 * (q00 + r01 + r10) = _
      rw [Nat.mul_add, Nat.mul_add]
    rw [Nat.mul_add] at hxy
    omega
  change ((((p11 + q01) % 18446744073709551616 + q10) % 18446744073709551616 +
      (((q00 + r01) % 18446744073709551616 + r10) % 18446744073709551616) / 4294967296) %
      18446744073709551616) = (xy / 18446744073709551616) % 18446744073709551616
  have hm1 : q00 + r01 < 18446744073709551616 := by omega
  have hm2 : q00 + r01 + r10 < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2]
  change ((((p11 + q01) % 18446744073709551616 + q10) % 18446744073709551616 + qm) %
      18446744073709551616) = (xy / 18446744073709551616) % 18446744073709551616
  omega

@[simp] theorem toBitVec_fastUmulh (x y : UInt64) :
    (fastUmulh x y).toBitVec =
      (((x.toBitVec.zeroExtend 128) * (y.toBitVec.zeroExtend 128)) >>> 64).truncate 64 := by
  have hx : x.toNat < 18446744073709551616 := x.toBitVec.isLt
  have hy : y.toNat < 18446744073709551616 := y.toBitVec.isLt
  have hx0 : x.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have hx1 : x.toNat / 4294967296 < 4294967296 := by omega
  have hy0 : y.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have hy1 : y.toNat / 4294967296 < 4294967296 := by omega
  have hp00 := mul_u32_lt hx0 hy0
  have hp01 := mul_u32_lt hx0 hy1
  have hp10 := mul_u32_lt hx1 hy0
  have hp11 := mul_u32_lt hx1 hy1
  have hprod : x.toNat * y.toNat < 340282366920938463463374607431768211456 := Nat.mul_lt_mul'' hx hy
  apply BitVec.eq_of_toNat_eq
  simp only [fastUmulh, uint64_toNat_and_mask32, uint64_toNat_shr32,
             UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_toBitVec,
             BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
             Nat.shiftRight_eq_div_pow,
             Nat.mod_eq_of_lt (by omega : x.toNat < 340282366920938463463374607431768211456),
             Nat.mod_eq_of_lt (by omega : y.toNat < 340282366920938463463374607431768211456),
             Nat.mod_eq_of_lt hprod]
  exact umulh_limbs _ _ _ _ _ hp00 hp01 hp10 hp11 (mul_decomp_32 x.toNat y.toNat)

/-! ## Unboxed Architectural State -/

/-- Unboxed fast execution state corresponding to `Arm64.State`. -/
structure FastState where
  regs         : FastRegs := {}
  vregs        : FastVRegs := {}
  sp           : UInt64 := 0
  pc           : UInt64 := 0
  pstate       : PState := PState.zero
  mem          : Memory := Memory.empty
  tpidrEl0     : UInt64 := 0
  fpsr         : UInt32 := 0
  brkStart     : UInt64 := 0
  brk          : UInt64 := 0
  physMemAvail : Nat := 0
  fs           : FsState := {}
  oracle       : Oracle := {}
  oracleIdx    : Nat := 0
  exclFails    : List Bool := []
  trace        : List TraceEvent := []
  status       : ExecStatus := .Running
  symtab       : String → String → Option (BitVec 64) := fun _ _ => none
  sigActions   : BitVec 32 → SigAction := fun _ => {}
  sigAltStack  : SigAltStack := {}
  deriving Inhabited

namespace FastState

/-- Project `FastState` to the trusted `Arm64.State`. -/
def toState (s : FastState) : State :=
  { regs         := s.regs.toRegFile
    vregs        := s.vregs.toVRegFile
    sp           := s.sp.toBitVec
    pc           := s.pc.toBitVec
    pstate       := s.pstate
    mem          := s.mem
    tpidrEl0     := s.tpidrEl0.toBitVec
    fpsr         := s.fpsr.toBitVec
    brkStart     := s.brkStart.toBitVec
    brk          := s.brk.toBitVec
    physMemAvail := s.physMemAvail
    fs           := s.fs
    oracle       := s.oracle
    oracleIdx    := s.oracleIdx
    exclFails    := s.exclFails
    trace        := s.trace
    status       := s.status
    symtab       := s.symtab
    sigActions   := s.sigActions
    sigAltStack  := s.sigAltStack }

/-- Lift a trusted `Arm64.State` into `FastState`. -/
@[inline] def ofState (s : State) : FastState :=
  { regs         := FastRegs.ofRegFile s.regs
    vregs        := FastVRegs.ofVRegFile s.vregs
    sp           := ⟨s.sp⟩
    pc           := ⟨s.pc⟩
    pstate       := s.pstate
    mem          := s.mem
    tpidrEl0     := ⟨s.tpidrEl0⟩
    fpsr         := ⟨s.fpsr⟩
    brkStart     := ⟨s.brkStart⟩
    brk          := ⟨s.brk⟩
    physMemAvail := s.physMemAvail
    fs           := s.fs
    oracle       := s.oracle
    oracleIdx    := s.oracleIdx
    exclFails    := s.exclFails
    trace        := s.trace
    status       := s.status
    symtab       := s.symtab
    sigActions   := s.sigActions
    sigAltStack  := s.sigAltStack }

@[simp] theorem toState_ofState (s : State) :
    (ofState s).toState = s := by
  cases s
  simp [ofState, toState]

@[inline] def readReg64 (s : FastState) (r : Reg) : UInt64 :=
  match r with
  | .gpr idx => if idx == 31#5 then 0 else s.regs.read idx
  | .sp      => s.sp
  | .xzr     => 0

@[inline] def writeReg64 (s : FastState) (r : Reg) (val : UInt64) : FastState :=
  match r with
  | .gpr idx => if idx == 31#5 then s else { s with regs := s.regs.write idx val }
  | .sp      => { s with sp := val }
  | .xzr     => s

@[inline] def readReg32 (s : FastState) (r : Reg) : UInt32 :=
  (s.readReg64 r).toUInt32

@[inline] def writeReg32 (s : FastState) (r : Reg) (val : UInt32) : FastState :=
  s.writeReg64 r val.toUInt64

@[inline] def readReg (s : FastState) (w : Width) (r : Reg) : UInt64 :=
  match w with
  | .W32 => (s.readReg64 r) &&& 0xffffffff
  | .W64 => s.readReg64 r

@[inline] def writeReg (s : FastState) (w : Width) (r : Reg) (val : UInt64) : FastState :=
  s.writeReg64 r (match w with | .W32 => val &&& 0xffffffff | .W64 => val)

@[inline] def advancePC (s : FastState) : FastState :=
  { s with pc := s.pc + 4 }

@[inline] def setPC (s : FastState) (newPC : UInt64) : FastState :=
  { s with pc := newPC }

@[inline] def setPState (s : FastState) (ps : PState) : FastState :=
  { s with pstate := ps }

@[inline] def setFpsr (s : FastState) (fpsr : UInt32) : FastState :=
  { s with fpsr := fpsr }

@[inline] def orFpsr (s : FastState) (flags : UInt32) : FastState :=
  { s with fpsr := s.fpsr ||| flags }

@[inline] def setMem (s : FastState) (m : Memory) : FastState :=
  { s with mem := m }

@[inline] def setStatus (s : FastState) (st : ExecStatus) : FastState :=
  { s with status := st }

@[inline] def spAligned (s : FastState) : Bool :=
  (s.sp &&& 0b1111) == 0

@[simp] theorem toBitVec_readReg64 (s : FastState) (r : Reg) :
    (s.readReg64 r).toBitVec = s.toState.readReg64 r := by
  cases r with
  | gpr idx =>
    simp only [readReg64, State.readReg64, toState, FastRegs.toRegFile_read]
    split <;> rfl
  | sp => rfl
  | xzr => rfl

@[simp] theorem toState_writeReg64 (s : FastState) (r : Reg) (val : UInt64) :
    (s.writeReg64 r val).toState = s.toState.writeReg64 r val.toBitVec := by
  cases r with
  | gpr idx =>
    simp only [writeReg64, State.writeReg64]
    split <;> simp [toState]
  | sp => simp [writeReg64, State.writeReg64, toState]
  | xzr => simp [writeReg64, State.writeReg64, toState]

@[simp] theorem toBitVec_readReg32 (s : FastState) (r : Reg) :
    (s.readReg32 r).toBitVec = s.toState.readReg32 r := by
  simp [readReg32, State.readReg32]

@[simp] theorem toState_writeReg32 (s : FastState) (r : Reg) (val : UInt32) :
    (s.writeReg32 r val).toState = s.toState.writeReg32 r val.toBitVec := by
  simp [writeReg32, State.writeReg32]

@[simp] theorem toBitVec_readReg (s : FastState) (w : Width) (r : Reg) :
    (s.readReg w r).toBitVec = s.toState.readReg w r := by
  cases w <;> simp [readReg, State.readReg, State.readReg32]

@[simp] theorem toState_writeReg (s : FastState) (w : Width) (r : Reg) (val : UInt64) :
    (s.writeReg w r val).toState = s.toState.writeReg w r val.toBitVec := by
  cases w <;> simp [writeReg, State.writeReg]

@[simp] theorem toState_advancePC (s : FastState) :
    s.advancePC.toState = s.toState.advancePC := rfl

@[simp] theorem toState_setPC (s : FastState) (newPC : UInt64) :
    (s.setPC newPC).toState = s.toState.setPC newPC.toBitVec := rfl

@[simp] theorem toState_setPState (s : FastState) (ps : PState) :
    (s.setPState ps).toState = s.toState.setPState ps := rfl

@[simp] theorem toState_setFpsr (s : FastState) (fpsr : UInt32) :
    (s.setFpsr fpsr).toState = s.toState.setFpsr fpsr.toBitVec := rfl

@[simp] theorem toState_orFpsr (s : FastState) (flags : UInt32) :
    (s.orFpsr flags).toState = s.toState.orFpsr flags.toBitVec := rfl

@[simp] theorem toState_setMem (s : FastState) (m : Memory) :
    (s.setMem m).toState = s.toState.setMem m := rfl

@[simp] theorem toState_setStatus (s : FastState) (st : ExecStatus) :
    (s.setStatus st).toState = s.toState.setStatus st := rfl

@[simp] theorem spAligned_eq (s : FastState) :
    s.spAligned = s.toState.spAligned := by
  simp [spAligned, State.spAligned, toState, ← UInt64.beq_toBitVec]

@[inline] def readVReg128 (s : FastState) (idx : BitVec 5) : BitVec 128 :=
  s.vregs.read idx

@[inline] def writeVReg128 (s : FastState) (idx : BitVec 5) (val : BitVec 128) : FastState :=
  { s with vregs := s.vregs.write idx val }

@[inline] def readVReg64 (s : FastState) (idx : BitVec 5) : BitVec 64 :=
  (s.readVReg128 idx).truncate 64

@[inline] def writeVReg64 (s : FastState) (idx : BitVec 5) (val : BitVec 64) : FastState :=
  s.writeVReg128 idx (val.zeroExtend 128)

@[inline] def readVReg32 (s : FastState) (idx : BitVec 5) : BitVec 32 :=
  (s.readVReg128 idx).truncate 32

@[inline] def writeVReg32 (s : FastState) (idx : BitVec 5) (val : BitVec 32) : FastState :=
  s.writeVReg128 idx (val.zeroExtend 128)

@[simp] theorem readVReg128_eq (s : FastState) (idx : BitVec 5) :
    s.readVReg128 idx = s.toState.readVReg128 idx := rfl

@[simp] theorem toState_writeVReg128 (s : FastState) (idx : BitVec 5) (val : BitVec 128) :
    (s.writeVReg128 idx val).toState = s.toState.writeVReg128 idx val := by
  simp [writeVReg128, State.writeVReg128, toState]

@[simp] theorem readVReg64_eq (s : FastState) (idx : BitVec 5) :
    s.readVReg64 idx = s.toState.readVReg64 idx := rfl

@[simp] theorem toState_writeVReg64 (s : FastState) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeVReg64 idx val).toState = s.toState.writeVReg64 idx val := by
  simp [writeVReg64, State.writeVReg64]

@[simp] theorem readVReg32_eq (s : FastState) (idx : BitVec 5) :
    s.readVReg32 idx = s.toState.readVReg32 idx := rfl

@[simp] theorem toState_writeVReg32 (s : FastState) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeVReg32 idx val).toState = s.toState.writeVReg32 idx val := by
  simp [writeVReg32, State.writeVReg32]

end FastState

/-! ## Shifts, Extensions, and ALU Evaluators -/

@[simp] theorem UInt64.toBitVec_shiftLeft (a b : UInt64) :
    (a <<< b).toBitVec = a.toBitVec <<< (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp

@[simp] theorem UInt64.toBitVec_shiftRight (a b : UInt64) :
    (a >>> b).toBitVec = a.toBitVec >>> (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp

@[simp] theorem UInt32.toBitVec_shiftLeft (a b : UInt32) :
    (a <<< b).toBitVec = a.toBitVec <<< (b.toNat % 32) := by
  apply BitVec.eq_of_toNat_eq
  simp

@[simp] theorem UInt32.toBitVec_shiftRight (a b : UInt32) :
    (a >>> b).toBitVec = a.toBitVec >>> (b.toNat % 32) := by
  apply BitVec.eq_of_toNat_eq
  simp

@[simp] private theorem ofNat_u64_toNat_mod64 (n : Nat) :
    (UInt64.ofNat n).toNat % 64 = n % 64 := by
  rw [UInt64.toNat_ofNat']
  omega

@[simp] private theorem ofNat_u32_toNat_mod32 (n : Nat) :
    (UInt32.ofNat n).toNat % 32 = n % 32 := by
  rw [UInt32.toNat_ofNat']
  omega

@[simp] theorem UInt64.toBitVec_toUInt8 (x : UInt64) :
    x.toUInt8.toBitVec = x.toBitVec.truncate 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

@[simp] theorem UInt64.toBitVec_toUInt16 (x : UInt64) :
    x.toUInt16.toBitVec = x.toBitVec.truncate 16 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

@[simp] theorem UInt8.toBitVec_toUInt64 (x : UInt8) :
    x.toUInt64.toBitVec = x.toBitVec.zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

@[simp] theorem UInt16.toBitVec_toUInt64 (x : UInt16) :
    x.toUInt64.toBitVec = x.toBitVec.zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

@[inline] def uint8Msb (x : UInt8) : Bool :=
  decide (0x80 ≤ x)

@[simp] theorem uint8Msb_eq (x : UInt8) :
    uint8Msb x = x.toBitVec.msb := by
  simp [uint8Msb, BitVec.msb_eq_toNat, UInt8.le_iff_toNat_le]

@[inline] def uint16Msb (x : UInt16) : Bool :=
  decide (0x8000 ≤ x)

@[simp] theorem uint16Msb_eq (x : UInt16) :
    uint16Msb x = x.toBitVec.msb := by
  simp [uint16Msb, BitVec.msb_eq_toNat, UInt16.le_iff_toNat_le]

/-- Sign-extend an 8-bit `UInt8` (`SXTB`) to `UInt64`. -/
@[inline] def signExtend8To64 (x : UInt8) : UInt64 :=
  if uint8Msb x then x.toUInt64 + 0xffffffffffffff00 else x.toUInt64

@[simp] theorem toBitVec_signExtend8To64 (x : UInt8) :
    (signExtend8To64 x).toBitVec = x.toBitVec.signExtend 64 := by
  have hx : x.toNat < 256 := x.toBitVec.isLt
  apply BitVec.eq_of_toNat_eq
  dsimp [signExtend8To64]
  rw [uint8Msb_eq, BitVec.toNat_signExtend]
  cases h : x.toBitVec.msb
  · simp only [Bool.false_eq_true, ↓reduceIte, UInt8.toBitVec_toUInt64, BitVec.toNat_setWidth,
               UInt8.toNat_toBitVec]
    omega
  · simp only [↓reduceIte, UInt64.toNat_toBitVec, UInt64.toNat_add, UInt8.toNat_toUInt64,
               BitVec.toNat_setWidth, UInt8.toNat_toBitVec]
    change (x.toNat + 18446744073709551360) % 18446744073709551616 =
      x.toNat % 18446744073709551616 + 18446744073709551360
    omega

/-- Sign-extend a 16-bit `UInt16` (`SXTH`) to `UInt64`. -/
@[inline] def signExtend16To64 (x : UInt16) : UInt64 :=
  if uint16Msb x then x.toUInt64 + 0xffffffffffff0000 else x.toUInt64

@[simp] theorem toBitVec_signExtend16To64 (x : UInt16) :
    (signExtend16To64 x).toBitVec = x.toBitVec.signExtend 64 := by
  have hx : x.toNat < 65536 := x.toBitVec.isLt
  apply BitVec.eq_of_toNat_eq
  dsimp [signExtend16To64]
  rw [uint16Msb_eq, BitVec.toNat_signExtend]
  cases h : x.toBitVec.msb
  · simp only [Bool.false_eq_true, ↓reduceIte, UInt16.toBitVec_toUInt64, BitVec.toNat_setWidth,
               UInt16.toNat_toBitVec]
    omega
  · simp only [↓reduceIte, UInt64.toNat_toBitVec, UInt64.toNat_add, UInt16.toNat_toUInt64,
               BitVec.toNat_setWidth, UInt16.toNat_toBitVec]
    change (x.toNat + 18446744073709486080) % 18446744073709551616 =
      x.toNat % 18446744073709551616 + 18446744073709486080
    omega

private theorem sshiftRight_eq_if_msb {w : Nat} (x : BitVec w) (amt : Nat) :
    x.sshiftRight amt = if x.msb then ~~~((~~~x) >>> amt) else x >>> amt := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight]
  split
  · next hlt =>
    cases hmsb : x.msb <;>
      simp [BitVec.getElem_not, BitVec.getElem_ushiftRight, BitVec.getLsbD_eq_getElem hlt]
  · next hge =>
    have h1 : x.getLsbD (amt + i) = false := BitVec.getLsbD_of_ge x (amt + i) (by omega)
    have h2 : (~~~x).getLsbD (amt + i) = false := BitVec.getLsbD_of_ge (~~~x) (amt + i) (by omega)
    cases hmsb : x.msb <;>
      simp [BitVec.getElem_not, BitVec.getElem_ushiftRight, h1, h2]

/-- Unboxed 32-bit shift (`LSL`, `LSR`, `ASR`, `ROR`). -/
@[inline] def fastShift32 (val : UInt32) (op : ShiftType) (amount : Nat) : UInt32 :=
  let amt := amount % 32
  let s := amt.toUInt32
  match op with
  | .LSL => val <<< s
  | .LSR => val >>> s
  | .ASR => if uint32Msb val then ~~~((~~~val) >>> s) else val >>> s
  | .ROR => if amt == 0 then val else (val >>> s) ||| (val <<< (32 - amt).toUInt32)

@[simp] theorem toBitVec_fastShift32 (val : UInt32) (op : ShiftType) (amount : Nat) :
    (fastShift32 val op amount).toBitVec = shift32 val.toBitVec op amount := by
  have hamt : amount % 32 < 32 := Nat.mod_lt _ (by decide)
  dsimp [fastShift32, shift32, Nat.toUInt32]
  cases op with
  | LSL => simp
  | LSR => simp
  | ASR =>
    rw [uint32Msb_eq, sshiftRight_eq_if_msb]
    cases val.toBitVec.msb <;> simp
  | ROR =>
    rw [BitVec.rotateRight_def, Nat.mod_mod]
    by_cases h0 : amount % 32 = 0
    · simp [h0]
    · have hsub : (32 - amount % 32) % 32 = 32 - amount % 32 := Nat.mod_eq_of_lt (by omega)
      simp [h0, hsub, UInt32.toBitVec_or]

/-- Unboxed 64-bit shift (`LSL`, `LSR`, `ASR`, `ROR`). -/
@[inline] def fastShift64 (val : UInt64) (op : ShiftType) (amount : Nat) : UInt64 :=
  let amt := amount % 64
  let s := amt.toUInt64
  match op with
  | .LSL => val <<< s
  | .LSR => val >>> s
  | .ASR => if uint64Msb val then ~~~((~~~val) >>> s) else val >>> s
  | .ROR => if amt == 0 then val else (val >>> s) ||| (val <<< (64 - amt).toUInt64)

@[simp] theorem toBitVec_fastShift64 (val : UInt64) (op : ShiftType) (amount : Nat) :
    (fastShift64 val op amount).toBitVec = shift64 val.toBitVec op amount := by
  have hamt : amount % 64 < 64 := Nat.mod_lt _ (by decide)
  dsimp [fastShift64, shift64, Nat.toUInt64]
  cases op with
  | LSL => simp
  | LSR => simp
  | ASR =>
    rw [uint64Msb_eq, sshiftRight_eq_if_msb]
    cases val.toBitVec.msb <;> simp
  | ROR =>
    rw [BitVec.rotateRight_def, Nat.mod_mod]
    by_cases h0 : amount % 64 = 0
    · simp [h0]
    · have hsub : (64 - amount % 64) % 64 = 64 - amount % 64 := Nat.mod_eq_of_lt (by omega)
      simp [h0, hsub, UInt64.toBitVec_or]

@[inline] def fastShiftVal (w : Width) (val : UInt64) (op : ShiftType) (amount : Nat) : UInt64 :=
  match w with
  | .W32 => (fastShift32 val.toUInt32 op amount).toUInt64
  | .W64 => fastShift64 val op amount

@[simp] theorem toBitVec_fastShiftVal (w : Width) (val : UInt64) (op : ShiftType) (amount : Nat) :
    (fastShiftVal w val op amount).toBitVec = shiftVal w val.toBitVec op amount := by
  cases w <;> simp [fastShiftVal, shiftVal]

@[inline] def fastExtend64 (val : UInt64) (ext : ExtendType) : UInt64 :=
  match ext with
  | .UXTB => val.toUInt8.toUInt64
  | .UXTH => val.toUInt16.toUInt64
  | .UXTW => val.toUInt32.toUInt64
  | .UXTX => val
  | .SXTB => signExtend8To64 val.toUInt8
  | .SXTH => signExtend16To64 val.toUInt16
  | .SXTW => signExtend32To64 val.toUInt32
  | .SXTX => val

@[inline] def fastExtendVal (w : Width) (val : UInt64) (ext : ExtendType) (amount : Nat) : UInt64 :=
  let ext64 := fastExtend64 val ext
  let shifted := if amount < 64 then ext64 <<< amount.toUInt64 else 0
  match w with
  | .W32 => shifted.toUInt32.toUInt64
  | .W64 => shifted

@[simp] private theorem bv64_mod_256_eq (b : BitVec 64) :
    b % 256#64 = (b.truncate 8).zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]
  omega

@[simp] private theorem bv64_mod_65536_eq (b : BitVec 64) :
    b % 65536#64 = (b.truncate 16).zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]
  omega

@[simp] private theorem bv64_mod_u32_eq (b : BitVec 64) :
    b % 4294967296#64 = (b.truncate 32).zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]
  omega

@[simp] theorem toBitVec_fastExtendVal (w : Width) (val : UInt64) (ext : ExtendType) (amount : Nat) :
    (fastExtendVal w val ext amount).toBitVec = extendVal w val.toBitVec ext amount := by
  have hext : (fastExtend64 val ext).toBitVec =
      (match ext with
      | .UXTB => (val.toBitVec.truncate 8).zeroExtend 64
      | .UXTH => (val.toBitVec.truncate 16).zeroExtend 64
      | .UXTW => (val.toBitVec.truncate 32).zeroExtend 64
      | .UXTX => val.toBitVec
      | .SXTB => (val.toBitVec.truncate 8).signExtend 64
      | .SXTH => (val.toBitVec.truncate 16).signExtend 64
      | .SXTW => (val.toBitVec.truncate 32).signExtend 64
      | .SXTX => val.toBitVec) := by
    cases ext <;> simp [fastExtend64]
  have hsh : (if amount < 64 then fastExtend64 val ext <<< amount.toUInt64 else 0).toBitVec =
      (fastExtend64 val ext).toBitVec <<< amount := by
    by_cases h : amount < 64
    · simp [h, Nat.toUInt64, Nat.mod_eq_of_lt h]
    · simp only [h, ↓reduceIte, UInt64.toBitVec_ofNat]
      exact (BitVec.shiftLeft_eq_zero (by omega)).symm
  cases w <;> (simp [fastExtendVal, extendVal, hsh, hext]; rfl)

private theorem append_ushiftRight_truncate {w : Nat} (n m : BitVec w) (k : Nat) (hk : k < w) :
    (((n ++ m) >>> k).truncate w) = if k = 0 then m else (m >>> k) ||| (n <<< (w - k)) := by
  ext i hi
  by_cases hk0 : k = 0
  · subst hk0
    simp [BitVec.getLsbD_append, hi]
  · simp only [hk0, ↓reduceIte, BitVec.getElem_or, BitVec.getElem_ushiftRight,
               BitVec.getElem_shiftLeft, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight,
               BitVec.getLsbD_append]
    by_cases hik : k + i < w
    · have h1 : i < w - k := by omega
      simp [hik, h1]
    · have h1 : ¬(i < w - k) := by omega
      have h2 : k + i - w < w := by omega
      have h3 : i - (w - k) = k + i - w := by omega
      have h4 : m.getLsbD (k + i) = false := BitVec.getLsbD_of_ge m (k + i) (by omega)
      simp [hik, h1, h3, h4, BitVec.getLsbD_eq_getElem h2]

/-- Unboxed 32-bit `EXTR` (`((n32 ++ m32) >>> (lsb % 32)).truncate 32`). -/
@[inline] def fastExtr32 (n m : UInt32) (lsb : Nat) : UInt32 :=
  let k := lsb % 32
  if k == 0 then m
  else (m >>> k.toUInt32) ||| (n <<< (32 - k).toUInt32)

@[simp] theorem toBitVec_fastExtr32 (n m : UInt32) (lsb : Nat) :
    (fastExtr32 n m lsb).toBitVec = ((n.toBitVec ++ m.toBitVec) >>> (lsb % 32)).truncate 32 := by
  have hk : lsb % 32 < 32 := Nat.mod_lt _ (by decide)
  rw [append_ushiftRight_truncate n.toBitVec m.toBitVec (lsb % 32) hk]
  dsimp [fastExtr32, Nat.toUInt32]
  by_cases h0 : lsb % 32 = 0
  · simp [h0]
  · have hsub : (32 - lsb % 32) % 32 = 32 - lsb % 32 := Nat.mod_eq_of_lt (by omega)
    simp [h0, hsub, Nat.mod_eq_of_lt hk, UInt32.toBitVec_or]

/-- Unboxed 64-bit `EXTR` (`((n64 ++ m64) >>> (lsb % 64)).truncate 64`), avoiding `BitVec 128`. -/
@[inline] def fastExtr64 (n m : UInt64) (lsb : Nat) : UInt64 :=
  let k := lsb % 64
  if k == 0 then m
  else (m >>> k.toUInt64) ||| (n <<< (64 - k).toUInt64)

@[simp] theorem toBitVec_fastExtr64 (n m : UInt64) (lsb : Nat) :
    (fastExtr64 n m lsb).toBitVec = ((n.toBitVec ++ m.toBitVec) >>> (lsb % 64)).truncate 64 := by
  have hk : lsb % 64 < 64 := Nat.mod_lt _ (by decide)
  rw [append_ushiftRight_truncate n.toBitVec m.toBitVec (lsb % 64) hk]
  dsimp [fastExtr64, Nat.toUInt64]
  by_cases h0 : lsb % 64 = 0
  · simp [h0]
  · have hsub : (64 - lsb % 64) % 64 = 64 - lsb % 64 := Nat.mod_eq_of_lt (by omega)
    simp [h0, hsub, Nat.mod_eq_of_lt hk, UInt64.toBitVec_or]

@[inline] def fastEvalAddSub (w : Width) (op : AddSubOp) (x y : UInt64) (carryIn : Option Bool := none) :
    UInt64 × Option PState :=
  let isSub := match op with | .SUB | .SUBS => true | .ADD | .ADDS => false
  let setFlags := match op with | .ADDS | .SUBS => true | .ADD | .SUB => false
  let cIn := match carryIn with | some c => c | none => isSub
  match w with
  | .W32 =>
    let x32 := x.toUInt32
    let y32 := if isSub then ~~~y.toUInt32 else y.toUInt32
    let (res32, ps) := fastAddWithCarry32 x32 y32 cIn
    (res32.toUInt64, if setFlags then some ps else none)
  | .W64 =>
    let y64 := if isSub then ~~~y else y
    let (res64, ps) := fastAddWithCarry64 x y64 cIn
    (res64, if setFlags then some ps else none)

@[simp] theorem fastEvalAddSub_fst (w : Width) (op : AddSubOp) (x y : UInt64) (carryIn : Option Bool) :
    (fastEvalAddSub w op x y carryIn).1.toBitVec = (evalAddSub w op x.toBitVec y.toBitVec carryIn).1 := by
  cases w <;> cases op <;>
    (simp [fastEvalAddSub, evalAddSub, fastAddWithCarry32_fst, fastAddWithCarry64_fst]; try rfl)

@[simp] theorem fastEvalAddSub_snd (w : Width) (op : AddSubOp) (x y : UInt64) (carryIn : Option Bool) :
    (fastEvalAddSub w op x y carryIn).2 = (evalAddSub w op x.toBitVec y.toBitVec carryIn).2 := by
  cases w <;> cases op <;>
    (simp [fastEvalAddSub, evalAddSub, fastAddWithCarry32_snd, fastAddWithCarry64_snd]; try rfl)

@[inline] def fastEvalLogical (w : Width) (op : LogicalOp) (x y : UInt64) (psOld : PState) :
    UInt64 × Option PState :=
  let yMod := match op with
    | .BIC | .ORN | .EON | .BICS => ~~~y
    | _ => y
  let raw := match op with
    | .AND | .BIC | .ANDS | .BICS => x &&& yMod
    | .ORR | .ORN => x ||| yMod
    | .EOR | .EON => x ^^^ yMod
  let setFlags := match op with | .ANDS | .BICS => true | _ => false
  match w with
  | .W32 =>
    let res32 := raw.toUInt32
    let ps : PState := { n := uint32Msb res32, z := res32 == 0, c := false, v := false }
    let _ := psOld
    (res32.toUInt64, if setFlags then some ps else none)
  | .W64 =>
    let ps : PState := { n := uint64Msb raw, z := raw == 0, c := false, v := false }
    (raw, if setFlags then some ps else none)

@[simp] theorem fastEvalLogical_fst (w : Width) (op : LogicalOp) (x y : UInt64) (psOld : PState) :
    (fastEvalLogical w op x y psOld).1.toBitVec = (evalLogical w op x.toBitVec y.toBitVec psOld).1 := by
  cases w <;> cases op <;> (simp [fastEvalLogical, evalLogical,
    UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_xor, UInt64.toBitVec_not]; try rfl)

@[simp] theorem fastEvalLogical_snd (w : Width) (op : LogicalOp) (x y : UInt64) (psOld : PState) :
    (fastEvalLogical w op x y psOld).2 = (evalLogical w op x.toBitVec y.toBitVec psOld).2 := by
  cases w <;> cases op <;> simp [fastEvalLogical, evalLogical,
    ← UInt32.beq_toBitVec, ← UInt64.beq_toBitVec,
    UInt64.toBitVec_and, UInt64.toBitVec_not]

@[inline] def fastCheckRegSPAligned (s : FastState) (r : Reg) : Bool :=
  match r with
  | .sp => s.spAligned
  | _ => true

@[simp] theorem fastCheckRegSPAligned_eq (s : FastState) (r : Reg) :
    fastCheckRegSPAligned s r = checkRegSPAligned s.toState r := by
  cases r <;> simp [fastCheckRegSPAligned, checkRegSPAligned]

@[inline] def fastCheckAddrSPAligned (s : FastState) (addr : AddrMode) : Bool :=
  fastCheckRegSPAligned s addr.baseReg

@[simp] theorem fastCheckAddrSPAligned_eq (s : FastState) (addr : AddrMode) :
    fastCheckAddrSPAligned s addr = checkAddrSPAligned s.toState addr := by
  simp [fastCheckAddrSPAligned, checkAddrSPAligned]

@[inline] def fastEvalAddrMode (s : FastState) (addr : AddrMode) : UInt64 × Option (Reg × UInt64) :=
  match addr with
  | .Offset base off =>
    (s.readReg64 base + ⟨off⟩, none)
  | .UnscaledOffset base off =>
    (s.readReg64 base + ⟨off⟩, none)
  | .PreIndex base off =>
    let ea := s.readReg64 base + ⟨off⟩
    (ea, some (base, ea))
  | .PostIndex base off =>
    let baseVal := s.readReg64 base
    (baseVal, some (base, baseVal + ⟨off⟩))
  | .RegOffset base index ext amount =>
    let baseVal := s.readReg64 base
    let idxVal := fastExtendVal .W64 (s.readReg64 index) ext amount
    (baseVal + idxVal, none)

@[simp] theorem fastEvalAddrMode_fst (s : FastState) (addr : AddrMode) :
    (fastEvalAddrMode s addr).1.toBitVec = (evalAddrMode s.toState addr).1 := by
  cases addr <;> simp [fastEvalAddrMode, evalAddrMode, UInt64.toBitVec_add]

@[simp] theorem fastEvalAddrMode_snd (s : FastState) (addr : AddrMode) :
    ((fastEvalAddrMode s addr).2.map fun (r, v) => (r, v.toBitVec)) = (evalAddrMode s.toState addr).2 := by
  cases addr <;> simp [fastEvalAddrMode, evalAddrMode, UInt64.toBitVec_add]

/-! ## Unboxed Memory Access Helpers -/

/-- Check permission predicate `p` over `[addr, addr + n)` using unboxed `UInt64` address steps. -/
def fastAllPerm (m : Memory) (p : Option Perm → Bool) (addr : UInt64) : Nat → Bool
  | 0 => true
  | n + 1 => p (m.perm addr.toBitVec) && fastAllPerm m p (addr + 1) n

@[simp] theorem fastAllPerm_eq (m : Memory) (p : Option Perm → Bool) (n : Nat) (addr : UInt64) :
    fastAllPerm m p addr n = m.allPerm p addr.toBitVec n := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
    simp only [fastAllPerm, Memory.allPerm, ih]
    rfl

/-- Check `!m.isLazyFree` over `[addr, addr + n)` using unboxed `UInt64` address steps. -/
def fastAllNoLazyFree (m : Memory) (addr : UInt64) : Nat → Bool
  | 0 => true
  | n + 1 => !m.isLazyFree addr.toBitVec && fastAllNoLazyFree m (addr + 1) n

@[simp] theorem fastAllNoLazyFree_eq (m : Memory) (n : Nat) (addr : UInt64) :
    fastAllNoLazyFree m addr n = m.allNoLazyFree addr.toBitVec n := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
    simp only [fastAllNoLazyFree, Memory.allNoLazyFree, ih]
    rfl

@[inline] def fastCanRead (m : Memory) (addr : UInt64) (n : Nat) : Bool :=
  fastAllPerm m (·.r) addr n && fastAllNoLazyFree m addr n

@[simp] theorem fastCanRead_eq (m : Memory) (addr : UInt64) (n : Nat) :
    fastCanRead m addr n = m.canRead addr.toBitVec n := by
  simp only [fastCanRead, Memory.canRead, fastAllPerm_eq, fastAllNoLazyFree_eq]

@[inline] def fastCanWrite (m : Memory) (addr : UInt64) (n : Nat) : Bool :=
  fastAllPerm m (fun p => p.w && !p.x) addr n

@[simp] theorem fastCanWrite_eq (m : Memory) (addr : UInt64) (n : Nat) :
    fastCanWrite m addr n = m.canWrite addr.toBitVec n :=
  fastAllPerm_eq m (fun p => p.w && !p.x) n addr

@[inline] def byteToU64 (b : BitVec 8) : UInt64 :=
  (UInt8.ofBitVec b).toUInt64

@[inline] def packByte64 (acc : UInt64) (b : BitVec 8) : UInt64 :=
  (acc <<< 8) ||| byteToU64 b

@[simp] theorem toBitVec_byteToU64 (b : BitVec 8) :
    (byteToU64 b).toBitVec = b.zeroExtend 64 := by
  simp [byteToU64]

@[simp] theorem byteToU64_eq (b : BitVec 8) :
    byteToU64 b = ⟨b.zeroExtend 64⟩ := by
  rw [← UInt64.toBitVec_inj, toBitVec_byteToU64]

private theorem toBitVec_packByte64_aux {m : Nat} (x : BitVec m) (b : BitVec 8) :
    (packByte64 ⟨x.zeroExtend 64⟩ b).toBitVec = (x ++ b).zeroExtend 64 := by
  ext i hi
  simp only [packByte64, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, toBitVec_byteToU64]
  change ((x.zeroExtend 64 <<< 8) ||| b.zeroExtend 64)[i] = ((x ++ b).zeroExtend 64)[i]
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
             BitVec.getLsbD_append]
  by_cases h8 : i < 8
  · simp [h8]
  · have hb : b.getLsbD i = false := BitVec.getLsbD_of_ge b i (by omega)
    simp [h8, hb]

@[simp] theorem packByte64_eq {m : Nat} (x : BitVec m) (b : BitVec 8) :
    packByte64 ⟨x.zeroExtend 64⟩ b = ⟨(x ++ b).zeroExtend 64⟩ := by
  rw [← UInt64.toBitVec_inj]
  exact toBitVec_packByte64_aux x b

@[inline] def fastRead8 (m : Memory) (ea : UInt64) : UInt64 :=
  byteToU64 (m.read8 ea.toBitVec)

@[inline] def fastRead16 (m : Memory) (ea : UInt64) : UInt64 :=
  let b0 := m.read8 (ea + 0).toBitVec
  let b1 := m.read8 (ea + 1).toBitVec
  packByte64 (byteToU64 b1) b0

@[inline] def fastRead32 (m : Memory) (ea : UInt64) : UInt64 :=
  let b0 := m.read8 (ea + 0).toBitVec
  let b1 := m.read8 (ea + 1).toBitVec
  let b2 := m.read8 (ea + 2).toBitVec
  let b3 := m.read8 (ea + 3).toBitVec
  packByte64 (packByte64 (packByte64 (byteToU64 b3) b2) b1) b0

@[inline] def fastRead64 (m : Memory) (ea : UInt64) : UInt64 :=
  let b0 := m.read8 (ea + 0).toBitVec
  let b1 := m.read8 (ea + 1).toBitVec
  let b2 := m.read8 (ea + 2).toBitVec
  let b3 := m.read8 (ea + 3).toBitVec
  let b4 := m.read8 (ea + 4).toBitVec
  let b5 := m.read8 (ea + 5).toBitVec
  let b6 := m.read8 (ea + 6).toBitVec
  let b7 := m.read8 (ea + 7).toBitVec
  packByte64 (packByte64 (packByte64 (packByte64 (packByte64 (packByte64 (packByte64 (byteToU64 b7) b6) b5) b4) b3) b2) b1) b0

@[simp] theorem toBitVec_fastRead8 (m : Memory) (ea : UInt64) :
    (fastRead8 m ea).toBitVec = (m.read8 ea.toBitVec).zeroExtend 64 := by
  simp [fastRead8]

@[simp] theorem toBitVec_fastRead16 (m : Memory) (ea : UInt64) :
    (fastRead16 m ea).toBitVec = (m.read16 ea.toBitVec).zeroExtend 64 := by
  simp [fastRead16, Memory.read16]

@[simp] theorem toBitVec_fastRead32 (m : Memory) (ea : UInt64) :
    (fastRead32 m ea).toBitVec = (m.read32 ea.toBitVec).zeroExtend 64 := by
  simp [fastRead32, Memory.read32]

@[simp] theorem toBitVec_fastRead64 (m : Memory) (ea : UInt64) :
    (fastRead64 m ea).toBitVec = m.read64 ea.toBitVec := by
  simp [fastRead64, Memory.read64]

@[inline] def fastReadSized (m : Memory) (size : MemWidth) (signed : Bool) (ea : UInt64) : UInt64 :=
  match size with
  | .B8  =>
    let b := fastRead8 m ea
    if signed then signExtend8To64 b.toUInt8 else b
  | .H16 =>
    let h := fastRead16 m ea
    if signed then signExtend16To64 h.toUInt16 else h
  | .W32 =>
    let w := fastRead32 m ea
    if signed then signExtend32To64 w.toUInt32 else w
  | .X64 =>
    fastRead64 m ea

@[simp] theorem toBitVec_fastReadSized (m : Memory) (size : MemWidth) (signed : Bool) (ea : UInt64) :
    (fastReadSized m size signed ea).toBitVec = m.readSized size signed ea.toBitVec := by
  cases size <;> cases signed <;> simp [fastReadSized, Memory.readSized]

@[inline] def extractByte (val : UInt64) (sh : UInt64) : BitVec 8 :=
  (val >>> sh).toUInt8.toBitVec

@[simp] theorem extractByte_eq (val : UInt64) (sh : UInt64) :
    extractByte val sh = val.toBitVec.extractLsb' (sh.toNat % 64) 8 := by
  ext i hi
  simp [extractByte]

private theorem extractLsb'_truncate (w : Nat) (x : BitVec 64) (s : Nat) (h : s + 8 ≤ w) :
    (x.truncate w).extractLsb' s 8 = x.extractLsb' s 8 := by
  ext i hi
  simp [show s + i < w by omega]

@[inline] def fastWrite8 (m : Memory) (ea val : UInt64) : Memory :=
  m.write8 ea.toBitVec val.toUInt8.toBitVec

@[inline] def fastWrite16 (m : Memory) (ea val : UInt64) : Memory :=
  let m := m.write8 (ea + 0).toBitVec (extractByte val 0)
  let m := m.write8 (ea + 1).toBitVec (extractByte val 8)
  m

@[inline] def fastWrite32 (m : Memory) (ea val : UInt64) : Memory :=
  let m := m.write8 (ea + 0).toBitVec (extractByte val 0)
  let m := m.write8 (ea + 1).toBitVec (extractByte val 8)
  let m := m.write8 (ea + 2).toBitVec (extractByte val 16)
  let m := m.write8 (ea + 3).toBitVec (extractByte val 24)
  m

@[inline] def fastWrite64 (m : Memory) (ea val : UInt64) : Memory :=
  let m := m.write8 (ea + 0).toBitVec (extractByte val 0)
  let m := m.write8 (ea + 1).toBitVec (extractByte val 8)
  let m := m.write8 (ea + 2).toBitVec (extractByte val 16)
  let m := m.write8 (ea + 3).toBitVec (extractByte val 24)
  let m := m.write8 (ea + 4).toBitVec (extractByte val 32)
  let m := m.write8 (ea + 5).toBitVec (extractByte val 40)
  let m := m.write8 (ea + 6).toBitVec (extractByte val 48)
  let m := m.write8 (ea + 7).toBitVec (extractByte val 56)
  m

@[inline] def fastWriteSized (m : Memory) (size : MemWidth) (ea val : UInt64) : Memory :=
  match size with
  | .B8  => fastWrite8 m ea val
  | .H16 => fastWrite16 m ea val
  | .W32 => fastWrite32 m ea val
  | .X64 => fastWrite64 m ea val

@[simp] theorem fastWrite8_eq (m : Memory) (ea val : UInt64) :
    fastWrite8 m ea val = m.write8 ea.toBitVec (val.toBitVec.truncate 8) := by
  simp [fastWrite8]

@[simp] theorem fastWrite16_eq (m : Memory) (ea val : UInt64) :
    fastWrite16 m ea val = m.write16 ea.toBitVec (val.toBitVec.truncate 16) := by
  simp only [fastWrite16, Memory.write16, extractByte_eq,
             extractLsb'_truncate 16 val.toBitVec 0 (by decide),
             extractLsb'_truncate 16 val.toBitVec 8 (by decide)]
  rfl

@[simp] theorem fastWrite32_eq (m : Memory) (ea val : UInt64) :
    fastWrite32 m ea val = m.write32 ea.toBitVec (val.toBitVec.truncate 32) := by
  simp only [fastWrite32, Memory.write32, extractByte_eq,
             extractLsb'_truncate 32 val.toBitVec 0 (by decide),
             extractLsb'_truncate 32 val.toBitVec 8 (by decide),
             extractLsb'_truncate 32 val.toBitVec 16 (by decide),
             extractLsb'_truncate 32 val.toBitVec 24 (by decide)]
  rfl

@[simp] theorem fastWrite64_eq (m : Memory) (ea val : UInt64) :
    fastWrite64 m ea val = m.write64 ea.toBitVec val.toBitVec := by
  simp only [fastWrite64, Memory.write64, extractByte_eq]
  rfl

@[simp] theorem fastWriteSized_eq (m : Memory) (size : MemWidth) (ea val : UInt64) :
    fastWriteSized m size ea val = m.writeSized size ea.toBitVec val.toBitVec := by
  cases size <;> simp [fastWriteSized, Memory.writeSized]

@[inline] def fastReadSimdSized (m : Memory) (size : SimdMemSize) (ea : UInt64) : BitVec 128 :=
  match size with
  | .B8   => (fastRead8 m ea).toBitVec.zeroExtend 128
  | .H16  => (fastRead16 m ea).toBitVec.zeroExtend 128
  | .S32  => (fastRead32 m ea).toBitVec.zeroExtend 128
  | .D64  => (fastRead64 m ea).toBitVec.zeroExtend 128
  | .Q128 => (fastRead64 m (ea + 8)).toBitVec ++ (fastRead64 m ea).toBitVec

@[simp] theorem fastReadSimdSized_eq (m : Memory) (size : SimdMemSize) (ea : UInt64) :
    fastReadSimdSized m size ea = m.readSimdSized size ea.toBitVec := by
  cases size <;> simp [fastReadSimdSized, Memory.readSimdSized, Memory.read128, UInt64.toBitVec_add]

@[inline] def fastWriteSimdSized (m : Memory) (size : SimdMemSize) (ea : UInt64) (val : BitVec 128) : Memory :=
  match size with
  | .B8   => fastWrite8 m ea ⟨val.truncate 64⟩
  | .H16  => fastWrite16 m ea ⟨val.truncate 64⟩
  | .S32  => fastWrite32 m ea ⟨val.truncate 64⟩
  | .D64  => fastWrite64 m ea ⟨val.truncate 64⟩
  | .Q128 =>
    let m := fastWrite64 m ea ⟨val.extractLsb' 0 64⟩
    fastWrite64 m (ea + 8) ⟨val.extractLsb' 64 64⟩

@[simp] theorem fastWriteSimdSized_eq (m : Memory) (size : SimdMemSize) (ea : UInt64) (val : BitVec 128) :
    fastWriteSimdSized m size ea val = m.writeSimdSized size ea.toBitVec val := by
  cases size <;> simp [fastWriteSimdSized, Memory.writeSimdSized, Memory.write128, UInt64.toBitVec_add]



/-! ## Per-Class Instruction Handlers -/

@[simp] theorem FastState.toState_pc (s : FastState) : s.toState.pc = s.pc.toBitVec := rfl
@[simp] theorem FastState.toState_sp (s : FastState) : s.toState.sp = s.sp.toBitVec := rfl
@[simp] theorem FastState.toState_pstate (s : FastState) : s.toState.pstate = s.pstate := rfl
@[simp] theorem FastState.toState_mem (s : FastState) : s.toState.mem = s.mem := rfl
@[simp] theorem FastState.toState_status (s : FastState) : s.toState.status = s.status := rfl
@[simp] theorem FastState.toState_fpsr (s : FastState) : s.toState.fpsr = s.fpsr.toBitVec := rfl
@[simp] theorem FastState.toState_tpidrEl0 (s : FastState) : s.toState.tpidrEl0 = s.tpidrEl0.toBitVec := rfl
@[simp] theorem FastState.toState_sigActions (s : FastState) : s.toState.sigActions = s.sigActions := rfl
@[simp] theorem FastState.toState_sigAltStack (s : FastState) : s.toState.sigAltStack = s.sigAltStack := rfl

@[simp] theorem FastState.toState_ite (c : Prop) [Decidable c] (a b : FastState) :
    (if c then a else b).toState = if c then a.toState else b.toState := by
  split <;> rfl

@[simp] theorem toBitVec_ite_u64 (c : Prop) [Decidable c] (a b : UInt64) :
    (if c then a else b).toBitVec = if c then a.toBitVec else b.toBitVec := by
  split <;> rfl

@[simp] theorem toBitVec_ite_u32 (c : Prop) [Decidable c] (a b : UInt32) :
    (if c then a else b).toBitVec = if c then a.toBitVec else b.toBitVec := by
  split <;> rfl

@[simp] theorem FastState.toNat_readReg (s : FastState) (w : Width) (r : Reg) :
    (s.readReg w r).toNat = (s.toState.readReg w r).toNat := by
  rw [← UInt64.toNat_toBitVec, FastState.toBitVec_readReg]

@[simp] theorem u64_eq_zero_iff (a : UInt64) : (a = 0) ↔ (a.toBitVec = 0#64) :=
  UInt64.toBitVec_inj.symm

@[simp] theorem u32_eq_zero_iff (a : UInt32) : (a = 0) ↔ (a.toBitVec = 0#32) :=
  UInt32.toBitVec_inj.symm

@[simp, reducible, inline] def fastApplyWb (s : FastState) (wb : Option (Reg × UInt64)) : FastState :=
  match wb with
  | some (base, newBase) => s.writeReg64 base newBase
  | none => s

@[simp, reducible, inline] def fastApplyOptPState (s : FastState) (optPs : Option PState) : FastState :=
  match optPs with
  | some ps => s.setPState ps
  | none => s

@[inline] def fastShiftLeft64Nat (x : UInt64) (n : Nat) : UInt64 :=
  if n < 64 then x <<< UInt64.ofNat n else 0

@[simp] theorem toBitVec_fastShiftLeft64Nat (x : UInt64) (n : Nat) :
    (fastShiftLeft64Nat x n).toBitVec = x.toBitVec <<< n := by
  simp only [fastShiftLeft64Nat]
  split
  · next h => simp [Nat.mod_eq_of_lt h]
  · next h =>
    ext i hi
    simp [show ¬(i ≥ n) by omega]

def fastExecLdr (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg) (addr : AddrMode) (s : FastState) : FastState :=
  if !fastCheckAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := fastEvalAddrMode s addr
    if !fastCanRead s.mem ea size.bytes then
      s.setStatus (.Exception "permission fault")
    else
      let val := fastReadSized s.mem size signed ea
      let s1 := fastApplyWb s wb
      (s1.writeReg w rt val).advancePC

@[simp] theorem fastExecLdr_toState (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg) (addr : AddrMode) (s : FastState) :
    (fastExecLdr w size signed rt addr s).toState = execLdr w size signed rt addr s.toState := by
  cases addr <;> simp [fastExecLdr, execLdr, fastEvalAddrMode, evalAddrMode, UInt64.toBitVec_add]

def fastExecLdrLit (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg) (offset : BitVec 64) (s : FastState) : FastState :=
  let ea := s.pc + ⟨offset⟩
  if !fastCanRead s.mem ea size.bytes then
    s.setStatus (.Exception "permission fault")
  else
    let val := fastReadSized s.mem size signed ea
    (s.writeReg w rt val).advancePC

@[simp] theorem fastExecLdrLit_toState (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg) (offset : BitVec 64) (s : FastState) :
    (fastExecLdrLit w size signed rt offset s).toState = execLdrLit w size signed rt offset s.toState := by
  simp [fastExecLdrLit, execLdrLit, UInt64.toBitVec_add]

def fastExecStr (size : MemWidth) (rt : Reg) (addr : AddrMode) (s : FastState) : FastState :=
  if !fastCheckAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := fastEvalAddrMode s addr
    if !fastCanWrite s.mem ea size.bytes then
      s.setStatus (.Exception "permission fault")
    else
      let val := s.readReg64 rt
      let s1 := s.setMem (fastWriteSized s.mem size ea val)
      let s2 := fastApplyWb s1 wb
      s2.advancePC

@[simp] theorem fastExecStr_toState (size : MemWidth) (rt : Reg) (addr : AddrMode) (s : FastState) :
    (fastExecStr size rt addr s).toState = execStr size rt addr s.toState := by
  cases addr <;> simp [fastExecStr, execStr, fastEvalAddrMode, evalAddrMode, UInt64.toBitVec_add]

def fastExecLdp (w : Width) (signed : Bool) (rt1 rt2 : Reg) (addr : AddrMode) (s : FastState) : FastState :=
  if !fastCheckAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := fastEvalAddrMode s addr
    let stepBytes : UInt64 := if signed then 4 else match w with | .W32 => 4 | .W64 => 8
    let sz : MemWidth := if signed then .W32 else match w with | .W32 => .W32 | .W64 => .X64
    if !(fastCanRead s.mem ea sz.bytes && fastCanRead s.mem (ea + stepBytes) sz.bytes) then
      s.setStatus (.Exception "permission fault")
    else
      let v1 := fastReadSized s.mem sz signed ea
      let v2 := fastReadSized s.mem sz signed (ea + stepBytes)
      let outW : Width := if signed then .W64 else w
      let s1 := fastApplyWb s wb
      let s2 := s1.writeReg outW rt1 v1
      let s3 := s2.writeReg outW rt2 v2
      s3.advancePC

@[simp] theorem fastExecLdp_toState (w : Width) (signed : Bool) (rt1 rt2 : Reg) (addr : AddrMode) (s : FastState) :
    (fastExecLdp w signed rt1 rt2 addr s).toState = execLdp w signed rt1 rt2 addr s.toState := by
  cases signed <;> cases w <;> cases addr <;>
    simp [fastExecLdp, execLdp, fastEvalAddrMode, evalAddrMode, UInt64.toBitVec_add]

def fastExecStp (w : Width) (rt1 rt2 : Reg) (addr : AddrMode) (s : FastState) : FastState :=
  if !fastCheckAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := fastEvalAddrMode s addr
    let stepBytes : UInt64 := match w with | .W32 => 4 | .W64 => 8
    let sz : MemWidth := match w with | .W32 => .W32 | .W64 => .X64
    if !(fastCanWrite s.mem ea sz.bytes && fastCanWrite s.mem (ea + stepBytes) sz.bytes) then
      s.setStatus (.Exception "permission fault")
    else
      let v1 := s.readReg64 rt1
      let v2 := s.readReg64 rt2
      let m1 := fastWriteSized s.mem sz ea v1
      let m2 := fastWriteSized m1 sz (ea + stepBytes) v2
      let s1 := s.setMem m2
      let s2 := fastApplyWb s1 wb
      s2.advancePC

@[simp] theorem fastExecStp_toState (w : Width) (rt1 rt2 : Reg) (addr : AddrMode) (s : FastState) :
    (fastExecStp w rt1 rt2 addr s).toState = execStp w rt1 rt2 addr s.toState := by
  cases w <;> cases addr <;>
    simp [fastExecStp, execStp, fastEvalAddrMode, evalAddrMode, UInt64.toBitVec_add]

def fastExecAddSubImm (w : Width) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12) (shift12 : Bool) (s : FastState) : FastState :=
  let x := s.readReg w rn
  let imm64 : UInt64 := ⟨imm12.zeroExtend 64⟩
  let imm : UInt64 := if shift12 then fastShiftLeft64Nat imm64 12 else imm64
  let (res, optPs) := fastEvalAddSub w op x imm none
  let s1 := s.writeReg w rd res
  let s2 := fastApplyOptPState s1 optPs
  s2.advancePC

@[simp] theorem fastExecAddSubImm_toState (w : Width) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12) (shift12 : Bool) (s : FastState) :
    (fastExecAddSubImm w op rd rn imm12 shift12 s).toState = execAddSubImm w op rd rn imm12 shift12 s.toState := by
  cases shift12 <;> (simp [fastExecAddSubImm, execAddSubImm]; split <;> simp [*])

def fastExecAddSubExt (w : Width) (op : AddSubOp) (rd rn rm : Reg) (ext : ExtendType) (amount : Nat) (s : FastState) : FastState :=
  let x := s.readReg w rn
  let y := fastExtendVal w (s.readReg64 rm) ext amount
  let (res, optPs) := fastEvalAddSub w op x y none
  let s1 := s.writeReg w rd res
  let s2 := fastApplyOptPState s1 optPs
  s2.advancePC

@[simp] theorem fastExecAddSubExt_toState (w : Width) (op : AddSubOp) (rd rn rm : Reg) (ext : ExtendType) (amount : Nat) (s : FastState) :
    (fastExecAddSubExt w op rd rn rm ext amount s).toState = execAddSubExt w op rd rn rm ext amount s.toState := by
  simp [fastExecAddSubExt, execAddSubExt]; split <;> simp [*]

def fastExecAddSubShift (w : Width) (op : AddSubOp) (rd rn rm : Reg) (shift : ShiftType) (amount : Nat) (s : FastState) : FastState :=
  let x := s.readReg w rn
  let y := fastShiftVal w (s.readReg w rm) shift amount
  let (res, optPs) := fastEvalAddSub w op x y none
  let s1 := s.writeReg w rd res
  let s2 := fastApplyOptPState s1 optPs
  s2.advancePC

@[simp] theorem fastExecAddSubShift_toState (w : Width) (op : AddSubOp) (rd rn rm : Reg) (shift : ShiftType) (amount : Nat) (s : FastState) :
    (fastExecAddSubShift w op rd rn rm shift amount s).toState = execAddSubShift w op rd rn rm shift amount s.toState := by
  simp [fastExecAddSubShift, execAddSubShift]; split <;> simp [*]

def fastExecAddSubCarry (w : Width) (op : AddSubOp) (rd rn rm : Reg) (s : FastState) : FastState :=
  let x := s.readReg w rn
  let y := s.readReg w rm
  let (res, optPs) := fastEvalAddSub w op x y (some s.pstate.c)
  let s1 := s.writeReg w rd res
  let s2 := fastApplyOptPState s1 optPs
  s2.advancePC

@[simp] theorem fastExecAddSubCarry_toState (w : Width) (op : AddSubOp) (rd rn rm : Reg) (s : FastState) :
    (fastExecAddSubCarry w op rd rn rm s).toState = execAddSubCarry w op rd rn rm s.toState := by
  simp [fastExecAddSubCarry, execAddSubCarry]; split <;> simp [*]

def fastExecLogicalImm (w : Width) (op : LogicalOp) (rd rn : Reg) (mask : BitVec 64) (s : FastState) : FastState :=
  let x := s.readReg w rn
  let (res, optPs) := fastEvalLogical w op x ⟨mask⟩ s.pstate
  let s1 := s.writeReg w rd res
  let s2 := fastApplyOptPState s1 optPs
  s2.advancePC

@[simp] theorem fastExecLogicalImm_toState (w : Width) (op : LogicalOp) (rd rn : Reg) (mask : BitVec 64) (s : FastState) :
    (fastExecLogicalImm w op rd rn mask s).toState = execLogicalImm w op rd rn mask s.toState := by
  simp [fastExecLogicalImm, execLogicalImm]; split <;> simp [*]

def fastExecLogicalShift (w : Width) (op : LogicalOp) (rd rn rm : Reg) (shift : ShiftType) (amount : Nat) (s : FastState) : FastState :=
  let x := s.readReg w rn
  let y := fastShiftVal w (s.readReg w rm) shift amount
  let (res, optPs) := fastEvalLogical w op x y s.pstate
  let s1 := s.writeReg w rd res
  let s2 := fastApplyOptPState s1 optPs
  s2.advancePC

@[simp] theorem fastExecLogicalShift_toState (w : Width) (op : LogicalOp) (rd rn rm : Reg) (shift : ShiftType) (amount : Nat) (s : FastState) :
    (fastExecLogicalShift w op rd rn rm shift amount s).toState = execLogicalShift w op rd rn rm shift amount s.toState := by
  simp [fastExecLogicalShift, execLogicalShift]; split <;> simp [*]

def fastExecMoveWide (w : Width) (op : MoveWideOp) (rd : Reg) (imm16 : BitVec 16) (hw : Nat) (s : FastState) : FastState :=
  let shifted : UInt64 := fastShiftLeft64Nat (UInt16.ofBitVec imm16).toUInt64 hw
  let res : UInt64 :=
    match op with
    | .MOVZ => shifted
    | .MOVN => ~~~shifted
    | .MOVK =>
      let old := s.readReg w rd
      let clearMask := ~~~(fastShiftLeft64Nat 0xffff hw)
      (old &&& clearMask) ||| shifted
  (s.writeReg w rd res).advancePC

@[simp] theorem fastExecMoveWide_toState (w : Width) (op : MoveWideOp) (rd : Reg) (imm16 : BitVec 16) (hw : Nat) (s : FastState) :
    (fastExecMoveWide w op rd imm16 hw s).toState = execMoveWide w op rd imm16 hw s.toState := by
  cases op <;> simp [fastExecMoveWide, execMoveWide]

def fastExecBitfield (w : Width) (op : BitfieldOp) (rd rn : Reg) (immr imms : Nat) (s : FastState) : FastState :=
  let dst := s.readReg w rd
  let src := s.readReg w rn
  let res : UInt64 := ⟨evalBitfield w op dst.toBitVec src.toBitVec immr imms⟩
  (s.writeReg w rd res).advancePC

@[simp] theorem fastExecBitfield_toState (w : Width) (op : BitfieldOp) (rd rn : Reg) (immr imms : Nat) (s : FastState) :
    (fastExecBitfield w op rd rn immr imms s).toState = execBitfield w op rd rn immr imms s.toState := by
  simp [fastExecBitfield, execBitfield]

def fastExecCondSelect (w : Width) (op : CondSelectOp) (rd rn rm : Reg) (cond : CondCode) (s : FastState) : FastState :=
  let holds := ConditionHolds cond s.pstate
  let res : UInt64 :=
    if holds then
      s.readReg w rn
    else
      let mVal := s.readReg w rm
      match op with
      | .CSEL  => mVal
      | .CSINC => mVal + 1
      | .CSINV => ~~~mVal
      | .CSNEG => 0 - mVal
  (s.writeReg w rd res).advancePC

@[simp] theorem fastExecCondSelect_toState (w : Width) (op : CondSelectOp) (rd rn rm : Reg) (cond : CondCode) (s : FastState) :
    (fastExecCondSelect w op rd rn rm cond s).toState = execCondSelect w op rd rn rm cond s.toState := by
  cases op <;> simp [fastExecCondSelect, execCondSelect, UInt64.toBitVec_add] <;> rfl

def fastExecCondCompare (w : Width) (isSub : Bool) (isImm : Bool)
    (rn : Reg) (rhs : UInt64) (rm : Reg) (nzcv : BitVec 4) (cond : CondCode) (s : FastState) : FastState :=
  if ConditionHolds cond s.pstate then
    let x := s.readReg w rn
    let y := if isImm then rhs else s.readReg w rm
    let op : AddSubOp := if isSub then .SUBS else .ADDS
    let (_, optPs) := fastEvalAddSub w op x y none
    (fastApplyOptPState s optPs).advancePC
  else
    (s.setPState (PState.ofBits4 nzcv)).advancePC

@[simp] theorem fastExecCondCompare_toState (w : Width) (isSub isImm : Bool)
    (rn : Reg) (rhs : UInt64) (rm : Reg) (nzcv : BitVec 4) (cond : CondCode) (s : FastState) :
    (fastExecCondCompare w isSub isImm rn rhs rm nzcv cond s).toState =
      execCondCompare w isSub isImm rn rhs.toBitVec rm nzcv cond s.toState := by
  by_cases h : ConditionHolds cond s.pstate <;> cases isImm <;>
    (simp [fastExecCondCompare, execCondCompare, h]; try (split <;> simp [*]))

def fastExecDataProc1 (w : Width) (op : DataProc1Op) (rd rn : Reg) (s : FastState) : FastState :=
  let v := (s.readReg w rn).toBitVec
  let res : BitVec 64 :=
    match w, op with
    | .W32, .RBIT  => (reverseBits (v.truncate 32)).zeroExtend 64
    | .W64, .RBIT  => reverseBits v
    | .W32, .REV16 => ((rev16_64 v).truncate 32).zeroExtend 64
    | .W64, .REV16 => rev16_64 v
    | .W32, .REV32 => ((rev32_64 v).truncate 32).zeroExtend 64
    | .W64, .REV32 => rev32_64 v
    | .W32, .REV   => ((rev32_64 v).truncate 32).zeroExtend 64
    | .W64, .REV   => rev64 v
    | .W32, .CLZ   => BitVec.ofNat 64 (countLeadingZeros (v.truncate 32))
    | .W64, .CLZ   => BitVec.ofNat 64 (countLeadingZeros v)
    | .W32, .CLS   => BitVec.ofNat 64 (countLeadingSigns (v.truncate 32))
    | .W64, .CLS   => BitVec.ofNat 64 (countLeadingSigns v)
  (s.writeReg w rd ⟨res⟩).advancePC

@[simp] theorem fastExecDataProc1_toState (w : Width) (op : DataProc1Op) (rd rn : Reg) (s : FastState) :
    (fastExecDataProc1 w op rd rn s).toState = execDataProc1 w op rd rn s.toState := by
  cases w <;> cases op <;> simp [fastExecDataProc1, execDataProc1]

def fastExecDataProc2 (w : Width) (op : DataProc2Op) (rd rn rm : Reg) (s : FastState) : FastState :=
  let x := s.readReg w rn
  let y := s.readReg w rm
  let res : UInt64 :=
    match w, op with
    | .W32, .UDIV =>
      let x32 := x.toUInt32
      let y32 := y.toUInt32
      (if y32 == 0 then 0 else x32 / y32).toUInt64
    | .W64, .UDIV =>
      if y == 0 then 0 else x / y
    | .W32, .SDIV =>
      let x32 := x.toBitVec.truncate 32
      let y32 := y.toBitVec.truncate 32
      ⟨(if y32 == 0#32 then 0#32 else BitVec.sdiv x32 y32).zeroExtend 64⟩
    | .W64, .SDIV =>
      ⟨if y.toBitVec == 0#64 then 0#64 else BitVec.sdiv x.toBitVec y.toBitVec⟩
    | .W32, .LSLV => (fastShift32 x.toUInt32 .LSL y.toUInt32.toNat).toUInt64
    | .W64, .LSLV => fastShift64 x .LSL y.toNat
    | .W32, .LSRV => (fastShift32 x.toUInt32 .LSR y.toUInt32.toNat).toUInt64
    | .W64, .LSRV => fastShift64 x .LSR y.toNat
    | .W32, .ASRV => (fastShift32 x.toUInt32 .ASR y.toUInt32.toNat).toUInt64
    | .W64, .ASRV => fastShift64 x .ASR y.toNat
    | .W32, .RORV => (fastShift32 x.toUInt32 .ROR y.toUInt32.toNat).toUInt64
    | .W64, .RORV => fastShift64 x .ROR y.toNat
  (s.writeReg w rd res).advancePC

@[simp] theorem fastExecDataProc2_toState (w : Width) (op : DataProc2Op) (rd rn rm : Reg) (s : FastState) :
    (fastExecDataProc2 w op rd rn rm s).toState = execDataProc2 w op rd rn rm s.toState := by
  cases w <;> cases op <;> simp [fastExecDataProc2, execDataProc2, -UInt32.toUInt64_div]

def fastExecDataProc3 (w : Width) (op : DataProc3Op) (rd rn rm ra : Reg) (s : FastState) : FastState :=
  let res : UInt64 :=
    match op with
    | .MADD =>
      match w with
      | .W32 => (s.readReg32 ra + s.readReg32 rn * s.readReg32 rm).toUInt64
      | .W64 => s.readReg64 ra + s.readReg64 rn * s.readReg64 rm
    | .MSUB =>
      match w with
      | .W32 => (s.readReg32 ra - s.readReg32 rn * s.readReg32 rm).toUInt64
      | .W64 => s.readReg64 ra - s.readReg64 rn * s.readReg64 rm
    | .SMADDL =>
      let n64 := signExtend32To64 (s.readReg32 rn)
      let m64 := signExtend32To64 (s.readReg32 rm)
      s.readReg64 ra + n64 * m64
    | .SMSUBL =>
      let n64 := signExtend32To64 (s.readReg32 rn)
      let m64 := signExtend32To64 (s.readReg32 rm)
      s.readReg64 ra - n64 * m64
    | .UMADDL =>
      let n64 := (s.readReg32 rn).toUInt64
      let m64 := (s.readReg32 rm).toUInt64
      s.readReg64 ra + n64 * m64
    | .UMSUBL =>
      let n64 := (s.readReg32 rn).toUInt64
      let m64 := (s.readReg32 rm).toUInt64
      s.readReg64 ra - n64 * m64
    | .SMULH =>
      let n128 := (s.readReg64 rn).toBitVec.signExtend 128
      let m128 := (s.readReg64 rm).toBitVec.signExtend 128
      ⟨((n128 * m128) >>> 64).truncate 64⟩
    | .UMULH =>
      fastUmulh (s.readReg64 rn) (s.readReg64 rm)
  (s.writeReg w rd res).advancePC

@[simp] theorem fastExecDataProc3_toState (w : Width) (op : DataProc3Op) (rd rn rm ra : Reg) (s : FastState) :
    (fastExecDataProc3 w op rd rn rm ra s).toState = execDataProc3 w op rd rn rm ra s.toState := by
  cases op <;> cases w <;>
    simp [fastExecDataProc3, execDataProc3, UInt64.toBitVec_add, UInt64.toBitVec_sub, UInt64.toBitVec_mul,
          -UInt32.toUInt64_add, -UInt32.toUInt64_sub, -UInt32.toUInt64_mul]

def fastExecLdpSimd (sz : SimdMemSize) (vt1 vt2 : BitVec 5) (addr : AddrMode) (s : FastState) : FastState :=
  if !fastCheckAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := fastEvalAddrMode s addr
    let stepBytes : UInt64 :=
      match sz with | .B8 => 1 | .H16 => 2 | .S32 => 4 | .D64 => 8 | .Q128 => 16
    if !(fastCanRead s.mem ea sz.bytes && fastCanRead s.mem (ea + stepBytes) sz.bytes) then
      s.setStatus (.Exception "permission fault")
    else
      let v1 := fastReadSimdSized s.mem sz ea
      let v2 := fastReadSimdSized s.mem sz (ea + stepBytes)
      let s1 := fastApplyWb s wb
      let s2 := s1.writeVReg128 vt1 v1
      let s3 := s2.writeVReg128 vt2 v2
      s3.advancePC

def fastExecStpSimd (sz : SimdMemSize) (vt1 vt2 : BitVec 5) (addr : AddrMode) (s : FastState) : FastState :=
  if !fastCheckAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := fastEvalAddrMode s addr
    let stepBytes : UInt64 :=
      match sz with | .B8 => 1 | .H16 => 2 | .S32 => 4 | .D64 => 8 | .Q128 => 16
    if !(fastCanWrite s.mem ea sz.bytes && fastCanWrite s.mem (ea + stepBytes) sz.bytes) then
      s.setStatus (.Exception "permission fault")
    else
      let v1 := s.readVReg128 vt1
      let v2 := s.readVReg128 vt2
      let m1 := fastWriteSimdSized s.mem sz ea v1
      let m2 := fastWriteSimdSized m1 sz (ea + stepBytes) v2
      let s1 := s.setMem m2
      let s2 := fastApplyWb s1 wb
      s2.advancePC

def fastExecLdrSimd (sz : SimdMemSize) (vt : BitVec 5) (addr : AddrMode) (s : FastState) : FastState :=
  if !fastCheckAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := fastEvalAddrMode s addr
    if !fastCanRead s.mem ea sz.bytes then
      s.setStatus (.Exception "permission fault")
    else
      let val := fastReadSimdSized s.mem sz ea
      let s1 := fastApplyWb s wb
      (s1.writeVReg128 vt val).advancePC

def fastExecStrSimd (sz : SimdMemSize) (vt : BitVec 5) (addr : AddrMode) (s : FastState) : FastState :=
  if !fastCheckAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := fastEvalAddrMode s addr
    if !fastCanWrite s.mem ea sz.bytes then
      s.setStatus (.Exception "permission fault")
    else
      let val := s.readVReg128 vt
      let s1 := s.setMem (fastWriteSimdSized s.mem sz ea val)
      let s2 := fastApplyWb s1 wb
      s2.advancePC

@[inline] def fastApplySimdResult (s : FastState) (rd : BitVec 5) (r : Except String (BitVec 128)) : FastState :=
  match r with
  | .ok res => (s.writeVReg128 rd res).advancePC
  | .error msg => { s with status := .Exception msg }

@[simp] theorem toState_fastApplySimdResult (s : FastState) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    (fastApplySimdResult s rd r).toState = applySimdResult s.toState rd r := by
  cases r with
  | ok res => simp [fastApplySimdResult, applySimdResult]
  | error msg => rfl

@[inline] def fastApplySimdSatResult (s : FastState) (rd : BitVec 5) (r : Except String (BitVec 128))
    (satFlags : Option (BitVec 32)) : FastState :=
  match r, satFlags with
  | .ok res, none => (s.writeVReg128 rd res).advancePC
  | .ok res, some flags => ((s.writeVReg128 rd res).orFpsr ⟨flags⟩).advancePC
  | .error msg, _ => { s with status := .Exception msg }

@[simp] theorem toState_fastApplySimdSatResult (s : FastState) (rd : BitVec 5) (r : Except String (BitVec 128))
    (satFlags : Option (BitVec 32)) :
    (fastApplySimdSatResult s rd r satFlags).toState = applySimdSatResult s.toState rd r satFlags := by
  cases r with
  | ok res =>
    cases satFlags <;> simp [fastApplySimdSatResult, applySimdSatResult]
  | error msg =>
    cases satFlags <;> rfl

def fastExecSimdImmShift (q op : Bool) (immh : BitVec 4) (immb : BitVec 3) (opc : BitVec 5)
    (rn rd : BitVec 5) (s : FastState) : FastState :=
  if immh == 0#4 then
    if opc.getLsbD 0 then
      fastApplySimdResult s rd (evalSimdModImmExt q op immb opc rn (s.readVReg128 rd))
    else
      let imm8 : BitVec 8 := immb ++ rn
      let cmode := opc.extractLsb' 1 4
      let writeD64 (d64 : BitVec 64) : FastState :=
        let res128 : BitVec 128 := if q then d64 ++ d64 else d64.zeroExtend 128
        (s.writeVReg128 rd res128).advancePC
      if !op && cmode == 0b1110#4 then
        writeD64 (imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8)
      else if op && cmode == 0b1110#4 then
        let b (i : Nat) : BitVec 8 := if imm8.getLsbD i then 0xff#8 else 0x00#8
        writeD64 (b 7 ++ b 6 ++ b 5 ++ b 4 ++ b 3 ++ b 2 ++ b 1 ++ b 0)
      else if !op && (cmode &&& 0b1001#4) == 0b0000#4 then
        let sh := (cmode.extractLsb' 1 2).toNat * 8
        let w32 : BitVec 32 := (imm8.zeroExtend 32) <<< sh
        writeD64 (w32 ++ w32)
      else if !op && (cmode &&& 0b1101#4) == 0b1000#4 then
        let sh := (cmode.extractLsb' 1 1).toNat * 8
        let h16 : BitVec 16 := (imm8.zeroExtend 16) <<< sh
        writeD64 (h16 ++ h16 ++ h16 ++ h16)
      else
        fastApplySimdResult s rd (evalSimdModImmExt q op immb opc rn (s.readVReg128 rd))
  else
    let immhb := (immh ++ immb).toNat
    let esize := if immhb >= 64 then 64 else if immhb >= 32 then 32 else if immhb >= 16 then 16 else 8
    let shiftLeftAmt := immhb - esize
    let shiftRightAmt := 2 * esize - immhb
    let vn := s.readVReg128 rn
    if !op && opc == 0b01010#5 && !(immh.getLsbD 3 && !q) then
      let res := mapSimdLanes q esize vn (fun lane => lane <<< shiftLeftAmt)
      (s.writeVReg128 rd res).advancePC
    else if op && opc == 0b10100#5 && !immh.getLsbD 3 then
      let half : BitVec 64 := if q then vn.extractLsb' 64 64 else vn.truncate 64
      let dstEsize := 2 * esize
      let numLanes := 64 / esize
      let srcMask : BitVec 64 := (1#64 <<< esize) - 1#64
      let res : BitVec 128 := Id.run do
        let mut acc : BitVec 128 := 0#128
        for i in [0:numLanes] do
          let lane64 := (half >>> (i * esize)) &&& srcMask
          let wide128 := (lane64.zeroExtend 128) <<< shiftLeftAmt
          acc := acc ||| (wide128 <<< (i * dstEsize))
        return acc
      (s.writeVReg128 rd res).advancePC
    else if op && opc == 0b00000#5 && !(immh.getLsbD 3 && !q) then
      let res := mapSimdLanes q esize vn (fun lane => lane >>> shiftRightAmt)
      (s.writeVReg128 rd res).advancePC
    else if op && (opc == 0b01000#5 || opc == 0b01010#5) && !(immh.getLsbD 3 && !q) then
      let isSli := opc == 0b01010#5
      let laneMask : BitVec 128 := (1#128 <<< esize) - 1#128
      let res := zipSimdLanes q esize vn (s.readVReg128 rd) (fun a d =>
        let m : BitVec 128 :=
          if isSli then (laneMask <<< shiftLeftAmt) &&& laneMask else laneMask >>> shiftRightAmt
        let sh := if isSli then (a <<< shiftLeftAmt) &&& laneMask else a >>> shiftRightAmt
        (d &&& ~~~m) ||| (sh &&& m))
      (s.writeVReg128 rd res).advancePC
    else
      fastApplySimdSatResult s rd
        (evalSimdImmShiftNonZeroExt q op immh immb opc (s.readVReg128 rd) vn)
        (evalSimdImmShiftNonZeroExtSatFlags q op immh immb opc vn)

def fastExecSimdInsDup (q op : Bool) (imm5 : BitVec 5) (imm4 : BitVec 4)
    (rn rd : BitVec 5) (s : FastState) : FastState :=
  if (imm5.extractLsb' 0 4) == 0#4 then
    { s with status := .Exception s!"unsupported AdvSIMD: simdInsDup (q={if q then 1 else 0} op={if op then 1 else 0} imm5={imm5.toNat} imm4={imm4.toNat}) — architecturally UNDEFINED" }
  else
    let esize : Nat :=
      if (imm5.extractLsb' 0 1) == 1#1 then 8
      else if (imm5.extractLsb' 0 2) == 2#2 then 16
      else if (imm5.extractLsb' 0 3) == 4#3 then 32
      else 64
    let dstIdx : Nat :=
      if esize == 8 then imm5.toNat >>> 1
      else if esize == 16 then imm5.toNat >>> 2
      else if esize == 32 then imm5.toNat >>> 3
      else imm5.toNat >>> 4
    let mask : BitVec 128 := (1#128 <<< esize) - 1#128
    if !op && imm4 == 0b0001#4 && !(esize == 64 && !q) then
      let elem := (((s.readReg64 (Reg.fromZRBits rn)).toBitVec).zeroExtend 128) &&& mask
      let res := mapSimdLanes q esize 0#128 (fun _ => elem)
      (s.writeVReg128 rd res).advancePC
    else if !op && imm4 == 0b0000#4 && !(esize == 64 && !q) then
      let elem := getSimdLane (s.readVReg128 rn) esize dstIdx
      let res := mapSimdLanes q esize 0#128 (fun _ => elem)
      (s.writeVReg128 rd res).advancePC
    else if q && !op && imm4 == 0b0011#4 then
      let elem := (((s.readReg64 (Reg.fromZRBits rn)).toBitVec).zeroExtend 128) &&& mask
      let old := s.readVReg128 rd
      let clearMask := ~~~(mask <<< (dstIdx * esize))
      let res := (old &&& clearMask) ||| (elem <<< (dstIdx * esize))
      (s.writeVReg128 rd res).advancePC
    else if !op && imm4 == 0b0111#4 && ((q && esize == 64) || (!q && esize < 64)) then
      let elem := (getSimdLane (s.readVReg128 rn) esize dstIdx).truncate 64
      let w : Width := if q then .W64 else .W32
      (s.writeReg w (Reg.fromZRBits rd) ⟨elem⟩).advancePC
    else if !op && imm4 == 0b0101#4 && ((q && esize < 64) || (!q && esize < 32)) then
      let elem := (getSimdLane (s.readVReg128 rn) esize dstIdx).truncate 64
      let signExt :=
        if elem.getLsbD (esize - 1) then elem ||| ~~~((1#64 <<< esize) - 1#64) else elem
      let w : Width := if q then .W64 else .W32
      (s.writeReg w (Reg.fromZRBits rd) ⟨signExt⟩).advancePC
    else if q && op then
      let srcIdx : Nat :=
        if esize == 8 then imm4.toNat
        else if esize == 16 then imm4.toNat >>> 1
        else if esize == 32 then imm4.toNat >>> 2
        else imm4.toNat >>> 3
      let elem := getSimdLane (s.readVReg128 rn) esize srcIdx
      let old := s.readVReg128 rd
      let clearMask := ~~~(mask <<< (dstIdx * esize))
      let res := (old &&& clearMask) ||| (elem <<< (dstIdx * esize))
      (s.writeVReg128 rd res).advancePC
    else
      { s with status := .Exception s!"unsupported AdvSIMD: simdInsDup (q={if q then 1 else 0} op={if op then 1 else 0} imm5={imm5.toNat} imm4={imm4.toNat}) — architecturally UNDEFINED" }

def fastExecSimdThreeSame (q u : Bool) (size : BitVec 2) (rm : BitVec 5) (opcode : BitVec 5)
    (rn rd : BitVec 5) (s : FastState) : FastState :=
  let vn := s.readVReg128 rn
  let vm := s.readVReg128 rm
  let esize := 8 <<< size.toNat
  let laneMask : BitVec 128 := (1#128 <<< esize) - 1#128
  let truncQ (v : BitVec 128) : BitVec 128 := if q then v else (v.truncate 64).zeroExtend 128
  if opcode == 0b00011#5 then
    match u, size with
    | false, 0b00#2 => (s.writeVReg128 rd (truncQ (vn &&& vm))).advancePC
    | false, 0b01#2 => (s.writeVReg128 rd (truncQ (vn &&& ~~~vm))).advancePC
    | false, 0b10#2 => (s.writeVReg128 rd (truncQ (vn ||| vm))).advancePC
    | false, 0b11#2 => (s.writeVReg128 rd (truncQ (vn ||| ~~~vm))).advancePC
    | true,  0b00#2 => (s.writeVReg128 rd (truncQ (vn ^^^ vm))).advancePC
    | true,  0b01#2 => (s.writeVReg128 rd (truncQ (((vn ^^^ vm) &&& s.readVReg128 rd) ^^^ vm))).advancePC
    | _, _ =>
      fastApplySimdSatResult s rd
        (evalSimdThreeSameExt q u size opcode (s.readVReg128 rd) vn vm)
        (evalSimdThreeSameExtSatFlags q u size opcode vn vm)
  else if size == 0b11#2 && !q then
    fastApplySimdSatResult s rd
      (evalSimdThreeSameExt q u size opcode (s.readVReg128 rd) vn vm)
      (evalSimdThreeSameExtSatFlags q u size opcode vn vm)
  else if opcode == 0b10000#5 then
    let res := zipSimdLanes q esize vn vm (fun a b => if u then a - b else a + b)
    (s.writeVReg128 rd res).advancePC
  else if opcode == 0b10001#5 then
    let res := zipSimdLanes q esize vn vm (fun a b =>
      let cond := if u then a == b else (a &&& b) != 0#128
      if cond then laneMask else 0#128)
    (s.writeVReg128 rd res).advancePC
  else if opcode == 0b00111#5 then
    let res := zipSimdLanes q esize vn vm (fun a b =>
      let cond :=
        if u then BitVec.ule b a
        else
          let signBit := 1#128 <<< (esize - 1)
          BitVec.ule (b ^^^ signBit) (a ^^^ signBit)
      if cond then laneMask else 0#128)
    (s.writeVReg128 rd res).advancePC
  else if opcode == 0b00110#5 then
    let res := zipSimdLanes q esize vn vm (fun a b =>
      let cond :=
        if u then BitVec.ult b a
        else
          let signBit := 1#128 <<< (esize - 1)
          BitVec.ult (b ^^^ signBit) (a ^^^ signBit)
      if cond then laneMask else 0#128)
    (s.writeVReg128 rd res).advancePC
  else if opcode == 0b01000#5 then
    let res := zipSimdLanes q esize vn vm (fun a b =>
      let shByte : BitVec 8 := b.truncate 8
      let shInt : Int := shByte.toInt
      if shInt >= 0 then
        let amt := shInt.toNat
        if amt >= esize then 0#128 else (a <<< amt) &&& laneMask
      else
        let amt := (-shInt).toNat
        if u || !a.getLsbD (esize - 1) then
          if amt >= esize then 0#128 else a >>> amt
        else
          if amt >= esize then laneMask
          else ((a >>> amt) ||| (laneMask <<< (esize - amt))) &&& laneMask)
    (s.writeVReg128 rd res).advancePC
  else if !u && opcode == 0b10111#5 then
    let elems := (if q then 128 else 64) / esize
    let half := elems / 2
    let pairLane (i : Nat) : BitVec 128 :=
      let src := if i < half then vn else vm
      let j := if i < half then i else i - half
      (getSimdLane src esize (2 * j) + getSimdLane src esize (2 * j + 1)) &&& laneMask
    let res : BitVec 128 := Id.run do
      let mut acc : BitVec 128 := 0#128
      for i in [0:elems] do
        acc := acc ||| (pairLane i <<< (i * esize))
      return acc
    (s.writeVReg128 rd res).advancePC
  else
    fastApplySimdSatResult s rd
      (evalSimdThreeSameExt q u size opcode (s.readVReg128 rd) vn vm)
      (evalSimdThreeSameExtSatFlags q u size opcode vn vm)

def fastExecSimdTwoRegMisc (q u : Bool) (size : BitVec 2) (opcode : BitVec 5)
    (rn rd : BitVec 5) (s : FastState) : FastState :=
  let vn := s.readVReg128 rn
  let esize := 8 <<< size.toNat
  let laneMask : BitVec 128 := (1#128 <<< esize) - 1#128
  if !u && opcode == 0b00000#5 && size != 0b11#2 then
    let subLanes := 64 / esize
    let revDword (d : BitVec 64) : BitVec 64 := Id.run do
      let mut acc : BitVec 64 := 0#64
      let m64 : BitVec 64 := (1#64 <<< esize) - 1#64
      for i in [0:subLanes] do
        let elem := (d >>> (i * esize)) &&& m64
        acc := acc ||| (elem <<< ((subLanes - 1 - i) * esize))
      return acc
    let lo := revDword (vn.truncate 64)
    let hi := if q then revDword (vn.extractLsb' 64 64) else 0#64
    (s.writeVReg128 rd (hi ++ lo)).advancePC
  else if u && opcode == 0b00000#5 && size.toNat < 2 then
    let subLanes := 32 / esize
    let revWord (w : BitVec 32) : BitVec 32 := Id.run do
      let mut acc : BitVec 32 := 0#32
      let m32 : BitVec 64 := (1#64 <<< esize) - 1#64
      for i in [0:subLanes] do
        let elem := (w >>> (i * esize)) &&& (m32.truncate 32)
        acc := acc ||| (elem <<< ((subLanes - 1 - i) * esize))
      return acc
    let w0 := revWord (vn.extractLsb' 0 32)
    let w1 := revWord (vn.extractLsb' 32 32)
    let w2 := if q then revWord (vn.extractLsb' 64 32) else 0#32
    let w3 := if q then revWord (vn.extractLsb' 96 32) else 0#32
    (s.writeVReg128 rd (w3 ++ w2 ++ w1 ++ w0)).advancePC
  else if !u && opcode == 0b01000#5 && !(size == 0b11#2 && !q) then
    let res := mapSimdLanes q esize vn (fun a => if !a.getLsbD (esize - 1) && a != 0#128 then laneMask else 0#128)
    (s.writeVReg128 rd res).advancePC
  else if u && opcode == 0b01000#5 && !(size == 0b11#2 && !q) then
    let res := mapSimdLanes q esize vn (fun a => if !a.getLsbD (esize - 1) then laneMask else 0#128)
    (s.writeVReg128 rd res).advancePC
  else if !u && opcode == 0b01001#5 && !(size == 0b11#2 && !q) then
    let res := mapSimdLanes q esize vn (fun a => if a == 0#128 then laneMask else 0#128)
    (s.writeVReg128 rd res).advancePC
  else if u && opcode == 0b01001#5 && !(size == 0b11#2 && !q) then
    let res := mapSimdLanes q esize vn (fun a => if a.getLsbD (esize - 1) || a == 0#128 then laneMask else 0#128)
    (s.writeVReg128 rd res).advancePC
  else if !u && opcode == 0b01010#5 && !(size == 0b11#2 && !q) then
    let res := mapSimdLanes q esize vn (fun a => if a.getLsbD (esize - 1) then laneMask else 0#128)
    (s.writeVReg128 rd res).advancePC
  else if u && opcode == 0b00101#5 && size == 0b00#2 then
    let raw := ~~~vn
    let res := if q then raw else (raw.truncate 64).zeroExtend 128
    (s.writeVReg128 rd res).advancePC
  else if !u && opcode == 0b00101#5 && size == 0b00#2 then
    let res := mapSimdLanes q 8 vn (fun a =>
      BitVec.ofNat 128 ((List.range 8).countP (fun i => a.getLsbD i)))
    (s.writeVReg128 rd res).advancePC
  else
    let vd := s.readVReg128 rd
    fastApplySimdSatResult s rd
      (evalSimdTwoRegMiscExt q u size opcode vd vn)
      (evalSimdTwoRegMiscExtSatFlags q u size opcode vd vn)

def fastExecSimdPermute (q : Bool) (size : BitVec 2) (rm : BitVec 5) (opcode : BitVec 3)
    (rn rd : BitVec 5) (s : FastState) : FastState :=
  if (opcode == 0b001#3 || opcode == 0b101#3 || opcode == 0b011#3 || opcode == 0b111#3) && !(size == 0b11#2 && !q) then
    let vn := s.readVReg128 rn
    let vm := s.readVReg128 rm
    let esize := 8 <<< size.toNat
    let numLanes := (if q then 128 else 64) / esize
    let halfLanes := numLanes / 2
    let res : BitVec 128 := Id.run do
      let mut acc : BitVec 128 := 0#128
      if opcode == 0b001#3 then
        for i in [0:halfLanes] do
          let e0 := getSimdLane vn esize (2 * i)
          let e1 := getSimdLane vm esize (2 * i)
          acc := acc ||| (e0 <<< (i * esize))
          acc := acc ||| (e1 <<< ((halfLanes + i) * esize))
      else if opcode == 0b101#3 then
        for i in [0:halfLanes] do
          let e0 := getSimdLane vn esize (2 * i + 1)
          let e1 := getSimdLane vm esize (2 * i + 1)
          acc := acc ||| (e0 <<< (i * esize))
          acc := acc ||| (e1 <<< ((halfLanes + i) * esize))
      else if opcode == 0b011#3 then
        for i in [0:halfLanes] do
          let e0 := getSimdLane vn esize i
          let e1 := getSimdLane vm esize i
          acc := acc ||| (e0 <<< ((2 * i) * esize))
          acc := acc ||| (e1 <<< ((2 * i + 1) * esize))
      else
        for i in [0:halfLanes] do
          let e0 := getSimdLane vn esize (halfLanes + i)
          let e1 := getSimdLane vm esize (halfLanes + i)
          acc := acc ||| (e0 <<< ((2 * i) * esize))
          acc := acc ||| (e1 <<< ((2 * i + 1) * esize))
      return acc
    (s.writeVReg128 rd res).advancePC
  else if (opcode == 0b010#3 || opcode == 0b110#3) && !(size == 0b11#2 && !q) then
    let vn := s.readVReg128 rn
    let vm := s.readVReg128 rm
    let esize := 8 <<< size.toNat
    let pairs := ((if q then 128 else 64) / esize) / 2
    let part := if opcode == 0b110#3 then 1 else 0
    let res : BitVec 128 := Id.run do
      let mut acc : BitVec 128 := 0#128
      for p in [0:pairs] do
        acc := acc ||| (getSimdLane vn esize (2 * p + part) <<< ((2 * p) * esize))
        acc := acc ||| (getSimdLane vm esize (2 * p + part) <<< ((2 * p + 1) * esize))
      return acc
    (s.writeVReg128 rd res).advancePC
  else
    { s with status := .Exception s!"unsupported AdvSIMD: simdPermute (q={if q then 1 else 0} size={size.toNat} opcode={opcode.toNat}) — architecturally UNDEFINED" }

def fastExecSimdExt (q : Bool) (rm : BitVec 5) (imm4 : BitVec 4) (rn rd : BitVec 5) (s : FastState) : FastState :=
  if !q && imm4.getLsbD 3 then
    { s with status := .Exception s!"unsupported AdvSIMD: simdExt (q=0 imm4={imm4.toNat}) — architecturally UNDEFINED" }
  else
    let vn := s.readVReg128 rn
    let vm := s.readVReg128 rm
    let idx := imm4.toNat
    if q then
      let pair256 : BitVec 256 := vm ++ vn
      let res128 : BitVec 128 := (pair256 >>> (idx * 8)).truncate 128
      (s.writeVReg128 rd res128).advancePC
    else
      let pair128 : BitVec 128 := (vm.truncate 64) ++ (vn.truncate 64)
      let res64 : BitVec 64 := (pair128 >>> (idx * 8)).truncate 64
      (s.writeVReg64 rd res64).advancePC

/-! ## Top-Level Fast Evaluator and Refinement -/

/-- Execute a single AArch64 `Instr` on `FastState`, delegating `SVC #0` to `svc` and falling back
    to `FastState.ofState (execInstWithSvc svc inst s.toState)` on less-frequent classes. -/
def fastExecInstWithSvc (svc : State → State) (inst : Instr) (s : FastState) : FastState :=
  match inst with
  -- Loads and Stores (GPR)
  | .ldr w sz signed rt addr =>
    fastExecLdr w sz signed rt addr s
  | .ldrLit w signed rt offset =>
    fastExecLdrLit w (if signed then .W32 else (w : MemWidth)) signed rt offset s
  | .str sz rt addr =>
    fastExecStr sz rt addr s
  | .ldp w signed rt1 rt2 addr =>
    fastExecLdp w signed rt1 rt2 addr s
  | .stp w rt1 rt2 addr =>
    fastExecStp w rt1 rt2 addr s

  -- Data Processing: Immediate
  | .adr page rd offset =>
    let base := if page then s.pc &&& 0xfffffffffffff000 else s.pc
    (s.writeReg64 rd (base + ⟨offset⟩)).advancePC
  | .addSubImm w op rd rn imm12 shift12 =>
    fastExecAddSubImm w op rd rn imm12 shift12 s
  | .logicalImm w op rd rn mask =>
    fastExecLogicalImm w op rd rn mask s
  | .moveWide w op rd imm16 hw =>
    fastExecMoveWide w op rd imm16 hw s
  | .bitfield w op rd rn immr imms =>
    fastExecBitfield w op rd rn immr imms s
  | .extr w rd rn rm lsb =>
    let res : UInt64 :=
      match w with
      | .W32 => (fastExtr32 (s.readReg32 rn) (s.readReg32 rm) lsb).toUInt64
      | .W64 => fastExtr64 (s.readReg64 rn) (s.readReg64 rm) lsb
    (s.writeReg w rd res).advancePC

  -- Data Processing: Register
  | .logicalShift w op rd rn rm shift amount =>
    fastExecLogicalShift w op rd rn rm shift amount s
  | .addSubShift w op rd rn rm shift amount =>
    fastExecAddSubShift w op rd rn rm shift amount s
  | .addSubExt w op rd rn rm ext amount =>
    fastExecAddSubExt w op rd rn rm ext amount s
  | .addSubCarry w op rd rn rm =>
    fastExecAddSubCarry w op rd rn rm s
  | .condCompareReg w isSub rn rm nzcv cond =>
    fastExecCondCompare w isSub false rn 0 rm nzcv cond s
  | .condCompareImm w isSub rn imm5 nzcv cond =>
    fastExecCondCompare w isSub true rn ⟨imm5.zeroExtend 64⟩ .xzr nzcv cond s
  | .condSelect w op rd rn rm cond =>
    fastExecCondSelect w op rd rn rm cond s
  | .dataProc1 w op rd rn =>
    fastExecDataProc1 w op rd rn s
  | .dataProc2 w op rd rn rm =>
    fastExecDataProc2 w op rd rn rm s
  | .dataProc3 w op rd rn rm ra =>
    fastExecDataProc3 w op rd rn rm ra s

  -- Control Flow
  | .b offset =>
    s.setPC (s.pc + ⟨offset⟩)
  | .bl offset =>
    let s1 := s.writeReg64 Reg.lr (s.pc + 4)
    s1.setPC (s.pc + ⟨offset⟩)
  | .bCond cond offset =>
    if ConditionHolds cond s.pstate then
      s.setPC (s.pc + ⟨offset⟩)
    else
      s.advancePC
  | .br rn =>
    s.setPC (s.readReg64 rn)
  | .blr rn =>
    let targetAddr := s.readReg64 rn
    let s1 := s.writeReg64 Reg.lr (s.pc + 4)
    s1.setPC targetAddr
  | .ret rn =>
    s.setPC (s.readReg64 rn)
  | .cbz w isNonZero rt offset =>
    let val := s.readReg w rt
    let cond := if isNonZero then (val == 0) != true else val == 0
    if cond then
      s.setPC (s.pc + ⟨offset⟩)
    else
      s.advancePC
  | .tbz _ isNonZero rt bitPos offset =>
    let val := (s.readReg64 rt).toBitVec
    let bit := val.getLsbD bitPos
    if bit == isNonZero then
      s.setPC (s.pc + ⟨offset⟩)
    else
      s.advancePC

  -- Misc / Hints / Barriers
  | .nop =>
    s.advancePC
  | .barrier _ _ =>
    s.advancePC
  | .hint _ =>
    s.advancePC
  | .prfm _ _ =>
    s.advancePC
  | .prfmLit _ _ =>
    s.advancePC

  -- SIMD Loads and Stores
  | .ldpSimd sz vt1 vt2 addr =>
    fastExecLdpSimd sz vt1 vt2 addr s
  | .stpSimd sz vt1 vt2 addr =>
    fastExecStpSimd sz vt1 vt2 addr s
  | .ldrSimd sz vt addr =>
    fastExecLdrSimd sz vt addr s
  | .strSimd sz vt addr =>
    fastExecStrSimd sz vt addr s
  | .ldrSimdLit sz vt offset =>
    let ea := s.pc + ⟨offset⟩
    if !fastCanRead s.mem ea sz.bytes then
      s.setStatus (.Exception "permission fault")
    else
      (s.writeVReg128 vt (fastReadSimdSized s.mem sz ea)).advancePC
  | .ldnp sz rn rt rt2 offset =>
    fastExecLdp (match sz with | .X64 => .W64 | _ => .W32) false rt rt2 (.Offset rn offset) s
  | .stnp sz rn rt rt2 offset =>
    fastExecStp (match sz with | .X64 => .W64 | _ => .W32) rt rt2 (.Offset rn offset) s

  -- SIMD and cryptographic register-to-register classes
  | .aes op vd vn =>
    let dVal := s.readVReg128 vd
    let nVal := s.readVReg128 vn
    let res := evalAesOp op dVal nVal
    (s.writeVReg128 vd res).advancePC
  | .simdImmShift q op immh immb opc rn rd =>
    fastExecSimdImmShift q op immh immb opc rn rd s
  | .simdInsDup q op imm5 imm4 rn rd =>
    fastExecSimdInsDup q op imm5 imm4 rn rd s
  | .simdThreeSame q u size rm opcode rn rd =>
    fastExecSimdThreeSame q u size rm opcode rn rd s
  | .simdTwoRegMisc q u size opcode rn rd =>
    fastExecSimdTwoRegMisc q u size opcode rn rd s
  | .simdPermute q size rm opcode rn rd =>
    fastExecSimdPermute q size rm opcode rn rd s
  | .simdExt q rm imm4 rn rd =>
    fastExecSimdExt q rm imm4 rn rd s
  | .simdTbl q rm len isTbx rn rd =>
    let nTbl := len.toNat + 1
    let tblByte (i : Nat) : BitVec 128 :=
      ((s.readVReg128 (rn + BitVec.ofNat 5 (i / 16))) >>> ((i % 16) * 8)) &&& 0xff#128
    let idxV := s.readVReg128 rm
    let vd := s.readVReg128 rd
    let elems := if q then 16 else 8
    let res : BitVec 128 := Id.run do
      let mut acc : BitVec 128 := 0#128
      for i in [0:elems] do
        let idx := ((idxV >>> (i * 8)) &&& 0xff#128).toNat
        let b : BitVec 128 :=
          if idx < 16 * nTbl then tblByte idx
          else if isTbx then (vd >>> (i * 8)) &&& 0xff#128 else 0#128
        acc := acc ||| (b <<< (i * 8))
      return acc
    (s.writeVReg128 rd res).advancePC
  | .simdAddpScalar rn rd =>
    let vn := s.readVReg128 rn
    (s.writeVReg64 rd (vn.extractLsb' 0 64 + vn.extractLsb' 64 64)).advancePC
  | .simdDupScalar imm5 rn rd =>
    if imm5.extractLsb' 0 4 == 0#4 then
      { s with status := .Exception s!"unsupported AdvSIMD: simdDupScalar (imm5={imm5.toNat}) — architecturally UNDEFINED" }
    else
      (s.writeVReg128 rd (evalSimdDupScalar imm5 (s.readVReg128 rn))).advancePC
  | .simdPmull q is64 rm rn rd =>
    (s.writeVReg128 rd (evalPmull q is64 (s.readVReg128 rn) (s.readVReg128 rm))).advancePC
  | .simdThreeDiff q u size rm opcode rn rd =>
    if !validSimdThreeDiff size opcode then
      { s with status := .Exception s!"unsupported AdvSIMD: simdThreeDiff (q={if q then 1 else 0} u={if u then 1 else 0} size={size.toNat} opcode={opcode.toNat}) — architecturally UNDEFINED or SQDM*" }
    else
      (s.writeVReg128 rd (evalSimdThreeDiff q u size opcode (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC
  | .cryptoSha2Reg opcode rn rd =>
    fastApplySimdResult s rd (evalCryptoSha2Reg opcode (s.readVReg128 rd) (s.readVReg128 rn))
  | .cryptoSha3Reg opcode rm rn rd =>
    fastApplySimdResult s rd (evalCryptoSha3Reg opcode (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))
  | .cryptoSha512Reg2 rn rd =>
    (s.writeVReg128 rd (evalCryptoSha512Reg2 (s.readVReg128 rd) (s.readVReg128 rn))).advancePC
  | .cryptoSha512Reg3 opcode rm rn rd =>
    (s.writeVReg128 rd (evalCryptoSha512Reg3 opcode (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC
  | .cryptoSha3FourReg isBcax rm ra rn rd =>
    (s.writeVReg128 rd (evalCryptoSha3FourReg isBcax (s.readVReg128 rn) (s.readVReg128 rm) (s.readVReg128 ra))).advancePC
  | .cryptoXar rm imm6 rn rd =>
    (s.writeVReg128 rd (evalCryptoXar imm6 (s.readVReg128 rn) (s.readVReg128 rm))).advancePC

  -- All other instructions fall back through `FastState.ofState (execInstWithSvc svc inst s.toState)`
  | inst =>
    FastState.ofState (execInstWithSvc svc inst s.toState)

/-- Fast single-instruction evaluator with `Syscall.standard`. -/
abbrev fastExecInst : Instr → FastState → FastState :=
  fastExecInstWithSvc Syscall.standard

@[simp] theorem fastExecLdpSimd_toState (svc : State → State) (sz : SimdMemSize) (vt1 vt2 : BitVec 5) (addr : AddrMode) (s : FastState) :
    (fastExecLdpSimd sz vt1 vt2 addr s).toState = execInstWithSvc svc (.ldpSimd sz vt1 vt2 addr) s.toState := by
  dsimp only [execInstWithSvc]
  cases sz <;> cases addr <;>
    simp [fastExecLdpSimd, fastEvalAddrMode, evalAddrMode, UInt64.toBitVec_add]

@[simp] theorem fastExecStpSimd_toState (svc : State → State) (sz : SimdMemSize) (vt1 vt2 : BitVec 5) (addr : AddrMode) (s : FastState) :
    (fastExecStpSimd sz vt1 vt2 addr s).toState = execInstWithSvc svc (.stpSimd sz vt1 vt2 addr) s.toState := by
  dsimp only [execInstWithSvc]
  cases sz <;> cases addr <;>
    simp [fastExecStpSimd, fastEvalAddrMode, evalAddrMode, UInt64.toBitVec_add]

@[simp] theorem fastExecLdrSimd_toState (svc : State → State) (sz : SimdMemSize) (vt : BitVec 5) (addr : AddrMode) (s : FastState) :
    (fastExecLdrSimd sz vt addr s).toState = execInstWithSvc svc (.ldrSimd sz vt addr) s.toState := by
  dsimp only [execInstWithSvc]
  cases addr <;>
    simp [fastExecLdrSimd, fastEvalAddrMode, evalAddrMode, UInt64.toBitVec_add]

@[simp] theorem fastExecStrSimd_toState (svc : State → State) (sz : SimdMemSize) (vt : BitVec 5) (addr : AddrMode) (s : FastState) :
    (fastExecStrSimd sz vt addr s).toState = execInstWithSvc svc (.strSimd sz vt addr) s.toState := by
  dsimp only [execInstWithSvc]
  cases addr <;>
    simp [fastExecStrSimd, fastEvalAddrMode, evalAddrMode, UInt64.toBitVec_add]

@[simp] theorem fastExecSimdImmShift_toState (svc : State → State) (q op : Bool) (immh : BitVec 4) (immb : BitVec 3) (opc : BitVec 5)
    (rn rd : BitVec 5) (s : FastState) :
    (fastExecSimdImmShift q op immh immb opc rn rd s).toState =
      execInstWithSvc svc (.simdImmShift q op immh immb opc rn rd) s.toState := by
  dsimp only [fastExecSimdImmShift, execInstWithSvc]
  simp only [FastState.toState_ite, FastState.toState_advancePC, FastState.toState_writeVReg128,
    toState_fastApplySimdResult, toState_fastApplySimdSatResult]
  rfl

@[simp] theorem fastExecSimdInsDup_toState (svc : State → State) (q op : Bool) (imm5 : BitVec 5) (imm4 : BitVec 4)
    (rn rd : BitVec 5) (s : FastState) :
    (fastExecSimdInsDup q op imm5 imm4 rn rd s).toState =
      execInstWithSvc svc (.simdInsDup q op imm5 imm4 rn rd) s.toState := by
  dsimp only [fastExecSimdInsDup, execInstWithSvc]
  repeat (first | rfl | simp | split)

@[simp] theorem fastExecSimdThreeSame_toState (svc : State → State) (q u : Bool) (size : BitVec 2) (rm : BitVec 5) (opcode : BitVec 5)
    (rn rd : BitVec 5) (s : FastState) :
    (fastExecSimdThreeSame q u size rm opcode rn rd s).toState =
      execInstWithSvc svc (.simdThreeSame q u size rm opcode rn rd) s.toState := by
  dsimp only [fastExecSimdThreeSame, execInstWithSvc]
  simp only [FastState.toState_ite, FastState.toState_advancePC, FastState.toState_writeVReg128,
    toState_fastApplySimdSatResult]
  congr 1
  split <;> simp [toState_fastApplySimdSatResult]

@[simp] theorem fastExecSimdTwoRegMisc_toState (svc : State → State) (q u : Bool) (size : BitVec 2) (opcode : BitVec 5)
    (rn rd : BitVec 5) (s : FastState) :
    (fastExecSimdTwoRegMisc q u size opcode rn rd s).toState =
      execInstWithSvc svc (.simdTwoRegMisc q u size opcode rn rd) s.toState := by
  dsimp only [fastExecSimdTwoRegMisc, execInstWithSvc]
  simp only [FastState.toState_ite, FastState.toState_advancePC, FastState.toState_writeVReg128,
    toState_fastApplySimdSatResult]
  rfl

@[simp] theorem fastExecSimdPermute_toState (svc : State → State) (q : Bool) (size : BitVec 2) (rm : BitVec 5) (opcode : BitVec 3)
    (rn rd : BitVec 5) (s : FastState) :
    (fastExecSimdPermute q size rm opcode rn rd s).toState =
      execInstWithSvc svc (.simdPermute q size rm opcode rn rd) s.toState := by
  dsimp only [fastExecSimdPermute, execInstWithSvc]
  simp only [FastState.toState_ite, FastState.toState_advancePC, FastState.toState_writeVReg128]
  repeat (first | rfl | split)

@[simp] theorem fastExecSimdExt_toState (svc : State → State) (q : Bool) (rm : BitVec 5) (imm4 : BitVec 4) (rn rd : BitVec 5) (s : FastState) :
    (fastExecSimdExt q rm imm4 rn rd s).toState =
      execInstWithSvc svc (.simdExt q rm imm4 rn rd) s.toState := by
  dsimp only [fastExecSimdExt, execInstWithSvc]
  simp only [FastState.toState_ite, FastState.toState_advancePC, FastState.toState_writeVReg128,
    FastState.toState_writeVReg64]
  repeat (first | rfl | split)

/-- Single-step refinement: `fastExecInstWithSvc` commutes with `FastState.toState`. -/
@[simp] theorem fastExecInstWithSvc_toState (svc : State → State) (inst : Instr) (s : FastState) :
    (fastExecInstWithSvc svc inst s).toState = execInstWithSvc svc inst s.toState := by
  cases inst with
  | ldr w sz signed rt addr => exact fastExecLdr_toState w sz signed rt addr s
  | ldrLit w signed rt offset =>
    exact fastExecLdrLit_toState w (if signed then .W32 else (w : MemWidth)) signed rt offset s
  | str sz rt addr => exact fastExecStr_toState sz rt addr s
  | ldp w signed rt1 rt2 addr => exact fastExecLdp_toState w signed rt1 rt2 addr s
  | stp w rt1 rt2 addr => exact fastExecStp_toState w rt1 rt2 addr s
  | adr page rd offset =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    cases page <;> simp [UInt64.toBitVec_add, UInt64.toBitVec_and]
  | addSubImm w op rd rn imm12 shift12 => exact fastExecAddSubImm_toState w op rd rn imm12 shift12 s
  | logicalImm w op rd rn mask => exact fastExecLogicalImm_toState w op rd rn mask s
  | moveWide w op rd imm16 hw => exact fastExecMoveWide_toState w op rd imm16 hw s
  | bitfield w op rd rn immr imms => exact fastExecBitfield_toState w op rd rn immr imms s
  | extr w rd rn rm lsb =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    cases w <;> simp
  | logicalShift w op rd rn rm shift amount => exact fastExecLogicalShift_toState w op rd rn rm shift amount s
  | addSubShift w op rd rn rm shift amount => exact fastExecAddSubShift_toState w op rd rn rm shift amount s
  | addSubExt w op rd rn rm ext amount => exact fastExecAddSubExt_toState w op rd rn rm ext amount s
  | addSubCarry w op rd rn rm => exact fastExecAddSubCarry_toState w op rd rn rm s
  | condCompareReg w isSub rn rm nzcv cond =>
    exact fastExecCondCompare_toState w isSub false rn 0 rm nzcv cond s
  | condCompareImm w isSub rn imm5 nzcv cond =>
    exact fastExecCondCompare_toState w isSub true rn ⟨imm5.zeroExtend 64⟩ .xzr nzcv cond s
  | condSelect w op rd rn rm cond => exact fastExecCondSelect_toState w op rd rn rm cond s
  | dataProc1 w op rd rn => exact fastExecDataProc1_toState w op rd rn s
  | dataProc2 w op rd rn rm => exact fastExecDataProc2_toState w op rd rn rm s
  | dataProc3 w op rd rn rm ra => exact fastExecDataProc3_toState w op rd rn rm ra s
  | b offset =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp [UInt64.toBitVec_add]
  | bl offset =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp [UInt64.toBitVec_add]
  | bCond cond offset =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    by_cases h : ConditionHolds cond s.pstate <;> simp [h, UInt64.toBitVec_add]
  | br rn =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp
  | blr rn =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp [UInt64.toBitVec_add]
  | ret rn =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp
  | cbz w isNonZero rt offset =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    cases isNonZero <;> simp [← UInt64.beq_toBitVec, UInt64.toBitVec_add]
  | tbz w isNonZero rt bitPos offset =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp [UInt64.toBitVec_add]
  | nop => rfl
  | barrier _ _ => rfl
  | hint _ => rfl
  | prfm _ _ => rfl
  | prfmLit _ _ => rfl
  | ldpSimd sz vt1 vt2 addr => exact fastExecLdpSimd_toState svc sz vt1 vt2 addr s
  | stpSimd sz vt1 vt2 addr => exact fastExecStpSimd_toState svc sz vt1 vt2 addr s
  | ldrSimd sz vt addr => exact fastExecLdrSimd_toState svc sz vt addr s
  | strSimd sz vt addr => exact fastExecStrSimd_toState svc sz vt addr s
  | ldrSimdLit sz vt offset =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp [UInt64.toBitVec_add]
  | ldnp sz rn rt rt2 offset =>
    exact fastExecLdp_toState (match sz with | .X64 => .W64 | _ => .W32) false rt rt2 (.Offset rn offset) s
  | stnp sz rn rt rt2 offset =>
    exact fastExecStp_toState (match sz with | .X64 => .W64 | _ => .W32) rt rt2 (.Offset rn offset) s
  | aes op vd vn =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp only [FastState.toState_advancePC, FastState.toState_writeVReg128]
    rfl
  | simdImmShift q op immh immb opc rn rd => exact fastExecSimdImmShift_toState svc q op immh immb opc rn rd s
  | simdInsDup q op imm5 imm4 rn rd => exact fastExecSimdInsDup_toState svc q op imm5 imm4 rn rd s
  | simdThreeSame q u size rm opcode rn rd => exact fastExecSimdThreeSame_toState svc q u size rm opcode rn rd s
  | simdTwoRegMisc q u size opcode rn rd => exact fastExecSimdTwoRegMisc_toState svc q u size opcode rn rd s
  | simdPermute q size rm opcode rn rd => exact fastExecSimdPermute_toState svc q size rm opcode rn rd s
  | simdExt q rm imm4 rn rd => exact fastExecSimdExt_toState svc q rm imm4 rn rd s
  | simdTbl q rm len isTbx rn rd =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp only [FastState.toState_advancePC, FastState.toState_writeVReg128]
    rfl
  | simdAddpScalar rn rd =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp only [FastState.toState_advancePC, FastState.toState_writeVReg64]
    rfl
  | simdDupScalar imm5 rn rd =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp only [FastState.toState_ite, FastState.toState_advancePC, FastState.toState_writeVReg128]
    split <;> rfl
  | simdPmull q is64 rm rn rd =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp only [FastState.toState_advancePC, FastState.toState_writeVReg128]
    rfl
  | simdThreeDiff q u size rm opcode rn rd =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp only [FastState.toState_ite, FastState.toState_advancePC, FastState.toState_writeVReg128]
    split <;> rfl
  | cryptoSha2Reg opcode rn rd =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    exact toState_fastApplySimdResult _ _ _
  | cryptoSha3Reg opcode rm rn rd =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    exact toState_fastApplySimdResult _ _ _
  | cryptoSha512Reg2 rn rd =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp only [FastState.toState_advancePC, FastState.toState_writeVReg128]
    rfl
  | cryptoSha512Reg3 opcode rm rn rd =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp only [FastState.toState_advancePC, FastState.toState_writeVReg128]
    rfl
  | cryptoSha3FourReg isBcax rm ra rn rd =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp only [FastState.toState_advancePC, FastState.toState_writeVReg128]
    rfl
  | cryptoXar rm imm6 rn rd =>
    dsimp only [fastExecInstWithSvc, execInstWithSvc]
    simp only [FastState.toState_advancePC, FastState.toState_writeVReg128]
    rfl
  | _ =>
    exact FastState.toState_ofState _

/-- Single-step refinement under `Syscall.standard`: `fastExecInst` commutes with `toState`. -/
@[simp] theorem fastExecInst_toState (inst : Instr) (s : FastState) :
    (fastExecInst inst s).toState = execInst inst s.toState :=
  fastExecInstWithSvc_toState Syscall.standard inst s

/-- Variant of `fastExecStr` that checks permissions and applies writeback/PC advance without
    allocating `Memory.write8` closures when the caller updates a flat page store directly. -/
def fastExecStrSkipMem (size : MemWidth) (rt : Reg) (addr : AddrMode) (s : FastState) : FastState :=
  let _ := rt
  if !fastCheckAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := fastEvalAddrMode s addr
    if !fastCanWrite s.mem ea size.bytes then
      s.setStatus (.Exception "permission fault")
    else
      let s1 := s.setMem Memory.empty
      let s2 := fastApplyWb s1 wb
      s2.advancePC

/-- Variant of `fastExecStp` that checks permissions and applies writeback/PC advance without
    allocating `Memory.write8` closures when the caller updates a flat page store directly. -/
def fastExecStpSkipMem (w : Width) (rt1 rt2 : Reg) (addr : AddrMode) (s : FastState) : FastState :=
  let _ := (rt1, rt2)
  if !fastCheckAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := fastEvalAddrMode s addr
    let stepBytes : UInt64 := match w with | .W32 => 4 | .W64 => 8
    let sz : MemWidth := match w with | .W32 => .W32 | .W64 => .X64
    if !(fastCanWrite s.mem ea sz.bytes && fastCanWrite s.mem (ea + stepBytes) sz.bytes) then
      s.setStatus (.Exception "permission fault")
    else
      let s1 := s.setMem Memory.empty
      let s2 := fastApplyWb s1 wb
      s2.advancePC

/-- Variant of `fastExecStrSimd` that skips `Memory.write8` closure allocation. -/
def fastExecStrSimdSkipMem (sz : SimdMemSize) (vt : BitVec 5) (addr : AddrMode) (s : FastState) : FastState :=
  let _ := vt
  if !fastCheckAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := fastEvalAddrMode s addr
    if !fastCanWrite s.mem ea sz.bytes then
      s.setStatus (.Exception "permission fault")
    else
      let s1 := s.setMem Memory.empty
      let s2 := fastApplyWb s1 wb
      s2.advancePC

/-- Variant of `fastExecStpSimd` that skips `Memory.write8` closure allocation. -/
def fastExecStpSimdSkipMem (sz : SimdMemSize) (vt1 vt2 : BitVec 5) (addr : AddrMode) (s : FastState) : FastState :=
  let _ := (vt1, vt2)
  if !fastCheckAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := fastEvalAddrMode s addr
    let stepBytes : UInt64 :=
      match sz with | .B8 => 1 | .H16 => 2 | .S32 => 4 | .D64 => 8 | .Q128 => 16
    if !(fastCanWrite s.mem ea sz.bytes && fastCanWrite s.mem (ea + stepBytes) sz.bytes) then
      s.setStatus (.Exception "permission fault")
    else
      let s1 := s.setMem Memory.empty
      let s2 := fastApplyWb s1 wb
      s2.advancePC

/-- Single-instruction evaluator for store instructions where the caller updates a flat page store
    directly and replaces `.mem` via `.setMem`. -/
def fastExecInstSkipMem (inst : Instr) (s : FastState) : FastState :=
  match inst with
  | .str sz rt addr => fastExecStrSkipMem sz rt addr s
  | .stp w rt1 rt2 addr => fastExecStpSkipMem w rt1 rt2 addr s
  | .stnp sz rn rt rt2 offset =>
    fastExecStpSkipMem (match sz with | .X64 => .W64 | _ => .W32) rt rt2 (.Offset rn offset) s
  | .strSimd sz vt addr => fastExecStrSimdSkipMem sz vt addr s
  | .stpSimd sz vt1 vt2 addr => fastExecStpSimdSkipMem sz vt1 vt2 addr s
  | _ => fastExecInst inst s

@[simp] theorem fastExecStrSkipMem_status (sz : MemWidth) (rt : Reg) (addr : AddrMode) (s : FastState) :
    (fastExecStrSkipMem sz rt addr s).status = (fastExecStr sz rt addr s).status := by
  dsimp only [fastExecStrSkipMem, fastExecStr, fastApplyWb, FastState.writeReg64, FastState.setMem, FastState.advancePC]
  repeat (first | rfl | split)

@[simp] theorem fastExecStpSkipMem_status (w : RegWidth) (rt1 rt2 : Reg) (addr : AddrMode) (s : FastState) :
    (fastExecStpSkipMem w rt1 rt2 addr s).status = (fastExecStp w rt1 rt2 addr s).status := by
  dsimp only [fastExecStpSkipMem, fastExecStp, fastApplyWb, FastState.writeReg64, FastState.setMem, FastState.advancePC]
  repeat (first | rfl | split)

@[simp] theorem fastExecStrSimdSkipMem_status (sz : SimdMemSize) (vt : BitVec 5) (addr : AddrMode) (s : FastState) :
    (fastExecStrSimdSkipMem sz vt addr s).status = (fastExecStrSimd sz vt addr s).status := by
  dsimp only [fastExecStrSimdSkipMem, fastExecStrSimd, fastApplyWb, FastState.writeReg64, FastState.setMem, FastState.advancePC]
  repeat (first | rfl | split)

@[simp] theorem fastExecStpSimdSkipMem_status (sz : SimdMemSize) (vt1 vt2 : BitVec 5) (addr : AddrMode) (s : FastState) :
    (fastExecStpSimdSkipMem sz vt1 vt2 addr s).status = (fastExecStpSimd sz vt1 vt2 addr s).status := by
  dsimp only [fastExecStpSimdSkipMem, fastExecStpSimd, fastApplyWb, FastState.writeReg64, FastState.setMem, FastState.advancePC]
  repeat (first | rfl | split)

@[simp] theorem fastExecStrSkipMem_setMem (sz : MemWidth) (rt : Reg) (addr : AddrMode) (s : FastState) (m : Memory) :
    (fastExecStrSkipMem sz rt addr s).setMem m = (fastExecStr sz rt addr s).setMem m := by
  dsimp only [fastExecStrSkipMem, fastExecStr, fastApplyWb, FastState.writeReg64, FastState.setMem, FastState.advancePC]
  repeat (first | rfl | split)

@[simp] theorem fastExecStpSkipMem_setMem (w : RegWidth) (rt1 rt2 : Reg) (addr : AddrMode) (s : FastState) (m : Memory) :
    (fastExecStpSkipMem w rt1 rt2 addr s).setMem m = (fastExecStp w rt1 rt2 addr s).setMem m := by
  dsimp only [fastExecStpSkipMem, fastExecStp, fastApplyWb, FastState.writeReg64, FastState.setMem, FastState.advancePC]
  repeat (first | rfl | split)

@[simp] theorem fastExecStrSimdSkipMem_setMem (sz : SimdMemSize) (vt : BitVec 5) (addr : AddrMode) (s : FastState) (m : Memory) :
    (fastExecStrSimdSkipMem sz vt addr s).setMem m = (fastExecStrSimd sz vt addr s).setMem m := by
  dsimp only [fastExecStrSimdSkipMem, fastExecStrSimd, fastApplyWb, FastState.writeReg64, FastState.setMem, FastState.advancePC]
  repeat (first | rfl | split)

@[simp] theorem fastExecStpSimdSkipMem_setMem (sz : SimdMemSize) (vt1 vt2 : BitVec 5) (addr : AddrMode) (s : FastState) (m : Memory) :
    (fastExecStpSimdSkipMem sz vt1 vt2 addr s).setMem m = (fastExecStpSimd sz vt1 vt2 addr s).setMem m := by
  dsimp only [fastExecStpSimdSkipMem, fastExecStpSimd, fastApplyWb, FastState.writeReg64, FastState.setMem, FastState.advancePC]
  repeat (first | rfl | split)

@[simp] theorem fastExecInstSkipMem_status (inst : Instr) (s : FastState) :
    (fastExecInstSkipMem inst s).status = (fastExecInst inst s).status := by
  cases inst with
  | str sz rt addr => exact fastExecStrSkipMem_status sz rt addr s
  | stp w rt1 rt2 addr => exact fastExecStpSkipMem_status w rt1 rt2 addr s
  | stnp sz rn rt rt2 offset =>
    exact fastExecStpSkipMem_status (match sz with | .X64 => .W64 | _ => .W32) rt rt2 (.Offset rn offset) s
  | strSimd sz vt addr => exact fastExecStrSimdSkipMem_status sz vt addr s
  | stpSimd sz vt1 vt2 addr => exact fastExecStpSimdSkipMem_status sz vt1 vt2 addr s
  | _ => rfl

@[simp] theorem fastExecInstSkipMem_setMem (inst : Instr) (s : FastState) (m : Memory) :
    (fastExecInstSkipMem inst s).setMem m = (fastExecInst inst s).setMem m := by
  cases inst with
  | str sz rt addr => exact fastExecStrSkipMem_setMem sz rt addr s m
  | stp w rt1 rt2 addr => exact fastExecStpSkipMem_setMem w rt1 rt2 addr s m
  | stnp sz rn rt rt2 offset =>
    exact fastExecStpSkipMem_setMem (match sz with | .X64 => .W64 | _ => .W32) rt rt2 (.Offset rn offset) s m
  | strSimd sz vt addr => exact fastExecStrSimdSkipMem_setMem sz vt addr s m
  | stpSimd sz vt1 vt2 addr => exact fastExecStpSimdSkipMem_setMem sz vt1 vt2 addr s m
  | _ => rfl

/-- Multi-step execution loop over `FastState` corresponding to `Process.runStepsPure`. -/
def fastRunStepsPure : Nat → FastState → FastState
  | 0, s => s
  | n + 1, s =>
    if s.status != .Running then
      s
    else
      match Program.pureMem.fetchMem s.mem s.pc.toBitVec with
      | some inst => fastRunStepsPure n (fastExecInst inst s)
      | none      => fastRunStepsPure n (s.setStatus .Halted)

/-- Multi-step refinement: `fastRunStepsPure` commutes with `Process.runStepsPure`. -/
@[simp] theorem fastRunStepsPure_toState (n : Nat) (s : FastState) :
    (fastRunStepsPure n s).toState = Process.runStepsPure n s.toState := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [fastRunStepsPure, Process.runStepsPure]
    by_cases h : s.status != .Running
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, FastState.toState_status,
        FastState.toState_mem, FastState.toState_pc]
      cases hfetch : Program.pureMem.fetchMem s.mem s.pc.toBitVec with
      | none =>
        rw [ih, FastState.toState_setStatus]
        rfl
      | some inst =>
        rw [ih, fastExecInst_toState]

/-- Multi-step refinement against `Process.runSteps n Program.pureMem`. -/
theorem fastRunSteps_eq_runSteps (n : Nat) (s : FastState) :
    (fastRunStepsPure n s).toState = Process.runSteps n Program.pureMem s.toState := by
  rw [fastRunStepsPure_toState, Process.runStepsPure_eq]

/-- Every `fastRunStepsPure` run is a valid multi-step transition in `Steps Program.pureMem`. -/
theorem fastRunSteps_steps (n : Nat) (s : FastState) :
    Steps Program.pureMem s.toState (fastRunStepsPure n s).toState := by
  rw [fastRunSteps_eq_runSteps]
  exact Process.runSteps_steps Process.pureMem_hooksKeepFrozen n s.toState

end Arm64.Fast
