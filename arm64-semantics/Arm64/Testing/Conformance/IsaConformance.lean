/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Testing.Harness.Encode

/-!
# Kernel-Checked ISA Conformance

`decide +kernel` conformance theorems over `Arm64.decode`, `Arm64.encode`, `Arm64.execInst`, and
the Linux syscall handlers (`execBrk`, `execMunmap`, `execMprotect`, `execMadvise`,
`execClockGettime`, and `SYS_GETRANDOM`).
-/

@[expose] public section

namespace Testing

open Arm64

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

/-- `PMULL` / `PMULL2` decode and re-encode round-trip across `.1Q <- .1D/.2D` (`size = 11`),
    `.8H <- .8B/.16B` (`size = 00`), and reserved `size ∈ {01, 10}`. -/
theorem pmull_decode_encode_conformance :
    decode 0x0ee2e020#32 = some (.simdPmull false true 2#5 1#5 0#5) ∧
    encode (.simdPmull false true 2#5 1#5 0#5) = some 0x0ee2e020#32 ∧
    decode 0x4ee5e083#32 = some (.simdPmull true true 5#5 4#5 3#5) ∧
    encode (.simdPmull true true 5#5 4#5 3#5) = some 0x4ee5e083#32 ∧
    decode 0x0e28e0e6#32 = some (.simdPmull false false 8#5 7#5 6#5) ∧
    encode (.simdPmull false false 8#5 7#5 6#5) = some 0x0e28e0e6#32 ∧
    decode 0x4e2be149#32 = some (.simdPmull true false 11#5 10#5 9#5) ∧
    encode (.simdPmull true false 11#5 10#5 9#5) = some 0x4e2be149#32 ∧
    decode 0x0e62e020#32 = none ∧
    decode 0x0ea2e020#32 = none ∧
    decode 0x4e62e020#32 = none ∧
    decode 0x4ea2e020#32 = none := by
  decide +kernel

/-- `PMULL` / `PMULL2` execution conformance on known GF(2)[x] carry-less products:
    - `(x + 1) * (x + 1) = x^2 + 1` (`3 * 3 = 5`),
    - `2^63 * 2^63 = 2^126`,
    - `(x^63 + ... + 1)^2 = x^126 + x^124 + ... + 1` (`0x5555...5555`),
    - `(x^63 + ... + 1) * (x + 1) = x^64 + 1`,
    - both `Q = 0` (lower 64-bit half) and `Q = 1` (upper 64-bit half) for `.1Q <- .1D/.2D` and `.8H <- .8B/.16B`. -/
theorem pmull_exec_conformance :
    evalPmull false true 3#128 3#128 = 5#128 ∧
    evalPmull false true 7#128 3#128 = 9#128 ∧
    evalPmull false true 0x8000000000000000#128 0x8000000000000000#128 =
      0x4000000000000000_0000000000000000#128 ∧
    evalPmull false true 0xffffffffffffffff#128 0xffffffffffffffff#128 =
      0x5555555555555555_5555555555555555#128 ∧
    evalPmull true true
      0xffffffffffffffff_0000000000000003#128
      0x0000000000000003_8000000000000001#128 =
      0x0000000000000001_0000000000000001#128 ∧
    evalPmull false false
      0xff80070302010003_ff80070302010003#128
      0x038003030201ff05_038003030201ff03#128 =
      0x0101400000090005_0004000100000005#128 ∧
    evalPmull true false
      0xff80070302010003_ff80070302010003#128
      0x038003030201ff05_038003030201ff03#128 =
      0x0101400000090005_000400010000000f#128 := by
  decide +kernel

/-- Conformance tests for AdvSIMD shifts, permutes, modified immediates, and lane moves:
    `SMOV`, `MOVI`/`MVNI`, `ORR`/`BIC` `#imm`, vector `FMOV`, rounding and saturating shifts,
    and `REV16`/`RBIT`/`CLZ`/`CLS`. -/
theorem simd_family_a_conformance :
    -- SMOV W0, V1.B[0] (negative byte 0x80 -> 0x00000000ffffff80) and SMOV X0, V1.S[2] (0x80000001 -> 0xffffffff80000001)
    let s1 := (({} : State).writeVReg128 1#5 0x0000000080000001_000000000000ff80#128)
    (execInst (.simdInsDup false false 0b00001#5 0b0101#4 1#5 0#5) s1).readReg64 .x0 = 0x00000000ffffff80#64 ∧
    (execInst (.simdInsDup true false 0b10100#5 0b0101#4 1#5 0#5) s1).readReg64 .x0 = 0xffffffff80000001#64 ∧
    -- MOVI MSL #8 (cmode = 1100, imm8 = 0xa5 -> 0x0000a5ff repeated) and MVNI MSL #16 (cmode = 1101, imm8 = 0xa5 -> ~~~0x00a5ffff)
    evalSimdModImmExt true false 0b101#3 (0b1100#4 ++ 0#1) 0b00101#5 0#128 =
      .ok 0x0000a5ff0000a5ff_0000a5ff0000a5ff#128 ∧
    evalSimdModImmExt false true 0b101#3 (0b1101#4 ++ 0#1) 0b00101#5 0#128 =
      .ok 0x0000000000000000_ff5a0000ff5a0000#128 ∧
    -- ORR / BIC #imm (16-bit and 32-bit) and vector FMOV #imm8 (1.0f = 0x70 -> 0x3f800000, 1.0d -> 0x3ff0000000000000)
    evalSimdModImmExt true false 0b000#3 (0b0001#4 ++ 0#1) 0b00011#5 0x1000000020000000_3000000040000000#128 =
      .ok 0x1000000320000003_3000000340000003#128 ∧
    evalSimdModImmExt true true 0b000#3 (0b0001#4 ++ 0#1) 0b00011#5 0xffffffffffffffff_ffffffffffffffff#128 =
      .ok 0xfffffffcfffffffc_fffffffcfffffffc#128 ∧
    evalSimdModImmExt true false 0b011#3 (0b1111#4 ++ 0#1) 0b10000#5 0#128 =
      .ok 0x3f8000003f800000_3f8000003f800000#128 ∧
    evalSimdModImmExt true true 0b011#3 (0b1111#4 ++ 0#1) 0b10000#5 0#128 =
      .ok 0x3ff0000000000000_3ff0000000000000#128 ∧
    -- REV16 in simdTwoRegMisc
    evalSimdTwoRegMiscExt false false 0b00#2 0b00001#5 0#128 0x0102030405060708#128 =
      .ok 0x0201040306050807#128 := by
  decide +kernel

/-- Conformance tests for cryptographic instructions
    (`SHA1*`, `SHA256*`, `SHA512*`, `EOR3`, `BCAX`, `RAX1`, `XAR`). -/
theorem simd_family_b_conformance :
    decode 0x5e280820#32 = some (.cryptoSha2Reg 0#5 1#5 0#5) ∧
    encode (.cryptoSha2Reg 0#5 1#5 0#5) = some 0x5e280820#32 ∧
    decode 0x5e020020#32 = some (.cryptoSha3Reg 0#3 2#5 1#5 0#5) ∧
    encode (.cryptoSha3Reg 0#3 2#5 1#5 0#5) = some 0x5e020020#32 ∧
    decode 0xcec08020#32 = some (.cryptoSha512Reg2 1#5 0#5) ∧
    encode (.cryptoSha512Reg2 1#5 0#5) = some 0xcec08020#32 ∧
    decode 0xce628020#32 = some (.cryptoSha512Reg3 0#2 2#5 1#5 0#5) ∧
    encode (.cryptoSha512Reg3 0#2 2#5 1#5 0#5) = some 0xce628020#32 ∧
    decode 0xce020c20#32 = some (.cryptoSha3FourReg false 2#5 3#5 1#5 0#5) ∧
    encode (.cryptoSha3FourReg false 2#5 3#5 1#5 0#5) = some 0xce020c20#32 ∧
    decode 0xce824420#32 = some (.cryptoXar 2#5 17#6 1#5 0#5) ∧
    encode (.cryptoXar 2#5 17#6 1#5 0#5) = some 0xce824420#32 ∧
    evalCryptoSha2Reg 0#5 0#128 0x67452301#128 = .ok 0x59d148c0#128 ∧
    evalCryptoSha3FourReg false 0x1111#128 0x2222#128 0x4444#128 = 0x7777#128 ∧
    evalCryptoSha3FourReg true 0x0f0f#128 0x00ff#128 0x0ff0#128 = 0x0f00#128 ∧
    evalCryptoXar 4#6 0x0000000000000012_0000000000000034#128 0#128 =
      0x2000000000000001_4000000000000003#128 := by
  decide +kernel

private theorem allPerm_of_forall {m : Memory} {p : Option Perm → Bool} {addr : BitVec 64} {n : Nat}
    (h : ∀ k < n, p (m.perm (addr + BitVec.ofNat 64 k)) = true) :
    m.allPerm p addr n = true := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
    simp only [Memory.allPerm]
    have h0 : p (m.perm addr) = true := by simpa using h 0 (Nat.zero_lt_succ n)
    have hrest : m.allPerm p (addr + 1#64) n = true :=
      ih fun k hk => by
        have hk' := h (1 + k) (by omega)
        have hadd : addr + 1#64 + BitVec.ofNat 64 k = addr + BitVec.ofNat 64 (1 + k) := by bv_omega
        rwa [hadd]
    rw [h0, hrest]; rfl

private theorem allPerm_eq_false_of_exists {m : Memory} {p : Option Perm → Bool} {addr : BitVec 64}
    {n k : Nat} (hk : k < n) (hp : p (m.perm (addr + BitVec.ofNat 64 k)) = false) :
    m.allPerm p addr n = false := by
  induction n generalizing addr k with
  | zero => omega
  | succ n ih =>
    simp only [Memory.allPerm]
    cases k with
    | zero =>
      have h0 : p (m.perm addr) = false := by simpa using hp
      rw [h0]; rfl
    | succ k' =>
      have hrec : m.allPerm p (addr + 1#64) n = false :=
        ih (k := k') (by omega) (by
          have hadd : addr + 1#64 + BitVec.ofNat 64 k' = addr + BitVec.ofNat 64 (k' + 1) := by bv_omega
          rwa [hadd])
      rw [hrec, Bool.and_false]

private abbrev brkTestMem0 : Memory :=
  (Memory.empty.mapZero 0x141000#64 0x1000).write8 0x141000#64 0x77#8

private theorem brkTestMem0_canMap_grow :
    brkTestMem0.canMap (BitVec.ofNat 64 0x40000) (0x41000 - 0x40000 + BRK_GUARD_GAP) = true := by
  apply allPerm_of_forall
  intro k hk
  have hne : 0x40000#64 + BitVec.ofNat 64 k ≠ 0x141000#64 := by
    unfold BRK_GUARD_GAP PAGE_SIZE at hk; bv_omega
  have hout : decide ((0x40000#64 + BitVec.ofNat 64 k - 0x141000#64).toNat < 0x1000) = false := by
    rw [decide_eq_false_iff_not]; unfold BRK_GUARD_GAP PAGE_SIZE at hk; bv_omega
  dsimp only [brkTestMem0, Memory.perm, Memory.write8, Memory.mapZero, Memory.empty, Option.mapped]
  simp only [hne, hout, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

private abbrev brkTestMem1 : Memory :=
  ((brkTestMem0.mapZero 0x40000#64 0x1000).write8 0x40000#64 0xab#8).unmapWritable 0x41000#64 0

private theorem brkTestMem1_canMap_overlap :
    brkTestMem1.canMap (BitVec.ofNat 64 0x41000) (0x42000 - 0x41000 + BRK_GUARD_GAP) = false :=
  allPerm_eq_false_of_exists (k := 0x100000)
    (by unfold BRK_GUARD_GAP PAGE_SIZE; omega)
    (by decide +kernel)

private theorem execBrk_grow_ok_eq (s : State) (m : Memory) (addr : BitVec 64) (oldPage newPage : Nat)
    (hm : s.mem = m)
    (hx0 : s.readReg64 Reg.x0 = addr)
    (h1 : (addr == 0#64 || addr.ult s.brkStart) = false)
    (hold : pageAlignUp s.brk.toNat = oldPage)
    (hnew : pageAlignUp addr.toNat = newPage)
    (hlt : ¬(newPage ≤ oldPage))
    (hlim : decide (newPage + BRK_GUARD_GAP ≤ USER_VA_LIMIT) = true)
    (hcan : m.canMap (BitVec.ofNat 64 oldPage) (newPage - oldPage + BRK_GUARD_GAP) = true)
    (hphys : decide (newPage - oldPage ≤ s.physMemAvail) = true) :
    execBrk s =
      ((((s.setBrk addr).setMem (m.mapZero (BitVec.ofNat 64 oldPage) (newPage - oldPage))).setPhysMemAvail
        (s.physMemAvail - (newPage - oldPage))).writeReg64 Reg.x0 addr).advancePC := by
  unfold execBrk
  simp only [hm, hx0, h1, Bool.false_eq_true, ↓reduceIte, hold, hnew, hlt, hlim, hcan,
    hphys, Bool.not_true, Bool.or_self]

private theorem execBrk_grow_oom_eq (s : State) (m : Memory) (addr : BitVec 64) (oldPage newPage : Nat)
    (hm : s.mem = m)
    (hx0 : s.readReg64 Reg.x0 = addr)
    (h1 : (addr == 0#64 || addr.ult s.brkStart) = false)
    (hold : pageAlignUp s.brk.toNat = oldPage)
    (hnew : pageAlignUp addr.toNat = newPage)
    (hlt : ¬(newPage ≤ oldPage))
    (hlim : decide (newPage + BRK_GUARD_GAP ≤ USER_VA_LIMIT) = true)
    (hcan : m.canMap (BitVec.ofNat 64 oldPage) (newPage - oldPage + BRK_GUARD_GAP) = true)
    (hphys : decide (newPage - oldPage ≤ s.physMemAvail) = false) :
    execBrk s = s.setStatus .OutOfMemory := by
  unfold execBrk
  simp only [hm, hx0, h1, Bool.false_eq_true, ↓reduceIte, hold, hnew, hlt, hlim, hcan,
    hphys, Bool.not_true, Bool.not_false, Bool.or_self]

private theorem execBrk_same_page_eq (s : State) (m : Memory) (addr : BitVec 64) (page : Nat)
    (hm : s.mem = m)
    (hx0 : s.readReg64 Reg.x0 = addr)
    (h1 : (addr == 0#64 || addr.ult s.brkStart) = false)
    (hold : pageAlignUp s.brk.toNat = page)
    (hnew : pageAlignUp addr.toNat = page) :
    execBrk s =
      ((((s.setBrk addr).setMem (m.unmapWritable (BitVec.ofNat 64 page) 0)).setPhysMemAvail
        s.physMemAvail).writeReg64 Reg.x0 addr).advancePC := by
  unfold execBrk
  simp only [hm, hx0, h1, Bool.false_eq_true, ↓reduceIte, hold, hnew, Nat.le_refl, Nat.sub_self,
    Memory.allPerm, Bool.not_true, Memory.countRw, Memory.countPerm, Nat.add_zero]

private theorem execBrk_refuse_of_not_canMap (s : State) (m : Memory) (addr : BitVec 64) (oldPage newPage : Nat)
    (hm : s.mem = m)
    (hx0 : s.readReg64 Reg.x0 = addr)
    (h1 : (addr == 0#64 || addr.ult s.brkStart) = false)
    (hold : pageAlignUp s.brk.toNat = oldPage)
    (hnew : pageAlignUp addr.toNat = newPage)
    (hlt : ¬(newPage ≤ oldPage))
    (hcan : m.canMap (BitVec.ofNat 64 oldPage) (newPage - oldPage + BRK_GUARD_GAP) = false) :
    execBrk s = (s.writeReg64 Reg.x0 s.brk).advancePC := by
  unfold execBrk
  simp only [hm, hx0, h1, Bool.false_eq_true, ↓reduceIte, hold, hnew, hlt, hcan,
    Bool.not_false, Bool.or_true]

private theorem prop_congr8 {α : Type} (P : α → α → α → α → α → α → α → α → Prop)
    {a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 : α}
    (h1 : a1 = b1) (h2 : a2 = b2) (h3 : a3 = b3) (h4 : a4 = b4)
    (h5 : a5 = b5) (h6 : a6 = b6) (h7 : a7 = b7) (h8 : a8 = b8)
    (hb : P b1 b2 b3 b4 b5 b6 b7 b8) :
    P a1 a2 a3 a4 a5 a6 a7 a8 := by
  subst h1 h2 h3 h4 h5 h6 h7 h8; exact hb

/-- Conformance tests for fail-closed `execBrk`:
    - `brk(0)` returns `s.brk` without consuming an oracle entry or modifying memory;
    - `brk(0x40004)` maps a 4 KiB zero-filled RW page `[0x40000, 0x41000)`, deducts `0x1000`
      from `s.physMemAvail`, and checks the 1 MiB VMA guard gap `[0x41000, 0x141000)`;
    - sub-page growth `brk(0x40100)` within `[0x40000, 0x41000)` leaves existing bytes intact;
    - growth whose 1 MiB guard gap hits an already-mapped page `[0x141000, 0x142000)`, shrinking
      below `s.brkStart`, or an address above `2 ^ 48 - BRK_GUARD_GAP` fails (`X0 = s.brk`,
      `s.mem` unchanged);
    - insufficient `s.physMemAvail` (`0 < 0x1000`) transitions to `.OutOfMemory`;
    - shrinking to `brkStart` (`0x40000`) unmaps `[0x40000, 0x41000)` and refunds `0x1000` to
      `s.physMemAvail`. -/
theorem brk_fail_closed_conformance :
    let mem0 := (Memory.empty.mapZero 0x141000#64 0x1000).write8 0x141000#64 0x77#8
    let s0 : State :=
      { mem := mem0, brkStart := 0x40000#64, brk := 0x40000#64, physMemAvail := 0x1000 }
    let sQuery := execBrk (s0.writeReg64 .x0 0#64)
    let sGrow := execBrk (sQuery.writeReg64 .x0 0x40004#64)
    let sSeed := sGrow.setMem (sGrow.mem.write8 0x40000#64 0xab#8)
    let sSub := execBrk (sSeed.writeReg64 .x0 0x40100#64)
    let sOverlap := execBrk (sSub.writeReg64 .x0 0x41008#64)
    let sBelow := execBrk (sSub.writeReg64 .x0 0x3ffff#64)
    let sAbove := execBrk (sSub.writeReg64 .x0 0x0001000000000001#64)
    let sShrink := execBrk (sSub.writeReg64 .x0 0x40000#64)
    let sOom := execBrk ({ s0 with physMemAvail := 0 }.writeReg64 .x0 0x40004#64)
    sQuery.readReg64 .x0 = 0x40000#64 ∧
    sQuery.oracleIdx = 0 ∧
    sQuery.mem.perm 0x40000#64 = none ∧
    sGrow.readReg64 .x0 = 0x40004#64 ∧
    sGrow.brk = 0x40004#64 ∧
    sGrow.physMemAvail = 0 ∧
    sGrow.oracleIdx = 0 ∧
    sGrow.mem.perm 0x40000#64 = some .rw ∧
    sGrow.mem.perm 0x40fff#64 = some .rw ∧
    sGrow.mem.read8 0x40fff#64 = 0#8 ∧
    sSub.readReg64 .x0 = 0x40100#64 ∧
    sSub.brk = 0x40100#64 ∧
    sSub.mem.read8 0x40000#64 = 0xab#8 ∧
    sOverlap.readReg64 .x0 = 0x40100#64 ∧
    sOverlap.brk = 0x40100#64 ∧
    sOverlap.mem.read8 0x141000#64 = 0x77#8 ∧
    sBelow.readReg64 .x0 = 0x40100#64 ∧
    sBelow.brk = 0x40100#64 ∧
    sBelow.mem.perm 0x40000#64 = some .rw ∧
    sAbove.readReg64 .x0 = 0x40100#64 ∧
    sAbove.brk = 0x40100#64 ∧
    sShrink.readReg64 .x0 = 0x40000#64 ∧
    sShrink.brk = 0x40000#64 ∧
    sShrink.physMemAvail = 0x1000 ∧
    sShrink.mem.perm 0x40000#64 = none ∧
    sOom.status = .OutOfMemory := by
  intro mem0 s0 sQuery sGrow sSeed sSub sOverlap sBelow sAbove sShrink sOom
  let sQueryVal : State := ((s0.writeReg64 .x0 0#64).writeReg64 .x0 0x40000#64).advancePC
  let sGrowIn : State := sQueryVal.writeReg64 .x0 0x40004#64
  let sGrowVal : State :=
    ((((sGrowIn.setBrk 0x40004#64).setMem (brkTestMem0.mapZero (BitVec.ofNat 64 0x40000) (0x41000 - 0x40000))).setPhysMemAvail
      (sGrowIn.physMemAvail - (0x41000 - 0x40000))).writeReg64 Reg.x0 0x40004#64).advancePC
  let sSeedVal : State := sGrowVal.setMem (sGrowVal.mem.write8 0x40000#64 0xab#8)
  let sSubIn : State := sSeedVal.writeReg64 .x0 0x40100#64
  let sSubVal : State :=
    ((((sSubIn.setBrk 0x40100#64).setMem brkTestMem1).setPhysMemAvail sSubIn.physMemAvail).writeReg64
      Reg.x0 0x40100#64).advancePC
  let sOverlapIn : State := sSubVal.writeReg64 .x0 0x41008#64
  let sOverlapVal : State := (sOverlapIn.writeReg64 Reg.x0 sOverlapIn.brk).advancePC
  let sBelowVal : State := execBrk (sSubVal.writeReg64 .x0 0x3ffff#64)
  let sAboveVal : State := execBrk (sSubVal.writeReg64 .x0 0x0001000000000001#64)
  let sShrinkVal : State := execBrk (sSubVal.writeReg64 .x0 0x40000#64)
  let sOomVal : State := ({ s0 with physMemAvail := 0 }.writeReg64 .x0 0x40004#64).setStatus .OutOfMemory
  have hQuery : sQuery = sQueryVal := rfl
  have hGrow : sGrow = sGrowVal :=
    (congrArg (fun s => execBrk (s.writeReg64 .x0 0x40004#64)) hQuery).trans
      (execBrk_grow_ok_eq sGrowIn brkTestMem0 0x40004#64 0x40000 0x41000
        rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) brkTestMem0_canMap_grow (by decide +kernel))
  have hSeed : sSeed = sSeedVal :=
    congrArg (fun s => s.setMem (s.mem.write8 0x40000#64 0xab#8)) hGrow
  have hSub : sSub = sSubVal :=
    (congrArg (fun s => execBrk (s.writeReg64 .x0 0x40100#64)) hSeed).trans
      (execBrk_same_page_eq sSubIn ((brkTestMem0.mapZero 0x40000#64 0x1000).write8 0x40000#64 0xab#8)
        0x40100#64 0x41000 rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have hOverlap : sOverlap = sOverlapVal :=
    (congrArg (fun s => execBrk (s.writeReg64 .x0 0x41008#64)) hSub).trans
      (execBrk_refuse_of_not_canMap sOverlapIn brkTestMem1 0x41008#64 0x41000 0x42000
        rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) brkTestMem1_canMap_overlap)
  have hBelow : sBelow = sBelowVal :=
    congrArg (fun s => execBrk (s.writeReg64 .x0 0x3ffff#64)) hSub
  have hAbove : sAbove = sAboveVal :=
    congrArg (fun s => execBrk (s.writeReg64 .x0 0x0001000000000001#64)) hSub
  have hShrink : sShrink = sShrinkVal :=
    congrArg (fun s => execBrk (s.writeReg64 .x0 0x40000#64)) hSub
  have hOom : sOom = sOomVal :=
    execBrk_grow_oom_eq ({ s0 with physMemAvail := 0 }.writeReg64 .x0 0x40004#64) brkTestMem0 0x40004#64 0x40000 0x41000
      rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) brkTestMem0_canMap_grow (by decide +kernel)
  exact prop_congr8
    (fun sQuery sGrow sSub sOverlap sBelow sAbove sShrink sOom =>
      sQuery.readReg64 .x0 = 0x40000#64 ∧
      sQuery.oracleIdx = 0 ∧
      sQuery.mem.perm 0x40000#64 = none ∧
      sGrow.readReg64 .x0 = 0x40004#64 ∧
      sGrow.brk = 0x40004#64 ∧
      sGrow.physMemAvail = 0 ∧
      sGrow.oracleIdx = 0 ∧
      sGrow.mem.perm 0x40000#64 = some .rw ∧
      sGrow.mem.perm 0x40fff#64 = some .rw ∧
      sGrow.mem.read8 0x40fff#64 = 0#8 ∧
      sSub.readReg64 .x0 = 0x40100#64 ∧
      sSub.brk = 0x40100#64 ∧
      sSub.mem.read8 0x40000#64 = 0xab#8 ∧
      sOverlap.readReg64 .x0 = 0x40100#64 ∧
      sOverlap.brk = 0x40100#64 ∧
      sOverlap.mem.read8 0x141000#64 = 0x77#8 ∧
      sBelow.readReg64 .x0 = 0x40100#64 ∧
      sBelow.brk = 0x40100#64 ∧
      sBelow.mem.perm 0x40000#64 = some .rw ∧
      sAbove.readReg64 .x0 = 0x40100#64 ∧
      sAbove.brk = 0x40100#64 ∧
      sShrink.readReg64 .x0 = 0x40000#64 ∧
      sShrink.brk = 0x40000#64 ∧
      sShrink.physMemAvail = 0x1000 ∧
      sShrink.mem.perm 0x40000#64 = none ∧
      sOom.status = .OutOfMemory)
    hQuery hGrow hSub hOverlap hBelow hAbove hShrink hOom
    (by decide +kernel)

/-- Conformance tests for `execMunmap`:
    - `munmap(0x50000, 0x2004)` unmaps `[0x50000, 0x53000)` across RW, `PROT_NONE`, and unmapped
      pages, returning `0` with `perm = none`;
    - returns `-EINVAL` (`-22`) on unaligned `addr`, `len = 0`, or ranges past `2 ^ 48`;
    - transitions to `.Exception` on frozen (`Perm.ro`) memory. -/
theorem munmap_conformance :
    let mem0 := (((Memory.empty.mapZero 0x50000#64 0x1000).write8 0x50000#64 0x41#8).mapFresh
      0x51000#64 0x1000 .protNone).mapFresh 0x60000#64 16 .ro
    let s0 : State := { mem := mem0 }
    let sUnmapOk := execMunmap ((s0.writeReg64 .x0 0x50000#64).writeReg64 .x1 0x2004#64)
    let sUnmapAlign := execMunmap ((s0.writeReg64 .x0 0x50001#64).writeReg64 .x1 0x1000#64)
    let sUnmapZero := execMunmap ((s0.writeReg64 .x0 0x50000#64).writeReg64 .x1 0#64)
    let sUnmapAbove := execMunmap ((s0.writeReg64 .x0 0x0001000000000000#64).writeReg64 .x1 0x1000#64)
    let sUnmapFrozen := execMunmap ((s0.writeReg64 .x0 0x60000#64).writeReg64 .x1 0x1000#64)
    s0.mem.perm 0x50000#64 = some .rw ∧
    s0.mem.perm 0x51000#64 = some .protNone ∧
    s0.mem.perm 0x52000#64 = none ∧
    sUnmapOk.readReg64 .x0 = 0#64 ∧
    sUnmapOk.mem.perm 0x50000#64 = none ∧
    sUnmapOk.mem.perm 0x50fff#64 = none ∧
    sUnmapOk.mem.perm 0x51000#64 = none ∧
    sUnmapOk.mem.perm 0x51fff#64 = none ∧
    sUnmapOk.mem.perm 0x52000#64 = none ∧
    sUnmapAlign.readReg64 .x0 = -22#64 ∧
    sUnmapZero.readReg64 .x0 = -22#64 ∧
    sUnmapAbove.readReg64 .x0 = -22#64 ∧
    sUnmapFrozen.status = .Exception "munmap on frozen memory" := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Conformance tests for `execMprotect`:
    - transitions `[0x50000, 0x51000)` to `some Perm.protNone` and back to `some Perm.rw`
      without altering byte contents;
    - returns `-EINVAL` on unaligned `addr`, `0` on `len = 0`, `-ENOMEM` on completely unmapped
      pages, and `.Exception` on partially mapped ranges, ranges past `2 ^ 48`, frozen
      (`Perm.ro`) memory, or unmodeled `prot`. -/
theorem mprotect_conformance :
    let mem0 := ((Memory.empty.mapZero 0x50000#64 0x1000).write8 0x50000#64 0x41#8).mapFresh
      0x60000#64 16 .ro
    let s0 : State := { mem := mem0, physMemAvail := 0x1000 }
    let sProtNone := execMprotect
      (((s0.writeReg64 .x0 0x50000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 0#64)
    let sProtRw := execMprotect
      (((sProtNone.writeReg64 .x0 0x50000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 3#64)
    let sProtEinval := execMprotect
      (((s0.writeReg64 .x0 0x50001#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 3#64)
    let sProtZero := execMprotect
      (((s0.writeReg64 .x0 0x50000#64).writeReg64 .x1 0#64).writeReg64 .x2 3#64)
    let sProtEnomem := execMprotect
      (((s0.writeReg64 .x0 0x52000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 3#64)
    let sProtPartial := execMprotect
      (((s0.writeReg64 .x0 0x50000#64).writeReg64 .x1 0x2000#64).writeReg64 .x2 0#64)
    let sProtAbove := execMprotect
      (((s0.writeReg64 .x0 0x0001000000000000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 3#64)
    let sProtFrozen := execMprotect
      (((s0.writeReg64 .x0 0x60000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 3#64)
    let sProtBad := execMprotect
      (((s0.writeReg64 .x0 0x50000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 1#64)
    sProtNone.readReg64 .x0 = 0#64 ∧
    sProtNone.mem.perm 0x50000#64 = some .protNone ∧
    sProtNone.mem.read8 0x50000#64 = 0x41#8 ∧
    sProtRw.readReg64 .x0 = 0#64 ∧
    sProtRw.mem.perm 0x50000#64 = some .rw ∧
    sProtRw.mem.read8 0x50000#64 = 0x41#8 ∧
    sProtEinval.readReg64 .x0 = -22#64 ∧
    sProtZero.readReg64 .x0 = 0#64 ∧
    sProtEnomem.readReg64 .x0 = -12#64 ∧
    sProtPartial.status = .Exception "mprotect on partially mapped range" ∧
    sProtAbove.status = .Exception "mprotect range exceeds user VA space" ∧
    sProtFrozen.status = .Exception "mprotect on frozen memory" ∧
    sProtBad.status = .Exception "unmodeled mprotect (only PROT_NONE and PROT_READ|PROT_WRITE)" := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Conformance tests for `execMadvise`:
    - `MADV_DONTNEED` (`4`) zero-fills `[0x50000, 0x51000)` and leaves permissions and
      neighboring bytes unchanged;
    - returns `0` on `MADV_HUGEPAGE` (`14`), `MADV_NOHUGEPAGE` (`15`), `MADV_DONTDUMP` (`16`),
      and `len = 0`, `-EINVAL` on unaligned `addr` or 64-bit wraparound, `-ENOMEM` on completely
      unmapped pages, and `.Exception` on partially mapped ranges, ranges past `2 ^ 48`, frozen
      memory, or unmodeled `advice`. -/
theorem madvise_conformance :
    let mem0 := (((Memory.empty.mapZero 0x50000#64 0x1000).write8 0x50000#64 0x41#8).write8
      0x51000#64 0x42#8).mapFresh 0x60000#64 16 .ro
    let s0 : State := { mem := mem0 }
    let sAdvHuge := execMadvise
      (((s0.writeReg64 .x0 0x50000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 14#64)
    let sAdvNohuge := execMadvise
      (((sAdvHuge.writeReg64 .x0 0x50000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 15#64)
    let sAdvNoop := execMadvise
      (((sAdvNohuge.writeReg64 .x0 0x50000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 16#64)
    let sAdvDontneed := execMadvise
      (((sAdvNoop.writeReg64 .x0 0x50000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 4#64)
    let sAdvEinval := execMadvise
      (((s0.writeReg64 .x0 0x50001#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 4#64)
    let sAdvWrap := execMadvise
      (((s0.writeReg64 .x0 0xfffffffffffff000#64).writeReg64 .x1 0x2000#64).writeReg64 .x2 4#64)
    let sAdvEnomem := execMadvise
      (((s0.writeReg64 .x0 0x52000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 4#64)
    let sAdvPartial := execMadvise
      (((s0.writeReg64 .x0 0x50000#64).writeReg64 .x1 0x2000#64).writeReg64 .x2 4#64)
    let sAdvAbove := execMadvise
      (((s0.writeReg64 .x0 0x0001000000000000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 4#64)
    let sAdvFrozen := execMadvise
      (((s0.writeReg64 .x0 0x60000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 4#64)
    let sAdvBad := execMadvise
      (((s0.writeReg64 .x0 0x50000#64).writeReg64 .x1 0x1000#64).writeReg64 .x2 99#64)
    sAdvHuge.readReg64 .x0 = 0#64 ∧
    sAdvHuge.mem.read8 0x50000#64 = 0x41#8 ∧
    sAdvNohuge.readReg64 .x0 = 0#64 ∧
    sAdvNohuge.mem.read8 0x50000#64 = 0x41#8 ∧
    sAdvNoop.readReg64 .x0 = 0#64 ∧
    sAdvNoop.mem.read8 0x50000#64 = 0x41#8 ∧
    sAdvDontneed.readReg64 .x0 = 0#64 ∧
    sAdvDontneed.mem.read8 0x50000#64 = 0#8 ∧
    sAdvDontneed.mem.perm 0x50000#64 = some .rw ∧
    sAdvDontneed.mem.read8 0x51000#64 = 0x42#8 ∧
    sAdvEinval.readReg64 .x0 = -22#64 ∧
    sAdvWrap.readReg64 .x0 = -22#64 ∧
    sAdvEnomem.readReg64 .x0 = -12#64 ∧
    sAdvPartial.status = .Exception "madvise on partially mapped range" ∧
    sAdvAbove.status = .Exception "madvise range exceeds user VA space" ∧
    sAdvFrozen.status = .Exception "madvise on frozen memory" ∧
    sAdvBad.status = .Exception "unmodeled madvise advice" := by
  decide +kernel

/-- Conformance tests for `execClockGettime`:
    - valid calls (`clk ∈ 0..7`, writable 16-byte buffer at `tp`) query
      `s.oracle.clockGettime s.oracleIdx`, write little-endian `tv_sec` at `tp` and `tv_nsec` at
      `tp + 8`, advance `s.oracleIdx`, and return `0`;
    - successive calls may return non-monotonic timestamps;
    - error paths (`-EFAULT` on unwritable `tp`, `.Exception` on `clk > 7`) leave `oracleIdx`
      unchanged. -/
theorem clock_gettime_conformance :
    let mem0 := Memory.empty.mapZero 0x2000#64 32
    let oracle0 : Oracle := {
      clockGettime := fun n =>
        if n == 0 then { sec := 1700000100#64, nsec := ⟨999999999, by decide⟩ }
        else { sec := 1700000050#64, nsec := ⟨42, by decide⟩ }
    }
    let s0 : State := { mem := mem0, oracle := oracle0 }
    let sCall0 := execClockGettime ((s0.writeReg64 .x0 1#64).writeReg64 .x1 0x2000#64)
    let sEfault := execClockGettime ((sCall0.writeReg64 .x0 0#64).writeReg64 .x1 0x3000#64)
    let sBadClk := execClockGettime ((sCall0.writeReg64 .x0 8#64).writeReg64 .x1 0x2000#64)
    let sCall1 := execClockGettime ((sEfault.writeReg64 .x0 7#64).writeReg64 .x1 0x2010#64)
    sCall0.status = .Running ∧
    sCall0.readReg64 .x0 = 0#64 ∧
    sCall0.oracleIdx = 1 ∧
    sCall0.mem.read64 0x2000#64 = 1700000100#64 ∧
    sCall0.mem.read64 0x2008#64 = 999999999#64 ∧
    sEfault.status = .Running ∧
    sEfault.readReg64 .x0 = -14#64 ∧
    sEfault.oracleIdx = 1 ∧
    sBadClk.status = .Exception "unmodeled clock_gettime clockid" ∧
    sBadClk.oracleIdx = 1 ∧
    sCall1.status = .Running ∧
    sCall1.readReg64 .x0 = 0#64 ∧
    sCall1.oracleIdx = 2 ∧
    sCall1.mem.read64 0x2010#64 = 1700000050#64 ∧
    sCall1.mem.read64 0x2018#64 = 42#64 := by
  decide +kernel

/-- Conformance tests for `SYS_GETRANDOM`:
    - valid `W2` flag masks (`0`, `GRND_NONBLOCK`, `GRND_RANDOM`, `GRND_INSECURE`, and allowed
      combinations, ignoring upper 32 bits of `X2`) with `count ≤ MAX_RW_COUNT` fill `count`
      bytes from `s.oracle.getrandom s.oracleIdx`, advance `oracleIdx`, and return `count`;
    - unknown flag bits, `GRND_RANDOM | GRND_INSECURE`, or `count > MAX_RW_COUNT` return
      `-EINVAL` (`-22`) without modifying memory or advancing `oracleIdx`;
    - unwritable buffers return `-EFAULT` (`-14`) without modifying memory or advancing
      `oracleIdx`. -/
theorem getrandom_conformance :
    let mem0 := Memory.empty.mapZero 0x2000#64 16
    let oracle0 : Oracle := { getrandom := fun n i => BitVec.ofNat 8 (16 * n + i + 0x10) }
    let s0 : State := ({ mem := mem0, oracle := oracle0 } : State).writeReg64 .x8 SYS_GETRANDOM
    let call (s : State) (buf count flags : BitVec 64) : State :=
      execSyscall (((s.writeReg64 .x0 buf).writeReg64 .x1 count).writeReg64 .x2 flags)
    let sOk0 := call s0 0x2000#64 2#64 0xdeadbeef_00000003#64
    let sBadBit := call sOk0 0x2000#64 2#64 0x8#64
    let sMutExcl6 := call sOk0 0x2000#64 2#64 0x6#64
    let sMutExcl7 := call sOk0 0x2000#64 2#64 0x7#64
    let sTooBig := call sOk0 0x2000#64 0x7ffff001#64 0#64
    let sEfault := call sOk0 0x3000#64 2#64 0#64
    sOk0.status = .Running ∧
    sOk0.readReg64 .x0 = 2#64 ∧
    sOk0.oracleIdx = 1 ∧
    sOk0.mem.readBytes 0x2000#64 2 = [0x10#8, 0x11#8] ∧
    sBadBit.readReg64 .x0 = -22#64 ∧
    sBadBit.oracleIdx = 1 ∧
    sBadBit.mem.readBytes 0x2000#64 2 = [0x10#8, 0x11#8] ∧
    sMutExcl6.readReg64 .x0 = -22#64 ∧
    sMutExcl6.oracleIdx = 1 ∧
    sMutExcl7.readReg64 .x0 = -22#64 ∧
    sMutExcl7.oracleIdx = 1 ∧
    sTooBig.readReg64 .x0 = -22#64 ∧
    sTooBig.oracleIdx = 1 ∧
    sTooBig.mem.readBytes 0x2000#64 2 = [0x10#8, 0x11#8] ∧
    sEfault.readReg64 .x0 = -14#64 ∧
    sEfault.oracleIdx = 1 := by
  decide +kernel

/-- Conformance tests for ASL boundary cases:
    - reserved and constrained encodings (`DecodeBitMasks` `len = 0` and `immr >= esize`, 8-bit
      register-offset `S = 1`, odd-register `CASP`, `STXP`/`STXR` register overlaps),
    - `BLR X30` target-before-link order,
    - `BFM`/`SBFM`/`UBFM` wrap-around (`imms < immr`),
    - `SADDLV`/`UADDLV`/`ADDV 2S` (`Q = 0, size = 10`) `UNDEFINED` fault,
    - `FMADD` `FPProcessNaNs3` (`QNaN + 0.0 * Inf -> DefaultNaN` vs `SNaN + 0.0 * Inf`). -/
theorem isa_asl_audit_conformance :
    decode 0x9200fc00#32 = none ∧
    decode 0x9210c000#32 = none ∧
    decode 0x38627820#32 = none ∧
    decode 0x3c617800#32 = none ∧
    decode 0x48217c40#32 = none ∧
    decode 0xc8200420#32 = none ∧
    (execInst (.simdAcrossLanes false false 0b10#2 0b00011#5 0#5 2#5) ({} : State)).status != .Running ∧
    (execInst (.simdAcrossLanes false true 0b10#2 0b00011#5 0#5 3#5) ({} : State)).status != .Running ∧
    evalBitfield .W64 .BFM 0xaaaaaaaaaaaaaaaa#64 0x123456789abcdef0#64 48 15 =
      0xaaaaaaaadef0aaaa#64 ∧
    evalBitfield .W64 .SBFM 0#64 0xfedcba9876543281#64 56 7 =
      0xffffffffffff8100#64 ∧
    evalBitfield .W32 .UBFM 0#64 0x9abcdef0#64 24 7 =
      0x000000000000f000#64 ∧
    fpFma32 0x7fc00001#32 0x00000000#32 0x7f800000#32 = 0x7fc00000#32 ∧
    fpFma32 0x7f800001#32 0x00000000#32 0x7f800000#32 = 0x7fc00001#32 ∧
    fpFma64 0x7ff8000000000001#64 0x0000000000000000#64 0x7ff0000000000000#64 =
      0x7ff8000000000000#64 ∧
    fpFma64 0x7ff0000000000001#64 0x0000000000000000#64 0x7ff0000000000000#64 =
      0x7ff8000000000001#64 := by
  decide +kernel

/-- Conformance tests for `FPSR` / `FPCR` system-register access and FP/AdvSIMD exception flags
    (`MRS`/`MSR` masking on `FPSR`, fail-closed nonzero writes to `FPCR`, and IEEE-754 / `QC`
    flag generation). -/
theorem fpsr_fpcr_conformance :
    let s0 : State := {}
    let sMrsFpcr := execInst (.sysReg true 0x5a20#15 .x0) (s0.writeReg64 .x0 0xdead#64)
    let sMsrFpcr0 := execInst (.sysReg false 0x5a20#15 .x0) (s0.writeReg64 .x0 0#64)
    let sMsrFpcrBad := execInst (.sysReg false 0x5a20#15 .x0) (s0.writeReg64 .x0 (1#64 <<< 22))
    let sMsrFpsrAll := execInst (.sysReg false 0x5a21#15 .x0) (s0.writeReg64 .x0 0xffffffff_ffffffff#64)
    let sMrsFpsr := execInst (.sysReg true 0x5a21#15 .x1) sMsrFpsrAll
    sMrsFpcr.readReg64 .x0 = 0#64 ∧
    sMsrFpcr0.status = .Running ∧
    sMsrFpcrBad.status = .Exception "unsupported FPCR value" ∧
    sMsrFpsrAll.fpsr = 0x0800009f#32 ∧
    sMrsFpsr.readReg64 .x1 = 0x0800009f#64 ∧
    -- Fp1Op flags (FMOV/FABS/FNEG on sNaN -> 0; FSQRT(-1) -> IOC; FRINTX(1.5) -> IXC; FRINTI/N(1.5) -> 0)
    evalFp1OpFlags64 0x00#6 0x7ff0000000000001#64 = 0#32 ∧
    evalFp1OpFlags64 0x01#6 0x7ff0000000000001#64 = 0#32 ∧
    evalFp1OpFlags64 0x02#6 0x7ff0000000000001#64 = 0#32 ∧
    evalFp1OpFlags64 0x03#6 0xbff0000000000000#64 = fpsrIOC ∧
    evalFp1OpFlags64 0x08#6 0x3ff8000000000000#64 = 0#32 ∧
    evalFp1OpFlags64 0x0e#6 0x3ff8000000000000#64 = fpsrIXC ∧
    evalFp1OpFlags64 0x0f#6 0x3ff8000000000000#64 = 0#32 ∧
    -- Fp2Op flags (FMUL/FDIV/FADD/FSUB/FMAX/FMIN/FMAXNM/FMINNM/FNMUL)
    evalFp2OpFlags64 0x0#4 0x0000000000000000#64 0x7ff0000000000000#64 = fpsrIOC ∧
    evalFp2OpFlags64 0x1#4 0x3ff0000000000000#64 0x0000000000000000#64 = fpsrDZC ∧
    evalFp2OpFlags64 0x2#4 0x7fefffffffffffff#64 0x7fefffffffffffff#64 = (fpsrOFC ||| fpsrIXC) ∧
    evalFp2OpFlags64 0x3#4 0x7ff0000000000000#64 0x7ff0000000000000#64 = fpsrIOC ∧
    evalFp2OpFlags64 0x4#4 0x7ff8000000000000#64 0x3ff0000000000000#64 = 0#32 ∧
    evalFp2OpFlags64 0x4#4 0x7ff0000000000001#64 0x3ff0000000000000#64 = fpsrIOC ∧
    evalFp2OpFlags64 0x6#4 0x7ff8000000000000#64 0x3ff0000000000000#64 = 0#32 ∧
    evalFp2OpFlags64 0x6#4 0x7ff0000000000001#64 0x3ff0000000000000#64 = fpsrIOC ∧
    evalFp2OpFlags64 0x8#4 0x0000000000000000#64 0x7ff0000000000000#64 = fpsrIOC ∧
    -- Fp3Op flags (FMADD 0*inf + qNaN -> IOC)
    evalFp3OpFlags64 false false 0x0000000000000000#64 0x7ff0000000000000#64 0x7ff8000000000001#64 = fpsrIOC ∧
    -- FCMP vs FCMPE on qNaN
    evalFpCmpFlags64 false 0x7ff8000000000000#64 0x3ff0000000000000#64 = 0#32 ∧
    evalFpCmpFlags64 true 0x7ff8000000000000#64 0x3ff0000000000000#64 = fpsrIOC ∧
    -- Conversions (D->S underflow, S->D sNaN, FP->int inexact vs out-of-range IOC without IXC)
    evalFpCvt64To32Flags 0x3808000000000001#64 = (fpsrUFC ||| fpsrIXC) ∧
    evalFpCvt32To64Flags 0x7f800001#32 = fpsrIOC ∧
    evalFpToIntFlags64_64 false 0b11#2 0x3ff8000000000000#64 = fpsrIXC ∧
    evalFpToIntFlags64_64 false 0b11#2 0x43e0000000000000#64 = fpsrIOC ∧
    evalIntToFpFlags32_64 false 0x01000001#64 = fpsrIXC ∧
    -- Saturating SIMD QC
    evalSimdThreeSameExtSatFlags false false 0b10#2 0b00001#5 0x00000001#128 0x7fffffff#128 = some fpsrQC := by
  decide +kernel

/-- Conformance tests for AdvSIMD lane/interleaved structure loads and stores (`LD1`..`LD4`,
    `ST1`..`ST4`), scalar `DUP`, and three-register-different arithmetic (`SMULL`, `UMULL`,
    `SMLAL`, `UMLAL`, `ADDHN`, `UADDW`). -/
theorem simd_multi_lane_threediff_conformance :
    decode 0x4d408513#32 = some (.simdLdSt1Single true true false 0#5 4#3 false 1#2 .x8 19#5) ∧
    encode (.simdLdSt1Single true true false 0#5 4#3 false 1#2 .x8 19#5) = some 0x4d408513#32 ∧
    decode 0x5e180400#32 = some (.simdDupScalar 0b11000#5 0#5 0#5) ∧
    encode (.simdDupScalar 0b11000#5 0#5 0#5) = some 0x5e180400#32 ∧
    decode 0x4c400100#32 = some (.simdLdStMulti true true 0#2 4 .x8 false 0#5 0#5) ∧
    encode (.simdLdStMulti true true 0#2 4 .x8 false 0#5 0#5) = some 0x4c400100#32 ∧
    decode 0x0e62c020#32 = some (.simdThreeDiff false false 1#2 2#5 0b1100#4 1#5 0#5) ∧
    encode (.simdThreeDiff false false 1#2 2#5 0b1100#4 1#5 0#5) = some 0x0e62c020#32 ∧
    evalSimdDupScalar 0b11000#5 0xfedcba9876543210_0123456789abcdef#128 = 0x0000000000000000_fedcba9876543210#128 ∧
    evalSimdThreeDiff false false 1#2 0b1100#4
      0#128
      0x0000000000000000_fffeffff_00030002#128
      0x0000000000000000_00040005_fffe0003#128 =
      0xfffffff8_fffffffb_fffffffa_00000006#128 ∧
    evalSimdThreeDiff true false 0#2 0b0100#4
      0xdeadbeefcafebabe_1122334455667788#128
      0x0200010000800040_0020001000080004#128
      0x0100010000800040_0020001000080004#128 =
      0x0302010000000000_1122334455667788#128 := by
  decide +kernel

end Testing
