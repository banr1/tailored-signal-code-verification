/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.Process
public import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP.Structural
public import ProofLib.Process.Core

@[expose] public section

set_option autoImplicit false

/-!
# Initial Process Stack Layout for the CLI

Computes `buildInitialStack` and `ElfImage.loadState` in closed form for
`processInputs ("signal-session" :: argv) stdin files dirs` on NUL-free ASCII argument
vectors satisfying `ArgvFitsInitialStack` (at most 16 KiB of strings and pointers on the
8 MiB stack, `top = 0x7fffffff0000`, `stackBase = 0x7fffff7f0000`).

- `buildInitialStack_eq` and `loadState_cli_layout`: closed-form initial stack frame
  `[sp0, top)` (`frameBytes`) and at least 8,371,824 zero read-write bytes in
  `[stackBase, sp0)`.
- `satisfies_initStack` and `satisfies_initStack_aux`: separation-logic decomposition into
  `argc` at `sp0`, `argvAt (sp0 + 8)`, `envp` `NULL` plus the 19 `auxv` pairs (`auxWords`),
  and the free stack `[stackBase, sp0)`.
-/

namespace CryptoVerification.SignalSession.InitStack

open Arm64 Arm64.Process ProofLib

/-! ## Closed Form of `packCStringList` -/

/-- Addresses of NUL-terminated strings packed from `base + off` on. -/
def packAddrs (base : BitVec 64) : Nat → List (List (BitVec 8)) → List (BitVec 64)
  | _, [] => []
  | off, s :: ss => (base + BitVec.ofNat 64 off) :: packAddrs base (off + s.length + 1) ss

theorem packAddrs_length (base : BitVec 64) (off : Nat) (strs : List (List (BitVec 8))) :
    (packAddrs base off strs).length = strs.length := by
  induction strs generalizing off with
  | nil => rfl
  | cons s ss ih => simp [packAddrs, ih]

private theorem packFold (base : BitVec 64) (strs : List (List (BitVec 8))) :
    ∀ (off : Nat) (bs : List (BitVec 8)) (as : List (BitVec 64)),
      strs.foldl
          (fun (acc : Nat × List (BitVec 8) × List (BitVec 64)) s =>
            (acc.1 + (s ++ [0#8]).length, acc.2.1 ++ (s ++ [0#8]),
              acc.2.2 ++ [base + BitVec.ofNat 64 acc.1]))
          (off, bs, as) =
        (off + (strs.map fun s => s.length + 1).sum,
          bs ++ strs.flatMap (· ++ [0#8]), as ++ packAddrs base off strs) := by
  induction strs with
  | nil => intro off bs as; simp [packAddrs]
  | cons s ss ih =>
    intro off bs as
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_singleton, List.map_cons, List.sum_cons,
      List.flatMap_cons, List.append_assoc, packAddrs, List.singleton_append, Prod.mk.injEq]
    refine ⟨by omega, trivial, ?_⟩
    simp only [Nat.add_assoc]

/-- `packCStringList` in closed form. -/
theorem packCStringList_eq (base : BitVec 64) (strs : List (List (BitVec 8))) :
    packCStringList base strs =
      ((strs.map fun s => s.length + 1).sum, strs.flatMap (· ++ [0#8]), packAddrs base 0 strs) := by
  have h := packFold base strs 0 [] []
  simp only [Nat.zero_add, List.nil_append] at h
  exact h

/-! ## Length Lemmas -/

theorem foldl_len_eq_sum (strs : List (List (BitVec 8))) (n : Nat) :
    strs.foldl (fun n s => n + s.length + 1) n = n + (strs.map fun s => s.length + 1).sum := by
  induction strs generalizing n with
  | nil => simp
  | cons s ss ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

theorem flatMap_bytesLE_length (ws : List (BitVec 64)) :
    (ws.flatMap (Obj.bytesLE 8)).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, Obj.bytesLE,
      List.length_map, List.length_range]
    omega

theorem flatMap_cstr_length (strs : List (List (BitVec 8))) :
    (strs.flatMap (· ++ [0#8])).length = (strs.map fun s => s.length + 1).sum := by
  induction strs with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_singleton, List.map_cons,
      List.sum_cons]

theorem le_alignUp16 (n : Nat) : n ≤ alignUp16 n := by unfold alignUp16; omega
theorem alignUp16_lt (n : Nat) : alignUp16 n < n + 16 := by unfold alignUp16; omega
theorem alignUp16_mod (n : Nat) : alignUp16 n % 16 = 0 := by unfold alignUp16; omega

/-- `buildInitialStack` pads the table to an even number of words. -/
theorem pad_eq (ws : List (BitVec 64)) (n : Nat) (h : ws.length = n) :
    (if (ws.length % 2 == 0) = true then ws else ws ++ [0#64]) =
      ws ++ List.replicate (n % 2) 0#64 := by
  subst h
  rcases Nat.mod_two_eq_zero_or_one ws.length with h | h <;> simp [h]

theorem flatMap_pair_length (ps : List (BitVec 64 × BitVec 64)) :
    (ps.flatMap fun x => [x.1, x.2]).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]
    omega

/-! ## Stack Frame Layout -/

def top : Nat := defaultStackTop.toNat

/-- CLI stack size (8 MiB): `processInputs` sets `stackSize := 8388608` (DEV-CLI7) rather than `defaultStackSize` (128 KiB). -/
def cliStackSize : Nat := 8388608

theorem cliStackSize_eq : cliStackSize = 8388608 := rfl

theorem processInputs_stackSize (argv : List String) (stdin : List (BitVec 8))
    (files : List (String × List (BitVec 8))) (dirs : List String) :
    (processInputs argv stdin files dirs).stackSize = cliStackSize := rfl

/-- Lowest stack address `defaultStackTop - cliStackSize` (`0x7fffff7f0000`). -/
def stackBase : Nat := defaultStackTop.toNat - cliStackSize

theorem top_eq : top = 0x7fffffff0000 := rfl
theorem stackBase_eq : stackBase = 0x7fffff7f0000 := by decide

section Frame

variable (elf : ElfImage) (strs : List (List (BitVec 8)))

/-- Total byte length of NUL-terminated `argv` strings. -/
def strLen : Nat := (strs.map fun s => s.length + 1).sum

/-- `upperRawLen` with `envp = []` and `execfn = []`: `"aarch64\0"` (8), `argv` strings, `"\0"` (1), and 8-byte sentinel. -/
def upperRawLen : Nat := 8 + strLen strs + 0 + 1 + 8

def infoPadLen : Nat := alignUp16 (upperRawLen strs) - upperRawLen strs

/-- `infoLen` with `envp = []` and `execfn = []`: 16-byte `AT_RANDOM` buffer plus 16-byte-aligned `upperRawLen`. -/
def infoLen : Nat := 16 + alignUp16 (upperRawLen strs)

def infoBase : Nat := top - infoLen strs

/-- Word count of `[sp0, infoBase)`: `argc`, `argv` pointers, `argv` `NULL`, `envp` `NULL`, and 19 `auxv` pairs, padded to even length. -/
def tableWords : Nat := strs.length + 41 + (strs.length + 41) % 2

def sp0 : Nat := infoBase strs - 8 * tableWords strs

/-- Address of the platform string `"aarch64\0"`. -/
def platformAddr : BitVec 64 :=
  BitVec.ofNat 64 (infoBase strs) + BitVec.ofNat 64 (16 + infoPadLen strs)

/-- Start of the packed NUL-terminated `argv` strings (`platformAddr + 8`). -/
def argvBase : BitVec 64 :=
  platformAddr strs + 8#64

/-- `AT_EXECFN` address (NUL-terminated `inputs.execfn` following `argv` and `envp`). -/
def execfnAddr : BitVec 64 :=
  argvBase strs + BitVec.ofNat 64 (strLen strs) + 0#64

def ptrWords : List (BitVec 64) := packAddrs (argvBase strs) 0 strs ++ [0#64]

/-- `envp` `NULL`, the 19 `auxv` pairs, and optional alignment padding word. -/
def restWords : List (BitVec 64) :=
  [ 0#64
  , AuxvTag.phdr,     elf.phdrVaddr
  , AuxvTag.phent,    BitVec.ofNat 64 elf.phent
  , AuxvTag.phnum,    BitVec.ofNat 64 elf.phnum
  , AuxvTag.pagesz,   BitVec.ofNat 64 Obj.pageSize
  , AuxvTag.base,     0#64
  , AuxvTag.flags,    0#64
  , AuxvTag.entry,    elf.entry
  , AuxvTag.uid,      1000#64
  , AuxvTag.euid,     1000#64
  , AuxvTag.gid,      1000#64
  , AuxvTag.egid,     1000#64
  , AuxvTag.platform, platformAddr strs
  , AuxvTag.hwcap,    0x3#64
  , AuxvTag.clktck,   100#64
  , AuxvTag.secure,   0#64
  , AuxvTag.random,   BitVec.ofNat 64 (infoBase strs)
  , AuxvTag.hwcap2,   0#64
  , AuxvTag.execfn,   execfnAddr strs
  , AuxvTag.null,     0#64 ] ++ List.replicate ((strs.length + 41) % 2) 0#64

/-- The 39 unpadded words of `restWords` (`envp` `NULL` and 19 `auxv` pairs) read by musl startup. -/
def auxWords : List (BitVec 64) :=
  [ 0#64
  , AuxvTag.phdr,     elf.phdrVaddr
  , AuxvTag.phent,    BitVec.ofNat 64 elf.phent
  , AuxvTag.phnum,    BitVec.ofNat 64 elf.phnum
  , AuxvTag.pagesz,   BitVec.ofNat 64 Obj.pageSize
  , AuxvTag.base,     0#64
  , AuxvTag.flags,    0#64
  , AuxvTag.entry,    elf.entry
  , AuxvTag.uid,      1000#64
  , AuxvTag.euid,     1000#64
  , AuxvTag.gid,      1000#64
  , AuxvTag.egid,     1000#64
  , AuxvTag.platform, platformAddr strs
  , AuxvTag.hwcap,    0x3#64
  , AuxvTag.clktck,   100#64
  , AuxvTag.secure,   0#64
  , AuxvTag.random,   BitVec.ofNat 64 (infoBase strs)
  , AuxvTag.hwcap2,   0#64
  , AuxvTag.execfn,   execfnAddr strs
  , AuxvTag.null,     0#64 ]

def argcBytes : List (BitVec 8) := Obj.bytesLE 8 (BitVec.ofNat 64 strs.length)

def ptrBytes : List (BitVec 8) := (ptrWords strs).flatMap (Obj.bytesLE 8)

def restBytes : List (BitVec 8) := (restWords elf strs).flatMap (Obj.bytesLE 8)

/-- 16 zero `AT_RANDOM` bytes, 16-byte alignment padding, and `"aarch64\0"` (`[infoBase, argvBase)`). -/
def headBytes : List (BitVec 8) :=
  List.replicate 16 0#8 ++ List.replicate (infoPadLen strs) 0#8 ++
    [0x61#8, 0x61#8, 0x72#8, 0x63#8, 0x68#8, 0x36#8, 0x34#8, 0x00#8]

def strBytes : List (BitVec 8) := strs.flatMap (· ++ [0#8])

/-- `inputs.execfn` (`"\0"`) followed by the 8-byte top-of-stack zero sentinel. -/
def tailBytes : List (BitVec 8) :=
  (0#8 :: List.replicate 8 0#8)

/-- Complete initial stack frame bytes in `[sp0, top)`. -/
def frameBytes : List (BitVec 8) :=
  argcBytes strs ++
    (ptrBytes strs ++ ((restBytes elf strs ++ headBytes strs) ++ (strBytes strs ++ tailBytes)))

end Frame

/-! ## Closed Form of `buildInitialStack` -/

/-- `buildInitialStack` with the CLI's stack, the default auxv and no envp, on NUL-free strings that fit. -/
theorem buildInitialStack_eq (elf : ElfImage) (inputs : ProcessInputs)
    (strs : List (List (BitVec 8)))
    (hargv : inputs.argv = strs) (henvp : inputs.envp = []) (hexecfn : inputs.execfn = [])
    (hauxv : inputs.auxv = {})
    (htop : inputs.stackTop = defaultStackTop) (hsize : inputs.stackSize = cliStackSize)
    (hnul : ∀ s ∈ strs, ∀ b ∈ s, b ≠ 0#8)
    (hbrk : elf.brkStart.toNat ≤ stackBase)
    (hfit : 8 * tableWords strs + infoLen strs ≤ cliStackSize) :
    buildInitialStack elf inputs =
      .ok (BitVec.ofNat 64 (sp0 strs),
        { start := BitVec.ofNat 64 (sp0 strs), perm := Perm.rw, bytes := frameBytes elf strs }) := by
  obtain ⟨argv, envp, execfn, stdin, files, dirs, ⟨auxv, stackTop, stackSize, physMemAvail, oracle⟩⟩ := inputs
  simp only [ProcessInputs.auxv, ProcessInputs.stackTop, ProcessInputs.stackSize] at hargv henvp hexecfn hauxv htop hsize
  subst hargv henvp hexecfn hauxv htop hsize
  have hany : argv.any (fun s => s.contains 0#8) = false := by
    rw [List.any_eq_false]
    intro s hs h
    exact hnul s hs 0#8 (List.contains_iff_mem.mp h) rfl
  have hex : ([] : List (BitVec 8)).contains 0#8 = false := rfl
  have hg1 : (defaultStackTop.toNat % Obj.pageSize != 0 || cliStackSize == 0 ||
      cliStackSize % Obj.pageSize != 0) = false := by decide
  have hg2 : ¬ (cliStackSize > defaultStackTop.toNat) := by decide
  have hg3 : ¬ (elf.brkStart.toNat > defaultStackTop.toNat - cliStackSize) := by
    unfold stackBase at hbrk; omega
  have hg4 : ¬ (infoLen argv > cliStackSize) := by omega
  have hraw : List.foldl (fun n s => n + s.length + 1) 0 argv = strLen argv := by
    rw [foldl_len_eq_sum, Nat.zero_add]; rfl
  have hSL : (argv.map fun s => s.length + 1).sum = strLen argv := rfl
  have hUR : 8 + strLen argv + 0 + 1 + 8 = upperRawLen argv := rfl
  have hPL : alignUp16 (upperRawLen argv) - upperRawLen argv = infoPadLen argv := rfl
  have hIL : 16 + alignUp16 (upperRawLen argv) = infoLen argv := rfl
  have hIB : defaultStackTop.toNat - infoLen argv = infoBase argv := rfl
  have hPA : BitVec.ofNat 64 (infoBase argv) + BitVec.ofNat 64 (16 + infoPadLen argv) =
      platformAddr argv := rfl
  have hAB : platformAddr argv + BitVec.ofNat 64 8 = argvBase argv := rfl
  unfold buildInitialStack
  simp only [hany, hex, List.any_nil, packCStringList_eq, List.length_replicate,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hg1, hg2, hg3, hg4, hraw, hSL, hUR, hPL,
    hIL, hIB, hPA, hAB, List.foldl_nil, List.length_cons, List.length_nil, Nat.add_zero,
    List.map_nil, List.sum_nil, List.flatMap_nil, packAddrs, List.append_nil, List.nil_append,
    pure, Except.pure]
  have hstr : (argv.flatMap (fun x => x ++ [0#8])).length = strLen argv := flatMap_cstr_length argv
  have hle : upperRawLen argv ≤ alignUp16 (upperRawLen argv) := le_alignUp16 _
  rw [pad_eq _ (argv.length + 41)]
  rotate_left
  · simp [packAddrs_length]
  split
  · rename_i h
    exfalso
    rw [flatMap_bytesLE_length] at h
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate,
      packAddrs_length, flatMap_pair_length, hstr] at h
    unfold tableWords infoLen upperRawLen at hfit
    unfold infoPadLen upperRawLen at h hle
    omega
  · simp only [Except.ok.injEq, Prod.mk.injEq, Snapshot.Region.mk.injEq, true_and, and_true,
      flatMap_bytesLE_length, List.length_append, List.length_cons, List.length_nil,
      List.length_replicate, packAddrs_length, flatMap_pair_length]
    refine ⟨?_, ?_, ?_⟩
    · congr 1; unfold sp0 tableWords; omega
    · congr 1; unfold sp0 tableWords; omega
    unfold frameBytes argcBytes ptrBytes ptrWords restBytes restWords headBytes strBytes tailBytes
      execfnAddr argvBase platformAddr
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc, List.cons_append, List.nil_append]

/-! ## Address Constants -/

theorem toNat_stackBase : (BitVec.ofNat 64 stackBase).toNat = stackBase := by
  rw [BitVec.toNat_ofNat, stackBase_eq]

theorem sub_toNat (x y : BitVec 64) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub]; have := x.isLt; omega

/-! ## Loaded Stack Memory -/

/-- Loaded memory combining ELF segments, the initial frame `bs` at `sp`, and zero-mapped `[stackBase, sp)`. -/
def stackMem (segs : List Snapshot.Region) (sp : BitVec 64) (bs : List (BitVec 8)) : Memory :=
  Memory.mapZero ⟨Snapshot.loadCellAt (segs ++ [{ start := sp, perm := Perm.rw, bytes := bs }])⟩
    (BitVec.ofNat 64 stackBase) cliStackSize

theorem cellAt_none_of (rs : List Snapshot.Region) (a : BitVec 64)
    (h : ∀ r ∈ rs, ¬ (a - r.start).toNat < r.bytes.length) : Snapshot.cellAt rs a = none := by
  unfold Snapshot.cellAt
  rw [List.findSome?_eq_none_iff]
  intro r hr
  dsimp only
  split
  · rename_i hlt; exact absurd hlt (h r hr)
  · rfl

private theorem loadCellAt_none_of (rs : List Snapshot.Region) (a : BitVec 64)
    (h : ∀ r ∈ rs, ¬ (a - r.start).toNat < r.bytes.length) : Snapshot.loadCellAt rs a = none := by
  unfold Snapshot.loadCellAt
  rw [List.findSome?_eq_none_iff]
  intro r hr
  dsimp only
  split
  · rename_i hlt; exact absurd hlt (h r hr)
  · rfl

theorem cellAt_segs_none (segs : List Snapshot.Region)
    (hsegs : ∀ r ∈ segs, r.start.toNat + r.bytes.length ≤ stackBase) (a : BitVec 64)
    (ha : stackBase ≤ a.toNat) : Snapshot.cellAt segs a = none := by
  refine cellAt_none_of segs a fun r hr => ?_
  have h1 := hsegs r hr
  rw [sub_toNat _ _ (by omega)]
  omega

/-- The frame bytes are in `stackMem`, read-write. -/
theorem stackMem_holdsBytes (segs : List Snapshot.Region) (sp : BitVec 64) (bs : List (BitVec 8))
    (hsegs : ∀ r ∈ segs, r.start.toNat + r.bytes.length ≤ stackBase)
    (hsp : stackBase ≤ sp.toNat) (hwrap : sp.toNat + bs.length ≤ 2 ^ 64) :
    Obj.HoldsBytes (stackMem segs sp bs) sp bs (fun _ => Perm.rw) := by
  unfold stackMem
  apply holdsBytes_mapZero
  intro i hi
  have hpre : segs.all (Snapshot.Below sp) = true := by
    rw [List.all_eq_true]
    intro r hr
    have := hsegs r hr
    simp only [Snapshot.Below, decide_eq_true_eq]
    omega
  have hcell := Snapshot.cellAt_of_split (post := []) (r := { start := sp, perm := Perm.rw, bytes := bs })
    hpre hi hwrap
  dsimp only at hcell
  refine ⟨?_, ?_, Snapshot.isLazyFree_loadCellAt _ _⟩
  · rw [Snapshot.read8_loadCellAt]; simp only [Memory.read8, hcell]
  · rw [Snapshot.perm_loadCellAt]; simp only [Memory.perm, hcell]; rfl

/-- Below the frame, `stackMem` is zero and read-write. -/
theorem stackMem_zero (segs : List Snapshot.Region) (sp : BitVec 64) (bs : List (BitVec 8))
    (hsegs : ∀ r ∈ segs, r.start.toNat + r.bytes.length ≤ stackBase)
    (htop : sp.toNat + bs.length = top) (a : BitVec 64)
    (ha1 : stackBase ≤ a.toNat) (ha2 : a.toNat < sp.toNat) :
    (stackMem segs sp bs).cells a = some (some Perm.rw, 0#8) := by
  have htop' := top_eq
  have hsb := stackBase_eq
  have hnone : Snapshot.loadCellAt (segs ++ [{ start := sp, perm := Perm.rw, bytes := bs }]) a = none := by
    refine loadCellAt_none_of _ a fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · have h1 := hsegs r hr
      rw [sub_toNat _ _ (by omega)]
      omega
    · rw [List.mem_singleton] at hr
      subst hr
      dsimp only
      rw [BitVec.toNat_sub]
      have := sp.isLt
      omega
  have hin : (a - BitVec.ofNat 64 stackBase).toNat < cliStackSize := by
    rw [sub_toNat _ _ (by rw [toNat_stackBase]; exact ha1), toNat_stackBase, cliStackSize_eq]
    omega
  unfold stackMem Memory.mapZero
  dsimp only
  have hp : (Memory.perm ⟨Snapshot.loadCellAt (segs ++ [{ start := sp, perm := Perm.rw, bytes := bs }])⟩ a)
      = none := by
    simp only [Memory.perm, hnone]
  rw [hp]
  simp only [hin, decide_true, Option.mapped, Option.isSome_none, Bool.not_false, Bool.and_self,
    ↓reduceIte]

/-- Outside the segments and the stack, `stackMem` has no cell. -/
theorem stackMem_outside (segs : List Snapshot.Region) (sp : BitVec 64) (bs : List (BitVec 8))
    (hsp : stackBase ≤ sp.toNat) (htop : sp.toNat + bs.length = top) (a : BitVec 64)
    (hseg : ∀ r ∈ segs, ¬ (a - r.start).toNat < r.bytes.length)
    (ha : a.toNat < stackBase ∨ top ≤ a.toNat) :
    (stackMem segs sp bs).cells a = none := by
  have htop' := top_eq
  have hsb := stackBase_eq
  have hlt := a.isLt
  have hnone : Snapshot.loadCellAt (segs ++ [{ start := sp, perm := Perm.rw, bytes := bs }]) a = none := by
    refine loadCellAt_none_of _ a fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact hseg r hr
    · rw [List.mem_singleton] at hr
      subst hr
      dsimp only
      rw [BitVec.toNat_sub]
      omega
  have hout : ¬ (a - BitVec.ofNat 64 stackBase).toNat < cliStackSize := by
    rw [BitVec.toNat_sub, toNat_stackBase, cliStackSize_eq]
    omega
  have hp : (Memory.perm ⟨Snapshot.loadCellAt (segs ++ [{ start := sp, perm := Perm.rw, bytes := bs }])⟩ a)
      = none := by
    simp only [Memory.perm, hnone]
  unfold stackMem Memory.mapZero
  dsimp only
  rw [hp]
  simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hnone]

/-! ## `ElfImage.loadState` Decomposition -/

theorem rawState_eq (elf : ElfImage) (inputs : ProcessInputs) (sp : BitVec 64)
    (bs : List (BitVec 8))
    (hb : buildInitialStack elf inputs = .ok (sp, { start := sp, perm := Perm.rw, bytes := bs }))
    (htop : inputs.stackTop = defaultStackTop) (hsize : inputs.stackSize = cliStackSize) :
    (elf.rawState inputs).sp = sp ∧ (elf.rawState inputs).mem = stackMem elf.segments sp bs := by
  unfold ElfImage.rawState
  unfold ProcessInputs.stackTop at htop
  unfold ProcessInputs.stackSize at hsize
  rw [hb]
  rw [htop, hsize]
  exact ⟨rfl, rfl⟩

theorem loadState_eq (elf : ElfImage) (inputs : ProcessInputs) (sp : BitVec 64)
    (bs : List (BitVec 8)) (hwf : elf.WellFormed = true)
    (hb : buildInitialStack elf inputs = .ok (sp, { start := sp, perm := Perm.rw, bytes := bs }))
    (hdirs : ∀ d ∈ inputs.dirs, Arm64.hasLeadingSlash d = false ∧ Arm64.hasDotDot d = false)
    (hfiles : ∀ f ∈ inputs.files,
      (Arm64.hasLeadingSlash f.1 = false ∧ Arm64.hasDotDot f.1 = false) ∧
        f.2.length ≤ Arm64.MAX_LFS_FILESIZE) :
    elf.loadState inputs = .ok (elf.rawState inputs) := by
  apply ElfImage.loadState_eq_rawState
  have hd : inputs.dirs.any (fun d => Arm64.hasLeadingSlash d || Arm64.hasDotDot d) = false :=
    List.any_eq_false.mpr fun d hd => Bool.eq_false_iff.mp (Bool.or_eq_false_iff.mpr (hdirs d hd))
  have hf : inputs.files.any (fun (p, bs) =>
      Arm64.hasLeadingSlash p || Arm64.hasDotDot p || !decide (bs.length ≤ Arm64.MAX_LFS_FILESIZE)) = false :=
    List.any_eq_false.mpr fun (p, bs) hf => by
      obtain ⟨⟨h1, h2⟩, h3⟩ := hfiles (p, bs) hf
      simp [h1, h2, h3]
  unfold ElfImage.loadState
  simp [hwf, hd, hf, hb, Functor.map, Except.map, Except.toOption]

/-! ## Frame Arithmetic -/

theorem strLen_def (strs : List (List (BitVec 8))) :
    (strs.map fun s => s.length + 1).sum = strLen strs := rfl

theorem frameBytes_length (elf : ElfImage) (strs : List (List (BitVec 8))) :
    (frameBytes elf strs).length = 8 * tableWords strs + infoLen strs := by
  have hle : upperRawLen strs ≤ alignUp16 (upperRawLen strs) := le_alignUp16 _
  unfold frameBytes argcBytes ptrBytes ptrWords restBytes restWords headBytes strBytes tailBytes
    tableWords infoLen infoPadLen
  simp only [List.length_append, flatMap_bytesLE_length, flatMap_cstr_length, strLen_def,
    List.length_cons, List.length_nil, List.length_replicate, packAddrs_length, Obj.bytesLE,
    List.length_map, List.length_range]
  unfold upperRawLen at *
  omega

theorem sp0_le_top (strs : List (List (BitVec 8))) : sp0 strs ≤ top := by
  unfold sp0 infoBase; omega

theorem toNat_sp0 (strs : List (List (BitVec 8))) : (BitVec.ofNat 64 (sp0 strs)).toNat = sp0 strs := by
  have := sp0_le_top strs
  have := top_eq
  rw [BitVec.toNat_ofNat]; omega

theorem sp0_add_frame (elf : ElfImage) (strs : List (List (BitVec 8)))
    (hfit : 8 * tableWords strs + infoLen strs ≤ cliStackSize) :
    sp0 strs + (frameBytes elf strs).length = top ∧ stackBase ≤ sp0 strs := by
  rw [frameBytes_length]
  have := top_eq
  have := stackBase_eq
  have := cliStackSize_eq
  unfold sp0 infoBase
  unfold stackBase at *
  constructor <;> omega

theorem segs_below (elf : ElfImage) (hwf : elf.WellFormed = true)
    (hbrk : elf.brkStart.toNat ≤ stackBase) :
    ∀ r ∈ elf.segments, r.start.toNat + r.bytes.length ≤ stackBase := by
  unfold ElfImage.WellFormed at hwf
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  intro r hr
  have := hwf.2 r hr
  omega

/-! ## Generic Loader Layout -/

/-- `rawState` stack pointer and memory layout for NUL-free `strs` fitting within `cliStackSize`. -/
theorem rawState_layout (elf : ElfImage) (inputs : ProcessInputs) (strs : List (List (BitVec 8)))
    (hargv : inputs.argv = strs) (henvp : inputs.envp = []) (hexecfn : inputs.execfn = [])
    (hauxv : inputs.auxv = {})
    (htop : inputs.stackTop = defaultStackTop) (hsize : inputs.stackSize = cliStackSize)
    (hnul : ∀ s ∈ strs, ∀ b ∈ s, b ≠ 0#8)
    (hbrk : elf.brkStart.toNat ≤ stackBase)
    (hfit : 8 * tableWords strs + infoLen strs ≤ cliStackSize) :
    (elf.rawState inputs).sp = BitVec.ofNat 64 (sp0 strs) ∧
      (elf.rawState inputs).mem =
        stackMem elf.segments (BitVec.ofNat 64 (sp0 strs)) (frameBytes elf strs) :=
  rawState_eq elf inputs _ _
    (buildInitialStack_eq elf inputs strs hargv henvp hexecfn hauxv htop hsize hnul hbrk hfit)
    htop hsize

/-- `ElfImage.loadState` layout for NUL-free `strs` fitting within `cliStackSize`. -/
theorem load_layout (elf : ElfImage) (inputs : ProcessInputs) (strs : List (List (BitVec 8)))
    (hargv : inputs.argv = strs) (henvp : inputs.envp = []) (hexecfn : inputs.execfn = [])
    (hauxv : inputs.auxv = {})
    (htop : inputs.stackTop = defaultStackTop) (hsize : inputs.stackSize = cliStackSize)
    (hnul : ∀ s ∈ strs, ∀ b ∈ s, b ≠ 0#8)
    (hwf : elf.WellFormed = true) (hbrk : elf.brkStart.toNat ≤ stackBase)
    (hfit : 8 * tableWords strs + infoLen strs ≤ cliStackSize)
    (hdirs : ∀ d ∈ inputs.dirs, Arm64.hasLeadingSlash d = false ∧ Arm64.hasDotDot d = false)
    (hfiles : ∀ f ∈ inputs.files,
      (Arm64.hasLeadingSlash f.1 = false ∧ Arm64.hasDotDot f.1 = false) ∧
        f.2.length ≤ Arm64.MAX_LFS_FILESIZE) :
    elf.loadState inputs = .ok (elf.rawState inputs) ∧
      (elf.rawState inputs).sp = BitVec.ofNat 64 (sp0 strs) ∧
      (elf.rawState inputs).mem =
        stackMem elf.segments (BitVec.ofNat 64 (sp0 strs)) (frameBytes elf strs) := by
  have hb := buildInitialStack_eq elf inputs strs hargv henvp hexecfn hauxv htop hsize hnul hbrk hfit
  obtain ⟨hsp, hmem⟩ := rawState_eq elf inputs _ _ hb htop hsize
  exact ⟨loadState_eq elf inputs _ _ hwf hb hdirs hfiles, hsp, hmem⟩

theorem readBytes_of_holdsBytes {m : Memory} {addr : BitVec 64} {bs : List (BitVec 8)}
    {p : BitVec 64 → Perm} (h : Obj.HoldsBytes m addr bs p) : m.readBytes addr bs.length = bs := by
  induction bs generalizing addr with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons, Memory.readBytes_succ, List.cons.injEq]
    refine ⟨?_, ih fun i hi => ?_⟩
    · have := (h 0 (Nat.zero_lt_succ _)).1
      simpa using this
    · have hadd : addr + 1#64 + BitVec.ofNat 64 i = addr + BitVec.ofNat 64 (i + 1) := by
        rw [BitVec.add_assoc]; congr 1
        change BitVec.ofNat 64 1 + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1)
        rw [BitVec.ofNat_add_ofNat, Nat.add_comm]
      rw [hadd]
      exact h (i + 1) (Nat.succ_lt_succ hi)

/-- A block that is read-write in `m` and whose contents `m` has is satisfied by `m`. -/
theorem sat_of_isBlock_rw {P : SepProp} {b : BitVec 64} {n : Nat} {Φ : Memory → Prop} {m : Memory}
    (hb : IsBlock P b n Φ) (hrw : m.RW b n) (hΦ : Φ m) :
    m ⊨ P := by
  have hm0 : m ⊨ memRegion b n ∗ emp := by
    rw [sepConj_emp]
    exact ProofLib.satisfies_memRegion m b n hrw
  have hm1 : m ⊨ P ∗ emp :=
    (IsBlock.memRegion b n).update hb (Nat.le_refl _) hm0 (AgreesOutside.rfl' m b n) hΦ
  rwa [sepConj_emp] at hm1

/-! ## C `argv` Table Predicate -/

/-- NUL-terminated byte slice `s ++ [0#8]` at `p`. -/
def cStrAt (p : BitVec 64) (s : List (BitVec 8)) : SepProp := p ↦ₛ (s ++ [0#8])

/-- C `argv` pointer table at `a` terminated by `0#64`, with separate NUL-terminated strings. -/
def argvAt : BitVec 64 → List (List (BitVec 8)) → SepProp
  | a, [] => a ↦₆₄ 0#64
  | a, s :: ss => ∃∗ p, (a ↦₆₄ p) ∗ cStrAt p s ∗ argvAt (a + 8#64) ss

theorem bytesLE8_eq (v : BitVec 64) : Obj.bytesLE 8 v = unpack64 v := rfl

theorem bytesLE8_length (v : BitVec 64) : (Obj.bytesLE 8 v).length = 8 := rfl

private theorem rearr1 {A R C T X : SepProp} (h : R ∗ T ⊢ X) : (A ∗ R) ∗ (C ∗ T) ⊢ A ∗ (C ∗ X) := by
  rw [sepConj_assoc, sepConj_left_comm R C T]
  exact sepConj_mono_right (sepConj_mono_right h)

private theorem entails_any (P : SepProp) : P ⊢ anyHeap :=
  ProofLib.entails_anyHeap P

private theorem rearr2 {A P R S T X : SepProp} (h : P ∗ S ⊢ X) :
    A ∗ (P ∗ (R ∗ (S ∗ T))) ⊢ X ∗ anyHeap := by
  rw [sepConj_left_comm R S T, sepConj_left_comm P S, sepConj_left_comm A S, sepConj_left_comm A P,
    ← sepConj_assoc S P, sepConj_comm S P]
  exact sepConj_mono h (entails_any _)

/-- The packed pointers and strings of `buildInitialStack` form `argvAt`. -/
theorem argvAt_of_packed (base : BitVec 64) (ss : List (List (BitVec 8))) :
    ∀ (a : BitVec 64) (off : Nat),
      (a ↦ₛ (packAddrs base off ss ++ [0#64]).flatMap (Obj.bytesLE 8)) ∗
          ((base + BitVec.ofNat 64 off) ↦ₛ ss.flatMap (· ++ [0#8])) ⊢ argvAt a ss := by
  induction ss with
  | nil =>
    intro a off
    simp only [packAddrs, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      pointsToBytes_nil, sepConj_emp, argvAt, bytesLE8_eq, pointsTo64_eq_pointsToBytes]
    exact Entails.refl _
  | cons s ss ih =>
    intro a off
    have hoff : base + BitVec.ofNat 64 off + BitVec.ofNat 64 (s ++ [0#8]).length =
        base + BitVec.ofNat 64 (off + s.length + 1) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, List.length_append, List.length_singleton,
        Nat.add_assoc]
    rw [packAddrs, List.cons_append, List.flatMap_cons, List.flatMap_cons,
      pointsToBytes_append a (Obj.bytesLE 8 _), bytesLE8_length,
      pointsToBytes_append (base + BitVec.ofNat 64 off) (s ++ [0#8]), hoff]
    simp only [argvAt, cStrAt]
    refine Entails.sepExists_right (base + BitVec.ofNat 64 off) ?_
    rw [bytesLE8_eq, ← pointsTo64_eq_pointsToBytes]
    exact rearr1 (ih (a + 8#64) (off + s.length + 1))

/-- The frame entails `argvAt (sp0 + 8)` and junk. -/
theorem frame_entails (elf : ElfImage) (strs : List (List (BitVec 8)))
    (hfit : 8 * tableWords strs + infoLen strs ≤ cliStackSize) :
    (BitVec.ofNat 64 (sp0 strs) ↦ₛ frameBytes elf strs) ⊢
      argvAt (BitVec.ofNat 64 (sp0 strs) + 8#64) strs ∗ anyHeap := by
  have e1 : BitVec.ofNat 64 (argcBytes strs).length = 8#64 := rfl
  have hp : (ptrBytes strs).length = 8 * (strs.length + 1) := by
    unfold ptrBytes ptrWords
    simp only [flatMap_bytesLE_length, List.length_append, packAddrs_length, List.length_singleton]
  have hr : (restBytes elf strs).length = 8 * (39 + (strs.length + 41) % 2) := by
    unfold restBytes restWords
    simp only [flatMap_bytesLE_length, List.length_append, List.length_cons, List.length_nil,
      List.length_replicate]
  have hh : (headBytes strs).length = 16 + infoPadLen strs + 8 := by
    unfold headBytes
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  have e3 : BitVec.ofNat 64 (sp0 strs) + 8#64 + BitVec.ofNat 64 (ptrBytes strs).length +
      BitVec.ofNat 64 (restBytes elf strs ++ headBytes strs).length =
      argvBase strs + BitVec.ofNat 64 0 := by
    rw [List.length_append, hp, hr, hh]
    unfold argvBase platformAddr
    simp only [BitVec.ofNat_add_ofNat]
    congr 1
    have := top_eq
    have := cliStackSize_eq
    unfold sp0 infoBase tableWords at *
    omega
  unfold frameBytes
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
    pointsToBytes_append _ (strBytes strs), e1, e3]
  exact rearr2 (argvAt_of_packed (argvBase strs) strs _ 0)

/-! ## Separation-Logic Stack Frame -/

/-- The loaded stack holds the frame bytes at `sp0` and the free stack below them. -/
theorem stackMem_sat_frame (elf : ElfImage) (strs : List (List (BitVec 8)))
    (hsegs : ∀ r ∈ elf.segments, r.start.toNat + r.bytes.length ≤ stackBase)
    (hfit : 8 * tableWords strs + infoLen strs ≤ cliStackSize) :
    stackMem elf.segments (BitVec.ofNat 64 (sp0 strs)) (frameBytes elf strs) ⊨
      memRegion (BitVec.ofNat 64 stackBase) (sp0 strs - stackBase) ∗
        (BitVec.ofNat 64 (sp0 strs) ↦ₛ frameBytes elf strs) := by
  obtain ⟨hlen, hsb⟩ := sp0_add_frame elf strs hfit
  have htop := top_eq
  have hsbe := stackBase_eq
  have hsp := toNat_sp0 strs
  have hh := stackMem_holdsBytes elf.segments (BitVec.ofNat 64 (sp0 strs)) (frameBytes elf strs)
    hsegs (by rw [hsp]; exact hsb) (by rw [hsp]; omega)
  have hadd : BitVec.ofNat 64 (sp0 strs) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 (sp0 strs - stackBase) := by
    rw [BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' hsb]
  have hnk : sp0 strs - stackBase + (frameBytes elf strs).length ≤ 2 ^ 64 := by omega
  have hblock := IsBlock.sepConj (IsBlock.memRegion (BitVec.ofNat 64 stackBase) (sp0 strs - stackBase))
    (IsBlock.pointsToBytes (BitVec.ofNat 64 (sp0 strs)) (frameBytes elf strs)) hadd hnk
  have hrw : (stackMem elf.segments (BitVec.ofNat 64 (sp0 strs)) (frameBytes elf strs)).RW
      (BitVec.ofNat 64 stackBase) (sp0 strs - stackBase + (frameBytes elf strs).length) := by
    intro a ha
    rw [Memory.permNoLazy_eq_some_rw_iff]
    unfold InRegion at ha
    rw [BitVec.toNat_sub, toNat_stackBase] at ha
    have hlt := a.isLt
    have ha1 : stackBase ≤ a.toNat := by omega
    have ha2 : a.toNat < top := by omega
    by_cases hlo : a.toNat < sp0 strs
    · have hz := stackMem_zero elf.segments (BitVec.ofNat 64 (sp0 strs)) (frameBytes elf strs)
        hsegs (by rw [hsp]; exact hlen) a ha1 (by rw [hsp]; exact hlo)
      refine ⟨?_, ?_⟩
      · simp only [Memory.perm, hz]; rfl
      · simp only [Memory.isLazyFree, hz]; rfl
    · have hi : a.toNat - sp0 strs < (frameBytes elf strs).length := by omega
      have hae : BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (a.toNat - sp0 strs) = a := by
        rw [BitVec.ofNat_add_ofNat]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        omega
      have := (hh (a.toNat - sp0 strs) hi).2
      rw [hae] at this
      exact this
  exact sat_of_isBlock_rw hblock hrw ⟨trivial, by omega, readBytes_of_holdsBytes hh⟩

theorem stackMem_sat (elf : ElfImage) (strs : List (List (BitVec 8)))
    (hsegs : ∀ r ∈ elf.segments, r.start.toNat + r.bytes.length ≤ stackBase)
    (hfit : 8 * tableWords strs + infoLen strs ≤ cliStackSize) :
    stackMem elf.segments (BitVec.ofNat 64 (sp0 strs)) (frameBytes elf strs) ⊨
      argvAt (BitVec.ofNat 64 (sp0 strs) + 8#64) strs ∗
        memRegion (BitVec.ofNat 64 stackBase) (sp0 strs - stackBase) ∗ anyHeap := by
  refine Arm64.Satisfies.mono ?_ (stackMem_sat_frame elf strs hsegs hfit)
  refine Arm64.Entails.trans (sepConj_mono_right (frame_entails elf strs hfit)) ?_
  rw [sepConj_left_comm]
  exact Entails.refl _

/-! ## Auxiliary Vector Words -/

theorem auxWords_length (elf : ElfImage) (strs : List (List (BitVec 8))) :
    (auxWords elf strs).length = 39 := rfl

theorem restWords_eq (elf : ElfImage) (strs : List (List (BitVec 8))) :
    restWords elf strs = auxWords elf strs ++ List.replicate ((strs.length + 41) % 2) 0#64 := rfl

private theorem rearr3 {A P W D S T X : SepProp} (h : P ∗ S ⊢ X) :
    A ∗ (P ∗ ((W ∗ D) ∗ (S ∗ T))) ⊢ A ∗ (X ∗ (W ∗ anyHeap)) := by
  have e : A ∗ (P ∗ ((W ∗ D) ∗ (S ∗ T))) = A ∗ ((P ∗ S) ∗ (W ∗ (D ∗ T))) := by ac_rfl
  rw [e]
  exact sepConj_mono_right (sepConj_mono h (sepConj_mono_right (entails_any _)))

/-- The frame entails argc at `sp0`, `argvAt (sp0 + 8)`, the envp `NULL` and the auxv
    (`auxWords`) after the argv table, and junk. -/
theorem frame_entails_aux (elf : ElfImage) (strs : List (List (BitVec 8)))
    (hfit : 8 * tableWords strs + infoLen strs ≤ cliStackSize) :
    (BitVec.ofNat 64 (sp0 strs) ↦ₛ frameBytes elf strs) ⊢
      (BitVec.ofNat 64 (sp0 strs) ↦₆₄ BitVec.ofNat 64 strs.length) ∗
        (argvAt (BitVec.ofNat 64 (sp0 strs) + 8#64) strs ∗
          ((BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (8 * (strs.length + 2))) ↦₆₄*
            auxWords elf strs) ∗ anyHeap) := by
  have e1 : BitVec.ofNat 64 (argcBytes strs).length = 8#64 := rfl
  have hp : (ptrBytes strs).length = 8 * (strs.length + 1) := by
    unfold ptrBytes ptrWords
    simp only [flatMap_bytesLE_length, List.length_append, packAddrs_length, List.length_singleton]
  have hu : (unpackL (auxWords elf strs)).length = 8 * 39 := by
    rw [unpackL_length, auxWords_length]
  have hr : (restBytes elf strs).length = 8 * (39 + (strs.length + 41) % 2) := by
    unfold restBytes restWords
    simp only [flatMap_bytesLE_length, List.length_append, List.length_cons, List.length_nil,
      List.length_replicate]
  have hh : (headBytes strs).length = 16 + infoPadLen strs + 8 := by
    unfold headBytes
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  have e2 : BitVec.ofNat 64 (sp0 strs) + 8#64 + BitVec.ofNat 64 (ptrBytes strs).length =
      BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (8 * (strs.length + 2)) := by
    rw [hp, BitVec.add_assoc]
    congr 1
    simp only [BitVec.ofNat_add_ofNat]
    congr 1
    omega
  have e3 : BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (8 * (strs.length + 2)) +
      BitVec.ofNat 64 (restBytes elf strs ++ headBytes strs).length =
      argvBase strs + BitVec.ofNat 64 0 := by
    rw [List.length_append, hr, hh]
    unfold argvBase platformAddr
    simp only [BitVec.ofNat_add_ofNat]
    congr 1
    have := top_eq
    have := cliStackSize_eq
    unfold sp0 infoBase tableWords at *
    omega
  have hrest : restBytes elf strs ++ headBytes strs =
      unpackL (auxWords elf strs) ++
        ((List.replicate ((strs.length + 41) % 2) (0#64)).flatMap (Obj.bytesLE 8) ++
          headBytes strs) := by
    unfold restBytes unpackL
    rw [restWords_eq, List.flatMap_append, List.append_assoc]
    rfl
  unfold frameBytes
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
    pointsToBytes_append _ (strBytes strs), e1,
    e2, e3, hrest, pointsToBytes_append, hu, ← pointsToWords64_eq_pointsToBytes,
    show argcBytes strs = unpack64 (BitVec.ofNat 64 strs.length) from rfl,
    ← pointsTo64_eq_pointsToBytes]
  exact rearr3 (argvAt_of_packed (argvBase strs) strs _ 0)

/-- Loaded stack separation-logic layout with `argc` at `sp0`, `argvAt (sp0 + 8)`, `auxWords`, and free stack `[stackBase, sp0)`. -/
theorem stackMem_sat_aux (elf : ElfImage) (strs : List (List (BitVec 8)))
    (hsegs : ∀ r ∈ elf.segments, r.start.toNat + r.bytes.length ≤ stackBase)
    (hfit : 8 * tableWords strs + infoLen strs ≤ cliStackSize) :
    stackMem elf.segments (BitVec.ofNat 64 (sp0 strs)) (frameBytes elf strs) ⊨
      (BitVec.ofNat 64 (sp0 strs) ↦₆₄ BitVec.ofNat 64 strs.length) ∗
        argvAt (BitVec.ofNat 64 (sp0 strs) + 8#64) strs ∗
        ((BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (8 * (strs.length + 2))) ↦₆₄*
          auxWords elf strs) ∗
        memRegion (BitVec.ofNat 64 stackBase) (sp0 strs - stackBase) ∗ anyHeap := by
  refine Arm64.Satisfies.mono ?_ (stackMem_sat_frame elf strs hsegs hfit)
  refine Arm64.Entails.trans (sepConj_mono_right (frame_entails_aux elf strs hfit)) ?_
  have e : ∀ M A X W : SepProp, M ∗ (A ∗ (X ∗ W ∗ anyHeap)) = A ∗ X ∗ W ∗ M ∗ anyHeap := by
    intro M A X W; ac_rfl
  rw [e]
  exact Entails.refl _

/-! ## CLI Argument Strings -/

/-- CLI argument byte slices with `argv[0] = "signal-session"`. -/
def cliStrs (argv : List String) : List (List (BitVec 8)) :=
  ("libsignal-cli" :: argv).map bytesOfString

theorem bytesOfString_nul (a : String) (ha : ∀ c ∈ a.toList, 0 < c.toNat ∧ c.toNat < 128) :
    ∀ b ∈ bytesOfString a, b ≠ 0#8 := by
  intro b hb
  unfold bytesOfString at hb
  rw [List.mem_map] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  have := ha c hc
  intro h
  have h2 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h2
  omega

theorem cliStrs_nul (argv : List String)
    (hargs : ∀ a ∈ argv, ∀ c ∈ a.toList, 0 < c.toNat ∧ c.toNat < 128) :
    ∀ s ∈ cliStrs argv, ∀ b ∈ s, b ≠ 0#8 := by
  intro s hs
  unfold cliStrs at hs
  rw [List.mem_map] at hs
  obtain ⟨a, ha, rfl⟩ := hs
  rcases List.mem_cons.mp ha with rfl | ha
  · exact bytesOfString_nul _ (by decide)
  · exact bytesOfString_nul a (hargs a ha)

theorem sum_add_eight (argv : List String) :
    (argv.map fun a => a.length + 1 + 8).sum = (argv.map fun a => a.length + 1).sum + 8 * argv.length := by
  induction argv with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega

theorem bytesOfString_length (a : String) : (bytesOfString a).length = a.length := by
  rw [bytesOfString, List.length_map]; rfl

theorem strLen_cli (argv : List String) :
    strLen (cliStrs argv) = 14 + (argv.map fun a => a.length + 1).sum := by
  have h13 : "libsignal-cli".length = 13 := by decide
  have hc : ((fun s : List (BitVec 8) => s.length + 1) ∘ bytesOfString) = fun a => a.length + 1 := by
    funext a; simp only [Function.comp_apply, bytesOfString_length]
  unfold strLen cliStrs
  simp only [List.map_cons, List.sum_cons, List.map_map, bytesOfString_length, h13, hc]

theorem cliStrs_length (argv : List String) : (cliStrs argv).length = argv.length + 1 := by
  simp [cliStrs]

theorem cli_bounds (argv : List String) (hfits : (argv.map fun a => a.length + 1 + 8).sum ≤ 16384) :
    8 * tableWords (cliStrs argv) + infoLen (cliStrs argv) ≤ cliStackSize ∧
      sp0 (cliStrs argv) % 16 = 0 ∧ stackBase + 8371824 ≤ sp0 (cliStrs argv) := by
  rw [sum_add_eight] at hfits
  have hS := strLen_cli argv
  have hk := cliStrs_length argv
  have htop := top_eq
  have hsb := stackBase_eq
  have hss := cliStackSize_eq
  unfold sp0 infoBase tableWords infoLen alignUp16 upperRawLen
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem sp0_sub (strs : List (List (BitVec 8))) (h : stackBase ≤ sp0 strs) :
    BitVec.ofNat 64 (sp0 strs) - BitVec.ofNat 64 (sp0 strs - stackBase) =
      BitVec.ofNat 64 stackBase := by
  apply BitVec.eq_of_toNat_eq
  have := sp0_le_top strs
  have := top_eq
  rw [BitVec.toNat_sub, toNat_sp0, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## CLI Stack Layout Theorems -/

/-- Loading the CLI (`argv[0] = "signal-session"`) on NUL-free ASCII arguments satisfying
`ArgvFitsInitialStack` succeeds with `elf.rawState`, 16-byte-aligned `sp0`, at least
8,371,824 zero read-write stack bytes in `[stackBase, sp0)`, `frameBytes` in `[sp0, top)`,
and unmapped memory outside the ELF segments and `[stackBase, top)`. -/
theorem loadState_cli_layout (elf : ElfImage) (argv : List String) (stdin : List (BitVec 8))
    (files : List (String × List (BitVec 8))) (dirs : List String)
    (hwf : elf.WellFormed = true)
    (hbrk : elf.brkStart.toNat ≤ defaultStackTop.toNat - cliStackSize)
    (hargs : ∀ a ∈ argv, ∀ c ∈ a.toList, 0 < c.toNat ∧ c.toNat < 128)
    (hfits : (argv.map fun a => a.length + 1 + 8).sum ≤ 16384)
    (hdirs : ∀ d ∈ dirs, Arm64.hasLeadingSlash d = false ∧ Arm64.hasDotDot d = false)
    (hfiles : ∀ f ∈ files,
      (Arm64.hasLeadingSlash f.1 = false ∧ Arm64.hasDotDot f.1 = false) ∧
        f.2.length ≤ Arm64.MAX_LFS_FILESIZE) :
    elf.loadState (processInputs ("libsignal-cli" :: argv) stdin files dirs) =
        .ok (elf.rawState (processInputs ("libsignal-cli" :: argv) stdin files dirs)) ∧
      (elf.rawState (processInputs ("libsignal-cli" :: argv) stdin files dirs)).sp =
        BitVec.ofNat 64 (sp0 (cliStrs argv)) ∧
      sp0 (cliStrs argv) % 16 = 0 ∧
      stackBase + 8371824 ≤ sp0 (cliStrs argv) ∧
      sp0 (cliStrs argv) + (frameBytes elf (cliStrs argv)).length = top ∧
      Obj.HoldsBytes (elf.rawState (processInputs ("libsignal-cli" :: argv) stdin files dirs)).mem
        (BitVec.ofNat 64 (sp0 (cliStrs argv))) (frameBytes elf (cliStrs argv)) (fun _ => Perm.rw) ∧
      (∀ a : BitVec 64, stackBase ≤ a.toNat → a.toNat < sp0 (cliStrs argv) →
        (elf.rawState (processInputs ("libsignal-cli" :: argv) stdin files dirs)).mem.cells a =
          some (some Perm.rw, 0#8)) ∧
      (∀ a : BitVec 64, (∀ r ∈ elf.segments, ¬ (a - r.start).toNat < r.bytes.length) →
        (a.toNat < stackBase ∨ top ≤ a.toNat) →
        (elf.rawState (processInputs ("libsignal-cli" :: argv) stdin files dirs)).mem.cells a =
          none) := by
  have hnul := cliStrs_nul argv hargs
  obtain ⟨hfit, hal, hlo⟩ := cli_bounds argv hfits
  have hsegs := segs_below elf hwf hbrk
  obtain ⟨hload, hsp, hmem⟩ :=
    load_layout elf (processInputs ("libsignal-cli" :: argv) stdin files dirs) (cliStrs argv)
      rfl rfl rfl rfl rfl rfl hnul hwf hbrk hfit hdirs hfiles
  obtain ⟨hlen, hsb⟩ := sp0_add_frame elf (cliStrs argv) hfit
  have hspn := toNat_sp0 (cliStrs argv)
  have htop := top_eq
  refine ⟨hload, hsp, hal, hlo, hlen, ?_, ?_, ?_⟩
  · rw [hmem]
    exact stackMem_holdsBytes _ _ _ hsegs (by rw [hspn]; exact hsb) (by rw [hspn]; omega)
  · intro a ha1 ha2
    rw [hmem]
    exact stackMem_zero _ _ _ hsegs (by rw [hspn]; exact hlen) a ha1 (by rw [hspn]; exact ha2)
  · intro a hseg ha
    rw [hmem]
    exact stackMem_outside _ _ _ (by rw [hspn]; exact hsb) (by rw [hspn]; exact hlen) a hseg ha

/-- Loaded CLI memory satisfies `argvAt (sp0 + 8) (cliStrs argv) ∗ memRegion stackBase (sp0 - stackBase) ∗ anyHeap`. -/
theorem satisfies_initStack (elf : ElfImage) (argv : List String) (stdin : List (BitVec 8))
    (files : List (String × List (BitVec 8))) (dirs : List String)
    (hwf : elf.WellFormed = true)
    (hbrk : elf.brkStart.toNat ≤ defaultStackTop.toNat - cliStackSize)
    (hargs : ∀ a ∈ argv, ∀ c ∈ a.toList, 0 < c.toNat ∧ c.toNat < 128)
    (hfits : (argv.map fun a => a.length + 1 + 8).sum ≤ 16384) :
    (elf.rawState (processInputs ("libsignal-cli" :: argv) stdin files dirs)).mem ⊨
      argvAt (BitVec.ofNat 64 (sp0 (cliStrs argv)) + 8#64) (cliStrs argv) ∗
        memRegion (BitVec.ofNat 64 stackBase) (sp0 (cliStrs argv) - stackBase) ∗ anyHeap := by
  have hnul := cliStrs_nul argv hargs
  obtain ⟨hfit, -, -⟩ := cli_bounds argv hfits
  obtain ⟨-, hmem⟩ :=
    rawState_layout elf (processInputs ("libsignal-cli" :: argv) stdin files dirs) (cliStrs argv)
      rfl rfl rfl rfl rfl rfl hnul hbrk hfit
  rw [hmem]
  exact stackMem_sat elf (cliStrs argv) (segs_below elf hwf hbrk) hfit

/-- Under `ArgvFitsInitialStack`, there are at most 1820 arguments (each takes at least 9 bytes). -/
theorem argv_length_le (argv : List String)
    (hfits : (argv.map fun a => a.length + 1 + 8).sum ≤ 16384) : argv.length ≤ 1820 := by
  have h : ∀ l : List String, 9 * l.length ≤ (l.map fun a => a.length + 1 + 8).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a as ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  have := h argv
  omega

/-- Loaded CLI memory holds `argc` at `sp0`, `argvAt (sp0 + 8)`, `auxWords` at
`sp0 + 8 * (argc + 2)`, and the free stack `[stackBase, sp0)`. -/
theorem satisfies_initStack_aux (elf : ElfImage) (argv : List String) (stdin : List (BitVec 8))
    (files : List (String × List (BitVec 8))) (dirs : List String)
    (hwf : elf.WellFormed = true)
    (hbrk : elf.brkStart.toNat ≤ defaultStackTop.toNat - cliStackSize)
    (hargs : ∀ a ∈ argv, ∀ c ∈ a.toList, 0 < c.toNat ∧ c.toNat < 128)
    (hfits : (argv.map fun a => a.length + 1 + 8).sum ≤ 16384) :
    (elf.rawState (processInputs ("libsignal-cli" :: argv) stdin files dirs)).mem ⊨
      (BitVec.ofNat 64 (sp0 (cliStrs argv)) ↦₆₄ BitVec.ofNat 64 (argv.length + 1)) ∗
        argvAt (BitVec.ofNat 64 (sp0 (cliStrs argv)) + 8#64) (cliStrs argv) ∗
        ((BitVec.ofNat 64 (sp0 (cliStrs argv)) + BitVec.ofNat 64 (8 * (argv.length + 3))) ↦₆₄*
          auxWords elf (cliStrs argv)) ∗
        memRegion (BitVec.ofNat 64 stackBase) (sp0 (cliStrs argv) - stackBase) ∗ anyHeap := by
  have hnul := cliStrs_nul argv hargs
  obtain ⟨hfit, -, -⟩ := cli_bounds argv hfits
  obtain ⟨-, hmem⟩ :=
    rawState_layout elf (processInputs ("libsignal-cli" :: argv) stdin files dirs) (cliStrs argv)
      rfl rfl rfl rfl rfl rfl hnul hbrk hfit
  have h := stackMem_sat_aux elf (cliStrs argv) (segs_below elf hwf hbrk) hfit
  have hk : 8 * (argv.length + 1 + 2) = 8 * (argv.length + 3) := rfl
  rw [cliStrs_length, hk] at h
  rw [hmem]
  exact h

end CryptoVerification.SignalSession.InitStack
