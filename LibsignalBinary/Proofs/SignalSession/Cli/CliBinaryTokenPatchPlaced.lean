/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliTokenPatchPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryTokenPatch
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable Initial Token Cells and `patchElfTokensPlaced` Transport (`DEV-CLI10`)

Relocatable `[LibsignalPlacement]` counterparts of `CliBinaryTokenPatch` for `cliTokenPatchPlaced`,
`lsρ LibsignalSpqrV1.tokenStorageName`, and `lsρ LibsignalSpqrV1.tokenName + 8#64`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession.MuslElf CryptoVerification.SignalSession.InitStack

/-- `PT_LOAD` `.data` slice bundle witnessing SPQR's initial unprobed CPU-feature cells under
`[LibsignalPlacement]` (`STORAGE.0 = 0xff` at `lsρ tokenStorageName`, `TOKEN` `Once` state `= 3` at
`lsρ tokenName + 8#64`). -/
structure CliElfTokenCellsPlaced [LibsignalPlacement] (elf : ElfImage) : Prop where
  storage : SegSlice elf (lsρ CryptoVerification.LibsignalSpqrV1.tokenStorageName)
    [0xff#8] Perm.rw
  once : SegSlice elf (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64)
    [3#8, 0#8, 0#8, 0#8] Perm.rw

theorem tokenCellsInitial_of_dataSeg_placed [LibsignalPlacement] {elf : ElfImage}
    (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCellsPlaced elf)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    s0.mem.read8 (lsρ CryptoVerification.LibsignalSpqrV1.tokenStorageName) = 0xff#8 ∧
    s0.mem.read32 (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64) = 3#32 := by
  have hs := (htok.storage.holdsBytes hE.1 hE.2 hload) 0 (by decide)
  have ho0 := (htok.once.holdsBytes hE.1 hE.2 hload) 0 (by decide)
  have ho1 := (htok.once.holdsBytes hE.1 hE.2 hload) 1 (by decide)
  have ho2 := (htok.once.holdsBytes hE.1 hE.2 hload) 2 (by decide)
  have ho3 := (htok.once.holdsBytes hE.1 hE.2 hload) 3 (by decide)
  have h0 : [0xff#8][0] = 0xff#8 := rfl
  refine ⟨by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, h0] using hs.1, ?_⟩
  unfold Memory.read32; dsimp only
  have e0 : s0.mem.read8 (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 0#64) = 3#8 := ho0.1
  have e1 : s0.mem.read8 (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 1#64) = 0#8 := ho1.1
  have e2 : s0.mem.read8 (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 2#64) = 0#8 := ho2.1
  have e3 : s0.mem.read8 (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 3#64) = 0#8 := ho3.1
  rw [e0, e1, e2, e3]; rfl

theorem tokenCellsInitial_cliProcessInputs_placed [LibsignalPlacement] {elf : ElfImage}
    (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCellsPlaced elf) :
    ∀ i s0, elf.loadState (cliProcessInputs i) = .ok s0 →
      s0.mem.read8 (lsρ CryptoVerification.LibsignalSpqrV1.tokenStorageName) = 0xff#8 ∧
      s0.mem.read32 (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64) = 3#32 :=
  fun _ _ hload => tokenCellsInitial_of_dataSeg_placed hE htok hload

/-- Ghost `ElfImage` with spqr's 5 CPU-probe `.data` bytes pre-set to `0` (`DEV-CLI10`) under
`[LibsignalPlacement]`, so its `loadState` equals `(elf.loadState ·).map cliTokenPatchPlaced`. -/
def patchElfTokensPlaced [LibsignalPlacement] (elf : ElfImage) : ElfImage :=
  let sAddr := lsρ CryptoVerification.LibsignalSpqrV1.tokenStorageName
  let oAddr := lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64
  patchElfByte (oAddr + 3#64) 0#8 (patchElfByte (oAddr + 2#64) 0#8
    (patchElfByte (oAddr + 1#64) 0#8 (patchElfByte oAddr 0#8 (patchElfByte sAddr 0#8 elf))))

theorem elfStaticOk_patchElfTokensPlaced [LibsignalPlacement] {elf : ElfImage}
    (hE : Cli.ElfStaticOk elf) : Cli.ElfStaticOk (patchElfTokensPlaced elf) :=
  elfStaticOk_patchElfByte (elfStaticOk_patchElfByte (elfStaticOk_patchElfByte
    (elfStaticOk_patchElfByte (elfStaticOk_patchElfByte hE))))

private theorem bv_add_1_1_placed (x : BitVec 64) : x + 1#64 + 1#64 = x + 2#64 := by
  rw [BitVec.add_assoc]; rfl

private theorem bv_add_2_1_placed (x : BitVec 64) : x + 2#64 + 1#64 = x + 3#64 := by
  rw [BitVec.add_assoc]; rfl

theorem loadState_patchElfTokensPlaced [LibsignalPlacement] {elf : ElfImage}
    (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCellsPlaced elf) (inputs : ProcessInputs) :
    (patchElfTokensPlaced elf).loadState inputs = (elf.loadState inputs).map cliTokenPatchPlaced := by
  have hs : AddrInElf elf (lsρ CryptoVerification.LibsignalSpqrV1.tokenStorageName) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      segSlice_addrInElf htok.storage hE (j := 0) (by decide)
  have ho0 : AddrInElf elf (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      segSlice_addrInElf htok.once hE (j := 0) (by decide)
  have ho1 : AddrInElf elf (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 1#64) :=
    segSlice_addrInElf htok.once hE (j := 1) (by decide)
  have ho2 : AddrInElf elf (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 2#64) :=
    segSlice_addrInElf htok.once hE (j := 2) (by decide)
  have ho3 : AddrInElf elf (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 3#64) :=
    segSlice_addrInElf htok.once hE (j := 3) (by decide)
  unfold patchElfTokensPlaced
  dsimp only
  rw [loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho3),
      loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho2),
      loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho1),
      loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho0),
      loadState_patchElfByte _ hs]
  cases elf.loadState inputs with
  | error _ => rfl
  | ok s0 =>
    simp only [Except.map, cliTokenPatchPlaced, Placed.cliTokenPatchPlaced, State.setMem,
      Memory.writeBytes, bv_add_1_1_placed, bv_add_2_1_placed]

private theorem keepsFrozen_write8_of_perm_rw_placed {m : Memory} {addr : BitVec 64} (val : BitVec 8)
    (hp : m.perm addr = some Perm.rw) : m.KeepsFrozen (m.write8 addr val) := by
  intro a ha
  have hne : a ≠ addr := by
    rintro rfl
    unfold Memory.Frozen at ha
    simp only [hp, Option.frozen, Perm.frozen] at ha
    exact Bool.noConfusion ha
  simp [Memory.write8, Memory.read8, Memory.perm, Memory.isLazyFree, Memory.isAnon, hne]

theorem keepsFrozen_cliTokenPatchPlaced [LibsignalPlacement] {elf : ElfImage}
    (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCellsPlaced elf)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    s0.mem.KeepsFrozen (cliTokenPatchPlaced s0).mem := by
  have ps : s0.mem.perm (lsρ CryptoVerification.LibsignalSpqrV1.tokenStorageName) = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.storage.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  have p0 : s0.mem.perm (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64) = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.once.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  have p1 : s0.mem.perm (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 1#64) = some .rw :=
    ((htok.once.holdsBytes hE.1 hE.2 hload) 1 (by decide)).2.1
  have p2 : s0.mem.perm (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 2#64) = some .rw :=
    ((htok.once.holdsBytes hE.1 hE.2 hload) 2 (by decide)).2.1
  have p3 : s0.mem.perm (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 3#64) = some .rw :=
    ((htok.once.holdsBytes hE.1 hE.2 hload) 3 (by decide)).2.1
  have hmem : (cliTokenPatchPlaced s0).mem =
      (((((s0.mem.write8 (lsρ CryptoVerification.LibsignalSpqrV1.tokenStorageName) 0#8).write8
        (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64) 0#8).write8
        (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 1#64) 0#8).write8
        (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 2#64) 0#8).write8
        (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 3#64) 0#8) := by
    simp only [cliTokenPatchPlaced, Placed.cliTokenPatchPlaced, State.setMem, Memory.writeBytes,
      bv_add_1_1_placed, bv_add_2_1_placed]
  rw [hmem]
  exact ((((keepsFrozen_write8_of_perm_rw_placed 0#8 ps).trans
    (keepsFrozen_write8_of_perm_rw_placed 0#8 (by simpa only [Memory.perm_write8_apply] using p0))).trans
    (keepsFrozen_write8_of_perm_rw_placed 0#8 (by simpa only [Memory.perm_write8_apply] using p1))).trans
    (keepsFrozen_write8_of_perm_rw_placed 0#8 (by simpa only [Memory.perm_write8_apply] using p2))).trans
    (keepsFrozen_write8_of_perm_rw_placed 0#8 (by simpa only [Memory.perm_write8_apply] using p3))

theorem segSlice_patchElfTokensPlaced_of_ne [LibsignalPlacement] {elf : ElfImage} {a : BitVec 64}
    {bs : List (BitVec 8)} {p : Perm} (hs : SegSlice elf a bs p) (hE : Cli.ElfStaticOk elf)
    (hs_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ lsρ CryptoVerification.LibsignalSpqrV1.tokenStorageName)
    (ho0_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64)
    (ho1_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 1#64)
    (ho2_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 2#64)
    (ho3_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 3#64) :
    SegSlice (patchElfTokensPlaced elf) a bs p := by
  have e1 := elfStaticOk_patchElfByte (addr := lsρ CryptoVerification.LibsignalSpqrV1.tokenStorageName) (val := 0#8) hE
  have e2 := elfStaticOk_patchElfByte (addr := lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64) (val := 0#8) e1
  have e3 := elfStaticOk_patchElfByte (addr := lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 1#64) (val := 0#8) e2
  have e4 := elfStaticOk_patchElfByte (addr := lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 2#64) (val := 0#8) e3
  exact segSlice_patchElfByte_of_ne
    (segSlice_patchElfByte_of_ne
      (segSlice_patchElfByte_of_ne
        (segSlice_patchElfByte_of_ne
          (segSlice_patchElfByte_of_ne hs hE hs_ne)
          e1 ho0_ne)
        e2 ho1_ne)
      e3 ho2_ne)
    e4 ho3_ne

theorem segSlice_patchElfTokensPlaced_of_ne_rw [LibsignalPlacement] {elf : ElfImage} {a : BitVec 64}
    {bs : List (BitVec 8)} {p : Perm} (hs : SegSlice elf a bs p) (hp_ne : p.rwx ≠ Perm.rw)
    (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCellsPlaced elf) :
    SegSlice (patchElfTokensPlaced elf) a bs p := by
  have hload := (loadState_cli_layout elf [] [] [] [] hE.1 hE.2
    (by simp) (by simp) (by simp) (by simp)).1
  have hperm_ne : ∀ addr,
      (elf.rawState (processInputs ["libsignal-cli"] [] [] [])).mem.perm addr = some .rw →
      ∀ j (_ : j < bs.length), a + BitVec.ofNat 64 j ≠ addr := by
    intro addr hrw j hj heq
    have hpj := ((hs.holdsBytes hE.1 hE.2 hload) j hj).2.1
    rw [heq, hrw] at hpj
    exact hp_ne (Option.some.inj hpj).symm
  have ps : (elf.rawState (processInputs ["libsignal-cli"] [] [] [])).mem.perm
      (lsρ CryptoVerification.LibsignalSpqrV1.tokenStorageName) = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.storage.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  have p0 : (elf.rawState (processInputs ["libsignal-cli"] [] [] [])).mem.perm
      (lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64) = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.once.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  exact segSlice_patchElfTokensPlaced_of_ne hs hE (hperm_ne _ ps) (hperm_ne _ p0)
    (hperm_ne _ ((htok.once.holdsBytes hE.1 hE.2 hload) 1 (by decide)).2.1)
    (hperm_ne _ ((htok.once.holdsBytes hE.1 hE.2 hload) 2 (by decide)).2.1)
    (hperm_ne _ ((htok.once.holdsBytes hE.1 hE.2 hload) 3 (by decide)).2.1)

end CryptoVerification.SignalSession
