/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
import ProofLib.SepLogic.WP.StateNorm

@[expose] public section

set_option autoImplicit false

/-!
# `bcmp` Hook Contract at `cliExterns` and `CliExternsOk`

Proves `HookSat (cliExterns W) cliBcmpName cliBcmpSpec` (`cli_hookSat_bcmp`) and its
`CliExternsOk`-backed counterparts (`hookSat_bcmp_ext`, `hookSat_bcmp_cliExternsWith`) by showing
that `cliBcmpHook W.bcmp` reads both slices (`ChainProofs.bytesAt`), preserves memory, and returns a
word whose low 32 bits vanish iff the byte slices are equal (`W.bcmp_ok`).
-/

namespace CryptoVerification.SignalSession.Cli.RunGlue

open Arm64 ProofLib CryptoVerification.SignalSession

/-- The `bcmp` row of `cliHookTable` (index 8 of its own rows). -/
theorem bcmp_row (W : CliHooks) : (cliBcmpName, cliBcmpHook W.bcmp) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 8) rfl)

/-- `cliExterns W` maps `bcmp` to `cliBcmpHook W.bcmp`. -/
theorem cliExterns_bcmp (W : CliHooks) : cliExterns W cliBcmpName = some (cliBcmpHook W.bcmp) :=
  cliExterns_row W (bcmp_row W)

/-- Either permission of `ChainProofs.bytesAt ro p bs` fixes the bytes read at `p`. -/
theorem bytesAt_readBytes {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)} {m : Memory}
    {R : SepProp} (h : m ⊨ SpqrV1.ChainProofs.bytesAt ro p bs ∗ R) (hlen : bs.length ≤ 2 ^ 64) :
    m.readBytes p bs.length = bs := by
  cases ro
  · rw [SpqrV1.ChainProofs.bytesAt_false] at h
    exact ((IsBlock.pointsToBytes p bs).read h).2
  · rw [SpqrV1.ChainProofs.bytesAt_true] at h
    exact (IsBlockRO.pointsToBytesRO p bs hlen).read h

/-- `cliBcmpHook W.bcmp` meets `cliBcmpSpec` (for any `ro` on either side): memory is unchanged,
`x0 := W.bcmp bsA bsB`, and `W.bcmp_ok` gives `w0 = 0 ↔ bsA = bsB`. -/
theorem cliBcmpHook_ok (W : CliHooks) : HookOk (cliBcmpHook W.bcmp) cliBcmpSpec := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [cliBcmpSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hlenA : x.bsA.length ≤ 2 ^ 64 := by
    have := (s0.readReg64 .x2).isLt
    omega
  have hreadA := bytesAt_readBytes hmem hlenA
  have hmemB : s0.mem ⊨ SpqrV1.ChainProofs.bytesAt x.bRo x.b x.bsB ∗
      (SpqrV1.ChainProofs.bytesAt x.aRo x.a x.bsA ∗
        (stackAt s0.sp LibsignalTripleRatchet.extHookStack ∗ R)) := by
    rwa [← sepConj_assoc, sepConj_comm (SpqrV1.ChainProofs.bytesAt x.aRo x.a x.bsA),
      sepConj_assoc] at hmem
  have hreadB := bytesAt_readBytes hmemB (by omega)
  rw [hlen] at hreadB
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [cliBcmpSpec, cliBcmpHook, retHook]
  rw [hx0, hx1, hx2, hreadA, hreadB]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨W.bcmp_ok x.bsA x.bsB hlen.symm, rfl⟩, hmem⟩

/-- `HookSat (cliExterns W) cliBcmpName cliBcmpSpec`. -/
theorem cli_hookSat_bcmp (W : CliHooks) : HookSat (cliExterns W) cliBcmpName cliBcmpSpec :=
  ⟨cliBcmpHook W.bcmp, cliExterns_bcmp W, cliBcmpHook_ok W⟩

/-! ## Contract-backed `bcmp` (`CliExternsOk`) -/

/-- Any non-panic symbol resolves in `cliExternsWith ext` to its entry in `ext`. -/
theorem cliExternsWith_of_not_panic (ext : String → Option (State → State)) {n : String}
    (hn : E2E.isImagePanicSymbol n = false) : cliExternsWith ext n = ext n := by
  simp [cliExternsWith, hn]

/-- Lift `HookSat ext n spec` to `cliExternsWith ext` when `n` is not a panic symbol. -/
theorem hookSat_cliExternsWith {α : Type} {ext : String → Option (State → State)} {n : String}
    {spec : Spec α} (hn : E2E.isImagePanicSymbol n = false) (h : HookSat ext n spec) :
    HookSat (cliExternsWith ext) n spec := by
  obtain ⟨f, hf, hok⟩ := h
  exact ⟨f, (cliExternsWith_of_not_panic ext hn).trans hf, hok⟩

/-- `HookOk f CliExt.bcmpSpec` gives `HookOk f cliBcmpSpec` (repackaging the ghost struct). -/
theorem hookOk_cliBcmpSpec_of_bcmpSpec {f : State → State} (h : HookOk f CliExt.bcmpSpec) :
    HookOk f cliBcmpSpec :=
  fun x R s0 hrun hpre hsp =>
    h ⟨x.a, x.aRo, x.bsA, x.b, x.bRo, x.bsB⟩ R s0 hrun hpre hsp

/-- `HookSat ext "bcmp" CliExt.bcmpSpec` gives `HookSat ext cliBcmpName cliBcmpSpec`. -/
theorem hookSat_bcmp_of_bcmpSpec {ext : String → Option (State → State)}
    (h : HookSat ext "bcmp" CliExt.bcmpSpec) :
    HookSat ext cliBcmpName cliBcmpSpec := by
  obtain ⟨f, hf, hok⟩ := h
  exact ⟨f, hf, hookOk_cliBcmpSpec_of_bcmpSpec hok⟩

/-- `HookSat ext cliBcmpName cliBcmpSpec` from `hOk.bcmp`. -/
theorem hookSat_bcmp_ext {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat ext cliBcmpName cliBcmpSpec :=
  hookSat_bcmp_of_bcmpSpec hOk.bcmp

/-- `HookSat (cliExternsWith ext) cliBcmpName cliBcmpSpec` from `hOk.bcmp`. -/
theorem hookSat_bcmp_cliExternsWith {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) cliBcmpName cliBcmpSpec :=
  hookSat_cliExternsWith
    (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, cliBcmpName])
    (hookSat_bcmp_ext hOk)

theorem hookSat_bcmp_of_externsOk {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) cliBcmpName cliBcmpSpec :=
  hookSat_bcmp_cliExternsWith hOk

end CryptoVerification.SignalSession.Cli.RunGlue
