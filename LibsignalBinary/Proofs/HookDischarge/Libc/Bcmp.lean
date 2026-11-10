/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Proofs.MemcmpProof
import ProofLib.SepLogic.LoopTactics
meta import ProofLib.SepLogic.LoopTactics
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import

/-!
# Byte-Exact `bcmp` / `memcmp` Hook Discharge (`LibsignalBinary.Proofs.HookDischarge.Libc.Bcmp`)

Byte-exact discharge of all `signal-session` CLI and E2E `bcmp` call-site contracts against
`VerifiedLibraries.Musl.bcmpWords` (`1` word `[0x17fffff6#32]`, patched tail-call `b memcmp` via
`bcmpCalls = [(0, "memcmp")]`) and `VerifiedLibraries.Musl.memcmpLibcaWords` (`13` words = `52` B,
verified word-for-word identical to `rustc 1.98.1`'s
`aarch64-unknown-linux-musl/lib/self-contained/libc.a` `bcmp.lo` and `memcmp.lo`). On
`stockhooks/train`'s snapshot ELF (`inputs.lock:64`) `bcmp`/`memcmp` are still in `native_only`;
these proved `self-contained/libc.a` words enter the shipped binary on the `stock-lld` link at the
second cutover.

## Consumer Specs Discharged & Spec-Postcondition Comparison
1. **Consumer `bcmp` specs on `stockhooks/train` today (proved with zero extra spatial, alignment,
   or trailing-pad premises on the consumer `Spec`s, region-locally on any hook-free sub-program
   `P_sub` holding the `bcmp` + `memcmp` words — `∀ pc, prog.externAt? pc = none`, transferred to
   the hooked CLI program via the `K`-route `linkedCallHook`/`P_sub` transfer as in
   `HooksDehook.MemsetCode`):**
   - `CryptoVerification.SignalSession.CliExt.bcmpSpec` (`CliExternsFixed.lean:222`) across **all**
     four `(aRo, bRo : Bool)` combinations, plus `keepsFs` and `withVmPreserved`.
   - `CryptoVerification.SignalSession.Cli.cliBcmpSpec` (`Cli/DirSpecs.lean:175`) across **all**
     four `(aRo, bRo : Bool)` combinations, plus `keepsFs` and `withVmPreserved`.
   - `CryptoVerification.E2E.HooksE.e2eBcmpSpec` (`E2E/HooksE/Common.lean:151`), plus `keepsFs` and
     `withVmPreserved`.
   - `CryptoVerification.E2E.HooksE.bcmpVregsSpec` (`E2E/HooksE/Common.lean:139`, requiring
     `sf.vregs = s0.vregs`), plus `keepsFs` and `withVmPreserved` — satisfied by the real bytes
     because `libc.a` `bcmp.lo` (`b memcmp`) + `memcmp.lo` (`13` scalar `ldrb`/`subs` words) execute
     zero SIMD/FP instructions.
2. **Comparison with engine's `c_type_spec`-generated `VerifiedLibraries.Musl.{bcmpSpec, bcmpROSpec}`:**
   - Engine's exported `bcmpSpec` (`↦ₛ ∗ ↦ₛ`) and `bcmpROSpec` (`↦ᵣ ∗ ↦ᵣ`) omit `sf.mem = s0.mem`,
     `sf.vregs = s0.vregs`, and `ProcessFieldsPreserved s0 sf` from `.post`. Alone, `bcmpSpec` +
     `subroutine_ok_lift_pureWords_process` discharges `e2eBcmpSpec` (`aRo = bRo = false`) and
     `bcmpROSpec` discharges homogeneous `(true, true)`, but neither alone can discharge mixed
     `(false, true)` / `(true, false)` `CliExt.bcmpSpec` (which needs `sf.mem = s0.mem` to preserve
     exclusive `↦ₛ` on one slice while reading the other as `↦ᵣ`) or `bcmpVregsSpec` (which needs
     `sf.vregs = s0.vregs`).
   - Rather than leaving those consumer specs conditional, §1 proves
     `memcmpLibca_memVregsRO_codeAt_ok` over `prog.hasWords a memcmpLibcaWords` alone (carrying
     `sf.mem = s0.mem ∧ sf.vregs = s0.vregs`), lifts it on any hook-free `P_sub`
     (`∀ pc, prog.externAt? pc = none`) with `subroutine_ok_lift_pureWords_process` to obtain
     `ProcessFieldsPreserved s0 sf` (`VmPreserved s0 sf` + `keepsFs`), and composes with the
     1-word `bcmp` tail-call `b memcmp` (`bcmp_cliBcmpStackSpec_withVmPreserved_keepsFs_ok`,
     `bcmp_bcmpVregsSpec_withVmPreserved_keepsFs_ok`, and the closed hook-free placement instance
     `bcmp_cliExtBcmpSpec_image_ok` on `muslStringProg pl (fun _ => none)`).
   - Note: only an idealized total hook like `cliBcmpHook W.bcmp` (`CliRun.lean`, reading
     `s.mem.readBytes` on unmapped memory without `bytesAt`) is unsatisfiable by real `ldrb` bytes;
     every consumer `Spec` on `stockhooks/train` owns both slices via `bytesAt` / `↦ₛ` / `↦ᵣ`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.Libc.Bcmp

open Arm64 ProofLib
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open VerifiedLibraries.Musl (bcmpWords bcmpCalls bcmpLibcaRelocs memcmpLibcaWords
  bcmpSpec bcmpROSpec memcmpROSpec RoSlice8 SliceLenPair memcmpBytes memcmpBytes_eq_zero_iff
  muslStringProg muslStringProg_hasWords_relocFree muslStringProg_hasWords_of_checkSegment
  muslStringLib_resolve_sym)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (BcmpCall bcmpSpec)
open CryptoVerification.SignalSession.Cli (CliBcmpCall cliBcmpSpec)
open CryptoVerification.E2E.HooksE (BcmpCall bcmpVregsSpec e2eBcmpSpec)
open LibsignalBinary.Heap (VmPreserved FdsHiFrame)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs bytesAt satisfies_bytesAt_to_ro
  subroutine_ok_drop_keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)

/-- Strengthened read-only `memcmp`/`bcmp` specification recording `sf.mem = s0.mem` and
    `sf.vregs = s0.vregs` (both satisfied by the 13 scalar store-free words `memcmpLibcaWords`
    and 1-word `b memcmp` `bcmpWords`). -/
@[expose] def bcmpMemVregsROSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (s1, s2, n, bs1, bs2) s0 =>
    ⌜s0.readReg64 .x0 = s1 ∧ s0.readReg64 .x1 = s2 ∧ s0.readReg64 .x2 = n ∧
      n.toNat = bs1.length ∧ n.toNat = bs2.length⌝ ∗
      (s1 ↦ᵣ bs1) ∗ (s2 ↦ᵣ bs2)
  post := fun (_s1, _s2, _n, bs1, bs2) s0 sf =>
    ⌜sf.readReg32 .x0 = memcmpBytes bs1 bs2 ∧ sf.mem = s0.mem ∧ sf.vregs = s0.vregs⌝ ∗
      (_s1 ↦ᵣ bs1) ∗ (_s2 ↦ᵣ bs2)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Stack-parameterized mirror of `CliExt.bcmpSpec` and `Cli.cliBcmpSpec`. -/
@[expose] def cliBcmpStackSpec (hookStack : Nat := extHookStack) :
    Spec CryptoVerification.SignalSession.CliExt.BcmpCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ s.readReg64 .x1 = x.b ∧
      (s.readReg64 .x2).toNat = x.bsA.length ∧ x.bsB.length = x.bsA.length⌝ ∗
      bytesAt x.aRo x.a x.bsA ∗ bytesAt x.bRo x.b x.bsB ∗
      stackAt s.sp hookStack
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 32 = 0#32 ↔ x.bsA = x.bsB) ∧ sf.trace = s0.trace⌝ ∗
      bytesAt x.aRo x.a x.bsA ∗ bytesAt x.bRo x.b x.bsB ∗
      stackAt s0.sp hookStack

/-- `cliBcmpStackSpec extHookStack` is definitionally (`rfl`) `CliExt.bcmpSpec`. -/
theorem cliBcmpStackSpec_extHookStack :
    cliBcmpStackSpec extHookStack = CryptoVerification.SignalSession.CliExt.bcmpSpec := rfl

/-- Pure-memory core of `cliBcmpStackSpec` (before adjoining `sf.trace = s0.trace`, `keepsFs`, and
    `VmPreserved` via `subroutine_ok_lift_pureWords_process`). -/
private def cliBcmpCoreSpec (hookStack : Nat := extHookStack) :
    Spec CryptoVerification.SignalSession.CliExt.BcmpCall where
  pre := (cliBcmpStackSpec hookStack).pre
  post := fun x s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ↔ x.bsA = x.bsB⌝ ∗
      bytesAt x.aRo x.a x.bsA ∗ bytesAt x.bRo x.b x.bsB ∗
      stackAt s0.sp hookStack

/-- Pure-memory core of `HooksE.bcmpVregsSpec` (retaining `sf.vregs = s0.vregs` before adjoining
    `sf.trace = s0.trace`, `keepsFs`, and `VmPreserved`). -/
private def bcmpVregsCoreSpec :
    Spec CryptoVerification.E2E.HooksE.BcmpCall where
  pre := CryptoVerification.E2E.HooksE.bcmpVregsSpec.pre
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 32 = 0#32 ↔ x.bsA = x.bsB) ∧ sf.vregs = s0.vregs⌝ ∗
      (x.a ↦ₛ x.bsA) ∗ (x.b ↦ₛ x.bsB) ∗
      stackAt s0.sp extHookStack

/-! ## 1. Real-Code Proofs on `memcmpLibcaWords` (`13` Words) and `bcmpWords` (`1` Word) -/

private theorem memcmp_drop_step {bs1 bs2 : List (BitVec 8)} {i : Nat}
    (h1 : i < bs1.length) (h2 : i < bs2.length) :
    memcmpBytes (bs1.drop i) (bs2.drop i) =
      if bs1.getD i 0#8 = bs2.getD i 0#8 then memcmpBytes (bs1.drop (i + 1)) (bs2.drop (i + 1))
      else (bs1.getD i 0#8).zeroExtend 32 - (bs2.getD i 0#8).zeroExtend 32 := by
  rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2]
  simp [memcmpBytes, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2]

@[local wp_norm] private theorem vregs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).vregs = s.vregs := rfl

@[local wp_norm] private theorem vregs_setPState (s : State) (ps : PState) :
    (s.setPState ps).vregs = s.vregs := rfl

@[local wp_norm] private theorem vregs_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).vregs = s.vregs := rfl

/-- Exact `libc.a` `memcmp` bytes (`memcmpLibcaWords`, `13` scalar words) satisfy
    `bcmpMemVregsROSpec` (`sf.mem = s0.mem ∧ sf.vregs = s0.vregs`). -/
theorem memcmpLibca_memVregsRO_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcmpLibcaWords) :
    subroutine_ok prog a bcmpMemVregsROSpec := by
  wp_init x s0
  rcases x with ⟨s1, s2, n, bs1, bs2⟩
  obtain ⟨hlen1, hlen2⟩ : n.toNat = bs1.length ∧ n.toNat = bs2.length := ⟨by assumption, by assumption⟩
  have hMlt : bs1.length < 2 ^ 64 := hlen1 ▸ n.isLt
  have hl2 : bs2.length = bs1.length := by omega
  obtain rfl : n = BitVec.ofNat 64 bs1.length :=
    BitVec.eq_of_toNat_eq (by rw [hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hMlt])
  clear hlen1 hlen2
  wp_step
  wp_step
  wp_loop_measure frame bs1.length (fun k st => k ≤ bs1.length ∧
    st.readReg64 .x0 = s1 ∧
    st.readReg64 .x1 = s2 - 1#64 ∧
    st.readReg64 .x2 = BitVec.ofNat 64 bs1.length ∧
    st.readReg64 .x3 = BitVec.ofNat 64 (bs1.length - k) ∧
    st.mem = s0.mem ∧
    st.vregs = s0.vregs ∧
    memcmpBytes (bs1.drop (bs1.length - k)) (bs2.drop (bs1.length - k)) = memcmpBytes bs1 bs2)
  case init => rw [Nat.sub_self, List.drop_zero, List.drop_zero]
  case base =>
    simp only [Nat.sub_zero] at *
    have hres : memcmpBytes (bs1.drop bs1.length) (bs2.drop bs1.length) = memcmpBytes bs1 bs2 := by
      assumption
    rw [List.drop_length, List.drop_eq_nil_of_le (by omega : bs2.length ≤ bs1.length)] at hres
    rw [← hres, show memcmpBytes [] [] = 0#32 from rfl]
    wp_sym_steps
    wp_done
  case step =>
    have hres : memcmpBytes (bs1.drop (bs1.length - (m' + 1))) (bs2.drop (bs1.length - (m' + 1))) =
        memcmpBytes bs1 bs2 := by assumption
    rw [memcmp_drop_step (by omega) (by omega)] at hres
    have hidx : bs1.length - (m' + 1) + 1 = bs1.length - m' := by omega
    have hne_end : BitVec.ofNat 64 (bs1.length - (m' + 1)) ≠ BitVec.ofNat 64 bs1.length := by
      intro heq
      have h1 : (BitVec.ofNat 64 (bs1.length - (m' + 1))).toNat =
          (BitVec.ofNat 64 bs1.length).toNat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hMlt] at h1
      omega
    have hx3' : BitVec.ofNat 64 (bs1.length - (m' + 1)) + 1#64 =
        BitVec.ofNat 64 (bs1.length - m') := by
      rw [← hidx]; bv_omega
    have hea2 : (s2 - 1#64) + BitVec.ofNat 64 (bs1.length - m') =
        s2 + BitVec.ofNat 64 (bs1.length - (m' + 1)) := by
      rw [← hidx]; bv_omega
    by_cases heq : bs1.getD (bs1.length - (m' + 1)) 0#8 = bs2.getD (bs1.length - (m' + 1)) 0#8
    · right
      simp only [heq, ↓reduceIte, hidx] at hres
      wp_sym_steps
      wp_done
    · left
      simp only [heq, ↓reduceIte] at hres
      rw [← hres]
      wp_sym_steps
      wp_done

private theorem pureWordsProg_hasWords_memcmpLibca (a : BitVec 64) :
    (pureWordsProg a memcmpLibcaWords).hasWords a memcmpLibcaWords :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range memcmpLibcaWords.length).all fun i =>
      (pureWordsProg 0#64 memcmpLibcaWords).readWordOff (4 * i) == memcmpLibcaWords[i]?) = true
    decide +kernel)

private theorem pureWordsProg_noSvcMsr_memcmpLibca (a : BitVec 64) :
    (pureWordsProg a memcmpLibcaWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  Program.allInstrs_of_code_eq (prog := pureWordsProg 0#64 memcmpLibcaWords) rfl (by prove_all_instrs)

private theorem vmPreserved_of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
    FdsHiFrame.of_fs_eq h.1⟩

private theorem setWidth32_readReg64_eq_readReg32 (s : State) :
    (s.readReg64 .x0).setWidth 32 = s.readReg32 .x0 := rfl

/-- Forward-simulate `bcmpMemVregsROSpec` to `cliBcmpCoreSpec hookStack` across all
    `(aRo, bRo : Bool)` combinations (using `sf.mem = s0.mem` before process-field lifting). -/
private theorem bcmpMemVregsRO_simulates_cliBcmpCoreSpec (hookStack : Nat := extHookStack) :
    SpecSimulates bcmpMemVregsROSpec (cliBcmpCoreSpec hookStack) := by
  refine SpecSimulates.of_map ?_
  intro x R s0 hpre
  dsimp only [cliBcmpCoreSpec, cliBcmpStackSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hmem_a : s0.mem ⊨ (x.a ↦ᵣ x.bsA) ∗ (bytesAt x.bRo x.b x.bsB ∗ (stackAt s0.sp hookStack ∗ R)) :=
    satisfies_bytesAt_to_ro (by simpa only [sepConj_assoc] using hmem)
  have hmem_ab : s0.mem ⊨ (x.b ↦ᵣ x.bsB) ∗ ((x.a ↦ᵣ x.bsA) ∗ (stackAt s0.sp hookStack ∗ R)) :=
    satisfies_bytesAt_to_ro (Satisfies.of_eq hmem_a)
  refine ⟨(x.a, x.b, s0.readReg64 .x2, x.bsA, x.bsB), stackAt s0.sp hookStack ∗ R, ?_,
    fun sf _ _ hpost => ?_⟩
  · dsimp only [bcmpMemVregsROSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, rfl, hx2, by omega⟩, Satisfies.of_eq hmem_ab⟩
  · dsimp only [bcmpMemVregsROSpec] at hpost
    dsimp only [cliBcmpCoreSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, setWidth32_readReg64_eq_readReg32] at hpost ⊢
    rcases hpost with ⟨⟨hret, hmem_eq, _hvregs⟩, _⟩
    rw [hmem_eq]
    refine ⟨?_, by simpa only [sepConj_assoc] using hmem⟩
    rw [hret]
    exact memcmpBytes_eq_zero_iff hlen.symm

/-- Forward-simulate `bcmpMemVregsROSpec` to `bcmpVregsCoreSpec` (`sf.vregs = s0.vregs` retained). -/
private theorem bcmpMemVregsRO_simulates_bcmpVregsCoreSpec :
    SpecSimulates bcmpMemVregsROSpec bcmpVregsCoreSpec := by
  refine SpecSimulates.of_map ?_
  intro x R s0 hpre
  dsimp only [bcmpVregsCoreSpec, CryptoVerification.E2E.HooksE.bcmpVregsSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hmem_a : s0.mem ⊨ (x.a ↦ᵣ x.bsA) ∗ ((x.b ↦ₛ x.bsB) ∗ (stackAt s0.sp extHookStack ∗ R)) :=
    Satisfies.pointsToBytes_to_ro (by simpa only [sepConj_assoc] using hmem)
  have hmem_ab : s0.mem ⊨ (x.b ↦ᵣ x.bsB) ∗ ((x.a ↦ᵣ x.bsA) ∗ (stackAt s0.sp extHookStack ∗ R)) :=
    Satisfies.pointsToBytes_to_ro (Satisfies.of_eq hmem_a)
  refine ⟨(x.a, x.b, s0.readReg64 .x2, x.bsA, x.bsB), stackAt s0.sp extHookStack ∗ R, ?_,
    fun sf _ _ hpost => ?_⟩
  · dsimp only [bcmpMemVregsROSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, rfl, hx2, by omega⟩, Satisfies.of_eq hmem_ab⟩
  · dsimp only [bcmpMemVregsROSpec] at hpost
    dsimp only [bcmpVregsCoreSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, setWidth32_readReg64_eq_readReg32] at hpost ⊢
    rcases hpost with ⟨⟨hret, hmem_eq, hvregs⟩, _⟩
    rw [hmem_eq]
    refine ⟨⟨?_, hvregs⟩, by simpa only [sepConj_assoc] using hmem⟩
    rw [hret]
    exact memcmpBytes_eq_zero_iff hlen.symm

/-- Region-local `subroutine_ok` on any hook-free `prog`: exact `libc.a` `memcmp` bytes
    (`memcmpLibcaWords`) satisfy `withVmPreserved (keepsFs (cliBcmpStackSpec hookStack))` across all
    `(aRo, bRo : Bool)`. -/
theorem memcmpLibca_cliBcmpStackSpec_withVmPreserved_keepsFs_ok {prog : Program} {a : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasWords a memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (withVmPreserved (keepsFs (cliBcmpStackSpec hookStack))) := by
  have hpure := (bcmpMemVregsRO_simulates_cliBcmpCoreSpec hookStack).subroutine_ok
    (memcmpLibca_memVregsRO_codeAt_ok _ a (pureWordsProg_hasWords_memcmpLibca a))
  have hlift := subroutine_ok_lift_pureWords_process hpure
    (pureWordsProg_noSvcMsr_memcmpLibca a) hc h_no_ext
    (h_pre_mem := fun _ _ _ => rfl) (h_post_mem := fun _ _ _ _ _ => rfl)
  refine subroutine_ok_map hlift (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
  dsimp only [cliBcmpCoreSpec, withVmPreserved, keepsFs, cliBcmpStackSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨vmPreserved_of_processFieldsPreserved hpost.1, hpost.1.1, ⟨hpost.2.1, hpost.1.2.1⟩,
    hpost.2.2⟩

/-- Region-local `subroutine_ok` on any hook-free `prog`: exact `libc.a` `memcmp` bytes
    (`memcmpLibcaWords`) satisfy `withVmPreserved (keepsFs HooksE.bcmpVregsSpec)`
    (`sf.vregs = s0.vregs` preserved). -/
theorem memcmpLibca_bcmpVregsSpec_withVmPreserved_keepsFs_ok {prog : Program} {a : BitVec 64}
    (hc : prog.hasWords a memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a
      (withVmPreserved (keepsFs CryptoVerification.E2E.HooksE.bcmpVregsSpec)) := by
  have hpure := bcmpMemVregsRO_simulates_bcmpVregsCoreSpec.subroutine_ok
    (memcmpLibca_memVregsRO_codeAt_ok _ a (pureWordsProg_hasWords_memcmpLibca a))
  have hlift := subroutine_ok_lift_pureWords_process hpure
    (pureWordsProg_noSvcMsr_memcmpLibca a) hc h_no_ext
    (h_pre_mem := fun _ _ _ => rfl) (h_post_mem := fun _ _ _ _ _ => rfl)
  refine subroutine_ok_map hlift (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
  dsimp only [bcmpVregsCoreSpec, withVmPreserved, keepsFs,
    CryptoVerification.E2E.HooksE.bcmpVregsSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨vmPreserved_of_processFieldsPreserved hpost.1, hpost.1.1,
    ⟨hpost.2.1.1, hpost.2.1.2, hpost.1.2.1⟩, hpost.2.2⟩

private theorem bcmp_tail_ok {α : Type} {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64} {spec : Spec α}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hwords : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hcallee : subroutine_ok prog (resolve "memcmp") spec)
    (hpre_pc : ∀ x s, spec.pre x (s.setPC (resolve "memcmp")) = spec.pre x s)
    (hpost_pc : ∀ x s sf, spec.post x (s.setPC (resolve "memcmp")) sf = spec.post x s sf)
    (hpanic : ∀ x s sf, spec.onPanic x s sf = ⌜False⌝)
    (hexit : ∀ x c s sf, spec.onExit x c s sf = ⌜False⌝)
    (hoom : ∀ x s sf, spec.onOom x (s.setPC (resolve "memcmp")) sf = spec.onOom x s sf) :
    subroutine_ok prog a spec := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hf := Obj.fetch_patchCalls_b (r := (0, "memcmp")) hwords rfl rfl (by decide) (by decide)
    hrange
  simp only [BitVec.add_zero, ← hpc] at hf
  apply reaches_outcome_step hrun hf
  dsimp only [Program.evalInst, execInstWithSvc]
  rw [show s0.pc + (resolve "memcmp" - s0.pc) = resolve "memcmp" by bv_omega]
  exact reaches_outcome_of_reaches_pc
    (reaches_pc_tailcall_subroutine hcallee x x rfl hrun rfl rfl (CalleeSavedPreserved.rfl s0)
      (by rw [hpre_pc]; exact hpre) (fun sf _ _ _ _ hq => hpost_pc x s0 sf ▸ hq) hsp
      (fun _ _ hp => by rw [hpanic] at hp; exact not_satisfies_false_sepConj hp)
      (fun _ _ _ he => by rw [hexit] at he; exact not_satisfies_false_sepConj he)
      (fun sf _ ho => hoom x s0 sf ▸ ho))
    (fun _ _ ho => ho)

/-- Region-local layout-generic real-bytes `bcmp` contract on any hook-free `prog` (`bcmpWords`
    patched to `resolve "memcmp"` + `memcmpLibcaWords` at `resolve "memcmp"`): satisfies
    `withVmPreserved (keepsFs (cliBcmpStackSpec hookStack))` across all `(aRo, bRo : Bool)`. -/
theorem bcmp_cliBcmpStackSpec_withVmPreserved_keepsFs_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hookStack : Nat := extHookStack)
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (withVmPreserved (keepsFs (cliBcmpStackSpec hookStack))) :=
  bcmp_tail_ok hrange hbcmp
    (memcmpLibca_cliBcmpStackSpec_withVmPreserved_keepsFs_ok hookStack hmemcmp h_no_ext)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

/-- Region-local layout-generic real-bytes `bcmp` contract on any hook-free `prog`: satisfies
    `withVmPreserved (keepsFs HooksE.bcmpVregsSpec)` (`sf.vregs = s0.vregs` preserved). -/
theorem bcmp_bcmpVregsSpec_withVmPreserved_keepsFs_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a
      (withVmPreserved (keepsFs CryptoVerification.E2E.HooksE.bcmpVregsSpec)) :=
  bcmp_tail_ok hrange hbcmp
    (memcmpLibca_bcmpVregsSpec_withVmPreserved_keepsFs_ok hmemcmp h_no_ext)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

/-! ## 2. Direct Real-Bytes Consumer Corollaries (`bcmpWords` + `memcmpLibcaWords`) -/

/-- Region-local `subroutine_ok` on any hook-free `prog`: real `libc.a` `bcmp` + `memcmp` bytes
    satisfy `withVmPreserved CliExt.bcmpSpec`. -/
theorem bcmp_cliExtBcmpSpec_withVmPreserved_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (withVmPreserved CryptoVerification.SignalSession.CliExt.bcmpSpec) := by
  have h := bcmp_cliBcmpStackSpec_withVmPreserved_keepsFs_ok extHookStack hrange hbcmp hmemcmp
    h_no_ext
  refine subroutine_ok_map h (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
  dsimp only [withVmPreserved, keepsFs] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1, hpost.2.2⟩

/-- Region-local `subroutine_ok` on any hook-free `prog`: real `libc.a` `bcmp` + `memcmp` bytes
    satisfy `CliExt.bcmpSpec` across all `(aRo, bRo : Bool)`. -/
theorem bcmp_cliExtBcmpSpec_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a CryptoVerification.SignalSession.CliExt.bcmpSpec :=
  LibsignalBinary.Heap.SpecBudget.subroutine_ok_of_withVmPreserved
    (bcmp_cliExtBcmpSpec_withVmPreserved_ok hrange hbcmp hmemcmp h_no_ext)

/-- Region-local `subroutine_ok` on any hook-free `prog`: real `libc.a` `bcmp` + `memcmp` bytes
    satisfy `keepsFs CliExt.bcmpSpec`. -/
theorem bcmp_cliExtBcmpSpec_keepsFs_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (keepsFs CryptoVerification.SignalSession.CliExt.bcmpSpec) :=
  LibsignalBinary.Heap.SpecBudget.subroutine_ok_of_withVmPreserved
    (bcmp_cliBcmpStackSpec_withVmPreserved_keepsFs_ok extHookStack hrange hbcmp hmemcmp h_no_ext)

/-- `VerifiedLibraries.muslStringLib` placement corollary: `muslStringProg pl (fun _ => none)`
    satisfies `withVmPreserved CliExt.bcmpSpec` at `"bcmp"`. -/
theorem bcmp_cliExtBcmpSpec_image_ok (pl : Obj.Placement)
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    subroutine_ok (muslStringProg pl (fun _ => none))
      ((muslStringProg pl (fun _ => none)).fnAddr "bcmp")
      (withVmPreserved CryptoVerification.SignalSession.CliExt.bcmpSpec) := by
  have ⟨hw, hrel⟩ := muslStringProg_hasWords_of_checkSegment (hooks := fun _ => none)
    (name := "bcmp") (ws := bcmpWords) (R := bcmpLibcaRelocs) hP rfl (by decide +kernel)
  have hpatch : Obj.patchRelocs bcmpLibcaRelocs bcmpWords
      ((muslStringProg pl (fun _ => none)).fnAddr "bcmp")
      (VerifiedLibraries.muslStringLib.text.resolve pl) =
      Obj.patchCalls bcmpCalls bcmpWords
        ((muslStringProg pl (fun _ => none)).fnAddr "bcmp")
        (VerifiedLibraries.muslStringLib.text.resolve pl) := by
    simp [Obj.patchRelocs, Obj.patchCalls, Obj.patchRelocWord, Obj.addSignedAddr,
      bcmpLibcaRelocs, bcmpCalls, bcmpWords]
  have hr := hrel { off := 0, kind := .jump26, sym := "memcmp", addend := 0 }
    (by simp [bcmpLibcaRelocs])
  simp only [Obj.CodeRelocInRange, Obj.addSignedAddr, BitVec.add_zero] at hr
  have hrange : Obj.BranchInRange
      ((muslStringProg pl (fun _ => none)).fnAddr "bcmp" + 0#64)
      (VerifiedLibraries.muslStringLib.text.resolve pl "memcmp") := by
    simpa [BitVec.add_zero] using hr
  have hmemcmp : (muslStringProg pl (fun _ => none)).hasWords
      (VerifiedLibraries.muslStringLib.text.resolve pl "memcmp") memcmpLibcaWords := by
    rw [muslStringLib_resolve_sym (hooks := fun _ => none) rfl]
    exact muslStringProg_hasWords_relocFree (name := "memcmp") hP rfl (by decide +kernel)
  have hno_ext : ∀ pc, (muslStringProg pl (fun _ => none)).externAt? pc = none := fun pc => by
    simp [muslStringProg, Obj.PlacedLib.program, Program.externAt?, Program.hookAtOff?]
  exact bcmp_cliExtBcmpSpec_withVmPreserved_ok hrange (hpatch ▸ hw) hmemcmp hno_ext

/-- Region-local `subroutine_ok` on any hook-free `prog`: real `libc.a` `bcmp` + `memcmp` bytes
    satisfy `withVmPreserved DirSpecs.cliBcmpSpec`. -/
theorem bcmp_dirCliBcmpSpec_withVmPreserved_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (withVmPreserved CryptoVerification.SignalSession.Cli.cliBcmpSpec) := by
  have h := bcmp_cliExtBcmpSpec_withVmPreserved_ok hrange hbcmp hmemcmp h_no_ext
  refine subroutine_ok_map h
    (fun x R s0 hpre => ⟨⟨x.a, x.aRo, x.bsA, x.b, x.bRo, x.bsB⟩, R, hpre, fun _ hpost => hpost⟩)

/-- Region-local `subroutine_ok` on any hook-free `prog`: real `libc.a` `bcmp` + `memcmp` bytes
    satisfy `DirSpecs.cliBcmpSpec` across all `(aRo, bRo : Bool)`. -/
theorem bcmp_dirCliBcmpSpec_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a CryptoVerification.SignalSession.Cli.cliBcmpSpec :=
  LibsignalBinary.Heap.SpecBudget.subroutine_ok_of_withVmPreserved
    (bcmp_dirCliBcmpSpec_withVmPreserved_ok hrange hbcmp hmemcmp h_no_ext)

/-- Region-local `subroutine_ok` on any hook-free `prog`: real `libc.a` `bcmp` + `memcmp` bytes
    satisfy `withVmPreserved HooksE.bcmpVregsSpec`. -/
theorem bcmp_bcmpVregsSpec_withVmPreserved_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (withVmPreserved CryptoVerification.E2E.HooksE.bcmpVregsSpec) := by
  have h := bcmp_bcmpVregsSpec_withVmPreserved_keepsFs_ok hrange hbcmp hmemcmp h_no_ext
  refine subroutine_ok_map h (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
  dsimp only [withVmPreserved, keepsFs] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1, hpost.2.2⟩

/-- Region-local `subroutine_ok` on any hook-free `prog`: real `libc.a` `bcmp` + `memcmp` bytes
    satisfy `HooksE.bcmpVregsSpec` (`sf.vregs = s0.vregs`). -/
theorem bcmp_bcmpVregsSpec_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a CryptoVerification.E2E.HooksE.bcmpVregsSpec :=
  LibsignalBinary.Heap.SpecBudget.subroutine_ok_of_withVmPreserved
    (bcmp_bcmpVregsSpec_withVmPreserved_ok hrange hbcmp hmemcmp h_no_ext)

/-- Region-local `subroutine_ok` on any hook-free `prog`: real `libc.a` `bcmp` + `memcmp` bytes
    satisfy `withVmPreserved HooksE.e2eBcmpSpec`. -/
theorem bcmp_e2eBcmpSpec_withVmPreserved_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (withVmPreserved CryptoVerification.E2E.HooksE.e2eBcmpSpec) := by
  have h := bcmp_bcmpVregsSpec_withVmPreserved_ok hrange hbcmp hmemcmp h_no_ext
  refine subroutine_ok_map h (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
  dsimp only [withVmPreserved, CryptoVerification.E2E.HooksE.bcmpVregsSpec,
    CryptoVerification.E2E.HooksE.e2eBcmpSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1, ⟨hpost.2.1.1, hpost.2.1.2.2⟩, hpost.2.2⟩

/-- Region-local `subroutine_ok` on any hook-free `prog`: real `libc.a` `bcmp` + `memcmp` bytes
    satisfy `HooksE.e2eBcmpSpec`. -/
theorem bcmp_e2eBcmpSpec_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a CryptoVerification.E2E.HooksE.e2eBcmpSpec :=
  LibsignalBinary.Heap.SpecBudget.subroutine_ok_of_withVmPreserved
    (bcmp_e2eBcmpSpec_withVmPreserved_ok hrange hbcmp hmemcmp h_no_ext)

end LibsignalBinary.Proofs.HookDischarge.Libc.Bcmp
