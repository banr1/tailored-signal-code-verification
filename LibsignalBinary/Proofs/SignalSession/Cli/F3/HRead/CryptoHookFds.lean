/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.Process.Core

/-!
# `FdsGe3Closed` Preservation for Shared-Pool (`mallocng`) Crypto Hooks

**Checked by Lean.**

Pre-conditional `State.fs` preservation and `withFdsGe3Closed` `HookOk` / `HookSat` lifts for
`aesEncHookMallocng`, `aesDecHookMallocng`, and `libcruxHmacHookMallocng`, together with full row
coverage across `cliExternsPlaced mmpl W` and `cliGhostExterns`.

Unconditional preservation on arbitrary non-`pre` states does not hold because
`codeROSubroutineHook` steps `Syscall.standard` over arbitrary RX bytes in `s0.mem`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds

open Arm64 ProofLib.SepLogic
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open CryptoGames.CBC (AesKey Block bytesToBlock)
open CryptoGames.HMAC (ShaState)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcEncrypt)
open CryptoVerification.E2E
  (aesDecFrameBytes aesDecHookMallocng aesEncFrameBytes aesEncHookMallocng
   libcruxHmacFrameBytes libcruxHmacHookMallocng mlkemEncaps1Hook restoreCallerRegs
   stepRustAlloc1 stepRustDealloc1 timeAddHook)
open CryptoVerification.LibsignalSpqrV1 (LibcruxHmacCall)
open CryptoVerification.LibsignalTripleRatchet (AesCall extHookStack)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced cliHookTablePlaced cliPqxdhHookTablePlaced durationSinceExactHook
   fromUtf8Hook lsAesDecSym lsAesEncSym memrchrHook strlenHook)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (aesDec_row_placed aesEnc_row_placed cliGhostExterns_sat_of_cliExternsPlaced
   libcruxHmac_row_placed lsLibcruxHmacSymCli)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits FitsEvent FitsEvents
   MallocngCostModelIface MallocngCostModelSound VmPreserved rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel fineCostModelSound)
open LibsignalBinary.Heap.SpecBudget
  (AesDecEnv LibcruxHmacEnv aesCallPreBudget aesDecBudgetSpec aesDecWeakBudgetSpec
   aesEncBudgetSpec aesEncFnBudgetSpec libcruxHmacBudgetSpec libcruxHmacSha256Events)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (aesDecHookMallocng_budget_ok aesDecWeakHookMallocng_budget_ok aesEncHookMallocng_budget_ok
   fineAesDec_budget_hookOk fineAesDecWeak_budget_hookOk fineAesEnc_budget_hookOk
   fineHookRustCliAllocBudget fineLibcruxHmac_budget_hookOk
   libcruxHmacHookMallocng_budget_ok mallocngHookBudgetPool mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (allocCallPreserved_refl allocCallPreserved_trans callocHookBridgeSpec freeHookBridgeSpec
   mallocHookBridgeSpec mallocngHook mallocngHookBudgetPool_transport spAligned_sub_16
   stackAt_split_frame vmPreserved_restoreCallerRegs vmPreserved_writeReg64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers
  (calloc_budget_hookOk fitsEvent_of_fitsAlloc1 free_budget_hookOk malloc_budget_hookOk
   pointsTo_replicate_to_memRegion rustAllocEvents_one)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed fdsGe3Closed_writeFileHook fdsGe3Closed_writeStdoutHook
   hookOk_withFdsGe3Closed withFdsGe3Closed)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize mallocngStackBytes)

/-! ## Non-`.Running` Stability and CPS Predicate Rules -/

/-- From a non-`.Running` state `s`, `Obj.MultiPlacedLib.codeROSubroutineHook` takes `0` machine
    steps (`Steps.from_not_running`), preserving non-`.Running` status and `State.fs`. -/
theorem codeROSubroutineHook_status_fs_of_not_running
    (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (fnName : String)
    (externs overrides : String → Option (State → State)) (svc : State → State)
    {s : State} (hnr : s.status ≠ .Running) :
    (lib.codeROSubroutineHook mpl fnName externs overrides svc s).status ≠ .Running ∧
      (lib.codeROSubroutineHook mpl fnName externs overrides svc s).fs = s.fs := by
  classical
  unfold Obj.MultiPlacedLib.codeROSubroutineHook
  cases Obj.lookupBlockSym fnName lib.blocks with
  | none => exact ⟨hnr, rfl⟩
  | some p =>
    rcases p with ⟨i, off⟩
    dsimp only
    split
    · rename_i h
      let s0' := multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s
      have hs0'_nr : s0'.status ≠ .Running := by
        simpa [s0', multiCodeROHookEntry_status] using hnr
      have hchoose_eq : Classical.choose h = s0' :=
        Steps.from_not_running (Classical.choose_spec h).1.toSteps hs0'_nr
      rw [hchoose_eq]
      refine ⟨?_, ?_⟩
      · rw [multiCodeROHookExit_status]
        exact hs0'_nr
      · rw [multiCodeROHookExit_fs, multiCodeROHookEntry_fs]
    · exact ⟨hnr, rfl⟩

/-- From a non-`.Running` state `s`, `stepRustAlloc1` stops at `if s1.status != .Running` without
    invoking `k`, leaving `State.fs` equal to `s.fs`. -/
theorem stepRustAlloc1_fs_of_not_running
    (mpl : Obj.MultiPlacement) (zeroed : Bool) (frameBytes size : Nat)
    (k : State → BitVec 64 → State) {s : State} (hnr : s.status ≠ .Running) :
    (stepRustAlloc1 mpl zeroed frameBytes size k s).fs = s.fs := by
  unfold stepRustAlloc1
  let spCall := s.sp - BitVec.ofNat 64 frameBytes
  let sCall0 := (s.writeReg64 .sp spCall).writeReg64 .x0 (BitVec.ofNat 64 size)
  let sCall := if zeroed then sCall0.writeReg64 .x1 1#64 else sCall0
  have hsCall_nr : sCall.status ≠ .Running := by cases zeroed <;> exact hnr
  have hsCall_fs : sCall.fs = s.fs := by cases zeroed <;> rfl
  let fnName := if zeroed then "calloc" else "malloc"
  obtain ⟨hs1_nr, hs1_fs⟩ := codeROSubroutineHook_status_fs_of_not_running
    VerifiedLibraries.mallocngLib mpl fnName (fun _ => none) (fun _ => none) Syscall.standard hsCall_nr
  dsimp only
  have hbne : ((VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl fnName
      (fun _ => none) (fun _ => none) Syscall.standard sCall).status != .Running) = true := by
    cases hst : (VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl fnName
      (fun _ => none) (fun _ => none) Syscall.standard sCall).status <;>
      first | rfl | exact False.elim (hs1_nr hst)
  rw [hbne]
  simp only [↓reduceIte]
  exact hs1_fs.trans hsCall_fs

/-- Non-OOM CPS proof rule for an arbitrary state predicate `P : State → Prop` across
    `stepRustAlloc1` under `FitsEvent M lim st (.alloc size)`: deterministic evaluation via
    `malloc_budget_hookOk` / `calloc_budget_hookOk` threads `AllocCallPreserved s0 s1`
    (in particular `s1.fs = s0.fs`) directly to `k`. -/
theorem stepRustAlloc1_pred_cps {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName}
    {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64} {lim : BudgetLimits} {st : M.σ}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    {P : State → Prop} {R Rest : SepProp} {s0 s : State}
    (zeroed : Bool) (frameBytes size : Nat) (hfb16 : frameBytes % 16 = 0)
    (hfb_le : frameBytes + mallocngStackBytes ≤ extHookStack)
    (hFit : FitsEvent M lim st (.alloc size))
    (hrun : s.status = .Running) (hsp_eq : s.sp = s0.sp) (hregs_eq : s.regs = s0.regs)
    (hvregs_eq : s.vregs = s0.vregs) (hsp_al : s0.spAligned = true)
    (hpres0 : AllocCallPreserved s0 s)
    (hmem : s.mem ⊨
      (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s ∗
        stackAt s0.sp extHookStack ∗ Rest) ∗ R)
    (k : State → BitVec 64 → State)
    (hk : ∀ (s1 : State) (p : BitVec 64),
      p ≠ 0#64 → 16 ∣ p.toNat → p.toNat + size < 2 ^ 64 →
      s1.status = .Running → s1.sp = s0.sp → s1.regs = s0.regs → s1.vregs = s0.vregs →
      AllocCallPreserved s0 s1 →
      (s1.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
          stackAt s0.sp extHookStack ∗
          I.BlockM γ p size 16 ∗
          (if zeroed then (p ↦ₛ List.replicate size 0#8) else memRegion p size) ∗
          Rest) ∗ R) →
      P (k s1 p)) :
    P (stepRustAlloc1 mpl zeroed frameBytes size k s) := by
  have hsz_le : size ≤ MallocngMaxAllocSize := hFit.1
  have hmax : MallocngMaxAllocSize < 2 ^ 64 := by decide
  have hsz_bv : (BitVec.ofNat 64 size).toNat = size := Nat.mod_eq_of_lt (by omega)
  let spCall := s.sp - BitVec.ofNat 64 frameBytes
  let sCall0 := (s.writeReg64 .sp spCall).writeReg64 .x0 (BitVec.ofNat 64 size)
  let sCall := if zeroed then sCall0.writeReg64 .x1 1#64 else sCall0
  have hsCall_run : sCall.status = .Running := by cases zeroed <;> exact hrun
  have hsCall_mem : sCall.mem = s.mem := by cases zeroed <;> rfl
  have hsCall_sp : sCall.sp = spCall := by cases zeroed <;> rfl
  have hsCall_x0 : sCall.readReg64 .x0 = BitVec.ofNat 64 size := by
    cases zeroed <;> simp [sCall, sCall0, State.writeReg64, State.readReg64, RegFile.read, RegFile.write]
  have hsCall_pres : AllocCallPreserved s0 sCall := by cases zeroed <;> exact hpres0
  have hsCall_al : sCall.spAligned = true := by
    simp only [State.spAligned, hsCall_sp, spCall, hsp_eq]; exact spAligned_sub_16 hsp_al hfb16
  have hsCall_vm : VmPreserved s sCall := by
    have hvm0 : VmPreserved s sCall0 :=
      (vmPreserved_writeReg64 s .sp spCall).trans
        (vmPreserved_writeReg64 (s.writeReg64 .sp spCall) .x0 (BitVec.ofNat 64 size))
    cases zeroed with
    | false => exact hvm0
    | true => exact hvm0.trans (vmPreserved_writeReg64 sCall0 .x1 1#64)
  let Slack := memRegion (s0.sp - BitVec.ofNat 64 extHookStack)
      (extHookStack - frameBytes - mallocngStackBytes) ∗
    memRegion (s0.sp - BitVec.ofNat 64 frameBytes) frameBytes
  have hstk_eq : stackAt s0.sp extHookStack = stackFrameAt spCall mallocngStackBytes ∗ Slack := by
    dsimp only [spCall, Slack]; rw [hsp_eq]; exact stackAt_split_frame s0.sp frameBytes hfb_le
  have hpool_call :
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st sCall =
        mallocngHookBudgetPool M I γ mpl tp brkStart lim st s :=
    mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hsCall_vm
  cases zeroed with
  | false =>
    let s1 := mallocngHook mpl "malloc" sCall
    have hstep_eq : stepRustAlloc1 mpl false frameBytes size k s =
        (if s1.status != .Running then s1 else let p := s1.readReg64 .x0
          let sKeep := restoreCallerRegs s s1
          if p == 0#64 then Rust.panicked sKeep else k sKeep p) := rfl
    rw [hstep_eq]
    have hpre_m : sCall.mem ⊨
        (mallocHookBridgeSpec M I γ mpl tp brkStart lim).pre
          (BitVec.ofNat 64 size, spCall, st) sCall ∗ ((Slack ∗ Rest) ∗ R) := by
      dsimp only [mallocHookBridgeSpec]
      rw [hsCall_mem, hpool_call, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hsCall_x0, hsCall_sp⟩, ?_⟩
      rw [hstk_eq] at hmem; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    obtain ⟨_, _, hout1⟩ := malloc_budget_hookOk hS γ tp brkStart lim hPl
      (BitVec.ofNat 64 size, spCall, st) ((Slack ∗ Rest) ∗ R) sCall hsCall_run hpre_m hsCall_al
    rcases hout1 with ⟨hret1, _, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom1⟩
    · have hs1_run : s1.status = .Running := hret1.2.2
      rw [show (s1.status != .Running) = false by rw [hs1_run]; rfl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [mallocHookBridgeSpec] at hpost1
      change s1.mem ⊨ _ at hpost1
      have hok : decide (size ≤ MallocngMaxAllocSize) = true := decide_eq_true hsz_le
      simp only [hsz_bv, hok, ↓reduceIte, sepConj_assoc] at hpost1
      rw [satisfies_pure_sepConj] at hpost1
      obtain ⟨hpres1', hpost1⟩ := hpost1
      have hpull :
          mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
            (stackFrameAt spCall mallocngStackBytes ∗
              (⌜s1.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (s1.readReg64 .x0).toNat ∧
                  (s1.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
                (I.BlockM γ (s1.readReg64 .x0) size 16 ∗
                  (memRegion (s1.readReg64 .x0) size ∗ (Slack ∗ (Rest ∗ R)))))) =
          ⌜s1.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (s1.readReg64 .x0).toNat ∧
              (s1.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
            (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
              (stackFrameAt spCall mallocngStackBytes ∗ Slack) ∗
              I.BlockM γ (s1.readReg64 .x0) size 16 ∗
              memRegion (s1.readReg64 .x0) size ∗ Rest ∗ R) := by sep_ac_rfl
      rw [hpull, satisfies_pure_sepConj] at hpost1
      obtain ⟨⟨hp_ne, hp_al16, hp_fit64⟩, hpost1⟩ := hpost1
      rw [beq_eq_false_iff_ne.mpr hp_ne]; simp only [Bool.false_eq_true, ↓reduceIte]
      let sKeep := restoreCallerRegs s s1
      have hpres1 := allocCallPreserved_trans hsCall_pres hpres1'
      have hpool_keep := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
        (M.step (.alloc size) st) (vmPreserved_restoreCallerRegs s s1)
      have hmem_keep : sKeep.mem ⊨
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) sKeep ∗
            stackAt s0.sp extHookStack ∗
            I.BlockM γ (s1.readReg64 .x0) size 16 ∗
            memRegion (s1.readReg64 .x0) size ∗ Rest) ∗ R := by
        change s1.mem ⊨ _
        rw [hpool_keep, hstk_eq]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost1
      exact hk sKeep (s1.readReg64 .x0) hp_ne hp_al16 hp_fit64
        hs1_run hsp_eq hregs_eq hvregs_eq hpres1 hmem_keep
    · exact False.elim (not_satisfies_false_sepConj hp)
    · exact False.elim (not_satisfies_false_sepConj he)
    · dsimp only [mallocHookBridgeSpec] at hoom1
      rw [satisfies_pure_sepConj] at hoom1
      rw [hsz_bv] at hoom1
      exact False.elim (hoom1.1.1 hFit)
  | true =>
    let s1 := mallocngHook mpl "calloc" sCall
    have hstep_eq : stepRustAlloc1 mpl true frameBytes size k s =
        (if s1.status != .Running then s1 else let p := s1.readReg64 .x0
          let sKeep := restoreCallerRegs s s1
          if p == 0#64 then Rust.panicked sKeep else k sKeep p) := rfl
    rw [hstep_eq]
    have hsCall_x1 : sCall.readReg64 .x1 = 1#64 := by
      simp [sCall, sCall0, State.writeReg64, State.readReg64, RegFile.read, RegFile.write]
    have hpre_c : sCall.mem ⊨
        (callocHookBridgeSpec M I γ mpl tp brkStart lim).pre
          (BitVec.ofNat 64 size, 1#64, spCall, st) sCall ∗ ((Slack ∗ Rest) ∗ R) := by
      dsimp only [callocHookBridgeSpec]
      rw [hsCall_mem, hpool_call, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hsCall_x0, hsCall_x1, hsCall_sp⟩, ?_⟩
      rw [hstk_eq] at hmem; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    obtain ⟨_, _, hout1⟩ := calloc_budget_hookOk hS γ tp brkStart lim hPl
      (BitVec.ofNat 64 size, 1#64, spCall, st) ((Slack ∗ Rest) ∗ R) sCall hsCall_run hpre_c hsCall_al
    have htot : (BitVec.ofNat 64 size).toNat * (1#64).toNat = size := by
      change (BitVec.ofNat 64 size).toNat * 1 = size; rw [Nat.mul_one, hsz_bv]
    rcases hout1 with ⟨hret1, _, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom1⟩
    · have hs1_run : s1.status = .Running := hret1.2.2
      rw [show (s1.status != .Running) = false by rw [hs1_run]; rfl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [callocHookBridgeSpec] at hpost1
      change s1.mem ⊨ _ at hpost1
      have hok : decide (size ≤ MallocngMaxAllocSize) = true := decide_eq_true hsz_le
      simp only [htot, hok, ↓reduceIte, sepConj_assoc] at hpost1
      rw [satisfies_pure_sepConj] at hpost1
      obtain ⟨hpres1', hpost1⟩ := hpost1
      have hpull :
          mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
            (stackFrameAt spCall mallocngStackBytes ∗
              (⌜s1.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (s1.readReg64 .x0).toNat ∧
                  (s1.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
                (I.BlockM γ (s1.readReg64 .x0) size 16 ∗
                  ((s1.readReg64 .x0 ↦ₛ List.replicate size 0#8) ∗ (Slack ∗ (Rest ∗ R)))))) =
          ⌜s1.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (s1.readReg64 .x0).toNat ∧
              (s1.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
            (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
              (stackFrameAt spCall mallocngStackBytes ∗ Slack) ∗
              I.BlockM γ (s1.readReg64 .x0) size 16 ∗
              (s1.readReg64 .x0 ↦ₛ List.replicate size 0#8) ∗ Rest ∗ R) := by sep_ac_rfl
      rw [hpull, satisfies_pure_sepConj] at hpost1
      obtain ⟨⟨hp_ne, hp_al16, hp_fit64⟩, hpost1⟩ := hpost1
      rw [beq_eq_false_iff_ne.mpr hp_ne]; simp only [Bool.false_eq_true, ↓reduceIte]
      let sKeep := restoreCallerRegs s s1
      have hpres1 := allocCallPreserved_trans hsCall_pres hpres1'
      have hpool_keep := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
        (M.step (.alloc size) st) (vmPreserved_restoreCallerRegs s s1)
      have hmem_keep : sKeep.mem ⊨
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) sKeep ∗
            stackAt s0.sp extHookStack ∗
            I.BlockM γ (s1.readReg64 .x0) size 16 ∗
            (s1.readReg64 .x0 ↦ₛ List.replicate size 0#8) ∗ Rest) ∗ R := by
        change s1.mem ⊨ _
        rw [hpool_keep, hstk_eq]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost1
      exact hk sKeep (s1.readReg64 .x0) hp_ne hp_al16 hp_fit64
        hs1_run hsp_eq hregs_eq hvregs_eq hpres1 hmem_keep
    · exact False.elim (not_satisfies_false_sepConj hp)
    · exact False.elim (not_satisfies_false_sepConj he)
    · dsimp only [callocHookBridgeSpec] at hoom1
      rw [satisfies_pure_sepConj] at hoom1
      rw [htot] at hoom1
      exact False.elim (hoom1.1.1 hFit)

/-- CPS proof rule for an arbitrary state predicate `P : State → Prop` across `stepRustDealloc1`
    (`align = 1`): deterministic evaluation via `free_budget_hookOk` threads
    `AllocCallPreserved s0 s1` (in particular `s1.fs = s0.fs`) directly to `k`. -/
theorem stepRustDealloc1_pred_cps {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName}
    {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64} {lim : BudgetLimits} {st : M.σ}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    {P : State → Prop} {R Rest : SepProp} {s0 s : State}
    (frameBytes size : Nat) (ptr : BitVec 64)
    (hptr_ne : ptr ≠ 0#64) (hptr_al16 : 16 ∣ ptr.toNat) (hptr_fit64 : ptr.toNat + size < 2 ^ 64)
    (hfb16 : frameBytes % 16 = 0)
    (hfb_le : frameBytes + mallocngStackBytes ≤ extHookStack) (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp) (hregs_eq : s.regs = s0.regs) (hvregs_eq : s.vregs = s0.vregs)
    (hsp_al : s0.spAligned = true)
    (hpres0 : AllocCallPreserved s0 s)
    (hmem : s.mem ⊨
      (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s ∗
        stackAt s0.sp extHookStack ∗
        I.BlockM γ ptr size 16 ∗ memRegion ptr size ∗ Rest) ∗ R)
    (k : State → State)
    (hk : ∀ (s1 : State), s1.status = .Running → s1.sp = s0.sp → s1.regs = s0.regs →
      s1.vregs = s0.vregs → AllocCallPreserved s0 s1 →
      (s1.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.free 1 size) st) s1 ∗
          stackAt s0.sp extHookStack ∗ Rest) ∗ R) →
      P (k s1)) :
    P (stepRustDealloc1 mpl frameBytes ptr k s) := by
  let spCall := s.sp - BitVec.ofNat 64 frameBytes
  let sCall := (s.writeReg64 .sp spCall).writeReg64 .x0 ptr
  have hsCall_al : sCall.spAligned = true := by
    simp only [State.spAligned, sCall, State.writeReg64, spCall, hsp_eq]
    exact spAligned_sub_16 hsp_al hfb16
  have hsCall_vm : VmPreserved s sCall :=
    (vmPreserved_writeReg64 s .sp spCall).trans
      (vmPreserved_writeReg64 (s.writeReg64 .sp spCall) .x0 ptr)
  let Slack := memRegion (s0.sp - BitVec.ofNat 64 extHookStack)
      (extHookStack - frameBytes - mallocngStackBytes) ∗
    memRegion (s0.sp - BitVec.ofNat 64 frameBytes) frameBytes
  have hstk_eq : stackAt s0.sp extHookStack = stackFrameAt spCall mallocngStackBytes ∗ Slack := by
    dsimp only [spCall, Slack]; rw [hsp_eq]; exact stackAt_split_frame s0.sp frameBytes hfb_le
  have hpool_call :=
    mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hsCall_vm
  let s1 := mallocngHook mpl "free" sCall
  have hstep_eq : stepRustDealloc1 mpl frameBytes ptr k s =
      (if s1.status != .Running then s1 else k (restoreCallerRegs s s1)) := rfl
  rw [hstep_eq]
  have hmax1 : max 1 16 = 16 := rfl
  have hpre_f : sCall.mem ⊨
      (freeHookBridgeSpec M I γ mpl tp brkStart lim).pre
        (ptr, size, 1, spCall, st) sCall ∗ ((Slack ∗ Rest) ∗ R) := by
    dsimp only [freeHookBridgeSpec]
    simp only [hptr_ne, ↓reduceIte, hmax1]
    change s.mem ⊨ _
    rw [hpool_call, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [sCall, State.writeReg64, State.readReg64, RegFile.read, RegFile.write],
      rfl, hptr_al16, hptr_fit64⟩, ?_⟩
    rw [hstk_eq] at hmem; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  obtain ⟨_, _, hout1⟩ := free_budget_hookOk hS γ tp brkStart lim hPl
    (ptr, size, 1, spCall, st) ((Slack ∗ Rest) ∗ R) sCall hrun hpre_f hsCall_al
  rcases hout1 with ⟨hret1, _, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · have hs1_run : s1.status = .Running := hret1.2.2
    rw [show (s1.status != .Running) = false by rw [hs1_run]; rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [freeHookBridgeSpec] at hpost1
    change s1.mem ⊨ _ at hpost1
    rw [beq_eq_false_iff_ne.mpr hptr_ne] at hpost1
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hpost1
    rw [satisfies_pure_sepConj] at hpost1
    obtain ⟨hpres1', hpost1⟩ := hpost1
    let sKeep := restoreCallerRegs s s1
    have hpres1 := allocCallPreserved_trans hpres0 hpres1'
    have hpool_keep := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
      (M.step (.free 1 size) st) (vmPreserved_restoreCallerRegs s s1)
    have hmem_keep : sKeep.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.free 1 size) st) sKeep ∗
          stackAt s0.sp extHookStack ∗ Rest) ∗ R := by
      change s1.mem ⊨ _
      rw [hpool_keep, hstk_eq]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost1
    exact hk sKeep hs1_run hsp_eq hregs_eq hvregs_eq hpres1 hmem_keep
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-! ## Pre-Conditional `fs` Equality and `FdsGe3Closed` Preservation -/

private theorem libcruxHmacSha256Events_eq_local :
    libcruxHmacSha256Events =
      [.alloc 64, .alloc 64, .alloc 64, .free 1 64, .free 1 64, .free 1 64, .alloc 32] := by
  unfold libcruxHmacSha256Events
  rw [rustAllocEvents_one (by decide : 1 ≤ 64), rustAllocEvents_one (by decide : 1 ≤ 32)]
  rfl

/-- `aesEncHookMallocng mpl E` leaves `State.fs` unchanged on every `sp`-aligned state `s0`
    satisfying `(aesEncBudgetSpec E M (mallocngHookRustCliAllocBudget …) lim).pre (x, st) s0 ∗ R`. -/
theorem aesEncHookMallocng_fs_eq_of_pre {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (E : AesKey → Block → Block)
    {x : AesCall} {st : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (aesEncBudgetSpec E M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim).pre
        (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    (aesEncHookMallocng mpl E s0).fs = s0.fs := by
  by_cases hrun : s0.status = .Running
  · dsimp only [aesEncBudgetSpec, aesCallPreBudget, mallocngHookRustCliAllocBudget] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨_, hx1, _, hx3, _, hx5, _, _, _, hin_lt, hFitEnv⟩, hmem⟩
    unfold aesEncHookMallocng
    have hguard : (s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64) = false := by
      rw [hx3, hx5]; rfl
    simp only [hguard, Bool.false_eq_true, ↓reduceIte, hx1]
    let ctLen := (x.input.length / 16 + 1) * 16
    simp only [show ¬(2 ^ 63 ≤ (x.input.length / 16 + 1) * 16) by omega, ↓reduceIte]
    have hpos : 1 ≤ ctLen := by dsimp [ctLen]; omega
    have hFit : FitsEvent M lim st (.alloc ctLen) :=
      fitsEvent_of_fitsAlloc1 hpos (hFitEnv (rustAllocEvents ctLen 1) rfl)
    have hmem0 : s0.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗ stackAt s0.sp extHookStack ∗
          (x.frame ∗ memRegion x.ret 24)) ∗ R := by
      unfold AesCall.frame; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    refine stepRustAlloc1_pred_cps hS hPl (P := fun sf => sf.fs = s0.fs) true aesEncFrameBytes ctLen
      (by decide) (by decide) hFit hrun rfl rfl rfl hsp (allocCallPreserved_refl s0) hmem0 _ ?_
    intro s1 _ _ _ _ _ _ _ _ hpres1 _
    exact hpres1.1
  · unfold aesEncHookMallocng
    split
    · rfl
    · dsimp only
      split
      · rfl
      · exact stepRustAlloc1_fs_of_not_running mpl true aesEncFrameBytes _ _ hrun

theorem aesEncHookMallocng_preserves_fdsGe3Closed_of_pre
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (E : AesKey → Block → Block)
    {x : AesCall} {st : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (aesEncBudgetSpec E M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim).pre
        (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true)
    (hfds : FdsGe3Closed s0.fs) :
    FdsGe3Closed (aesEncHookMallocng mpl E s0).fs := by
  rw [aesEncHookMallocng_fs_eq_of_pre hS γ tp brkStart lim hPl E hpre hsp]
  exact hfds

theorem fineAesEncHookMallocng_preserves_fdsGe3Closed_of_pre
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (E : AesKey → Block → Block)
    {x : AesCall} {st : fineCostModel.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (aesEncBudgetSpec E fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim).pre
        (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true)
    (hfds : FdsGe3Closed s0.fs) :
    FdsGe3Closed (aesEncHookMallocng mpl E s0).fs :=
  aesEncHookMallocng_preserves_fdsGe3Closed_of_pre fineCostModelSound γ tp brkStart lim hPl E
    hpre hsp hfds

/-- `aesDecHookMallocng mpl D` leaves `State.fs` unchanged on every `sp`-aligned state `s0`
    satisfying `(aesDecBudgetSpec D M (mallocngHookRustCliAllocBudget …) lim).pre (x, st) s0 ∗ R`
    (covering the bad-ciphertext-length early `Err`, the `some pt` `calloc` path, and the `none`
    `calloc` + `free` PKCS#7-rejection path). -/
theorem aesDecHookMallocng_fs_eq_of_pre {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block)
    {x : AesCall} {st : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (aesDecBudgetSpec D M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim).pre
        (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    (aesDecHookMallocng mpl D s0).fs = s0.fs := by
  by_cases hrun : s0.status = .Running
  · dsimp only [aesDecBudgetSpec, aesCallPreBudget, mallocngHookRustCliAllocBudget] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨_, hx1, _, hx3, _, hx5, _, _, _, _, hFitEnv⟩, hmem⟩
    unfold aesDecHookMallocng
    have hguard : (s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64) = false := by
      rw [hx3, hx5]; rfl
    simp only [hguard, Bool.false_eq_true, ↓reduceIte, hx1]
    by_cases hbad : (x.input.length == 0 || x.input.length % 16 != 0) = true
    · simp only [hbad, ↓reduceIte]
      rfl
    · simp only [Bool.eq_false_iff.mpr hbad, Bool.false_eq_true, ↓reduceIte]
      have hnot_bad : ¬(x.input.length = 0 ∨ x.input.length % 16 ≠ 0) := by
        rintro (h0 | hm)
        · exact hbad (Bool.or_eq_true_iff.mpr (Or.inl (beq_iff_eq.mpr h0)))
        · exact hbad (Bool.or_eq_true_iff.mpr (Or.inr (bne_iff_ne.mpr hm)))
      have hpos : 1 ≤ x.input.length := by omega
      have hEnvOk : AesDecEnv x (rustAllocEvents x.input.length 1) := by
        unfold AesDecEnv; split
        · next h => exact False.elim (hnot_bad h)
        · exact Or.inl rfl
      have hFit : FitsEvent M lim st (.alloc x.input.length) :=
        fitsEvent_of_fitsAlloc1 hpos (hFitEnv _ hEnvOk)
      have hmem0 : s0.mem ⊨
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗ stackAt s0.sp extHookStack ∗
            (x.frame ∗ memRegion x.ret 24)) ∗ R := by
        unfold AesCall.frame; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
      refine stepRustAlloc1_pred_cps hS hPl (P := fun sf => sf.fs = s0.fs) true aesDecFrameBytes
        x.input.length (by decide) (by decide) hFit hrun rfl rfl rfl hsp
        (allocCallPreserved_refl s0) hmem0 _ ?_
      intro s1 p hp_ne hp_al16 hp_fit64 hs1_run hs1_sp hs1_regs hs1_vregs hpres1 hmem1
      simp only [↓reduceIte] at hmem1
      cases CryptoVerification.E2E.aesDecOut D s1 with
      | some pt =>
        exact hpres1.1
      | none =>
        dsimp only
        have hm_free : s1.mem ⊨
            (mallocngHookBudgetPool M I γ mpl tp brkStart lim
                (M.step (.alloc x.input.length) st) s1 ∗
              stackAt s0.sp extHookStack ∗
              I.BlockM γ p x.input.length 16 ∗ memRegion p x.input.length ∗
              (x.frame ∗ memRegion x.ret 24)) ∗ R :=
          Satisfies.mono (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left (pointsTo_replicate_to_memRegion p x.input.length))))))
            (Entails.of_eq (by sep_ac_rfl))) hmem1
        refine stepRustDealloc1_pred_cps hS hPl (P := fun sf => sf.fs = s0.fs) aesDecFrameBytes
          x.input.length p hp_ne hp_al16 hp_fit64 (by decide) (by decide)
          hs1_run hs1_sp hs1_regs hs1_vregs hsp hpres1 hm_free _ ?_
        intro _ _ _ _ _ hpres2 _
        exact hpres2.1
  · unfold aesDecHookMallocng
    split
    · rfl
    · dsimp only
      split
      · rfl
      · exact stepRustAlloc1_fs_of_not_running mpl true aesDecFrameBytes _ _ hrun

theorem aesDecHookMallocng_preserves_fdsGe3Closed_of_pre
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block)
    {x : AesCall} {st : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (aesDecBudgetSpec D M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim).pre
        (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true)
    (hfds : FdsGe3Closed s0.fs) :
    FdsGe3Closed (aesDecHookMallocng mpl D s0).fs := by
  rw [aesDecHookMallocng_fs_eq_of_pre hS γ tp brkStart lim hPl D hpre hsp]
  exact hfds

/-- Pre-conditional `FdsGe3Closed` preservation for `aesDecHookMallocng mpl D` under
`aesDecWeakBudgetSpec.pre`. -/
theorem aesDecWeakHookMallocng_preserves_fdsGe3Closed_of_pre
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block)
    {x : AesCall} {st : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (aesDecWeakBudgetSpec D M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim).pre
        (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true)
    (hfds : FdsGe3Closed s0.fs) :
    FdsGe3Closed (aesDecHookMallocng mpl D s0).fs :=
  aesDecHookMallocng_preserves_fdsGe3Closed_of_pre hS γ tp brkStart lim hPl D hpre hsp hfds

theorem fineAesDecHookMallocng_preserves_fdsGe3Closed_of_pre
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block)
    {x : AesCall} {st : fineCostModel.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (aesDecBudgetSpec D fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim).pre
        (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true)
    (hfds : FdsGe3Closed s0.fs) :
    FdsGe3Closed (aesDecHookMallocng mpl D s0).fs :=
  aesDecHookMallocng_preserves_fdsGe3Closed_of_pre fineCostModelSound γ tp brkStart lim hPl D
    hpre hsp hfds

theorem fineAesDecWeakHookMallocng_preserves_fdsGe3Closed_of_pre
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block)
    {x : AesCall} {st : fineCostModel.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (aesDecWeakBudgetSpec D fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim).pre
        (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true)
    (hfds : FdsGe3Closed s0.fs) :
    FdsGe3Closed (aesDecHookMallocng mpl D s0).fs :=
  aesDecWeakHookMallocng_preserves_fdsGe3Closed_of_pre fineCostModelSound γ tp brkStart lim hPl D
    hpre hsp hfds

/-- `libcruxHmacHookMallocng mpl F` leaves `State.fs` unchanged on every `sp`-aligned state `s0`
    satisfying `(libcruxHmacBudgetSpec F M (mallocngHookRustCliAllocBudget …) lim).pre (x, st) s0 ∗ R`
    (covering both the `2 ^ 32 ≤ keyLen || 2 ^ 32 ≤ dataLen` `Rust.panicked s0` branch and the
    7-call `mallocng` SHA-256 sequence). -/
theorem libcruxHmacHookMallocng_fs_eq_of_pre {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (F : ShaState → List (BitVec 8) → ShaState)
    {x : LibcruxHmacCall} {st : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (libcruxHmacBudgetSpec F M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim).pre
        (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    (libcruxHmacHookMallocng mpl F s0).fs = s0.fs := by
  by_cases hrun : s0.status = .Running
  · dsimp only [libcruxHmacBudgetSpec, mallocngHookRustCliAllocBudget] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨_, hx0, _, hx2, _, hx4, _, _, hFitEnv⟩, hmem⟩
    unfold libcruxHmacHookMallocng
    simp only [show ((s0.readReg64 .x0).setWidth 32 != 0#32) = false by rw [hx0]; rfl,
      Bool.false_eq_true, ↓reduceIte, hx2, hx4]
    by_cases hbig : (decide (2 ^ 32 ≤ x.key.length) || decide (2 ^ 32 ≤ x.data.length)) = true
    · simp only [hbig, ↓reduceIte]
      rfl
    · simp only [Bool.eq_false_iff.mpr hbig, Bool.false_eq_true, ↓reduceIte]
      have hkey_lt : x.key.length < 2 ^ 32 := by
        have : ¬(2 ^ 32 ≤ x.key.length) := fun h =>
          hbig (Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true h)))
        omega
      have hdata_lt : x.data.length < 2 ^ 32 := by
        have : ¬(2 ^ 32 ≤ x.data.length) := fun h =>
          hbig (Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true h)))
        omega
      have hEnv : LibcruxHmacEnv x libcruxHmacSha256Events := by
        unfold LibcruxHmacEnv; split
        · rfl
        · next h => exact False.elim (h ⟨hkey_lt, hdata_lt⟩)
      have hFitsAll : FitsEvents M lim st libcruxHmacSha256Events := hFitEnv _ hEnv
      rw [libcruxHmacSha256Events_eq_local] at hFitsAll
      rcases hFitsAll with ⟨hFit0, hFit1, hFit2, _, _, _, hFit6, -⟩
      have hmem0 : s0.mem ⊨
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗ stackAt s0.sp extHookStack ∗
            ((x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24)) ∗ R :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
      refine stepRustAlloc1_pred_cps hS hPl (P := fun sf => sf.fs = s0.fs) true
        libcruxHmacFrameBytes 64 (by decide) (by decide) hFit0 hrun rfl rfl rfl hsp
        (allocCallPreserved_refl s0) hmem0 _ ?_
      intro s1 pKey hpKey_ne hpKey_al16 hpKey_fit64 hs1_run hs1_sp hs1_regs hs1_vregs hpres1 hmem1
      simp only [↓reduceIte] at hmem1
      let st1 := M.step (.alloc 64) st
      have hmem1' : s1.mem ⊨
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim st1 s1 ∗ stackAt s0.sp extHookStack ∗
            (I.BlockM γ pKey 64 16 ∗ memRegion pKey 64 ∗
              (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24)) ∗ R :=
        Satisfies.mono (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (pointsTo_replicate_to_memRegion pKey 64))))))
          (Entails.of_eq (by sep_ac_rfl))) hmem1
      refine stepRustAlloc1_pred_cps hS hPl (P := fun sf => sf.fs = s0.fs) false
        libcruxHmacFrameBytes 64 (by decide) (by decide) hFit1 hs1_run hs1_sp hs1_regs hs1_vregs hsp
        hpres1 hmem1' _ ?_
      intro s2 pIpad hpIpad_ne hpIpad_al16 hpIpad_fit64 hs2_run hs2_sp hs2_regs hs2_vregs hpres2 hmem2
      simp only [Bool.false_eq_true, ↓reduceIte] at hmem2
      let st2 := M.step (.alloc 64) st1
      refine stepRustAlloc1_pred_cps hS hPl (P := fun sf => sf.fs = s0.fs) false
        libcruxHmacFrameBytes 64 (by decide) (by decide) hFit2 hs2_run hs2_sp hs2_regs hs2_vregs hsp
        hpres2
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem2 : s2.mem ⊨
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim st2 s2 ∗ stackAt s0.sp extHookStack ∗
            (I.BlockM γ pIpad 64 16 ∗ memRegion pIpad 64 ∗
              I.BlockM γ pKey 64 16 ∗ memRegion pKey 64 ∗
              (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24)) ∗ R) _ ?_
      intro s3 pOpad hpOpad_ne hpOpad_al16 hpOpad_fit64 hs3_run hs3_sp hs3_regs hs3_vregs hpres3 hmem3
      simp only [Bool.false_eq_true, ↓reduceIte] at hmem3
      let st3 := M.step (.alloc 64) st2
      refine stepRustDealloc1_pred_cps hS hPl (P := fun sf => sf.fs = s0.fs)
        libcruxHmacFrameBytes 64 pOpad hpOpad_ne hpOpad_al16 hpOpad_fit64 (by decide) (by decide)
        hs3_run hs3_sp hs3_regs hs3_vregs hsp hpres3 hmem3 _ ?_
      intro s4 hs4_run hs4_sp hs4_regs hs4_vregs hpres4 hmem4
      let st4 := M.step (.free 1 64) st3
      refine stepRustDealloc1_pred_cps hS hPl (P := fun sf => sf.fs = s0.fs)
        libcruxHmacFrameBytes 64 pIpad hpIpad_ne hpIpad_al16 hpIpad_fit64 (by decide) (by decide)
        hs4_run hs4_sp hs4_regs hs4_vregs hsp hpres4
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem4 : s4.mem ⊨
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim st4 s4 ∗ stackAt s0.sp extHookStack ∗
            I.BlockM γ pIpad 64 16 ∗ memRegion pIpad 64 ∗
            (I.BlockM γ pKey 64 16 ∗ memRegion pKey 64 ∗
              (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24)) ∗ R) _ ?_
      intro s5 hs5_run hs5_sp hs5_regs hs5_vregs hpres5 hmem5
      let st5 := M.step (.free 1 64) st4
      refine stepRustDealloc1_pred_cps hS hPl (P := fun sf => sf.fs = s0.fs)
        libcruxHmacFrameBytes 64 pKey hpKey_ne hpKey_al16 hpKey_fit64 (by decide) (by decide)
        hs5_run hs5_sp hs5_regs hs5_vregs hsp hpres5
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem5 : s5.mem ⊨
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim st5 s5 ∗ stackAt s0.sp extHookStack ∗
            I.BlockM γ pKey 64 16 ∗ memRegion pKey 64 ∗
            ((x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24)) ∗ R) _ ?_
      intro s6 hs6_run hs6_sp hs6_regs hs6_vregs hpres6 hmem6
      refine stepRustAlloc1_pred_cps hS hPl (P := fun sf => sf.fs = s0.fs) false
        libcruxHmacFrameBytes 32 (by decide) (by decide) hFit6 hs6_run hs6_sp hs6_regs hs6_vregs hsp
        hpres6 hmem6 _ ?_
      intro _ _ _ _ _ _ _ _ _ hpres7 _
      exact hpres7.1
  · unfold libcruxHmacHookMallocng
    split
    · rfl
    · dsimp only
      split
      · rfl
      · exact stepRustAlloc1_fs_of_not_running mpl true libcruxHmacFrameBytes 64 _ hrun

theorem libcruxHmacHookMallocng_preserves_fdsGe3Closed_of_pre
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (F : ShaState → List (BitVec 8) → ShaState)
    {x : LibcruxHmacCall} {st : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (libcruxHmacBudgetSpec F M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim).pre
        (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true)
    (hfds : FdsGe3Closed s0.fs) :
    FdsGe3Closed (libcruxHmacHookMallocng mpl F s0).fs := by
  rw [libcruxHmacHookMallocng_fs_eq_of_pre hS γ tp brkStart lim hPl F hpre hsp]
  exact hfds

theorem fineLibcruxHmacHookMallocng_preserves_fdsGe3Closed_of_pre
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (F : ShaState → List (BitVec 8) → ShaState)
    {x : LibcruxHmacCall} {st : fineCostModel.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (libcruxHmacBudgetSpec F fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim).pre
        (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true)
    (hfds : FdsGe3Closed s0.fs) :
    FdsGe3Closed (libcruxHmacHookMallocng mpl F s0).fs :=
  libcruxHmacHookMallocng_preserves_fdsGe3Closed_of_pre fineCostModelSound γ tp brkStart lim hPl F
    hpre hsp hfds

/-! ## Pre-Conditional `withFdsGe3Closed` Lifts -/

/-- Lift `HookOk f spec` to `HookOk f (withFdsGe3Closed spec)` when `f` preserves `FdsGe3Closed`
on running, `sp`-aligned states satisfying `spec.pre x s0 ∗ R`. -/
theorem hookOk_withFdsGe3Closed_of_pre {α : Type} {f : State → State} {spec : Spec α}
    (hpres : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.status = .Running → (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      FdsGe3Closed s0.fs → FdsGe3Closed (f s0).fs)
    (hok : HookOk f spec) :
    HookOk f (withFdsGe3Closed spec) := by
  intro x R s0 hrun hpre0 hsp
  obtain ⟨hClosed0, hpre⟩ := extract_withFdsGe3Closed hpre0
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpres x R s0 hrun hpre hsp hClosed0, hpost⟩
  · exact Or.inr hrest

theorem hookOk_withFdsGe3Closed_of_fs_eq_on_pre {α : Type} {f : State → State} {spec : Spec α}
    (hfs : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.status = .Running → (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      (f s0).fs = s0.fs)
    (hok : HookOk f spec) :
    HookOk f (withFdsGe3Closed spec) :=
  hookOk_withFdsGe3Closed_of_pre
    (fun x R s0 hrun hpre hsp hClosed0 => (hfs x R s0 hrun hpre hsp).symm ▸ hClosed0) hok

theorem hookSat_withFdsGe3Closed {α : Type} {abs : String → Option (State → State)}
    {name : String} {spec : Spec α}
    (hpres : ∀ f, abs name = some f → ∀ s : State, FdsGe3Closed s.fs → FdsGe3Closed (f s).fs)
    (hsat : HookSat abs name spec) :
    HookSat abs name (withFdsGe3Closed spec) := by
  obtain ⟨f, hH, hok⟩ := hsat
  exact ⟨f, hH, hookOk_withFdsGe3Closed (hpres f hH) hok⟩

theorem hookSat_withFdsGe3Closed_of_pre {α : Type} {abs : String → Option (State → State)}
    {name : String} {spec : Spec α}
    (hpres : ∀ f, abs name = some f → ∀ (x : α) (R : SepProp) (s0 : State),
      s0.status = .Running → (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      FdsGe3Closed s0.fs → FdsGe3Closed (f s0).fs)
    (hsat : HookSat abs name spec) :
    HookSat abs name (withFdsGe3Closed spec) := by
  obtain ⟨f, hH, hok⟩ := hsat
  exact ⟨f, hH, hookOk_withFdsGe3Closed_of_pre (hpres f hH) hok⟩

theorem aesEncHookMallocng_budget_withFdsGe3Closed_ok
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (E : AesKey → Block → Block) :
    HookOk (aesEncHookMallocng mpl E)
      (withFdsGe3Closed (aesEncBudgetSpec E M
        (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim)) :=
  hookOk_withFdsGe3Closed_of_fs_eq_on_pre
    (fun ⟨_, _⟩ _ _ _ hpre hsp =>
      aesEncHookMallocng_fs_eq_of_pre hS γ tp brkStart lim hPl E hpre hsp)
    (aesEncHookMallocng_budget_ok hS γ tp brkStart lim hPl E)

theorem aesEncFnHookMallocng_budget_withFdsGe3Closed_ok
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (E : AesKey → Block → Block) :
    HookOk (aesEncHookMallocng mpl E)
      (withFdsGe3Closed (aesEncFnBudgetSpec
        (fun pt k iv => aesCbcEncrypt E (bytesToKey32 k) (bytesToBlock iv) pt)
        M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim)) :=
  aesEncHookMallocng_budget_withFdsGe3Closed_ok hS γ tp brkStart lim hPl E

theorem fineAesEnc_budget_withFdsGe3Closed_hookOk (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (E : AesKey → Block → Block) :
    HookOk (aesEncHookMallocng mpl E)
      (withFdsGe3Closed (aesEncBudgetSpec E fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)) :=
  hookOk_withFdsGe3Closed_of_pre
    (fun ⟨_, _⟩ _ _ _ hpre hsp hfds =>
      fineAesEncHookMallocng_preserves_fdsGe3Closed_of_pre γ tp brkStart lim hPl E hpre hsp hfds)
    (fineAesEnc_budget_hookOk γ tp brkStart lim hPl E)

theorem fineAesEnc_budget_withFdsGe3Closed_hookSat
    {abs : String → Option (State → State)} {name : String}
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (E : AesKey → Block → Block)
    (hH : abs name = some (aesEncHookMallocng mpl E)) :
    HookSat abs name
      (withFdsGe3Closed (aesEncBudgetSpec E fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)) :=
  ⟨aesEncHookMallocng mpl E, hH, fineAesEnc_budget_withFdsGe3Closed_hookOk γ tp brkStart lim hPl E⟩

theorem aesDecHookMallocng_budget_withFdsGe3Closed_ok
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (D : AesKey → Block → Block) :
    HookOk (aesDecHookMallocng mpl D)
      (withFdsGe3Closed (aesDecBudgetSpec D M
        (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim)) :=
  hookOk_withFdsGe3Closed_of_fs_eq_on_pre
    (fun ⟨_, _⟩ _ _ _ hpre hsp =>
      aesDecHookMallocng_fs_eq_of_pre hS γ tp brkStart lim hPl D hpre hsp)
    (aesDecHookMallocng_budget_ok hS γ tp brkStart lim hPl D)

theorem aesDecWeakHookMallocng_budget_withFdsGe3Closed_ok
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (D : AesKey → Block → Block) :
    HookOk (aesDecHookMallocng mpl D)
      (withFdsGe3Closed (aesDecWeakBudgetSpec D M
        (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim)) :=
  hookOk_withFdsGe3Closed_of_pre
    (fun ⟨_, _⟩ _ _ _ hpre hsp hfds =>
      aesDecWeakHookMallocng_preserves_fdsGe3Closed_of_pre hS γ tp brkStart lim hPl D hpre hsp hfds)
    (aesDecWeakHookMallocng_budget_ok hS γ tp brkStart lim hPl D)

theorem fineAesDec_budget_withFdsGe3Closed_hookOk (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block) :
    HookOk (aesDecHookMallocng mpl D)
      (withFdsGe3Closed
        (aesDecBudgetSpec D fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)) :=
  hookOk_withFdsGe3Closed_of_pre
    (fun ⟨_, _⟩ _ _ _ hpre hsp hfds =>
      fineAesDecHookMallocng_preserves_fdsGe3Closed_of_pre γ tp brkStart lim hPl D hpre hsp hfds)
    (fineAesDec_budget_hookOk γ tp brkStart lim hPl D)

theorem fineAesDecWeak_budget_withFdsGe3Closed_hookOk (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block) :
    HookOk (aesDecHookMallocng mpl D)
      (withFdsGe3Closed
        (aesDecWeakBudgetSpec D fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)) :=
  hookOk_withFdsGe3Closed_of_pre
    (fun ⟨_, _⟩ _ _ _ hpre hsp hfds =>
      fineAesDecWeakHookMallocng_preserves_fdsGe3Closed_of_pre γ tp brkStart lim hPl D hpre hsp hfds)
    (fineAesDecWeak_budget_hookOk γ tp brkStart lim hPl D)

theorem fineAesDec_budget_withFdsGe3Closed_hookSat
    {abs : String → Option (State → State)} {name : String}
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block)
    (hH : abs name = some (aesDecHookMallocng mpl D)) :
    HookSat abs name
      (withFdsGe3Closed
        (aesDecBudgetSpec D fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)) :=
  ⟨aesDecHookMallocng mpl D, hH, fineAesDec_budget_withFdsGe3Closed_hookOk γ tp brkStart lim hPl D⟩

theorem fineAesDecWeak_budget_withFdsGe3Closed_hookSat
    {abs : String → Option (State → State)} {name : String}
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block)
    (hH : abs name = some (aesDecHookMallocng mpl D)) :
    HookSat abs name
      (withFdsGe3Closed
        (aesDecWeakBudgetSpec D fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)) :=
  ⟨aesDecHookMallocng mpl D, hH,
    fineAesDecWeak_budget_withFdsGe3Closed_hookOk γ tp brkStart lim hPl D⟩

theorem libcruxHmacHookMallocng_budget_withFdsGe3Closed_ok
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (F : ShaState → List (BitVec 8) → ShaState) :
    HookOk (libcruxHmacHookMallocng mpl F)
      (withFdsGe3Closed
        (libcruxHmacBudgetSpec F M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim)) :=
  hookOk_withFdsGe3Closed_of_fs_eq_on_pre
    (fun ⟨_, _⟩ _ _ _ hpre hsp =>
      libcruxHmacHookMallocng_fs_eq_of_pre hS γ tp brkStart lim hPl F hpre hsp)
    (libcruxHmacHookMallocng_budget_ok hS γ tp brkStart lim hPl F)

theorem fineLibcruxHmac_budget_withFdsGe3Closed_hookOk (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (F : ShaState → List (BitVec 8) → ShaState) :
    HookOk (libcruxHmacHookMallocng mpl F)
      (withFdsGe3Closed
        (libcruxHmacBudgetSpec F fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)) :=
  hookOk_withFdsGe3Closed_of_pre
    (fun ⟨_, _⟩ _ _ _ hpre hsp hfds =>
      fineLibcruxHmacHookMallocng_preserves_fdsGe3Closed_of_pre γ tp brkStart lim hPl F hpre hsp hfds)
    (fineLibcruxHmac_budget_hookOk γ tp brkStart lim hPl F)

theorem fineLibcruxHmac_budget_withFdsGe3Closed_hookSat
    {abs : String → Option (State → State)} {name : String}
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (F : ShaState → List (BitVec 8) → ShaState)
    (hH : abs name = some (libcruxHmacHookMallocng mpl F)) :
    HookSat abs name
      (withFdsGe3Closed
        (libcruxHmacBudgetSpec F fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)) :=
  ⟨libcruxHmacHookMallocng mpl F, hH,
    fineLibcruxHmac_budget_withFdsGe3Closed_hookOk γ tp brkStart lim hPl F⟩

/-! ## `cliExternsPlaced` and `cliGhostExterns` Row Coverage -/

private theorem list_lookup_mem {β : Type} {xs : List (String × β)} {k : String} {v : β}
    (h : xs.lookup k = some v) : (k, v) ∈ xs := by
  induction xs with
  | nil => nomatch h
  | cons p tl ih =>
    rcases p with ⟨k', v'⟩
    simp only [List.lookup] at h
    split at h
    · rename_i heq
      injection h with hv
      have hk : k = k' := beq_iff_eq.mp heq
      subst hk; subst hv
      exact List.Mem.head tl
    · exact List.Mem.tail _ (ih h)

private theorem table_cliPqxdhPlaced_nonMallocng_fdsGe3Closed
    (mmpl : Obj.MultiPlacement) (W : CliHooks) {sym : String} {f : State → State}
    (hne_hmac : sym ≠ lsLibcruxHmacSymCli)
    (hp : (sym, f) ∈ cliPqxdhHookTablePlaced mmpl W.C W.Q) :
    ∀ u : State, FdsGe3Closed u.fs → FdsGe3Closed (f u).fs := by
  simp only [cliPqxdhHookTablePlaced, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    first
    | (rcases Prod.mk.inj h with ⟨_, rfl⟩; exact fun _ hfs => hfs)
    | exact False.elim (hne_hmac (Prod.mk.inj h).1)
    | (rcases Prod.mk.inj h with ⟨_, rfl⟩
       intro u hfs; unfold mlkemEncaps1Hook retHook; dsimp only; split <;> exact hfs)

/-- Every row `sym` of `cliExternsPlaced mmpl W` outside the 3 `mallocng` crypto symbols
    (`lsAesEncSym`, `lsAesDecSym`, `lsLibcruxHmacSymCli`) preserves `FdsGe3Closed` unconditionally. -/
theorem cliExternsPlaced_nonMallocngSym_preserves_fdsGe3Closed
    (mmpl : Obj.MultiPlacement) (W : CliHooks) {sym : String} {f : State → State}
    (hne_enc : sym ≠ lsAesEncSym) (hne_dec : sym ≠ lsAesDecSym)
    (hne_hmac : sym ≠ lsLibcruxHmacSymCli) (hlook : cliExternsPlaced mmpl W sym = some f) :
    ∀ u : State, FdsGe3Closed u.fs → FdsGe3Closed (f u).fs := by
  unfold cliExternsPlaced at hlook
  split at hlook
  · injection hlook with hrf; subst hrf; exact fun _ hfs => hfs
  · have hp : (sym, f) ∈ cliHookTablePlaced mmpl W := list_lookup_mem hlook
    unfold cliHookTablePlaced at hp
    rw [List.mem_append] at hp
    rcases hp with hpq | hcli
    · exact table_cliPqxdhPlaced_nonMallocng_fdsGe3Closed mmpl W hne_hmac hpq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcli
      rcases hcli with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        first
        | (rcases Prod.mk.inj h with ⟨_, rfl⟩; exact fun _ hfs => hfs)
        | exact False.elim (hne_enc (Prod.mk.inj h).1)
        | exact False.elim (hne_dec (Prod.mk.inj h).1)
        | (rcases Prod.mk.inj h with ⟨_, rfl⟩; exact fun _ hfs => fdsGe3Closed_writeFileHook hfs)
        | (rcases Prod.mk.inj h with ⟨_, rfl⟩; exact fun _ hfs => fdsGe3Closed_writeStdoutHook hfs)
        | (rcases Prod.mk.inj h with ⟨_, rfl⟩
           intro u hfs; unfold strlenHook; dsimp only; split <;> exact hfs)
        | (rcases Prod.mk.inj h with ⟨_, rfl⟩
           intro u hfs; unfold memrchrHook; dsimp only; split <;> first | exact hfs | (split <;> exact hfs))
        | (rcases Prod.mk.inj h with ⟨_, rfl⟩
           intro u hfs; unfold fromUtf8Hook; dsimp only; split <;> first | exact hfs | (split <;> exact hfs))
        | (rcases Prod.mk.inj h with ⟨_, rfl⟩
           intro u hfs; unfold durationSinceExactHook; dsimp only; split <;> first | exact hfs | (split <;> exact hfs))
        | (rcases Prod.mk.inj h with ⟨_, rfl⟩
           intro u hfs; unfold timeAddHook; dsimp only; split <;> split <;> exact hfs)

theorem cliExternsPlaced_nonMallocngSym_hookSat_withFdsGe3Closed
    {α : Type} (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {sym : String} {spec : Spec α}
    (hsat : HookSat (cliExternsPlaced mmpl W) sym spec)
    (hne_enc : sym ≠ lsAesEncSym := by decide)
    (hne_dec : sym ≠ lsAesDecSym := by decide)
    (hne_hmac : sym ≠ lsLibcruxHmacSymCli := by decide) :
    HookSat (cliExternsPlaced mmpl W) sym (withFdsGe3Closed spec) :=
  hookSat_withFdsGe3Closed
    (fun _ hH =>
      cliExternsPlaced_nonMallocngSym_preserves_fdsGe3Closed mmpl W hne_enc hne_dec hne_hmac hH)
    hsat

theorem cliExternsPlaced_aesEnc_withFdsGe3Closed_hookSat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (W : CliHooks) (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliExternsPlaced mmpl W) lsAesEncSym
      (withFdsGe3Closed (aesEncBudgetSpec W.C.E fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :=
  fineAesEnc_budget_withFdsGe3Closed_hookSat γ tp brkStart lim hPl W.C.E
    (cliExternsPlaced_row mmpl W (aesEnc_row_placed mmpl W))

theorem cliGhostExterns_aesEnc_withFdsGe3Closed_hookSat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
      (withFdsGe3Closed (aesEncBudgetSpec W.C.E fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :=
  cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
    (cliExternsPlaced_aesEnc_withFdsGe3Closed_hookSat γ mmpl tp brkStart lim W hPl)

theorem cliExternsPlaced_aesDec_withFdsGe3Closed_hookSat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (W : CliHooks) (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliExternsPlaced mmpl W) lsAesDecSym
      (withFdsGe3Closed (aesDecBudgetSpec W.C.D fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :=
  fineAesDec_budget_withFdsGe3Closed_hookSat γ tp brkStart lim hPl W.C.D
    (cliExternsPlaced_row mmpl W (aesDec_row_placed mmpl W))

theorem cliGhostExterns_aesDec_withFdsGe3Closed_hookSat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (withFdsGe3Closed (aesDecBudgetSpec W.C.D fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :=
  cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
    (cliExternsPlaced_aesDec_withFdsGe3Closed_hookSat γ mmpl tp brkStart lim W hPl)

theorem cliExternsPlaced_aesDecWeak_withFdsGe3Closed_hookSat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (W : CliHooks) (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliExternsPlaced mmpl W) lsAesDecSym
      (withFdsGe3Closed (aesDecWeakBudgetSpec W.C.D fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :=
  fineAesDecWeak_budget_withFdsGe3Closed_hookSat γ tp brkStart lim hPl W.C.D
    (cliExternsPlaced_row mmpl W (aesDec_row_placed mmpl W))

theorem cliGhostExterns_aesDecWeak_withFdsGe3Closed_hookSat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (withFdsGe3Closed (aesDecWeakBudgetSpec W.C.D fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :=
  cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
    (cliExternsPlaced_aesDecWeak_withFdsGe3Closed_hookSat γ mmpl tp brkStart lim W hPl)

theorem cliExternsPlaced_libcruxHmac_withFdsGe3Closed_hookSat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (W : CliHooks) (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliExternsPlaced mmpl W) lsLibcruxHmacSymCli
      (withFdsGe3Closed (libcruxHmacBudgetSpec W.C.F fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :=
  fineLibcruxHmac_budget_withFdsGe3Closed_hookSat γ tp brkStart lim hPl W.C.F
    (cliExternsPlaced_row mmpl W (libcruxHmac_row_placed mmpl W))

theorem cliGhostExterns_libcruxHmac_withFdsGe3Closed_hookSat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (withFdsGe3Closed (libcruxHmacBudgetSpec W.C.F fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :=
  cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
    (cliExternsPlaced_libcruxHmac_withFdsGe3Closed_hookSat γ mmpl tp brkStart lim W hPl)

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds
