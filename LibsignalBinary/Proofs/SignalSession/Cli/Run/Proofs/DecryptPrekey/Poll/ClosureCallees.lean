/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.E2E.Pqxdh.TopLevel.SessionRecvPrekeyClosureCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Pure and Crypto Callee Discharges for `cliDpPollName`

Discharges the pure, allocator, clone, drop, Bob-session-init, stack-frame arithmetic, and
filesystem invariant obligations on `tripleRatchetProgAtExt img.base (cliExterns W)` from
`Obj.Loads libsignalSessionImage img` and `RunHooks img E2E.HooksE.A0 (cliExterns W)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 2. `AllocContracts`, `ChainClone3`, `SenderChainClone3`, & `DropSessionStructure3` from `RunHooks` -/

theorem cliAllocContracts {img : Obj.Image} {W : CliHooks}
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W)) :
    AllocContracts img.base E2E.HooksE.A0 (cliExterns W) :=
  hh.allocContracts

theorem cliAllocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hh : RunHooksExt img A ext) :
    CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext :=
  hh.alloc

theorem cliChainClone3_ok {img : Obj.Image} {W : CliHooks}
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W)) :
    ChainClone3OkExt img.base E2E.HooksE.A0 (cliExterns W) :=
  chainClone3_ok_ext hh.allocContracts

theorem cliSenderChainClone3_ok {img : Obj.Image} {W : CliHooks}
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W)) :
    SenderChainClone3OkExt img.base E2E.HooksE.A0 (cliExterns W) :=
  senderChainClone3_ok_ext hh.allocContracts

theorem cliDropSessionStructure3_ok {img : Obj.Image} {W : CliHooks}
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W)) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Spec
        E2E.HooksE.A0) :=
  drop_session_structure3_ok_ext hh.allocContracts

theorem cliBase_aligned {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) :
    (img.base &&& 0xfff#64) = 0#64 :=
  base_aligned himg

theorem cliExterns_blackBox (W : CliHooks) :
    Rust.withPanics (cliExterns W) "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook := by
  have h := Cli.Slots.cliExterns_agree W 0#64 (n := "subtle::black_box::<u8>") (by decide)
  simpa [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns,
    CryptoVerification.LibsignalSession.sessionExterns,
    dhName, pubFromSecretName, staticDropName, sharedDropName, rngFillName, noHookNames] using h.symm

/-! ## 3. Closure Entry Stack Frame Arithmetic (`s0.sp` vs `sp = s0.sp - 0xcd0#64`) -/

theorem dpPollFrame_le_need (B : RunBudgets) : dpPollFrame ≤ dpPollNeed B := by
  unfold dpPollFrame dpPollNeed; omega

theorem sp_frame_sub_add (sp0 : BitVec 64) : (sp0 - 0xcd0#64) + 0xcd0#64 = sp0 := by
  bv_omega

theorem sp_frame_toNat_eq {sp0 : BitVec 64} {B : RunBudgets} {stk' : Nat}
    (hneed : dpPollNeed B ≤ stk') (hsp : stk' ≤ sp0.toNat) :
    (sp0 - 0xcd0#64).toNat = sp0.toNat - dpPollFrame ∧
      stk' - dpPollFrame ≤ (sp0 - 0xcd0#64).toNat := by
  have hf : dpPollFrame ≤ sp0.toNat := Nat.le_trans (dpPollFrame_le_need B) (Nat.le_trans hneed hsp)
  dsimp only [dpPollFrame] at hf ⊢
  have hsub : (sp0 - 0xcd0#64).toNat = sp0.toNat - 3280 := by
    have hlt := sp0.isLt
    bv_omega
  exact ⟨hsub, by omega⟩

theorem stackAt_dpPoll_entry_split (sp0 : BitVec 64) {B : RunBudgets} {stk' : Nat}
    (hneed : dpPollNeed B ≤ stk') (hstk64 : stk' ≤ 2 ^ 63) :
    stackAt sp0 stk' =
      memRegion (sp0 - BitVec.ofNat 64 stk') (stk' - dpPollFrame) ∗
      memRegion (sp0 - 0xcd0#64) dpPollFrame := by
  have hf : dpPollFrame ≤ stk' := Nat.le_trans (dpPollFrame_le_need B) hneed
  have h := CryptoVerification.E2E.Pqxdh.TopLevel.stackAt_sub_split sp0 stk' dpPollFrame hf (by omega)
  dsimp only [dpPollFrame, stackAt] at h ⊢
  exact h

theorem dpClosSubStack_le_dpPollSub (B : RunBudgets) {stk' : Nat} (hneed : dpPollNeed B ≤ stk') :
    dpClosSubStack B ≤ stk' - dpPollFrame := by
  dsimp only [dpClosSubStack, dpPollNeed, dpPollFrame] at hneed ⊢
  omega

theorem dpClosSubStack_le_sp_sub {sp0 : BitVec 64} {B : RunBudgets} {stk' : Nat}
    (hneed : dpPollNeed B ≤ stk') (hsp : stk' ≤ sp0.toNat) :
    dpClosSubStack B ≤ (sp0 - 0xcd0#64).toNat :=
  Nat.le_trans (dpClosSubStack_le_dpPollSub B hneed) (sp_frame_toNat_eq hneed hsp).2

theorem rootStack_le_dpPollSub (B : RunBudgets) {stk' : Nat} (hneed : dpPollNeed B ≤ stk') :
    CryptoVerification.LibsignalTripleRatchet.rootStack ≤ stk' - dpPollFrame := by
  have hr : CryptoVerification.LibsignalTripleRatchet.rootStack ≤ 524288 := by decide
  dsimp only [dpPollNeed, dpPollFrame] at hneed ⊢
  omega

theorem stageP1CallStack_le_subStack {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (B : RunBudgets) :
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP1CallStack
      (cliPollSessKit A b F0 Scope peer (cliKitStk B))
      (cliPollIdKit A b F0 peer (cliKitStk B)) ≤ dpClosSubStack B :=
  Nat.le_trans (Nat.le_max_left _ _) (stageP1UntrustedCallStack_le_subStack b F0 Scope peer B)

/-! ## 4. Filesystem Invariant (`FsAt` & `TraceFsSound`) Helpers -/

theorem cliFsAt_of_files_eq {img : Obj.Image} {W : CliHooks} {envOk : FsFiles → Prop} {Q : Prop}
    {F0 : FsFiles} {s : State}
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hQ : Q) (henv : envOk F0) (hf : s.fs.files = F0) :
    FsAt envOk Q (tripleRatchetProgAtExt img.base (cliExterns W)) s :=
  .inr ⟨hQ, hh.fs, hf ▸ henv⟩

theorem cliFiles_eq_of_trace_eq {img : Obj.Image} {W : CliHooks} {s0 sf : State}
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hst : Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf)
    (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  hh.fs.files_eq hst (evs := []) (by rw [htr, List.append_nil]) NoFsEv.nil

theorem cliSlotTraceFT_of_trace_eq {img : Obj.Image} {W : CliHooks} {s0 sf : State}
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hst : Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf)
    (htr : sf.trace = s0.trace) :
    slotTraceFT s0.fs s0.trace sf.fs sf.trace :=
  ⟨htr ▸ List.prefix_refl s0.trace,
   cliFiles_eq_of_trace_eq hh hst htr,
   congrArg (ProcessOutcome.traceStreamBytes .stdout) htr⟩

theorem cliFsAt_of_files_eq_ext {img : Obj.Image} {ext : String → Option (State → State)}
    {envOk : FsFiles → Prop} {Q : Prop} {F0 : FsFiles} {s : State}
    (hfs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hQ : Q) (henv : envOk F0) (hf : s.fs.files = F0) :
    FsAt envOk Q (tripleRatchetProgAtExt img.base ext) s :=
  .inr ⟨hQ, hfs, hf ▸ henv⟩

theorem cliFiles_eq_of_trace_eq_ext {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 sf : State}
    (hfs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hst : Steps (tripleRatchetProgAtExt img.base ext) s0 sf)
    (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  hfs.files_eq hst (evs := []) (by rw [htr, List.append_nil]) NoFsEv.nil

theorem cliSlotTraceFT_of_trace_eq_ext {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 sf : State}
    (hfs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hst : Steps (tripleRatchetProgAtExt img.base ext) s0 sf)
    (htr : sf.trace = s0.trace) :
    slotTraceFT s0.fs s0.trace sf.fs sf.trace :=
  ⟨htr ▸ List.prefix_refl s0.trace,
   cliFiles_eq_of_trace_eq_ext hfs hst htr,
   congrArg (ProcessOutcome.traceStreamBytes .stdout) htr⟩

theorem cliFsAt_of_runHooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {envOk : FsFiles → Prop} {Q : Prop}
    {F0 : FsFiles} {s : State}
    (hh : RunHooksExt img A ext)
    (hQ : Q) (henv : envOk F0) (hf : s.fs.files = F0) :
    FsAt envOk Q (tripleRatchetProgAtExt img.base ext) s :=
  cliFsAt_of_files_eq_ext hh.fs hQ henv hf

theorem cliFiles_eq_of_runHooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {s0 sf : State}
    (hh : RunHooksExt img A ext)
    (hst : Steps (tripleRatchetProgAtExt img.base ext) s0 sf)
    (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  cliFiles_eq_of_trace_eq_ext hh.fs hst htr

theorem cliSlotTraceFT_of_runHooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {s0 sf : State}
    (hh : RunHooksExt img A ext)
    (hst : Steps (tripleRatchetProgAtExt img.base ext) s0 sf)
    (htr : sf.trace = s0.trace) :
    slotTraceFT s0.fs s0.trace sf.fs sf.trace :=
  cliSlotTraceFT_of_trace_eq_ext hh.fs hst htr

/-- `subroutine_ok` from `SepWPp` at entry, additionally exposing `Steps prog s0 sf` to the
return and panic postcondition obligations (used to discharge `TraceFsSound.files_eq`). -/
theorem subroutine_ok_of_sepWPp_steps {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f =>
            (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
              sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f =>
            Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hL
  obtain ⟨P, Fr, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  obtain ⟨sf, hsteps, hout⟩ := hwp Fr hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hq, hspf, hcsf⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hmo⟩
  · exact reaches_outcome_steps hsteps
      (reaches_outcome.of_outcome (Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, hq hsteps hmf⟩))
  · exact reaches_outcome_steps hsteps
      (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, hqp hsteps hmf⟩)))
  · exact (not_satisfies_false_sepConj hmo).elim

end CryptoVerification.SignalSession.Cli.RunProofs.Poll

