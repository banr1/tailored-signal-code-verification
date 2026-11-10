/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Defs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollFetches
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
public import LibsignalBinary.Specifications.AsmConstants -- shake: keep

/-!
# `IdentityFiles::get_local_registration_id::{closure#0}` Poll Verification

Verifies `get_local_registration_id::{closure#0}` against `idRegIdPollSpec`, reading
`"registration-id"` via `Dir::get`, parsing a 4-byte little-endian `u32` on length `4`, and
allocating `"malformed file"` (`InvalidState`) otherwise.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalSession
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace RegNorm

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).trace = s.trace := by cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (idx : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setMem_pre (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setPState_pre (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) (idx : BitVec 5) :
    (s.writeReg32 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64)
    (idx : BitVec 5) :
    (s.writeReg w r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem cap_reconstruct_norm (cap : BitVec 64) :
    ((cap.truncate 32).zeroExtend 64 |||
      (((cap >>> 32).truncate 32).zeroExtend 64 <<< 32)) = cap :=
  PollCommon.cap_reconstruct_u32_pair cap

@[local arm64_norm ↓, local wp_norm ↓]
theorem speWord_one_eq : speWord 1 = asm64% speNicheBase + 1#64 := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem okTagVec_eq_neg2 : okTagVec = -2#64 := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem awc_speWord1_two :
    (AddWithCarry64 (speWord 1) 2#64 false).2.z = false := by decide +kernel

@[local arm64_norm ↓, local wp_norm ↓]
theorem awc_okTagVec_two :
    (AddWithCarry64 okTagVec 2#64 false).2.z = true := by decide +kernel

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate32_zeroExtend64 (v : BitVec 32) :
    (v.zeroExtend 64).truncate 32 = v := by bv_bits

private theorem malformedFileStrAddr_add_6 (b : BitVec 64) :
    malformedFileStrAddr b + 6#64 =
      b + bv% (ls_xref%
        (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}" + 156)
        (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}" + 160) + 6) := by
  unfold malformedFileStrAddr
  rw [BitVec.add_assoc]
  rfl

end RegNorm

open RegNorm

/-! ## Inner Specification and Symbolic Execution -/

abbrev regCalleeStk (getStk : Nat) : Nat :=
  max getStk extHookStack

private def cliIdRegIdPollInnerSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (img : Obj.Image) (w0 wTail : BitVec 64) (calleeStk : Nat) :
    Spec IdOwnPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.own.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.own.path (utf8 "registration-id"))⌝ ∗
      (idRegIdFileNameAddr img.base ↦ᵣ utf8 "registration-id") ∗
      (malformedFileStrAddr img.base ↦₆₄ᵣ w0) ∗
      ((malformedFileStrAddr img.base + 6#64) ↦₆₄ᵣ wTail) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 0#8) ∗
      dirAt A x.self x.own ∗
      memRegion x.out 48 ∗ A.pool ∗
      stackAt (s.sp - 112#64) calleeStk ∗ cells (s.sp - 112#64) 14
  post := fun x s0 sf =>
    regPostAns A x.out ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files) s0 sf ∗
      (idRegIdFileNameAddr img.base ↦ᵣ utf8 "registration-id") ∗
      (malformedFileStrAddr img.base ↦₆₄ᵣ w0) ∗
      ((malformedFileStrAddr img.base + 6#64) ↦₆₄ᵣ wTail) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗
      dirAt A x.self x.own ∗
      A.pool ∗
      stackAt (s0.sp - 112#64) calleeStk ∗ cells (s0.sp - 112#64) 14
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private def cliIdRegIdPollExpandedSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (img : Obj.Image) (w0 wTail : BitVec 64) (calleeStk : Nat) :
    Spec IdOwnPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.own.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.own.path (utf8 "registration-id"))⌝ ∗
      (idRegIdFileNameAddr img.base ↦ᵣ utf8 "registration-id") ∗
      (malformedFileStrAddr img.base ↦₆₄ᵣ w0) ∗
      ((malformedFileStrAddr img.base + 6#64) ↦₆₄ᵣ wTail) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 0#8) ∗
      dirAt A x.self x.own ∗
      memRegion x.out 48 ∗ A.pool ∗
      stackAt (s.sp - 112#64) calleeStk ∗
      (memRegion (s.sp - 112#64) 48 ∗
        (∃∗ s29 : BitVec 64, (s.sp - 64#64) ↦₆₄ s29) ∗
        (∃∗ s30 : BitVec 64, (s.sp - 56#64) ↦₆₄ s30) ∗
        (∃∗ s23 : BitVec 64, (s.sp - 48#64) ↦₆₄ s23) ∗
        (∃∗ sPad : BitVec 64, (s.sp - 40#64) ↦₆₄ sPad) ∗
        (∃∗ s22 : BitVec 64, (s.sp - 32#64) ↦₆₄ s22) ∗
        (∃∗ s21 : BitVec 64, (s.sp - 24#64) ↦₆₄ s21) ∗
        (∃∗ s20 : BitVec 64, (s.sp - 16#64) ↦₆₄ s20) ∗
        (∃∗ s19 : BitVec 64, (s.sp - 8#64) ↦₆₄ s19))
  post := fun x s0 sf =>
    regPostAns A x.out ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files) s0 sf ∗
      (idRegIdFileNameAddr img.base ↦ᵣ utf8 "registration-id") ∗
      (malformedFileStrAddr img.base ↦₆₄ᵣ w0) ∗
      ((malformedFileStrAddr img.base + 6#64) ↦₆₄ᵣ wTail) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗
      dirAt A x.self x.own ∗
      A.pool ∗
      stackAt (s0.sp - 112#64) calleeStk ∗
      (memRegion (s0.sp - 112#64) 48 ∗
        (∃∗ s29 : BitVec 64, (s0.sp - 64#64) ↦₆₄ s29) ∗
        (∃∗ s30 : BitVec 64, (s0.sp - 56#64) ↦₆₄ s30) ∗
        (∃∗ s23 : BitVec 64, (s0.sp - 48#64) ↦₆₄ s23) ∗
        (∃∗ sPad : BitVec 64, (s0.sp - 40#64) ↦₆₄ sPad) ∗
        (∃∗ s22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ s22) ∗
        (∃∗ s21 : BitVec 64, (s0.sp - 24#64) ↦₆₄ s21) ∗
        (∃∗ s20 : BitVec 64, (s0.sp - 16#64) ↦₆₄ s20) ∗
        (∃∗ s19 : BitVec 64, (s0.sp - 8#64) ↦₆₄ s19))
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem cliIdRegIdPollExpandedSpec_eq (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (img : Obj.Image) (w0 wTail : BitVec 64) (calleeStk : Nat) :
    cliIdRegIdPollExpandedSpec rd pathOk A img w0 wTail calleeStk =
      cliIdRegIdPollInnerSpec rd pathOk A img w0 wTail calleeStk := by
  unfold cliIdRegIdPollExpandedSpec cliIdRegIdPollInnerSpec
  congr 1
  · funext x s; rw [cells_14_reg s.sp]
  · funext x s0 sf; rw [cells_14_reg s0.sp]

set_option maxHeartbeats 1200000 in
private theorem idRegIdPollInner_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {w0 wTail : BitVec 64} {getStk : Nat}
    (hC : AllocContractsX img A ext)
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hhi : regCalleeStk getStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idRegIdPollName)
      ((cliIdRegIdPollInnerSpec rd pathOk A img w0 wTail (regCalleeStk getStk)).inImage img) := by
  let calleeStk := regCalleeStk getStk
  rw [← cliIdRegIdPollExpandedSpec_eq]
  unfold Spec.inImage
  simp (config := { maxSteps := 2000000 }) only [cliIdRegIdPollExpandedSpec,
    sepExists_sepConj_left, sepExists_sepConj_right]
  rw [malformedFileStrAddr_add_6 img.base]
  have hfn : libsignalSessionCode.fnOff idRegIdPollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") :=
    idRegIdPoll_fnOff
  have hGetCells := dirGetRo_cells_ok (calleeStk := calleeStk) hGet
    (by dsimp [calleeStk, regCalleeStk]; omega) hhi
  have hDeallocCells := deallocAt_cells_ok (calleeStk := calleeStk) hC reg_dealloc_fnOff_rel
    (by dsimp [calleeStk, regCalleeStk]; omega) hhi
  have hShimCells := shimAt_cells_ok (calleeStk := calleeStk) hC
    (by dsimp [calleeStk, regCalleeStk]; omega) hhi
  have hAllocCells := alloc14At_cells_ok (calleeStk := calleeStk) hC
    (by dsimp [calleeStk, regCalleeStk]; omega) hhi
  have hPanic := panic_at_handle_error_ext img.base ext idRegIdPollName
    (num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
      "alloc::raw_vec::handle_error"))
    reg_handle_error_fnOff_rel
  rw [reg_dirGet_fnAddr_eq] at hGetCells
  have hadrp40 := idRegIdPoll_adrp_40 (H := Rust.withPanics ext) hb
  have hadrp156 := idRegIdPoll_adrp_156 (H := Rust.withPanics ext) hb
  have hadrp216 := idRegIdPoll_adrp_216 (H := Rust.withPanics ext) hb
  code_fetches CryptoVerification.libsignalSessionCode cliIdRegIdPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}")) 308
  dsimp only [tripleRatchetProgAtExt] at hGetCells hDeallocCells hShimCells hAllocCells hPanic ⊢
  clear hfn hGet hC
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr idRegIdPollName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hname_len : (utf8 "registration-id").length = 15 := utf8_regId_length
  have hname_lt : (utf8 "registration-id").length < 2 ^ 32 := by
    rw [utf8_regId_length]; decide
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (2 ^ 64 + ls_off% "<libsignal_cli::stores::Dir>::get" -
      ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"))
    hinv0
  wp_steps
  apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
  intro hinv1
  wp_call_inImage hGetCells hinv1
    (s0.sp - 112#64, x.self, x.own,
      idRegIdFileNameAddr img.base, utf8 "registration-id", s0.sp - 112#64)
  case panic =>
    intro sf_p _ hm
    dsimp only at hm
    exact close_panic_subgoal s0 hm (by simp only [wp_norm, arm64_norm, *])
  have h_reg0 : sf.sp = s0.sp - 112#64 ∧
      sf.readReg64 (.gpr 19#5) = x.fut ∧
      sf.readReg64 (.gpr 20#5) = x.out ∧
      sf.readReg64 (.gpr 29#5) = s0.sp - 64#64 :=
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  rcases h_reg0 with ⟨_, _, _, _⟩
  cases w with
  | error u =>
    cases u
    have hget_err : .error () = x.own.get rd s0.fs.files (utf8 "registration-id") ∧
        sf.trace = s0.trace := ⟨by assumption, by assumption⟩
    have hans_err : (IdGhost.mk x.own (.new [])).regId rd s0.fs.files = .error () := by
      unfold IdGhost.regId
      rw [← hget_err.1]
      rfl
    apply SepWPp.of_sepWP_ret
    apply SepWP.focus_rw (getResultAt_err_sp_112 A s0.sp)
    wp_pull_exists
    apply SepWP.focus_rw (out_48_reg_split x.out)
    wp_pull_exists
    wp_steps
    apply SepWP.focus_weaken (sp_112_err_fold_48 s0.sp _ _ _ _ _ _ _)
    apply SepWP.focus_weaken (out_reg_err_read_fold A x.out _ _ _ _)
    refine focus_regPostAns A x.out
      ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files)
      (.error ()) s0 (by sep_focus) ?_ ?_
    · exact ⟨hans_err.symm, by simp only [wp_norm, arm64_norm, *]⟩
    wp_done
  | ok bs =>
    have hget_ok : .ok bs = x.own.get rd s0.fs.files (utf8 "registration-id") ∧
        sf.trace = s0.trace := ⟨by assumption, by assumption⟩
    rw [getResultAt_ok_sp_112 A s0.sp bs]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bCap
    apply SepWPp.exists_elim; intro bPtr
    apply SepWPp.pure_elim; rintro ⟨hbCap_le, hbCap_lt, hbPtr_ne⟩
    by_cases hlen4 : bs.length = 4
    ·
      match bs, hlen4 with
      | [b0, b1, b2, b3], _ =>
        have hans_ok : (IdGhost.mk x.own (.new [])).regId rd s0.fs.files =
            .ok (b3 ++ b2 ++ b1 ++ b0) := by
          unfold IdGhost.regId
          rw [← hget_ok.1]
          rfl
        have hbCap_ne : bCap ≠ 0#64 :=
          Store.IdTrustPoll.Helpers.cap_ne_zero_of_cons hbCap_le
        have hbCap_beq : (bCap == 0#64) = false := beq_false_of_ne hbCap_ne
        apply SepWPp.of_sepWP_inImage
          (mid := fnBase + BitVec.ofNat 64 (num% (ls_rel%
            "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
            "__rustc::__rust_dealloc")))
          (by assumption)
        apply SepWP.focus_rw (pointsToBytes4_eq_pointsTo32 bPtr b0 b1 b2 b3)
        wp_steps
        apply SepWP.focus_rw (pointsToBytes4_eq_pointsTo32 bPtr b0 b1 b2 b3).symm
        apply SepWP.focus_weaken (sp_112_ok_fold_48 s0.sp _ _ _ _ _)
        apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
        intro hinv_d0
        wp_call_inImage hDeallocCells hinv_d0 (bPtr, bCap, [b0, b1, b2, b3], s0.sp - 112#64)
        case panic =>
          intro sf_p _ hm
          dsimp only at hm
          simpa only [sepConj_assoc] using close_panic_subgoal s0 hm (by simp only [wp_norm, arm64_norm, *])
        have h_reg_b2 : sf_1.sp = s0.sp - 112#64 ∧
            sf_1.readReg64 (.gpr 19#5) = x.fut ∧
            sf_1.readReg64 (.gpr 20#5) = x.out ∧
            sf_1.readReg64 (.gpr 22#5) = (b3 ++ b2 ++ b1 ++ b0).zeroExtend 64 :=
          ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
           by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
        rcases h_reg_b2 with ⟨_, _, _, _⟩
        apply SepWPp.of_sepWP_ret
        apply SepWP.focus_rw (out_48_reg_split x.out)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_weaken (out_reg_ok_fold A x.out (b3 ++ b2 ++ b1 ++ b0) _ _ _ _ _)
        refine focus_regPostAns A x.out
          ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files)
          (.ok (b3 ++ b2 ++ b1 ++ b0)) s0 (by sep_focus) ?_ ?_
        · exact ⟨hans_ok.symm, by simp only [wp_norm, arm64_norm, *]⟩
        wp_done
    ·
      have hans_err4 : (IdGhost.mk x.own (.new [])).regId rd s0.fs.files = .error () := by
        unfold IdGhost.regId
        rw [← hget_ok.1]
        exact match_regId_ne_4 hlen4
      have hlen_lt : bs.length < 2 ^ 63 := Nat.lt_of_le_of_lt hbCap_le hbCap_lt
      have hne4_bv : BitVec.ofNat 64 bs.length ≠ 4#64 := len_bv_ne_four_of_ne hlen_lt hlen4
      have hne4_beq : (BitVec.ofNat 64 bs.length == 4#64) = false := beq_false_of_ne hne4_bv
      have hne4_sub : (BitVec.ofNat 64 bs.length - 4#64 == 0#64) = false :=
        beq_false_of_ne (fun h => hne4_bv (by bv_omega))
      have hne4_awc : (AddWithCarry64 (BitVec.ofNat 64 bs.length) (~~~4#64) true).2.z = false := by
        unfold AddWithCarry64
        simp only [ite_true]
        exact beq_false_of_ne (fun h => hne4_bv (by bv_omega))
      apply SepWPp.of_sepWP_inImage
        (mid := fnBase + BitVec.ofNat 64 (num% (ls_rel%
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2")))
        (by assumption)
      wp_steps
      apply SepWP.focus_weaken (sp_112_ok_fold_48 s0.sp _ _ _ _ _)
      apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
      intro hinv_s
      wp_call_inImage hShimCells hinv_s (s0.sp - 112#64)
      case panic =>
        intro sf_p _ hm
        dsimp only at hm
        simpa only [sepConj_assoc] using close_panic_subgoal s0 hm (by simp only [wp_norm, arm64_norm, *])
      have h_reg_s : sf_1.sp = s0.sp - 112#64 ∧
          sf_1.readReg64 (.gpr 19#5) = x.fut ∧
          sf_1.readReg64 (.gpr 20#5) = x.out ∧
          sf_1.readReg64 (.gpr 21#5) = bPtr ∧
          sf_1.readReg64 (.gpr 23#5) = bCap :=
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]; exact PollCommon.cap_reconstruct_u32_pair bCap⟩
      rcases h_reg_s with ⟨_, _, _, _, _⟩
      apply SepWPp.of_sepWP_inImage
        (mid := fnBase + BitVec.ofNat 64 (num% (ls_rel%
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
          "__rustc::__rust_alloc")))
        (by assumption)
      wp_steps
      apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
      intro hinv_a
      wp_call_inImage hAllocCells hinv_a (s0.sp - 112#64)
      case panic =>
        intro sf_p _ hm
        dsimp only at hm
        simpa only [sepConj_assoc] using close_panic_subgoal s0 hm (by simp only [wp_norm, arm64_norm, *])
      have h_reg_a : sf_2.sp = s0.sp - 112#64 ∧
          sf_2.readReg64 (.gpr 19#5) = x.fut ∧
          sf_2.readReg64 (.gpr 20#5) = x.out ∧
          sf_2.readReg64 (.gpr 21#5) = bPtr ∧
          sf_2.readReg64 (.gpr 23#5) = bCap :=
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]; exact PollCommon.cap_reconstruct_u32_pair bCap⟩
      rcases h_reg_a with ⟨_, _, _, _, _⟩
      by_cases hbuf0 : sf_2.readReg64 (.gpr 0#5) = 0#64
      ·
        have hbuf0' : sf_2.readReg64 .x0 = 0#64 := hbuf0
        simp only [hbuf0', ite_true]
        rw [← sepConj_assoc, sepConj_comm (A.pool ∗ stackAt (s0.sp - 112#64) calleeStk), sepConj_assoc]
        apply SepWPp.pure_elim; intro htr_oom
        apply SepWPp.of_sepWP
          (mid := fnBase + BitVec.ofNat 64 (num% (ls_rel%
            "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
            "alloc::raw_vec::handle_error")))
        wp_steps
        apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
        refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked
            (LibsignalTripleRatchet.allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
      ·
        have hbuf_ne : sf_2.readReg64 .x0 ≠ 0#64 := hbuf0
        have hbuf_beq : (sf_2.readReg64 (.gpr 0#5) == 0#64) = false := beq_false_of_ne hbuf0
        simp only [hbuf_ne, ite_false]
        rw [← sepConj_assoc, sepConj_comm (A.pool ∗ stackAt (s0.sp - 112#64) calleeStk), sepConj_assoc]
        simp only [sepConj_assoc]
        apply SepWPp.pure_elim; intro htr_alloc
        by_cases hc0 : bCap = 0#64
        ·
          subst hc0
          have hbs_nil : bs = [] := by
            cases bs with
            | nil => rfl
            | cons _ _ => simp at hbCap_le
          subst hbs_nil
          apply SepWPp.of_sepWP_ret
          have hemp : ((bPtr ↦ₛ ([] : List (BitVec 8))) ∗
              Store.IdTrustPoll.Helpers.vecU8BufRest A 0#64 bPtr 0) = emp := by
            simp [Store.IdTrustPoll.Helpers.vecU8BufRest]
          apply SepWP.focus_rw hemp
          apply SepWP.focus_rw (PollCommon.memRegion_14_split_8_6 (sf_2.readReg64 .x0))
          wp_pull_exists
          apply SepWP.focus_rw (out_48_reg_split x.out)
          wp_pull_exists
          wp_steps
          apply SepWP.focus_weaken (PollCommon.write_14_overlap_mid (sf_2.readReg64 .x0) w0)
          wp_pull_exists
          wp_steps
          apply SepWP.focus_weaken (PollCommon.write_14_overlap_done (sf_2.readReg64 .x0) w0 wTail)
          apply SepWP.focus_weaken
            (out_reg_err_malformed_fold A x.out (sf_2.readReg64 .x0) _ _
              ((unpack64 w0).take 6 ++ unpack64 wTail)
              hbuf_ne (PollCommon.write_14_overlap_length w0 wTail))
          refine focus_regPostAns A x.out
            ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files)
            (.error ()) s0 (by sep_focus) ?_ ?_
          · exact ⟨hans_err4.symm, by simp only [wp_norm, arm64_norm, *]⟩
          wp_done
        ·
          have hc0_beq : (bCap == 0#64) = false := beq_false_of_ne hc0
          apply SepWPp.of_sepWP_inImage
            (mid := fnBase + BitVec.ofNat 64 (num% (ls_rel%
              "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
              "__rustc::__rust_dealloc")))
            (by assumption)
          apply SepWP.focus_rw (PollCommon.memRegion_14_split_8_6 (sf_2.readReg64 .x0))
          wp_pull_exists
          wp_steps
          apply SepWP.focus_weaken (PollCommon.write_14_overlap_mid (sf_2.readReg64 .x0) w0)
          wp_pull_exists
          wp_steps
          apply SepWP.focus_weaken (PollCommon.write_14_overlap_done (sf_2.readReg64 .x0) w0 wTail)
          apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
          intro hinv_d1
          wp_call_inImage hDeallocCells hinv_d1 (bPtr, bCap, bs, s0.sp - 112#64)
          case panic =>
            intro sf_p _ hm
            dsimp only at hm
            simpa only [sepConj_assoc] using close_panic_subgoal s0 hm (by simp only [wp_norm, arm64_norm, *])
          have h_reg_d : sf_3.sp = s0.sp - 112#64 ∧
              sf_3.readReg64 (.gpr 19#5) = x.fut ∧
              sf_3.readReg64 (.gpr 20#5) = x.out ∧
              sf_3.readReg64 (.gpr 22#5) = sf_2.readReg64 .x0 :=
            ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
          rcases h_reg_d with ⟨_, _, _, _⟩
          apply SepWPp.of_sepWP_ret
          apply SepWP.focus_rw (out_48_reg_split x.out)
          wp_pull_exists
          wp_steps
          apply SepWP.focus_weaken
            (out_reg_err_malformed_fold A x.out (sf_2.readReg64 .x0) _ _
              ((unpack64 w0).take 6 ++ unpack64 wTail)
              hbuf_ne (PollCommon.write_14_overlap_length w0 wTail))
          refine focus_regPostAns A x.out
            ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files)
            (.error ()) s0 (by sep_focus) ?_ ?_
          · exact ⟨hans_err4.symm, by simp only [wp_norm, arm64_norm, *]⟩
          wp_done

/-! ## Outer Wrapper and CLI Instantiation -/

set_option maxRecDepth 2000000 in
theorem idRegIdPoll_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : AllocContractsX img A ext)
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hstk : 0x70 + regCalleeStk getStk ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idRegIdPollName)
      (idRegIdPollSpec rd pathOk A img stk) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
      x.own.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.own.path (utf8 "registration-id"))⌝ ∗
      idOwnFutBoxAt x.fut x.self 0#8 ∗ dirAt A x.self x.own ∗
      memRegion x.out 48 ∗ A.pool ∗ stackAt s0.sp stk)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hpath, hpok⟩, hmem⟩
  dsimp only [idOwnFutBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine Store.IdTrustPoll.Helpers.memRegion_bound_of_pointsTo64
      (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₈ 0#8) ∗ memRegion (x.fut + 9#64) 7 ∗
        dirAt A x.self x.own ∗ memRegion x.out 48 ∗ A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  let calleeStk := regCalleeStk getStk
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 112 ≤ 2 ^ 64 := by omega
  rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp (subStk := calleeStk + 112)
        (by omega) hstk_hi,
      ProofLib.stackAt_split_cells s0.sp calleeStk 14 hframe_hi] at hmem
  obtain ⟨w0, wTail, hro⟩ := PollCommon.rodata_regId_and_malformed himg hinv.1 hmem
  let F_extra :=
    memRegion (x.fut + 9#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 112))
  have hpre_in : s0.mem ⊨ ((cliIdRegIdPollInnerSpec rd pathOk A img w0 wTail calleeStk).inImage img).pre
      x s0 ∗ (F_extra ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [cliIdRegIdPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hpath, hpok⟩, ?_⟩
    dsimp only [F_extra]
    exact Satisfies.mono (by sep_focus) hro
  refine (idRegIdPollInner_ok (w0 := w0) (wTail := wTail) hC hGet hb hcal_hi).mono_outcome x
      (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, cliIdRegIdPollInnerSpec, idRegIdPollSpec,
      idOwnFutBoxAt, regPostAns] at hq ⊢
    have hq_ro : sf.mem ⊨
        ((idRegIdFileNameAddr img.base ↦ᵣ utf8 "registration-id") ∗
          (malformedFileStrAddr img.base ↦₆₄ᵣ w0) ∗
          ((malformedFileStrAddr img.base + 6#64) ↦₆₄ᵣ wTail)) ∗
        (((∃∗ ans : Except Unit (BitVec 32),
            ⌜ans = (IdGhost.mk x.own (.new [])).regId rd s0.fs.files ∧ sf.trace = s0.trace⌝ ∗
            idRegIdOutAt A x.out ans) ∗
          ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗ memRegion (x.fut + 9#64) 7) ∗
          dirAt A x.self x.own ∗ A.pool ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 112)) ∗
            (stackAt (s0.sp - 112#64) calleeStk ∗ cells (s0.sp - 112#64) 14))) ∗ R) := by
      dsimp only [F_extra] at hq
      exact Satisfies.mono (by sep_focus) hq
    have hq_drop := Satisfies.of_sep_right hq_ro
    rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp (subStk := calleeStk + 112)
          (by omega) hstk_hi,
        ProofLib.stackAt_split_cells s0.sp calleeStk 14 hframe_hi]
    exact hq_drop
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, cliIdRegIdPollInnerSpec, idRegIdPollSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem idRegIdPoll_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooks img A (cliExterns W))
    (hGet : subroutine_ok (initProg img W)
      ((initProg img W).fnAddr dirGetName)
      (dirGetSpec cliIo.rd cliWrOk A img B.dirGetNeed))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr idRegIdPollName)
      (idRegIdPollSpec cliIo.rd cliWrOk A img
        (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have he : extHookStack ≤ 65536 := by decide
  exact idRegIdPoll_ok_of_deps himg hh.alloc hGet
    (by dsimp only [regCalleeStk]; omega)
    (RunSkeleton.base_aligned himg)

theorem idRegIdPoll_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A ext1)
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr dirGetName)
      (dirGetSpec cliIo.rd cliWrOk A img B.dirGetNeed))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr idRegIdPollName)
      (idRegIdPollSpec cliIo.rd cliWrOk A img
        (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have he : extHookStack ≤ 65536 := by decide
  exact idRegIdPoll_ok_of_deps himg hh.alloc hGet
    (by dsimp only [regCalleeStk]; omega)
    (RunSkeleton.base_aligned himg)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll
