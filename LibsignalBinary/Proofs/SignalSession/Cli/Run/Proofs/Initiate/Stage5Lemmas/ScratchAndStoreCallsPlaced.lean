/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCalls
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EpiloguePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Stage 5 Callee Call Combinators (`[LibsignalPlacement]`)

Relocatable `[LibsignalPlacement]` `SepWPp` call combinators for Stage 5 session and store callees
on `initProgPlaced W`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding LibsignalCodeRoLoaded withLsCodeRoLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

set_option linter.unusedSimpArgs false
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

/-! ## Typed `SepWPp` Call Combinators -/

theorem s5_call_setUnackMsg_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {callee ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (withLsCodeRoLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A)))
    (fsp : BitVec 64) (g : Pqxdh.TopLevel.SetUnackExactGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = g.statePtr)
    (hx1 : (s.readReg64 .x1).setWidth 32 = g.optOpkTag)
    (hx2 : (s.readReg64 .x2).setWidth 32 = g.optOpkVal)
    (hx3 : (s.readReg64 .x3).setWidth 32 = g.spkId)
    (hx4 : s.readReg64 .x4 = g.baseKeyPtr)
    (hx5 : s.readReg64 .x5 = 0#64)
    (hx6 : (s.readReg64 .x6).setWidth 32 = 0#32)
    (hbLen : g.baseKeyBytes.length = 32)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ ((g.baseKeyPtr ↦ₛ Pqxdh.Initiator.bytesToBv8 g.baseKeyBytes) ∗
      ((g.statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.statePtr + 0x100#64) 40 ∗
      stackAt (fsp - 144#64) (allocHookStack + 32) ∗
      cells (fsp - 144#64) 18 ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        (((g.baseKeyPtr ↦ₛ Pqxdh.Initiator.bytesToBv8 g.baseKeyBytes) ∗
          Pqxdh.Initiator.vecU8 A (g.statePtr + 0xf8#64)
            (Pqxdh.Initiator.bytesToBv8 (SignalPqxdh.encodeEC g.baseKeyBytes)) ∗
          ((g.statePtr + 0x110#64) ↦₃₂ g.optOpkTag) ∗
          ((g.statePtr + 0x114#64) ↦₃₂ g.optOpkVal) ∗
          ((g.statePtr + 0x118#64) ↦₆₄ 0#64) ∗
          ((g.statePtr + 0x120#64) ↦₃₂ g.spkId) ∗
          memRegion (g.statePtr + 0x124#64) 4 ∗
          stackAt (fsp - 144#64) (allocHookStack + 32) ∗
          cells (fsp - 144#64) 18 ∗ A.pool) ∗ F) Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hcall g F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [setUnackPreKeyMsgEpochInnerSpec, hsp, sepConj_assoc]
    exact Entails.pure_right ⟨hx5, hx6⟩
      (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbLen⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [setUnackPreKeyMsgEpochInnerSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro sm R' hpost
    simp only [setUnackPreKeyMsgEpochInnerSpec, Pqxdh.Initiator.rustPanicOnOomPlaced,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1.1
  · intro code sm R' hpost
    simp only [setUnackPreKeyMsgEpochInnerSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [setUnackPreKeyMsgEpochInnerSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [setUnackPreKeyMsgEpochInnerSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm)

theorem s5_call_setUnackKyb_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {callee ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (withLsCodeRoLoaded lsmpl Pqxdh.setUnackKyberPreKeyIdSpec))
    (fsp statePtr cap : BitVec 64) (w0 kpkId : BitVec 32) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = statePtr)
    (hx1 : (s.readReg64 .x1).setWidth 32 = kpkId)
    (hcap : cap + 1#64 ≠ 0#64)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (((statePtr + 0x128#64) ↦₆₄ cap) ∗ ((statePtr + 0x140#64) ↦₃₂ w0)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((((statePtr + 0x128#64) ↦₆₄ cap) ∗ ((statePtr + 0x140#64) ↦₃₂ kpkId)) ∗ F) Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hcall (statePtr, cap, kpkId) F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [Pqxdh.setUnackKyberPreKeyIdSpec, sepConj_assoc]
    refine Entails.pure_right ⟨hx0, hx1, hcap⟩ ?_
    exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right w0 (Entails.refl _)))
  · intro sm R' hpost
    simp only [Pqxdh.setUnackKyberPreKeyIdSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro sm R' hpost
    simp only [Pqxdh.setUnackKyberPreKeyIdSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    simp only [Pqxdh.setUnackKyberPreKeyIdSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [Pqxdh.setUnackKyberPreKeyIdSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [Pqxdh.setUnackKyberPreKeyIdSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm)

theorem s5_call_idRegIdShim_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (fsp self : BitVec 64) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 603)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = self)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      sm.readReg64 .x1 = lsρ idRegIdFutVtSym →
      sm.readReg64 .x0 ≠ 0#64 → (sm.readReg64 .x0).toNat % 8 = 0 →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((A.live (sm.readReg64 .x0) 16 8 ∗
          idOwnFutBoxAt (sm.readReg64 .x0) self 0#8 ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hStore.idRegIdShim self F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [hsp, sepConj_assoc]
    exact Entails.pure_right hx0 (Entails.refl _)
  · intro sm R' hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1.2.2.2
  · intro sm R' hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    change SepWPp _ _ _ (_ ∗ F) _ _
    simp only [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1m, hnz, hal8, _⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by dsimp only [idOwnFutBoxAtPlaced, idOwnFutBoxAt]; ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm hx1m hnz hal8)

theorem s5_call_idRegIdPoll_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (fsp : BitVec 64) (g : IdOwnPollGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 568)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = g.fut)
    (hx8 : s.readReg64 .x8 = g.out)
    (hpathLt : g.own.path.length < 2 ^ 32)
    (hpathOk : cliWrOk (pathOf g.own.path (utf8 "registration-id")))
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (idOwnFutBoxAt g.fut g.self 0#8 ∗ dirAt A g.self g.own ∗
      memRegion g.out 48 ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ (sm : State) (ans : Except Unit (BitVec 32)),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      ans = (IdGhost.mk g.own (.new [])).regId cliIo.rd s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((idRegIdOutAt A g.out ans ∗ idOwnFutBoxAt g.fut g.self 1#8 ∗
          dirAt A g.self g.own ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hStore.idRegIdPoll ⟨g.fut, g.out, g.self, g.own⟩ F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [hsp, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx8, hpathLt, hpathOk⟩ (Entails.of_eq (by dsimp only [idOwnFutBoxAtPlaced, idOwnFutBoxAt]))
  · intro sm R' hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨_, ⟨_, htrm⟩, _⟩ := hpost
    exact htrm
  · intro sm R' hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [hsp, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun ans => ?_
    refine SepWPp.pure_elim fun ⟨hans, _⟩ => ?_
    have houtEq : idRegIdOutAtPlaced A g.out ans = idRegIdOutAt A g.out ans := by
      cases ans <;> rfl
    rw [houtEq]
    exact sepWPp_conseq (Entails.of_eq (by dsimp only [idOwnFutBoxAtPlaced, idOwnFutBoxAt]; ac_rfl))
      (hnext sm ans hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm hans)

theorem s5_call_idSaveShim_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (fsp : BitVec 64) (c : IdentityShimCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 600)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = c.self)
    (hx1 : s.readReg64 .x1 = c.addrA)
    (hx2 : s.readReg64 .x2 = c.keyA)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      sm.readReg64 .x1 = lsρ idSaveFutVtSym →
      sm.readReg64 .x0 ≠ 0#64 → (sm.readReg64 .x0).toNat % 8 = 0 →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((A.live (sm.readReg64 .x0) 32 8 ∗
          idSaveBoxAt (sm.readReg64 .x0) c.self c.addrA c.keyA 0#8 ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hStore.idSaveShim c F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [hsp, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1.2.2.2
  · intro sm R' hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1m, hnz, hal8, _⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm hx1m hnz hal8)

theorem s5_call_idSavePoll_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (fsp : BitVec 64) (g : IdPollGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 565)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = g.call.fut)
    (hx8 : s.readReg64 .x8 = g.call.out)
    (hnameLt : g.call.call.addr.name.bytes.length < 2 ^ 32)
    (hpathLt : g.peers.path.length < 2 ^ 32)
    (hchgLt : g.peers.changed.length < 2 ^ 32)
    (hpathOk : cliWrOk (pathOf g.peers.path g.call.call.addr.val.name))
    (hwf : ∀ bs, g.peers.get cliIo.rd s.fs.files g.call.call.addr.val.name = .ok bs → IdFileWf bs)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (idSaveBoxAt g.call.fut g.self g.call.call.addrA g.call.call.keyA 0#8 ∗
      dirAt A (g.self + 0x28#64) g.peers ∗ memRegion g.call.out 48 ∗
      protocolAddressAt A g.call.call.addr g.call.call.addrA ∗
      (g.call.call.keyA ↦ₛ g.call.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
      A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ (sm : State) (gr : Except Unit (List (BitVec 8)))
      (p : Except Unit (Option IdentityKey)),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      gr = g.peers.get cliIo.rd s.fs.files g.call.call.addr.val.name →
      IdPeerAns gr p →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((idSaveOutAt A g.call.out (idSaveOf p g.call.call.key) ∗
          dirAt A (g.self + 0x28#64)
            (idSavePeers g.peers g.call.call.addr.val.name g.call.call.key p) ∗
          idSaveBoxAt g.call.fut g.self g.call.call.addrA g.call.call.keyA 1#8 ∗
          protocolAddressAt A g.call.call.addr g.call.call.addrA ∗
          (g.call.call.keyA ↦ₛ g.call.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hStore.idSavePoll g F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [hsp, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx8, hnameLt, hpathLt, hchgLt, hpathOk, hwf⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨_, _, ⟨⟨_, htrm⟩, _⟩, _⟩ := hpost
    exact htrm
  · intro sm R' hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [hsp, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun gr => SepWPp.exists_elim fun p => ?_
    refine SepWPp.pure_elim fun ⟨⟨hgr, _⟩, hp⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm gr p hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm hgr hp)

theorem s5_call_memcpy_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {callee ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (withLsCodeRoLoaded lsmpl (sessionMemcpySpec extHookStack)))
    (fsp dst src : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack) ∗ F) Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hcall (dst, src, bs) F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [sessionMemcpySpec, libcMemcpySpec, stackAt, hsp, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [sessionMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1.2
  · intro sm R' hpost
    simp only [sessionMemcpySpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    simp only [sessionMemcpySpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [sessionMemcpySpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [sessionMemcpySpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm)

theorem s5_call_promoteState_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {callee ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (withLsCodeRoLoaded lsmpl Pqxdh.ResponderStore.promoteStateEmptySpec))
    (fsp recPtr srcPtr : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = recPtr) (hx1 : s.readReg64 .x1 = srcPtr)
    (hbLen : bs.length = 344)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (recPtr + 0x20#64) 336 ∗ (srcPtr ↦ₛ bs) ∗
      cells (fsp - 96#64) 8 ∗ cells (fsp - 32#64) 4) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((((recPtr + 0x18#64) ↦ₛ bs) ∗ (srcPtr ↦ₛ bs) ∗
          cells (fsp - 96#64) 8 ∗ cells (fsp - 32#64) 4) ∗ F) Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hcall (recPtr, srcPtr, bs) F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [Pqxdh.ResponderStore.promoteStateEmptySpec, hsp, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hbLen⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [Pqxdh.ResponderStore.promoteStateEmptySpec, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro sm R' hpost
    simp only [Pqxdh.ResponderStore.promoteStateEmptySpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    simp only [Pqxdh.ResponderStore.promoteStateEmptySpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [Pqxdh.ResponderStore.promoteStateEmptySpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [Pqxdh.ResponderStore.promoteStateEmptySpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm)

theorem s5_call_sessStoreShim_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (fsp : BitVec 64) (c : StoreShimCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 605)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = c.self)
    (hx1 : s.readReg64 .x1 = c.addrA)
    (hx2 : s.readReg64 .x2 = c.recA)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      sm.readReg64 .x1 = lsρ sessStoreFutVtSym →
      sm.readReg64 .x0 ≠ 0#64 → (sm.readReg64 .x0).toNat % 8 = 0 →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((A.live (sm.readReg64 .x0) 32 8 ∗
          sessStoreBoxAt (sm.readReg64 .x0) c.self c.addrA c.recA 0#8 ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hStore.sessStoreShim c F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [hsp, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1.2.2.2
  · intro sm R' hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1m, hnz, hal8, _⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm hx1m hnz hal8)

theorem s5_call_sessStorePoll_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (fsp : BitVec 64) (g : SessStorePollGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 570)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = g.call.fut)
    (hx8 : s.readReg64 .x8 = g.call.out)
    (hnameLt : g.call.call.addr.name.bytes.length < 2 ^ 32)
    (hencLt : (E2E.Record.encodeRecord g.call.call.record).length < 2 ^ 32)
    (hchgLt : g.dir.changed.length < 2 ^ 32)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (sessStoreBoxAt g.call.fut g.self g.call.call.addrA g.call.call.recA 0#8 ∗
      dirAt A g.self g.dir ∗ memRegion g.call.out 48 ∗
      protocolAddressAt A g.call.call.addr g.call.call.addrA ∗
      sessionRecordAt A g.call.call.recA g.call.call.g g.call.call.record ∗
      A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((sessStoreBoxAt g.call.fut g.self g.call.call.addrA g.call.call.recA 1#8 ∗
          dirAt A g.self (g.dir.put (addressText g.call.call.addr.val)
            (E2E.Record.encodeRecord g.call.call.record)) ∗
          (g.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (g.call.out + 8#64) 40 ∗
          protocolAddressAt A g.call.call.addr g.call.call.addrA ∗
          sessionRecordAt A g.call.call.recA g.call.call.g g.call.call.record ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hStore.sessStorePoll g F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [hsp, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx8, hnameLt, hencLt, hchgLt⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro sm R' hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
