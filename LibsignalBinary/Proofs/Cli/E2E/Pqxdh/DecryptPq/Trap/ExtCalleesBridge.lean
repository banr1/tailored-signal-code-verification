/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtCallees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ExtS2B
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ExtS2Sym
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmk
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCtPkEq
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S2Sym
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt

@[expose] public section

set_option autoImplicit false

/-!
# `S2LogBridge` & `CliExternsOk` Callees Bridge for `try_decrypt_with_state::<Coins>`

Proves `S2SpecLog_ext`, `s2_ok_log_ext`, `allocContractsMem4K_of_externsOk`, and
`tryDecryptPqCallees_of_externsOk_ext` on `tripleRatchetProgAtExt img.base (cliExternsWith ext)`.
-/

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SignalSession.Coins (coinsAfter)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtCallees

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

section S2LogBridge

open CryptoGames.LibsignalSession (RatchetState SessionState TripleRatchet)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte ratchetAt)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet (FindReceiverChainKeyGhost TrGhost
  TryDecryptGhost findReceiverChainKeyResultAt logOff trAt)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq (tryDecryptMidMeta
  tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
  (memRegion_0x140_split_findReceiverChainKey sepWP_to_reaches_pc signalMessageAt_eq_srk_rest
   signalMessageRestAt stackAt_tryDecryptSubStack_sub trAt_eq_ratchetAt_trRestAt trRestAt
   tryDecryptMidMeta.to_wpInv)
open CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq (errTailPC segS2PC segS3PC segS4PC
  tryDecryptEntry)

/-- `S2Spec_ext` variant taking `ExtFindCmk.FindReceiverChainKeyOkExt144` (`logOff img` in `pre`/`post`). -/
def S2SpecLog_ext
    (img : Obj.Image) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  CryptoVerification.Cli.LibsignalTripleRatchet.ExtFindCmk.FindReceiverChainKeyOkExt144 img A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2State A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | .ok (some ck) =>
        reaches_pc (tripleRatchetProgAtExt img.base ext) (segS4PC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG tr st1 ck 0 R s0)
      | .ok none =>
        reaches_pc (tripleRatchetProgAtExt img.base ext) (segS3PC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3State A ctl img x trG tr st1 R s0)
      | .error e =>
        reaches_pc (tripleRatchetProgAtExt img.base ext) (errTailPC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 e 0 R s0)

private theorem s2_call_findReceiverChainKey_reaches_log_ext
    {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hfrck : CryptoVerification.Cli.LibsignalTripleRatchet.ExtFindCmk.FindReceiverChainKeyOkExt144 img A ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hS2 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2State A ctl img x trG tr st1 R s0 s) :
    let prog := tripleRatchetProgAtExt img.base ext
    let sp := s0.sp - 1504#64
    reaches_pc prog (tryDecryptEntry img + 0x2a8#64) s
      (fun s_ret =>
        tryDecryptMidMeta img s0 s_ret ∧
        s_ret.readReg64 .x19 = x.ret ∧
        s_ret.readReg64 .x20 = sp + 0x140#64 ∧
        s_ret.readReg64 .x21 = x.ss ∧
        s_ret.readReg64 .x22 = x.msgA ∧
        s_ret.readReg64 .x23 = sp + 0x500#64 ∧
        (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s_ret.readReg64 .x25 = sp + 0x190#64 ∧
        s_ret.readReg64 .x27 = sp + 0x38#64 ∧
        s_ret.readReg64 .x28 = sp + 0x2c0#64 ∧
        (s_ret.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 0x38#64) trG tr ∗
          memRegion x.ret 48 ∗
          memRegion sp 0x20 ∗
          ((sp + 0x20#64) ↦₆₄ x.locA) ∗
          ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 0x2c#64) 4 ∗
          ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 0x140#64) 0x50 ∗
          findReceiverChainKeyResultAt (sp + 0x190#64) (tr.ratchet.findReceiverChainKey
            x.msg.senderRatchetKey) ∗
          memRegion (sp + 0x1b8#64) 0x3c8 ∗
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hS2 with ⟨hpc, hmeta, hx0, hx1, hx8, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
      hmem⟩
  have hentry :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry_eq_fnAddr_ext
      (ext := ext) himg
  dsimp only [segS2PC] at hpc
  rw [hentry] at hpc
  have hwp_bl :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_bl_wp_ext
      hpc (tryDecryptMidMeta.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x440 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    rw [emp_sepConj]; exact hmem
  have hinv_s : img.FrozenLoaded s ∧ s.symtab = img.symtab :=
    ⟨hmeta.2.2.2.2.2.2.1, hmeta.2.2.2.2.2.2.2.1⟩
  refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA.reaches_pc_seq_callInv hinv_s
      (sepWP_to_reaches_pc hwp_bl hmem_emp) ?_
  intro s_call hpc_call _ ⟨P1, hm_call, ⟨hP1, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c,
      hcs_c⟩⟩ hinv_call
  subst hP1
  rw [emp_sepConj] at hm_call
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap at hm_call
  rw [trAt_eq_ratchetAt_trRestAt, signalMessageAt_eq_srk_rest,
      memRegion_0x140_split_findReceiverChainKey,
      stackAt_tryDecryptSubStack_sub s0.sp
        CryptoVerification.Cli.LibsignalTripleRatchet.ExtFindCmk.findReceiverChainKeyStackExt144
        (by decide)] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  have hlr_call' : s_call.readReg64 Reg.lr = tryDecryptEntry img + 0x2a8#64 := by
    rw [hentry]; exact hlr_call
  let fg : FindReceiverChainKeyGhost :=
    { self := sp + 0x38#64
      G := trG.ratchet
      st := tr.ratchet
      theirA := x.msgA + 0x38#64
      their := x.msg.senderRatchetKey
      ret := sp + 0x190#64 }
  let F_call : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trRestAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1b8#64) 0x3c8 ∗
    protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗
    signalMessageRestAt A x.msgG x.msgA x.msg ∗
    coinsAfter img.base x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64)
      (tryDecryptSubStack -
        CryptoVerification.Cli.LibsignalTripleRatchet.ExtFindCmk.findReceiverChainKeyStackExt144) ∗
    tryDecryptSavedRegs s0.sp s0 ∗
    A.pool ∗ R
  have hpre_call :
      s_call.mem ⊨
        (⌜s_call.readReg64 .x0 = fg.self ∧ s_call.readReg64 .x1 = fg.theirA ∧
            s_call.readReg64 .x8 = fg.ret⌝ ∗
         ratchetAt A fg.self fg.G fg.st ∗
         (fg.theirA ↦ₛ fg.their.bytes.toList) ∗
         memRegion fg.ret 40 ∗
         logOff img ∗
         stackAt s_call.sp
           CryptoVerification.Cli.LibsignalTripleRatchet.ExtFindCmk.findReceiverChainKeyStackExt144) ∗
        F_call := by
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c.trans hx0, hx1_c.trans hx1, hx8_c.trans hx8⟩, ?_⟩
    rw [hsp_call]
    dsimp only [fg, F_call, sp] at hm_call ⊢
    convert hm_call using 1; sep_ac_rfl
  refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA.reaches_pc_call_inImage hfrck
      fg F_call hpc_call hwpInv_call.1 hlr_call' hinv_call hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hinv_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  have hcs : CalleeSavedPreserved s s_ret := CalleeSavedPreserved.trans hcs_c hcs_ret
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.ExtFindCmk.findReceiverChainKeySpecWithStack]
    at hpost_ret
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨htr_ret, hm_ret⟩
  have hsp_ret' : s_ret.sp = s0.sp - 1504#64 := hsp_ret.trans hsp_call
  have halign_ret : s_ret.spAligned = true := by
    rw [State.spAligned, hsp_ret', ← hwpInv_call.2.1]
    exact halign_call
  have hmeta_ret : tryDecryptMidMeta img s0 s_ret :=
    ⟨hrun_ret, hsp_ret', hwpInv_call.2.2.1, halign_ret,
     (hcs_ret.2.2.2.2.2.2.2.2.2.2.1).trans hwpInv_call.2.2.2.2.1,
     htr_ret.trans hwpInv_call.2.2.2.2.2.1, hinv_ret.1, hinv_ret.2,
     (hcs.2.2.2.2.2.2.2.2.2.2.2).trans hmeta.2.2.2.2.2.2.2.2⟩
  refine ⟨hmeta_ret,
    (hcs.1).trans hx19,
    (hcs.2.1).trans hx20,
    (hcs.2.2.1).trans hx21,
    (hcs.2.2.2.1).trans hx22,
    (hcs.2.2.2.2.1).trans hx23,
    by change (s_ret.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hcs.2.2.2.2.2.1]; exact hx24,
    (hcs.2.2.2.2.2.2.1).trans hx25,
    (hcs.2.2.2.2.2.2.2.2.1).trans hx27,
    (hcs.2.2.2.2.2.2.2.2.2.1).trans hx28,
    ?_⟩
  rw [hsp_call] at hm_ret
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
  rw [trAt_eq_ratchetAt_trRestAt, signalMessageAt_eq_srk_rest,
      stackAt_tryDecryptSubStack_sub s0.sp
        CryptoVerification.Cli.LibsignalTripleRatchet.ExtFindCmk.findReceiverChainKeyStackExt144
        (by decide)]
  dsimp only [fg, F_call, sp] at hm_ret ⊢
  convert hm_ret using 1; sep_ac_rfl

/-- `S2` segment verification using `ExtFindCmk.FindReceiverChainKeyOkExt144`. -/
theorem s2_ok_log_ext
    {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)} :
    S2SpecLog_ext img A ctl ext := by
  intro himg hfrck x trG tr st1 R s0 s hs2 _hcode
  have hcall :=
    s2_call_findReceiverChainKey_reaches_log_ext himg hfrck x trG tr st1 R s0 s hs2
  cases hres : tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
  | ok optCk =>
    cases optCk with
    | some ck =>
      rw [hres] at hcall
      refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret,
          hx22_ret, hx23_ret, hx24_ret, hx25_ret, _, hx28_ret, hm_ret⟩ => ?_)
      exact
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_after_call_ok_some_ext
          himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret
          hx23_ret hx24_ret hx25_ret hx28_ret hm_ret
    | none =>
      rw [hres] at hcall
      refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret,
          hx22_ret, hx23_ret, hx24_ret, hx25_ret, hx27_ret, hx28_ret, hm_ret⟩ => ?_)
      exact
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_after_call_ok_none_ext
          himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret
          hx23_ret hx24_ret hx25_ret hx27_ret hx28_ret hm_ret
  | error e =>
    rw [hres] at hcall
    refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, _, _, _, _,
        hx25_ret, _, _, hm_ret⟩ => ?_)
    exact
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_after_call_error_ext
        himg hpc_ret hmeta_ret hx19_ret hx20_ret hx25_ret hm_ret

end S2LogBridge

theorem allocContractsMem4K_of_externsOk
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (b : BitVec 64)
    (hOk : CryptoVerification.SignalSession.CliExternsOk P A ext) :
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
      b A (CryptoVerification.SignalSession.cliExternsWith ext) :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K.of_hooks
    b A (CryptoVerification.SignalSession.cliExternsWith ext)
    (CryptoVerification.SignalSession.Cli.Slots.ext_allocHooks hOk)
    (CryptoVerification.SignalSession.Cli.Slots.ext_shim hOk)
    (CryptoVerification.SignalSession.Cli.Slots.ext_memcpy hOk)
    (CryptoVerification.SignalSession.Cli.Slots.ext_memmove hOk)
    (CryptoVerification.SignalSession.Cli.Slots.ext_memset hOk)

theorem tryDecryptPqCallees_of_externsOk_ext
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CryptoVerification.SignalSession.CliExternsOk P A ext)
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img) :
    TryDecryptCalleesLog_ext img P.C A uuidTryParse
      (CryptoVerification.SignalSession.cliExternsWith ext) := by
  have hAg := CryptoVerification.SignalSession.Cli.Slots.AgreeOnCliHooks.cliExternsWith ext
  have hA :=
    CryptoVerification.SignalSession.Cli.Slots.allocContractsX_cliExternsWith_of_externsOk hOk img
  have hHkdf :=
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq.hkdfContractsExt_of_externsOk_on
      img hOk hAg
  have h_bb :=
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq.hookSat_blackBox32_of_externsOk_on
      hOk hAg
  exact tryDecryptPqCallees_of_cmk_ext hOk img himg
    (Proofs.libsignal.Stage1X.CmkX.cmk_ok_tr_ext_x himg hA hHkdf h_bb)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtCallees
