/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.Common
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S1Sym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Trap-at-RNG Segment S1 Symbolic Steps

Basic-block `SepWP` lemmas (`+0x1d8 → +0x2a4 / +0x384 → +0x3b0`) on `trTrapProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Segment S1 (`+0x1d8 → +0x2a4 / +0x384 → +0x3b0`) -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_bl_wp_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s0 s : State}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x1d8#64)
    (hmeta : tryDecryptWPInv s0 s) :
    let sp := s0.sp - 1504#64
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr trFromName) s
      emp
      (fun s1 P1 =>
        P1 = emp ∧
        tryDecryptWPInv s0 s1 ∧
        s1.readReg64 Reg.lr = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x1e4#64 ∧
        s1.readReg64 .x0 = s.readReg64 .x21 ∧
        (s1.readReg64 .x1).setWidth 32 = (s.readReg64 .x1).setWidth 32 ∧
        s1.readReg64 .x8 = sp + 0x190#64 ∧
        CalleeSavedPreserved s s1) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  have hcal : (trTrapProgAt b C abs).fnAddr trFromName =
      (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        (0x1e0#64 + BitVec.signExtend 64 (-(BitVec.ofNat 28 (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 480 - ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state"))) : BitVec 28)) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.fnAddr_tryDecrypt_rel64_trap libsignalSessionCode_fnOff_0x1c60c (by decide)
  dec_fetches_cli b (trTrapExterns C abs) hfn 0x1d8 12
  rw [hcal]
  clear hcal hfn
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_call_trFrom_reaches_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (htrFrom : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TrFromOk_trap img C A abs)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State)
    (hS1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1State A ctl img x R s0 s) :
    let prog := trTrapProgAt img.base C abs
    let sp := s0.sp - 1504#64
    let res := Mut.exec TripleRatchet.fromSessionState x.st
    reaches_pc prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x1e4#64) s
      (fun s_ret =>
        tryDecryptMidMeta img s0 s_ret ∧
        s_ret.readReg64 .x19 = x.ret ∧
        s_ret.readReg64 .x20 = sp + 0x140#64 ∧
        s_ret.readReg64 .x21 = x.ss ∧
        s_ret.readReg64 .x22 = x.msgA ∧
        s_ret.readReg64 .x23 = sp + 0x500#64 ∧
        (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s_ret.readReg64 .x25 = x.locA ∧
        (s_ret.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom res.2 ∗
          trResultAt A (sp + 0x190#64) x.G res.1 ∗
          memRegion x.ret 48 ∗
          memRegion sp 0x30 ∗
          ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 0x38#64) 0x158 ∗
          memRegion (sp + 0x298#64) 0x2e8 ∗
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hS1 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx1, hmem⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_trap (C := C) (abs := abs) himg
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC] at hpc
  rw [hentry] at hpc
  have hwp_bl := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_bl_wp_trap hpc (tryDecryptMidMeta.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt A x.ss x.G x.st ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x38#64) 0x548 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    rw [emp_sepConj]; exact hmem
  have hinv_s : img.FrozenLoaded s ∧ s.symtab = img.symtab := ⟨hmeta.2.2.2.2.2.2.1,
      hmeta.2.2.2.2.2.2.2.1⟩
  refine reaches_pc_seq_callInv hinv_s (sepWP_to_reaches_pc hwp_bl hmem_emp) ?_
  intro s_call hpc_call _ ⟨P1, hm_call, ⟨hP1, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c,
      hcs_c⟩⟩ hinv_call
  subst hP1
  rw [emp_sepConj] at hm_call
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap at hm_call
  rw [memRegion_0x38_split_trFrom,
      stackAt_tryDecryptSubStack_sub s0.sp trFromStack (by decide)] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  have hlr_call' : s_call.readReg64 Reg.lr = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x1e4#64 := by
    rw [hentry]; exact hlr_call
  let tg : TrFromGhost :=
    { ss := x.ss
      G := x.G
      st := x.st
      ret := sp + 0x190#64 }
  let F_call : SepProp :=
    memRegion x.ret 48 ∗
    memRegion sp 0x30 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x158 ∗
    memRegion (sp + 0x298#64) 0x2e8 ∗
    protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗
    signalMessageAt A x.msgG x.msgA x.msg ∗
    CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64) (tryDecryptSubStack - trFromStack) ∗
    tryDecryptSavedRegs s0.sp s0 ∗ R
  have hpre_call :
      s_call.mem ⊨
        (⌜s_call.readReg64 .x0 = tg.ss ∧ (s_call.readReg64 .x1).setWidth 32 = 0#32 ∧
            s_call.readReg64 .x8 = tg.ret⌝ ∗
         sessionStateAt A tg.ss tg.G tg.st ∗
         memRegion tg.ret 264 ∗
         logOff img ∗
         stackAt s_call.sp trFromStack ∗
         A.pool) ∗ F_call := by
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c.trans hx21, hx1_c.trans hx1, hx8_c⟩, ?_⟩
    rw [hsp_call]
    dsimp only [tg, F_call, sp] at hm_call ⊢
    convert hm_call using 1; sep_ac_rfl
  refine reaches_pc_call_inImage htrFrom tg F_call hpc_call hwpInv_call.1 hlr_call' hinv_call
      hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hinv_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  have hcs : CalleeSavedPreserved s s_ret := CalleeSavedPreserved.trans hcs_c hcs_ret
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨⟨_, htr_ret⟩, hm_ret⟩
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
    ?_⟩
  rw [hsp_call] at hm_ret
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
  rw [stackAt_tryDecryptSubStack_sub s0.sp trFromStack (by decide)]
  dsimp only [tg, TrFromGhost.model, F_call, sp] at hm_ret ⊢
  convert hm_ret using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_err_wp_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    {ret tag w0 w1 w2 w3 w4 t0 t1 t2 t3 t4 t5 r0 r1 r2 r3 r4 r5 : BitVec 64}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x1e4#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64) :
    let prog := trTrapProgAt img.base C abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC img) s
      (((sp + 0x190#64) ↦₆₄ errTag) ∗
       ((sp + 0x198#64) ↦₆₄ tag) ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
       ((sp + 0x500#64) ↦₆₄ t0) ∗
       words5At (sp + 0x508#64) t1 t2 t3 t4 t5 ∗
       (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5)
      (fun sf P =>
        P = (((sp + 0x190#64) ↦₆₄ errTag) ∗
             ((sp + 0x198#64) ↦₆₄ tag) ∗
             words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
             ((sp + 0x500#64) ↦₆₄ tag) ∗
             words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗
             (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4) ∧
        tryDecryptWPInv s0 sf) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_trap (C := C) (abs := abs) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base (trTrapExterns C abs) hfn 0x1e4 32
  dec_fetches_cli img.base (trTrapExterns C abs) hfn 0x384 16
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC]
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  unfold words5At errTag
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_1a_wp_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    {cap locA g20 w0 w1 w2 w3 w4 w5 t0 t1 t2 t3 t4 t5 : BitVec 64}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hcap : cap + 1#64 ≠ 0#64)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x1e4#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = locA) :
    let prog := trTrapProgAt img.base C abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x210#64) s
      (((sp + 0x20#64) ↦₆₄ g20) ∗
       ((sp + 0x190#64) ↦₆₄ cap) ∗
       words4At (sp + 0x198#64) w0 w1 w2 w3 ∗
       ((sp + 0x1b8#64) ↦₆₄ w4) ∗
       ((sp + 0x1c0#64) ↦₆₄ w5) ∗
       words4At (sp + 0x500#64) t0 t1 t2 t3 ∗
       ((sp + 0x520#64) ↦₆₄ t4) ∗
       ((sp + 0x528#64) ↦₆₄ t5))
      (fun sf P =>
        P = (((sp + 0x20#64) ↦₆₄ locA) ∗
             ((sp + 0x190#64) ↦₆₄ cap) ∗
             words4At (sp + 0x198#64) w0 w1 w2 w3 ∗
             ((sp + 0x1b8#64) ↦₆₄ w4) ∗
             ((sp + 0x1c0#64) ↦₆₄ w5) ∗
             words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
             ((sp + 0x520#64) ↦₆₄ w4) ∗
             ((sp + 0x528#64) ↦₆₄ w5)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x8 = cap ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x27 = sp + 0x38#64) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_trap (C := C) (abs := abs) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base (trTrapExterns C abs) hfn 0x1e4 44
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  unfold words4At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_1b_wp_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    {cap remA msgA d_cap w6 w7 w16 w17 : BitVec 64}
    {w24 w25 w26 w27 w28 w29 w30 w31 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x210#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx8 : s.readReg64 .x8 = cap)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64) :
    let prog := trTrapProgAt img.base C abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x24c#64) s
      (((sp + 0x30#64) ↦₆₄ remA) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       ((sp + 0x1c8#64) ↦₆₄ w6) ∗
       ((sp + 0x1d0#64) ↦₆₄ w7) ∗
       ((sp + 0x218#64) ↦₆₄ w16) ∗
       ((sp + 0x220#64) ↦₆₄ w17) ∗
       words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
       words8At (sp + 0x100#64) d24 d25 d26 d27 d28 d29 d30 d31)
      (fun sf P =>
        P = (((sp + 0x30#64) ↦₆₄ remA) ∗
             ((sp + 0x38#64) ↦₆₄ cap) ∗
             ((sp + 0x1c8#64) ↦₆₄ w6) ∗
             ((sp + 0x1d0#64) ↦₆₄ w7) ∗
             ((sp + 0x218#64) ↦₆₄ w16) ∗
             ((sp + 0x220#64) ↦₆₄ w17) ∗
             words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
             words8At (sp + 0x100#64) w24 w25 w26 w27 w28 w29 w30 w31) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x0 = sp + 0x38#64 ∧
        sf.readReg64 .x1 = msgA + 0x38#64 ∧
        sf.readReg64 .x8 = remA ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = sp + 0x2c0#64 ∧
        sf.readVReg128 0#5 = w17 ++ w16 ∧
        sf.readVReg128 2#5 = w7 ++ w6) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_trap (C := C) (abs := abs) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base (trTrapExterns C abs) hfn 0x210 60
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  unfold words8At words4At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_1c_wp_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    {w8 w9 w16 w17 w18 w19 w20 w21 w22 w23 d16 d17 d18 d19 d20 d21 d22 d23 : BitVec 64}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x24c#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64)
    (hq0 : s.readVReg128 0#5 = w17 ++ w16) :
    let prog := trTrapProgAt img.base C abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x26c#64) s
      (((sp + 0x1d8#64) ↦₆₄ w8) ∗
       ((sp + 0x1e0#64) ↦₆₄ w9) ∗
       ((sp + 0x228#64) ↦₆₄ w18) ∗
       ((sp + 0x230#64) ↦₆₄ w19) ∗
       words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
       words8At (sp + 0xc0#64) d16 d17 d18 d19 d20 d21 d22 d23)
      (fun sf P =>
        P = (((sp + 0x1d8#64) ↦₆₄ w8) ∗
             ((sp + 0x1e0#64) ↦₆₄ w9) ∗
             ((sp + 0x228#64) ↦₆₄ w18) ∗
             ((sp + 0x230#64) ↦₆₄ w19) ∗
             words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
             words8At (sp + 0xc0#64) w16 w17 w18 w19 w20 w21 w22 w23) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧
        sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 0#5 = w9 ++ w8 ∧
        sf.readVReg128 2#5 = s.readVReg128 2#5) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_trap (C := C) (abs := abs) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base (trTrapExterns C abs) hfn 0x24c 32
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  unfold words8At words4At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_1d_wp_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    {remA msgA g2a0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64}
    {counter g28 : BitVec 32} {g2ac : BitVec 8}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x26c#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx8 : s.readReg64 .x8 = remA)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hq0 : s.readVReg128 0#5 = w9 ++ w8)
    (hq2 : s.readVReg128 2#5 = w7 ++ w6) :
    let prog := trTrapProgAt img.base C abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS2PC img) s
      (((sp + 0x28#64) ↦₃₂ g28) ∗
       ((sp + 0x1e8#64) ↦₆₄ w10) ∗
       ((sp + 0x1f0#64) ↦₆₄ w11) ∗
       words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
       ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
       ((sp + 0x520#64) ↦₆₄ w4) ∗
       ((sp + 0x528#64) ↦₆₄ w5) ∗
       ((msgA + 0x68#64) ↦₃₂ counter) ∗
       words8At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 ∗
       words8At (sp + 0x80#64) d8 d9 d10 d11 d12 d13 d14 d15)
      (fun sf P =>
        P = (((sp + 0x28#64) ↦₃₂ counter) ∗
             ((sp + 0x1e8#64) ↦₆₄ w10) ∗
             ((sp + 0x1f0#64) ↦₆₄ w11) ∗
             words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗
             ((sp + 0x2a0#64) ↦₆₄ remA) ∗
             ((sp + 0x2ac#64) ↦₈ (s.readReg64 .x26).setWidth 8) ∗
             words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
             ((sp + 0x520#64) ↦₆₄ w4) ∗
             ((sp + 0x528#64) ↦₆₄ w5) ∗
             ((msgA + 0x68#64) ↦₃₂ counter) ∗
             words8At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 ∗
             words8At (sp + 0x80#64) w8 w9 w10 w11 w12 w13 w14 w15) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧
        sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x8 = sp + 0x190#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_trap (C := C) (abs := abs) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base (trTrapExterns C abs) hfn 0x26c 56
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS2PC]
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  unfold words8At words4At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_wp_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    {cap locA remA msgA g20 d_cap g2a0 t0 t1 t2 t3 t4 t5 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
     d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64}
    {counter g28 : BitVec 32} {g2ac : BitVec 8}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hcap : cap + 1#64 ≠ 0#64)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x1e4#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = locA) :
    let prog := trTrapProgAt img.base C abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS2PC img) s
      (((sp + 0x20#64) ↦₆₄ g20) ∗
       ((sp + 0x28#64) ↦₃₂ g28) ∗
       ((sp + 0x30#64) ↦₆₄ remA) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 0x190#64) ↦₆₄ cap) ∗
       words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
       ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       words4At (sp + 0x500#64) t0 t1 t2 t3 ∗
       ((sp + 0x520#64) ↦₆₄ t4) ∗
       ((sp + 0x528#64) ↦₆₄ t5) ∗
       ((msgA + 0x68#64) ↦₃₂ counter))
      (fun sf P =>
        ∃ b2ac : BitVec 8,
          P = (((sp + 0x20#64) ↦₆₄ locA) ∗
               ((sp + 0x28#64) ↦₃₂ counter) ∗
               ((sp + 0x30#64) ↦₆₄ remA) ∗
               ((sp + 0x38#64) ↦₆₄ cap) ∗
               words32At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
                 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
               ((sp + 0x190#64) ↦₆₄ cap) ∗
               words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
                 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
               ((sp + 0x2a0#64) ↦₆₄ remA) ∗
               ((sp + 0x2ac#64) ↦₈ b2ac) ∗
               words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
               ((sp + 0x520#64) ↦₆₄ w4) ∗
               ((sp + 0x528#64) ↦₆₄ w5) ∗
               ((msgA + 0x68#64) ↦₃₂ counter)) ∧
          tryDecryptWPInv s0 sf ∧
          sf.readReg64 .x0 = sp + 0x38#64 ∧
          sf.readReg64 .x1 = msgA + 0x38#64 ∧
          sf.readReg64 .x8 = sp + 0x190#64 ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧
          sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧
          sf.readReg64 .x25 = sp + 0x190#64 ∧
          sf.readReg64 .x27 = sp + 0x38#64 ∧
          sf.readReg64 .x28 = sp + 0x2c0#64) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have h1a := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_1a_wp_trap (C := C) (abs := abs)
    (cap := cap) (locA := locA) (g20 := g20)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    himg hcap hpc hmeta hx20 hx23 hx25
  refine SepWP.rw_pre (by rw [words32At_40_eq, words32At_198_eq]) ?_
  refine SepWP.bind_framed
    (F := ((sp + 0x28#64) ↦₃₂ g28) ∗
          ((sp + 0x30#64) ↦₆₄ remA) ∗
          ((sp + 0x38#64) ↦₆₄ d_cap) ∗
          words8At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 ∗
          words8At (sp + 0x80#64) d8 d9 d10 d11 d12 d13 d14 d15 ∗
          words8At (sp + 0xc0#64) d16 d17 d18 d19 d20 d21 d22 d23 ∗
          words8At (sp + 0x100#64) d24 d25 d26 d27 d28 d29 d30 d31 ∗
          ((sp + 0x1c8#64) ↦₆₄ w6) ∗
          ((sp + 0x1d0#64) ↦₆₄ w7) ∗
          ((sp + 0x1d8#64) ↦₆₄ w8) ∗
          ((sp + 0x1e0#64) ↦₆₄ w9) ∗
          ((sp + 0x1e8#64) ↦₆₄ w10) ∗
          ((sp + 0x1f0#64) ↦₆₄ w11) ∗
          words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗
          ((sp + 0x218#64) ↦₆₄ w16) ∗
          ((sp + 0x220#64) ↦₆₄ w17) ∗
          ((sp + 0x228#64) ↦₆₄ w18) ∗
          ((sp + 0x230#64) ↦₆₄ w19) ∗
          words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
          words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
          ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
          ((sp + 0x2ac#64) ↦₈ g2ac) ∗
          ((msgA + 0x68#64) ↦₃₂ counter))
    h1a ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s1a P1a ⟨hP1a, hmeta1a, hx8_1a, hx19_1a, hx20_1a, hx21_1a, hx22_1a, hx23_1a, hx24_1a,
      hx25_1a, hx27_1a⟩ hpc1a
  subst hP1a
  have h1b := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_1b_wp_trap (C := C) (abs := abs)
    (cap := cap) (remA := remA) (msgA := msgA) (d_cap := d_cap)
    (w6 := w6) (w7 := w7) (w16 := w16) (w17 := w17)
    (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27)
    (w28 := w28) (w29 := w29) (w30 := w30) (w31 := w31)
    (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27)
    (d28 := d28) (d29 := d29) (d30 := d30) (d31 := d31)
    himg hpc1a hmeta1a hx8_1a (hx22_1a.trans hx22) hx25_1a hx27_1a
  refine SepWP.bind_framed
    (F := ((sp + 0x20#64) ↦₆₄ locA) ∗
          ((sp + 0x28#64) ↦₃₂ g28) ∗
          words8At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 ∗
          words8At (sp + 0x80#64) d8 d9 d10 d11 d12 d13 d14 d15 ∗
          words8At (sp + 0xc0#64) d16 d17 d18 d19 d20 d21 d22 d23 ∗
          ((sp + 0x190#64) ↦₆₄ cap) ∗
          words4At (sp + 0x198#64) w0 w1 w2 w3 ∗
          ((sp + 0x1b8#64) ↦₆₄ w4) ∗
          ((sp + 0x1c0#64) ↦₆₄ w5) ∗
          ((sp + 0x1d8#64) ↦₆₄ w8) ∗
          ((sp + 0x1e0#64) ↦₆₄ w9) ∗
          ((sp + 0x1e8#64) ↦₆₄ w10) ∗
          ((sp + 0x1f0#64) ↦₆₄ w11) ∗
          words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗
          ((sp + 0x228#64) ↦₆₄ w18) ∗
          ((sp + 0x230#64) ↦₆₄ w19) ∗
          words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
          ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
          ((sp + 0x2ac#64) ↦₈ g2ac) ∗
          words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
          ((sp + 0x520#64) ↦₆₄ w4) ∗
          ((sp + 0x528#64) ↦₆₄ w5) ∗
          ((msgA + 0x68#64) ↦₃₂ counter))
    h1b ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s1b P1b ⟨hP1b, hmeta1b, hx0_1b, hx1_1b, hx8_1b, hx19_1b, hx20_1b, hx21_1b, hx22_1b,
      hx23_1b, hx24_1b, hx25_1b, hx27_1b, hx28_1b, hq0_1b, hq2_1b⟩ hpc1b
  subst hP1b
  have h1c := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_1c_wp_trap (C := C) (abs := abs)
    (w8 := w8) (w9 := w9) (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19)
    (w20 := w20) (w21 := w21) (w22 := w22) (w23 := w23)
    (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19)
    (d20 := d20) (d21 := d21) (d22 := d22) (d23 := d23)
    himg hpc1b hmeta1b (hx25_1b.trans hx25_1a) (hx27_1b.trans hx27_1a) hq0_1b
  refine SepWP.bind_framed
    (F := ((sp + 0x20#64) ↦₆₄ locA) ∗
          ((sp + 0x28#64) ↦₃₂ g28) ∗
          ((sp + 0x30#64) ↦₆₄ remA) ∗
          ((sp + 0x38#64) ↦₆₄ cap) ∗
          words8At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 ∗
          words8At (sp + 0x80#64) d8 d9 d10 d11 d12 d13 d14 d15 ∗
          words8At (sp + 0x100#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
          ((sp + 0x190#64) ↦₆₄ cap) ∗
          words4At (sp + 0x198#64) w0 w1 w2 w3 ∗
          ((sp + 0x1b8#64) ↦₆₄ w4) ∗
          ((sp + 0x1c0#64) ↦₆₄ w5) ∗
          ((sp + 0x1c8#64) ↦₆₄ w6) ∗
          ((sp + 0x1d0#64) ↦₆₄ w7) ∗
          ((sp + 0x1e8#64) ↦₆₄ w10) ∗
          ((sp + 0x1f0#64) ↦₆₄ w11) ∗
          words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗
          ((sp + 0x218#64) ↦₆₄ w16) ∗
          ((sp + 0x220#64) ↦₆₄ w17) ∗
          words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
          ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
          ((sp + 0x2ac#64) ↦₈ g2ac) ∗
          words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
          ((sp + 0x520#64) ↦₆₄ w4) ∗
          ((sp + 0x528#64) ↦₆₄ w5) ∗
          ((msgA + 0x68#64) ↦₃₂ counter))
    h1c ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s1c P1c ⟨hP1c, hmeta1c, hx0_1c, hx1_1c, hx8_1c, hx19_1c, hx20_1c, hx21_1c, hx22_1c,
      hx23_1c, hx24_1c, hx25_1c, hx27_1c, hx28_1c, hq0_1c, hq2_1c⟩ hpc1c
  subst hP1c
  have h1d := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_1d_wp_trap (C := C) (abs := abs)
    (remA := remA) (msgA := msgA) (g2a0 := g2a0)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (w6 := w6) (w7 := w7) (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11)
    (w12 := w12) (w13 := w13) (w14 := w14) (w15 := w15)
    (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14) (d15 :=
      d15)
    (counter := counter) (g28 := g28) (g2ac := g2ac)
    himg hpc1c hmeta1c (hx8_1c.trans hx8_1b)
    (hx22_1c.trans (hx22_1b.trans (hx22_1a.trans hx22)))
    (hx23_1c.trans (hx23_1b.trans (hx23_1a.trans hx23)))
    (hx25_1c.trans (hx25_1b.trans hx25_1a))
    hq0_1c (hq2_1c.trans hq2_1b)
  refine SepWP.bind_framed
    (F := ((sp + 0x20#64) ↦₆₄ locA) ∗
          ((sp + 0x30#64) ↦₆₄ remA) ∗
          ((sp + 0x38#64) ↦₆₄ cap) ∗
          words8At (sp + 0xc0#64) w16 w17 w18 w19 w20 w21 w22 w23 ∗
          words8At (sp + 0x100#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
          ((sp + 0x190#64) ↦₆₄ cap) ∗
          words4At (sp + 0x198#64) w0 w1 w2 w3 ∗
          ((sp + 0x1b8#64) ↦₆₄ w4) ∗
          ((sp + 0x1c0#64) ↦₆₄ w5) ∗
          ((sp + 0x1c8#64) ↦₆₄ w6) ∗
          ((sp + 0x1d0#64) ↦₆₄ w7) ∗
          ((sp + 0x1d8#64) ↦₆₄ w8) ∗
          ((sp + 0x1e0#64) ↦₆₄ w9) ∗
          ((sp + 0x218#64) ↦₆₄ w16) ∗
          ((sp + 0x220#64) ↦₆₄ w17) ∗
          ((sp + 0x228#64) ↦₆₄ w18) ∗
          ((sp + 0x230#64) ↦₆₄ w19) ∗
          words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
          words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31)
    h1d ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro sf Pf ⟨hPf, hmetaf, hx0_f, hx1_f, hx8_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx27_f, hx28_f⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨(s1c.readReg64 .x26).setWidth 8, ?_, hmetaf,
    hx0_f.trans (hx0_1c.trans hx0_1b),
    hx1_f.trans (hx1_1c.trans hx1_1b),
    hx8_f,
    hx19_f.trans (hx19_1c.trans (hx19_1b.trans hx19_1a)),
    hx20_f.trans (hx20_1c.trans (hx20_1b.trans hx20_1a)),
    hx21_f.trans (hx21_1c.trans (hx21_1b.trans hx21_1a)),
    hx22_f.trans (hx22_1c.trans (hx22_1b.trans hx22_1a)),
    hx23_f.trans (hx23_1c.trans (hx23_1b.trans hx23_1a)),
    hx24_f.trans (hx24_1c.trans (hx24_1b.trans hx24_1a)),
    hx25_f.trans (hx25_1c.trans (hx25_1b.trans hx25_1a)),
    hx27_f.trans (hx27_1c.trans (hx27_1b.trans hx27_1a)),
    hx28_f.trans (hx28_1c.trans hx28_1b)⟩
  rw [words32At_40_eq, words32At_198_eq]
  dsimp only [sp]; sep_ac_rfl

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
