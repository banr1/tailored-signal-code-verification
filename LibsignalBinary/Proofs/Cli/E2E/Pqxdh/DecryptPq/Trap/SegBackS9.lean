/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegBackS9
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegBackDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegBackDefs
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegBackDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Trap-at-RNG Segment S9 Proof (`ApplyRatchet` & Return)

Proves `s9_ok_trap : S9Spec_trap` (`+0x6a4 → +0x4b8 → +0x394 → +0x3b0`) for
`try_decrypt_with_state::<signal_session_handshake::Coins>` on `trTrapProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

open CryptoVerification.LibsignalSession

open ProofLib.ProgramReflection

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] BitVec.toNat_zero

/-! ## Segment 9 (`+0x6a4 → +0x4b8 → +0x394 → +0x3b0`) -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s9_from_6d0_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hTrApply : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TrApplyOk_trap img.base C A abs)
    (hClearUpk : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ClearUpkOk_trap img.base C A abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (newPqrCap newPqrPtr ptCap ptPtr : BitVec 64)
    (R : SepProp) (s0 s1 : State)
    (hok : (x.model C S uuidTryParse).1 = .ok pt)
    (hst : (x.model C S uuidTryParse).2 =
      (({ tr with pqrState :=
        newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage)
    (hpad : trG.ratchet.senderPad.length = 100)
    (hnew_le : newPqrState.length ≤ newPqrCap.toNat)
    (hnew_lt : newPqrCap.toNat < 2 ^ 63)
    (hnew_nz : newPqrPtr ≠ 0)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_nz : ptPtr ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hpc1 : s1.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 1744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1504#64)
    (hsp_al1 : s1.spAligned = true)
    (htr1 : s1.trace = s0.trace)
    (hfl1 : img.FrozenLoaded s1)
    (hsym1 : s1.symtab = img.symtab)
    (hx9_1 : s1.readReg64 .x9 = s0.sp - 800#64)
    (hx19_1 : s1.readReg64 .x19 = x.ret)
    (hx20_1 : s1.readReg64 .x20 = s0.sp - 1184#64)
    (hx21_1 : s1.readReg64 .x21 = x.ss)
    (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length)
    (_hx29_1 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    SepWPp (trTrapProgAt img.base C abs) (s0.readReg64 .lr) s1
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trWithoutPqAt A (s0.sp - 1448#64) trG.ratchet tr ∗
       ((s0.sp - 1272#64) ↦₆₄ trG.pq.cap) ∗
       ((s0.sp - 1264#64) ↦₆₄ trG.pq.ptr) ∗
       ((s0.sp - 1256#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       (if newPqrCap
         = 0 then emp else (A.live newPqrPtr newPqrCap.toNat 1 ∗ (newPqrPtr ↦ₛ newPqrState)) ∗
         memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat -
           newPqrState.length)) ∗
       ((s0.sp - 528#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 520#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 512#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (if ptCap = 0 then emp else (A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt)) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       memRegion x.ret 8 ∗
       memRegion (x.ret + 8#64) 8 ∗
       memRegion (x.ret + 16#64) 8 ∗
       memRegion (x.ret + 24#64) 8 ∗
       memRegion (x.ret + 32#64) 16 ∗
       memRegion (s0.sp - 1504#64) 8 ∗
       ((s0.sp - 1496#64) ↦₆₄ newPqrCap) ∗
       memRegion (s0.sp - 1488#64) 24 ∗
       ((s0.sp - 1464#64) ↦₆₄ newPqrPtr) ∗
       memRegion (s0.sp - 1456#64) 8 ∗
       memRegion (s0.sp - 1184#64) 8 ∗
       memRegion (s0.sp - 1176#64) 8 ∗
       memRegion (s0.sp - 1168#64) 8 ∗
       memRegion (s0.sp - 1160#64) 16 ∗
       memRegion (s0.sp - 1144#64) 8 ∗
       memRegion (s0.sp - 1136#64) 8 ∗
       memRegion (s0.sp - 1128#64) 8 ∗
       memRegion (s0.sp - 1120#64) 16 ∗
       memRegion (s0.sp - 1104#64) 264 ∗
       memRegion (s0.sp - 840#64) 120 ∗
       ((s0.sp - 720#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 712#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 704#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       memRegion (s0.sp - 696#64) 168 ∗
       memRegion (s0.sp - 504#64) 0x198 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
       logOff img ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).post x s0 sf ∗
          R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗
        R) → (sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R)) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.hfn_tryDecrypt
  decrypt_fetches_cli_trap img.base C abs hfn 0x6d0 36
  decrypt_fetches_cli_trap img.base C abs hfn 0x4b8 72
  decrypt_fetches_cli_trap img.base C abs hfn 0x394 32
  have hmemcpy := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.memcpy_ok_at_trap img C abs
  have hbl_trApply := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.bl_trApply_target_trap img C abs
  have hbl_clearUpk := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.bl_clearUpk_target_trap img C abs
  dsimp only [trTrapProgAt, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TrApplyOk_trap, TrApplyOkExt, tripleRatchetProgAtExt, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ClearUpkOk_trap] at *
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics (trTrapExterns C
    abs))).fnAddr trApplyName = trApply_entry at hbl_trApply hTrApply
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics (trTrapExterns C
    abs))).fnAddr clearUpkName = clearUpk_entry at hbl_clearUpk hClearUpk
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  simp only [wp_norm] at hpc1 hsp1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1184#64) (by sep_focus) fun w1184 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1176#64) (by sep_focus) fun w1176 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1168#64) (by sep_focus) fun w1168 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun w1128 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 8#64) (by sep_focus) fun wret8 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 16#64) (by sep_focus) fun wret16 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 24#64) (by sep_focus) fun wret24 => ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl1 hsym1 (mid := entry + bv% ((2^64 + ls_off% "memcpy" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hfl2 hsym2
  refine SepWPp.mono_focus
    (trAt_of_withoutPq A s0.sp trG tr newPqrCap newPqrPtr newPqrState hnew_le hnew_lt hnew_nz)
    (by sep_focus) ?_
  rw [trAt_eq_stack_heap A (s0.sp - 1448#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } hpad]
  refine SepWPp.elim_exists_focus
    (Φ := fun pad : BitVec 32 =>
      ((s0.sp - 1448#64) ↦ₛ trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
        { tr with pqrState := newPqrState } pad) ∗
      trHeapPart A { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState })
    (by sep_focus) fun pad => ?_
  have hbs_len : (trStackBytes { trG with pq := ⟨newPqrCap,
    newPqrPtr⟩ } { tr with pqrState := newPqrState } pad).length = 264 :=
    length_trStackBytes _ _ pad hpad
  generalize hbs_def : trStackBytes { trG with pq := ⟨newPqrCap,
    newPqrPtr⟩ } { tr with pqrState := newPqrState } pad = bs at hbs_len ⊢
  rw [show memRegion (s0.sp - 1104#64) 264 = memRegion (s0.sp - 1104#64) bs.length by rw [hbs_len]]
  simp only [← sepConj_assoc]
  refine SepWPp.call_frame_frozen (img := img) (spec := sessionMemcpyRegionSpec)
    (x := (s0.sp - 1104#64, s0.sp - 1448#64, bs))
    (T := memRegion (s0.sp - 1104#64) bs.length ∗ ((s0.sp - 1448#64) ↦ₛ bs))
    (ret_pc := entry + 1248#64)
    hfl2 hsym2 hmemcpy (by rfl) (by exact hrun1)
    (BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm, hbs_len]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [sessionMemcpyRegionSpec,
      memcpyRegionSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [sessionMemcpyRegionSpec,
      memcpyRegionSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl2 hsym2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    _hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx24_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx24_2 hvregs_2
  dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
  simp only [wp_norm, sepConj_assoc]
  apply SepWPp.elim_pure; rintro ⟨_, htr2⟩
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  rw [← hbs_def]
  refine SepWPp.mono_focus
    (trAt_of_stack_heap A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } pad hpad)
    (by sep_focus) ?_
  rw [hbs_def]
  rw [stackAt_sub_split (s0.sp - 1504#64) trApplyStack (by decide)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl2 hsym2 (mid := trApply_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hfl3 hsym3
  refine SepWPp.call_frame_frozen (img := img) (spec := trApplySpec A)
    (x := ⟨s0.sp - 1104#64, { trG with pq := ⟨newPqrCap, newPqrPtr⟩ },
           { tr with pqrState := newPqrState }, x.ss, x.G.afterTrFrom, st1⟩)
    (T := trAt A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
            { tr with pqrState := newPqrState } ∗
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          stackAt (s0.sp - 1504#64) trApplyStack ∗ A.pool)
    (ret_pc := entry + 1260#64)
    hfl3 hsym3 hTrApply (by rfl) (by exact hrun2)
    (BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [trApplySpec]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [trApplySpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by
      have h0m : s0.trace <+: (s2.writeReg64 .x0 (s0.sp - 1104#64)
        |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 (entry + 1260#64)
        |>.setPC trApply_entry).trace := by
        rw [show (s2.writeReg64 .x0 (s0.sp - 1104#64)
          |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 (entry + 1260#64)
          |>.setPC trApply_entry).trace = s2.trace from rfl, htr20]
      exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecrypt_onPanic_of_callee C A ctl S img x s0 _ sf _ R h0m hm_pan) ?_
  clear hfl3 hsym3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hfl3 hsym3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3,
    _hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx24_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx24_3 hvregs_3
  dsimp only [trApplySpec]
  simp only [wp_norm, hsp2, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr3
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  apply SepWPp.elim_exists; intro G1
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hG1
  refine SepWPp.mono_focus (trApplyStack_to_clearUpkStack s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl3 hsym3 (mid := clearUpk_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hfl4 hsym4
  refine SepWPp.call_frame_frozen (img := img) (spec := clearUpkSpec A)
    (x := ⟨x.ss, G1, ({ tr with pqrState := newPqrState }).applyToSessionState st1⟩)
    (T := sessionStateAt A x.ss G1 (({ tr with pqrState := newPqrState }).applyToSessionState st1) ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) clearUpkStack)
    (ret_pc := entry + 1268#64)
    hfl4 hsym4 hClearUpk (by rfl) (by exact hrun3)
    (BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
    (by dsimp only [clearUpkSpec]; simp only [wp_norm, hsp3]; rfl)
    (by simp only [wp_norm])
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [clearUpkSpec] at h; rw [satisfies_pure_sepConj] at h; exact
      h.1)
    (fun sf _ hm_pan => by dsimp only [clearUpkSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl4 hsym4
  intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hfl4 hsym4
  simp only [wp_norm, hsp3] at hsp4
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4,
    _hx29_4, hvregs_4⟩
  simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx24_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx24_4 hvregs_4
  dsimp only [clearUpkSpec]
  simp only [wp_norm, hsp3, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr4
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  refine SepWPp.mono_focus (clearUpkStack_to_subStack s0.sp) (by sep_focus) ?_
  refine SepWPp.mono_focus
    (s9_local_frame_entails_memRegion s0.sp newPqrCap newPqrPtr ptCap ptPtr
      (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      ptCap ptPtr (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      bs hbs_len) (by sep_focus) ?_
  refine SepWPp.mono_focus (Entails.refl (tryDecryptSavedRegs s0.sp s0)) (by sep_focus) ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret) (by sep_focus) fun wret => ?_
  unfold tryDecryptSavedRegs
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun4)
  refine ⟨fun hmf => ?_, by simp only [wp_norm], ?_⟩
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage]
    rw [hok]
    rw [← hst] at hmf
    have hdec := decRel_of_trApplyRel hG1
    have hsaved := tryDecryptSavedRegs_entails_memRegion s0.sp s0
    unfold tryDecryptSavedRegs at hsaved
    have hmf1 := Satisfies.mono_focus hsaved (by sep_focus) hmf
    have hmf3 := Satisfies.mono_focus (stackAt_rootStack_of_parts s0.sp) (by sep_focus) hmf1
    rw [show (18446744073709551614#64 : BitVec 64) = okTagVec from rfl] at hmf3
    have hmf4 := Satisfies.mono_focus
      (decResultAt_ok_of_parts A x.ret pt ptCap ptPtr hpt_le hpt_lt hpt_nz) (by sep_focus) hmf3
    have hss :
        sessionStateAt A x.ss { G1 with pending := none, kyber := none }
          (x.model C S uuidTryParse).2 ⊢
        ∃∗ G' : SessionGhost,
          ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
          sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 := by
      refine Entails.trans ?_
        (Entails.sepExists_intro
          (P := fun G' : SessionGhost =>
            ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
            sessionStateAt A x.ss G' (x.model C S uuidTryParse).2)
          { G1 with pending := none, kyber := none })
      exact Entails.pure_right hdec (Entails.refl _)
    have hmf5 := Satisfies.mono_focus hss (by sep_focus) hmf4
    clear hmf hmf1 hmf3 hmf4
    have hno_pan : (Except.ok pt : Except SignalProtocolError (List (BitVec 8))) ≠ .error .panic :=
      nofun
    simp only [wp_norm, sepConj_assoc, satisfies_pure_sepConj] at hmf5 ⊢
    refine ⟨⟨hno_pan, htr40⟩, ?_⟩
    generalize (∃∗ G',
      ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
      sessionStateAt A x.ss G' (x.model C S uuidTryParse).2) = SS at hmf5 ⊢
    sep_close
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, hvregs_4]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s9_ok_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec_trap img C A ctl uuidTryParse S abs := by
  intro himg hS hTrApply hClearUpk x trG tr st1 newPqrState pt R s0 s hok hst h9
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.hfn_tryDecrypt
  decrypt_fetches_cli_trap img.base C abs hfn 0x6a4 44
  have hS9_pc := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS9PC_eq_trap himg C abs
  have hdealloc := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.dealloc_ok_at_trap img C A S abs hS
  rcases h9 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx23, hx24, newPqrCap, newPqrPtr, hnew_le, hnew_lt, hnew_nz, hmem⟩
  rw [hS9_pc] at hpc
  have h6d0 := @CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s9_from_6d0_trap img C A ctl S abs hTrApply hClearUpk x trG tr st1
    newPqrState pt newPqrCap newPqrPtr
  clear hTrApply hClearUpk
  dsimp only [trTrapProgAt] at *
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  have hpad : trG.ratchet.senderPad.length = 100 := by
    have htr_front := hmem
    rw [← sepConj_assoc, sepConj_comm (sessionStateAt A x.ss x.G.afterTrFrom st1),
      sepConj_assoc] at htr_front
    exact trAt_senderPad_len htr_front
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap at hmem
  rw [trAt_eq_withoutPq A s0.sp trG tr,
      s9_scr_split s0.sp,
      s9_ret_split x.ret,
      show s0.sp - 1504#64 + 0x3d0#64 = s0.sp - 528#64 by bv_omega,
      show s0.sp - 1504#64 + 0x8#64 = s0.sp - 1496#64 by bv_omega,
      show s0.sp - 1504#64 + 0x10#64 = s0.sp - 1488#64 by bv_omega,
      show s0.sp - 1504#64 + 0x28#64 = s0.sp - 1464#64 by bv_omega,
      show s0.sp - 1504#64 + 0x30#64 = s0.sp - 1456#64 by bv_omega,
      show s0.sp - 1504#64 + 0x3e8#64 = s0.sp - 504#64 by bv_omega] at hmem
  simp only [wp_norm] at hpc hx20 hx23 hx29
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_reaches_outcome hmem ?_
  refine SepWPp.elim_pure_focus
    (φ := tr.pqrState.length ≤ trG.pq.cap.toNat ∧ trG.pq.cap.toNat < 2 ^ 63 ∧ trG.pq.ptr ≠ 0)
    (by sep_focus) fun ⟨hpq_le, hpq_lt, hpq_nz⟩ => ?_
  refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
    (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
  rw [show s0.sp - 528#64 + 8#64 = s0.sp - 520#64 by bv_omega,
      show s0.sp - 528#64 + 16#64 = s0.sp - 512#64 by bv_omega]
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 720#64) (by sep_focus) fun w720 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 712#64) (by sep_focus) fun w712 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 704#64) (by sep_focus) fun w704 => ?_
  by_cases hpq_cap : trG.pq.cap = 0#64
  · refine SepWPp.mono_focus (newPqr_zero_prep A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap) (by
    sep_focus) ?_
    rw [emp_sepConj]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl hsym (mid := entry + 1744#64)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hfl1 hsym1
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun) (by simp only [wp_norm, hsp])
        (BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al)
        htr hfl1 hsym1
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19])
        (by simp only [wp_norm, hx20])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx24])
        (by simp only [wp_norm, hx29])
        (by simp only [wp_norm, hvregs]))
  · refine SepWPp.mono_focus (newPqr_dealloc_prep' A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap
    hpq_le hpq_lt) (by sep_focus) ?_
    rw [stackAt_sub_split (s0.sp - 1504#64) allocHookStack (by decide)]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl hsym (mid := entry + 1728#64)
    wp_steps
    apply SepWP.setPC_setMem_ite_false (by simp only [beq_iff_eq, hpq_cap, not_false_eq_true])
    apply SepWP.done (by rfl) (by exact hrun)
    intro hfl0 hsym0
    apply SepWPp.of_sepWP_frozen hfl0 hsym0 (mid :=
      entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hfl1 hsym1
    refine SepWPp.call_frame_frozen (img := img) (spec := rustDeallocSpec A)
      (x := (trG.pq.ptr, trG.pq.cap.toNat, 1))
      (T := A.pool ∗ A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat ∗
            stackAt (s0.sp - 1504#64) allocHookStack)
      (ret_pc := entry + 1740#64)
      hfl1 hsym1 hdealloc (by rfl) (by exact hrun)
      (BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
      (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp]; rfl)
      (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
      (by sep_focus)
      (fun _ _ _ _ h => by
        dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun sf _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hfl0 hsym0 hfl1 hsym1
    intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hfl1 hsym1
    simp only [wp_norm, hsp] at hsp1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, hx19, hx20, hx21, hx24, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx24_1 hx29_1 hvregs_1
    dsimp only [rustDeallocSpec]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr1
    have htr10 : s1.trace = s0.trace := htr1.trans htr
    refine SepWPp.mono_focus (allocHookStack_to_subStack s0.sp) (by sep_focus) ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl1 hsym1 (mid := entry + 1744#64)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun1)
    intro hfl2 hsym2
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun1) (by simp only [wp_norm, hsp1])
        (BS10.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1)
        htr10 hfl2 hsym2
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19_1])
        (by simp only [wp_norm, hx20_1])
        (by simp only [wp_norm, hx21_1])
        (by simp only [wp_norm, hx24_1])
        (by simp only [wp_norm, hx29_1])
        (by simp only [wp_norm, hvregs_1]))

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD
