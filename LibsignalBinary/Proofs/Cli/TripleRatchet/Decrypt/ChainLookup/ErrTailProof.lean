/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Defs
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.ErrTailSym
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
import ProofLib.SepLogic.WPp

/-!
# `try_decrypt_with_state` Error Tail Proof

Proves the error cleanup and return epilogue contract (`ErrTailSpec`, `+0x30c → +0x3b0`) for
`try_decrypt_with_state` in the CLI image, including the `Stage2ContractsX` variant (`errTail_ok_x`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Writes `speAt` to `x.ret`, drops `tr.ratchet.receiver_chains` and `tr.pqr_state`, and executes
the return epilogue (`+0x30c → +0x3b0`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok_ext_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpecExt_trap img C A ctl uuidTryParse S ext := by
  intro himg hA hdrop x trG tr st1 e R s0 s he hmod1 hmod2 herr
  rcases herr with ⟨hpc, hmeta, hx19, hx20, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta.to_wpInv hmeta
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hmem_tr :
      s.mem ⊨ trAt A (sp + 0x38#64) trG tr ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion x.ret 48 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion x.ret 48 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp] at hmem1 ⊢; convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_speBodyAt he hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 =
      memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide,
        memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗
         (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    rw [h140_split] at hmem3
    dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp :
      SepWP (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.retEpiloguePC img) s
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         ((sp + 0x140#64) ↦₆₄ t0) ∗
         ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
         (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStack)
        (fun sf P =>
          P = (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
               ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
               ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
               ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
               ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
               ((sp + 0x140#64) ↦₆₄ w0) ∗
               ((sp + 0x148#64) ↦₆₄ w1) ∗
               ((sp + 0x150#64) ↦₆₄ w2) ∗
               words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
               (x.ret ↦₆₄ speTag e) ∗
                words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
                A.pool ∗ stackAt sp dropChainStack) ∧
           tryDecryptWPInv s0 sf) := by
    have hcopy := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_copy_spe_wp (img := img) (ext := ext)
      (chainsPtr := trG.ratchet.chainsPtr) (chainsLen := BitVec.ofNat 64 cs.length)
      (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
      (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
      (t0 := t0) (t1 := t1) (t2 := t2)
      himg hpc hmeta_wp hx19 hx20 hx26
    refine SepWP.bind_framed
      (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
            A.pool ∗ stackAt sp dropChainStack)
      hcopy ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro s1 P1 ⟨hP1, hmeta1, hx20_1, hx21_1⟩ hpc1
    subst hP1
    have hcs_lt' : cs.length * 104 < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 104 hcs_le) hcs_lt
    have hdrop_cs := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_drop_chains_wp (img := img) (A := A) (ext := ext)
      himg hdrop hcs_lt' hpc1 hmeta1 hx20_1 hx21_1
    refine SepWP.bind_framed
      (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))
      hdrop_cs ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro s2 P2 ⟨hP2, hmeta2, hx20_2⟩ hpc2
    subst hP2
    have hre_cs :
        (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗ stackAt sp dropChainStack) ∗
          (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
           ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
           ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
           ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
           ((sp + 0x140#64) ↦₆₄ w0) ∗
           ((sp + 0x148#64) ↦₆₄ w1) ∗
           ((sp + 0x150#64) ↦₆₄ w2) ∗
           words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
           (x.ret ↦₆₄ speTag e) ∗
           words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
           (if trG.ratchet.chainsCap = 0#64 then emp
            else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
              memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
           (if trG.pq.cap = 0#64 then emp
            else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
              memRegion trG.pq.ptr trG.pq.cap.toNat)))) ⊢
        ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
          A.pool ∗ stackAt sp allocHookStack) ∗
         (memRegion (sp - 4144#64) 48 ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗
          ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗
          words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          (x.ret ↦₆₄ speTag e) ∗
          words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
             memRegion trG.pq.ptr trG.pq.cap.toNat))) := by
      rw [stackAt_dropChainStack_sub sp]
      have hcomm1 :
          (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗
              (stackAt sp allocHookStack ∗ memRegion (sp - 4144#64) 48)) ∗
            (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
             ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
             ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
             ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
             ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
             ((sp + 0x140#64) ↦₆₄ w0) ∗
             ((sp + 0x148#64) ↦₆₄ w1) ∗
             ((sp + 0x150#64) ↦₆₄ w2) ∗
             words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
             (x.ret ↦₆₄ speTag e) ∗
             words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
             (if trG.ratchet.chainsCap = 0#64 then emp
              else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
                memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                  ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
             (if trG.pq.cap = 0#64 then emp
              else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
                memRegion trG.pq.ptr trG.pq.cap.toNat)))) =
          (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
           (memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((trG.ratchet.chainsCap.toNat - cs.length) * 104))) ∗
           (A.pool ∗ stackAt sp allocHookStack ∗ memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))) := by dsimp only [sp]; sep_ac_rfl
      have hcomm2 :
          ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
            A.pool ∗ stackAt sp allocHookStack) ∗
           (memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))) =
          (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
           (if trG.ratchet.chainsCap = 0#64 then emp
            else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
              memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
           (A.pool ∗ stackAt sp allocHookStack ∗ memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))) := by dsimp only [sp]; sep_ac_rfl
      rw [hcomm1, hcomm2]
      exact sepConj_mono_right (sepConj_mono_left (chains_recombine_entails hcs_le hcs_lt))
    refine SepWP.mono_pre (by dsimp only [sp] at hre_cs ⊢; exact hre_cs) ?_
    have hdealloc_cs := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_dealloc_chains_wp (img := img) (A := A) (ext := ext)
      himg hA.toAllocContracts hcs_lt hpc2 hmeta2 hx20_2
    refine SepWP.bind_framed
      (F := memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))
      hdealloc_cs ?_ ?_
    · dsimp only [sp]
    intro s3 P3 ⟨hP3, hmeta3⟩ hpc3
    subst hP3
    have hdealloc_pq := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_dealloc_pq_wp (img := img) (A := A) (ext := ext)
      (pqCap := trG.pq.cap) (pqPtr := trG.pq.ptr)
      himg hA.toAllocContracts hpc3 hmeta3
    refine SepWP.bind_framed
      (F := memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4)
      hdealloc_pq ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro sf Pf ⟨hPf, hmeta_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
    rw [stackAt_dropChainStack_sub sp]
    dsimp only [sp]; sep_ac_rfl
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap at hmem4
  rw [stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         ((sp + 0x140#64) ↦₆₄ t0) ∗
         ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
         (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗
         H_spe ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
         logOff img ∗
         tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]
    exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]
    exact decRel_afterTrFrom x.G
  apply CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.reaches_epilogue_to_outcome himg x x.G.afterTrFrom R s0 s hnpan hG'
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩
  subst hPf
  refine ⟨hmeta_f, ?_⟩
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap
  rw [hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hdec_ent :
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      vecResultAt A x.ret (x.model C S uuidTryParse).1 := by
    rw [hmod1]
    exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗
          ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗
          ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
          memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗
          ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗
          words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          (stackAt sp dropChainStack ∗
           memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ∗ R := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right
      (sepConj_mono hdec_ent
      (sepConj_mono_left
        (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
          (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4))))
    hmem_f_re

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpecExt img C A ctl uuidTryParse S ext :=
  fun himg hA => CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok_ext_trap himg hA.to_trap

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpec_trap img C A ctl uuidTryParse S abs :=
  fun himg hH hdrop => CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok_ext_trap himg (Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A S abs hH) hdrop

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpec img C A ctl uuidTryParse S abs :=
  fun himg hH hdrop => CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok_ext himg (Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl S abs hH) hdrop

/-- `Stage2ContractsX` variant of `errTail_ok_ext_trap`, writing `decResultFnAt` to `x.ret`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok_x {img : Obj.Image} {C : Crypto}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpecX img C encFn decFn A ctl uuidTryParse S ext := by
  intro himg hA hdrop x trG tr st1 e R s0 s he hmod1 hmod2 herr
  rcases herr with ⟨hpc, hmeta, hx19, hx20, b, hb, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta.to_wpInv hmeta
  have hinv : img.FrozenLoaded s ∧ s.symtab = img.symtab :=
    ⟨hmeta.2.2.2.2.2.2.1, hmeta.2.2.2.2.2.2.2.1⟩
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  set tag := if b then speTag e else speWord 20
  have hmem_tr :
      s.mem ⊨ trAt A (sp + 0x38#64) trG tr ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion x.ret 48 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         (if b then speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e
          else memRegion (sp + 0x168#64) 40) ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, hpq_lt, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ (if b then speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e
               else memRegion (sp + 0x168#64) 40) ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion x.ret 48 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp] at hmem1 ⊢; convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ :=
    exists_words5_of_errTailBody he hb hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 =
      memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide,
        memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗
         (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    rw [h140_split] at hmem3
    dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp :
      SepWP (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.retEpiloguePC img) s
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         ((sp + 0x140#64) ↦₆₄ t0) ∗
         ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
         (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStackX)
        (fun sf P =>
          P = (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
               ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
               ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
               ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
               ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
               ((sp + 0x140#64) ↦₆₄ w0) ∗
               ((sp + 0x148#64) ↦₆₄ w1) ∗
               ((sp + 0x150#64) ↦₆₄ w2) ∗
               words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
               (x.ret ↦₆₄ tag) ∗
               words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
               A.pool ∗ stackAt sp dropChainStackX) ∧
           tryDecryptWPInv s0 sf) := by
    have hcopy := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_copy_spe_wp (img := img) (ext := ext)
      (chainsPtr := trG.ratchet.chainsPtr) (chainsLen := BitVec.ofNat 64 cs.length)
      (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
      (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
      (t0 := t0) (t1 := t1) (t2 := t2)
      himg hpc hmeta_wp hx19 hx20 hx26
    refine SepWP.bind_framed_callInv
      (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
            A.pool ∗ stackAt sp dropChainStackX)
      hinv hcopy ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro s1 P1 ⟨hP1, hmeta1, hx20_1, hx21_1⟩ hpc1 hinv1
    subst hP1
    have hcs_lt' : cs.length * 104 < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 104 hcs_le) hcs_lt
    have hdrop_cs := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_drop_chains_x_wp (img := img) (A := A) (ext := ext)
      himg hdrop hcs_lt' hpc1 hmeta1 hinv1 hx20_1 hx21_1
    refine SepWP.bind_framed_callInv
      (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ tag) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))
      hinv1 hdrop_cs ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro s2 P2 ⟨hP2, hmeta2, hx20_2⟩ hpc2 hinv2
    subst hP2
    have hre_cs :
        (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗ stackAt sp dropChainStackX) ∗
          (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
           ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
           ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
           ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
           ((sp + 0x140#64) ↦₆₄ w0) ∗
           ((sp + 0x148#64) ↦₆₄ w1) ∗
           ((sp + 0x150#64) ↦₆₄ w2) ∗
           words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
           (x.ret ↦₆₄ tag) ∗
           words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
           (if trG.ratchet.chainsCap = 0#64 then emp
            else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
              memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
           (if trG.pq.cap = 0#64 then emp
            else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
              memRegion trG.pq.ptr trG.pq.cap.toNat)))) ⊢
        ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
          A.pool ∗ stackAt sp extHookStack) ∗
         (memRegion (sp - 16432#64) 48 ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗
          ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗
          words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          (x.ret ↦₆₄ tag) ∗
          words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
             memRegion trG.pq.ptr trG.pq.cap.toNat))) := by
      rw [stackAt_dropChainStackX_sub sp]
      have hcomm1 :
          (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗
              (stackAt sp extHookStack ∗ memRegion (sp - 16432#64) 48)) ∗
            (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
             ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
             ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
             ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
             ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
             ((sp + 0x140#64) ↦₆₄ w0) ∗
             ((sp + 0x148#64) ↦₆₄ w1) ∗
             ((sp + 0x150#64) ↦₆₄ w2) ∗
             words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
             (x.ret ↦₆₄ tag) ∗
             words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
             (if trG.ratchet.chainsCap = 0#64 then emp
              else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
                memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                  ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
             (if trG.pq.cap = 0#64 then emp
              else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
                memRegion trG.pq.ptr trG.pq.cap.toNat)))) =
          (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
           (memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((trG.ratchet.chainsCap.toNat - cs.length) * 104))) ∗
           (A.pool ∗ stackAt sp extHookStack ∗ memRegion (sp - 16432#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ tag) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))) := by dsimp only [sp]; sep_ac_rfl
      have hcomm2 :
          ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
            A.pool ∗ stackAt sp extHookStack) ∗
           (memRegion (sp - 16432#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ tag) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))) =
          (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
           (if trG.ratchet.chainsCap = 0#64 then emp
            else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
              memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
           (A.pool ∗ stackAt sp extHookStack ∗ memRegion (sp - 16432#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ tag) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))) := by dsimp only [sp]; sep_ac_rfl
      rw [hcomm1, hcomm2]
      exact sepConj_mono_right (sepConj_mono_left (chains_recombine_entails hcs_le hcs_lt))
    refine SepWP.mono_pre (by dsimp only [sp] at hre_cs ⊢; exact hre_cs) ?_
    have hdealloc_cs := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_dealloc_chains_x_wp (img := img) (A := A) (ext := ext)
      himg hA.toAllocContractsX hcs_lt hpc2 hmeta2 hinv2 hx20_2
    refine SepWP.bind_framed_callInv
      (F := memRegion (sp - 16432#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ tag) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))
      hinv2 hdealloc_cs ?_ ?_
    · dsimp only [sp]
    intro s3 P3 ⟨hP3, hmeta3⟩ hpc3 hinv3
    subst hP3
    have hdealloc_pq := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_dealloc_pq_x_wp (img := img) (A := A) (ext := ext)
      (pqCap := trG.pq.cap) (pqPtr := trG.pq.ptr)
      himg hA.toAllocContractsX hpq_lt hpc3 hmeta3 hinv3
    refine SepWP.bind_framed
      (F := memRegion (sp - 16432#64) 48 ∗
            ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ tag) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4)
      hdealloc_pq ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro sf Pf ⟨hPf, hmeta_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
    rw [stackAt_dropChainStackX_sub sp]
    dsimp only [sp]; sep_ac_rfl
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap at hmem4
  rw [stackAt_tryDecryptSubStack_sub s0.sp dropChainStackX (by decide)] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         ((sp + 0x140#64) ↦₆₄ t0) ∗
         ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
         (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStackX) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStackX) ∗
         H_spe ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
         logOff img ∗
         tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.modelFn C decFn S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]
    exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.modelFn C decFn S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]
    exact decRel_afterTrFrom x.G
  apply CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.reaches_epilogue_to_outcome_fn himg x x.G.afterTrFrom R s0 s hnpan hG'
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩
  subst hPf
  refine ⟨hmeta_f, ?_⟩
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap
  rw [hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStackX (by decide)]
  have hdec_ent :
      ((x.ret ↦₆₄ tag) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      decResultFnAt A x.ret (x.modelFn C decFn S uuidTryParse).1 := by
    rw [hmod1]
    exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ tag) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗
          ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗
          ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
          memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗
          ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗
          words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          (stackAt sp dropChainStackX ∗
           memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStackX)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ∗ R := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right
      (sepConj_mono hdec_ent
      (sepConj_mono_left
        (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
          (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4))))
    hmem_f_re

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
