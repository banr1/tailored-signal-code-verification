/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244Placed
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

namespace ReceiveRatchetFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

theorem trFrom_step_244_to_ret
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hRemoteIk : RemoteIdentityKeyOkExt img A ext)
    (hDropSpe : DropSpeOkExt img A ext)
    (hDropVecChain : DropVecChainOkExt img.base A ext)
    (x : TrFromGhost) (senderPad : List (BitVec 8))
    (s0 s : State) (post : State → SepProp → Prop)
    (u_284 : BitVec 32)
    (hpad : senderPad.length = 100)
    (hclamp : ∀ sc, x.st.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hchains : x.G.chains.length = x.st.receiverChains.length)
    (hpq_ne : x.G.pq.cap ≠ 0 → 0 < x.G.pq.cap.toNat ∧ x.G.pq.cap.toNat < 2 ^ 63 ∧ x.G.pq.ptr ≠ 0)
    (hlik : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey)
    (hlik_toNat : (BitVec.ofNat 64 x.G.localIk.bytes.length).toNat = x.G.localIk.bytes.length)
    (hrik : match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 580#64)
    (hrun : s.status = .Running) (halign : (s0.sp &&& 0xf#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = x.G.localIk.ptr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 x.G.localIk.bytes.length)
    (hx8 : s.readReg64 .x8 = s0.sp - 160#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.G.pq.cap)
    (hx21 : s.readReg64 .x21 = x.G.pq.ptr)
    (hx22 : s.readReg64 .x22 = x.ss)
    (hx23 : s.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.st.pqRatchetState.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hsp : s.sp = s0.sp - 496#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hdone : ∀ sf,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.trace = s0.trace →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) sf
        (sessionStateAt A x.ss x.G.afterTrFrom x.model.2 ∗
         trResultAt A x.ret x.G x.model.1 ∗
         logOff img ∗ stackAt s0.sp trFromStack ∗ A.pool)
        post) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (((x.G.localIk.ptr ↦ₛ x.G.localIk.bytes) ∗
        vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
        memRegion (s0.sp - 496#64) 40 ∗
        memRegion (s0.sp - 280#64) 184 ∗
        stackAt (s0.sp - 496#64) dropVecChainStack ∗
        (A.pool ∗
         ((s0.sp - 456#64) ↦₆₄ x.G.chainsCap) ∗
         ((s0.sp - 448#64) ↦₆₄ x.G.chainsPtr) ∗
         ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
         vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
         vecU8Buf A x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
         ((s0.sp - 432#64) ↦ₛ optSenderChainBytes x.st.senderChain senderPad) ∗
         ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) ∗
         ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
         ((s0.sp - 288#64) ↦₃₂ x.st.previousCounter) ∗
         ((s0.sp - 284#64) ↦₃₂ u_284) ∗
         memRegion x.ret 264 ∗
         sessionAfter208Frame A x.ss x.G x.st ∗
         (logOff img ∗ trFromSavedRegs s0.sp s0))))
      post := by
  apply trFrom_step_244_to_0e8 himg hA hRemoteIk hDropSpe hDropVecChain
    x.ret x.ss x.G x.st senderPad s0 s (s0.readReg64 .lr)
    (trFromSavedRegs s0.sp s0) post
    hpad hclamp hchains hpq_ne hlik hlik_toNat hrik hfl hsym hpc hrun halign htr
    hx0 hx1 hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 hsp
  intro sf hfl_f hsym_f hpc_f hrun_f htr_f hsp_f hvregs_f
  have hm1 : ∀ a, a = (match x.st.remoteIdentity with
        | some rem =>
          .ok ⟨⟨x.st.rootKey, x.st.senderChain, x.st.receiverChains,
                x.st.previousCounter, maxForwardJumps⟩,
               x.st.pqRatchetState, x.st.localIdentity, rem⟩
        | none => .error (.invalidSessionStructure .missingRemoteIdentity)) →
      trResultAt A x.ret x.G a = trResultAt A x.ret x.G x.model.1 := by
    rintro _ rfl
    rcases x with ⟨ss, G, ⟨sv, lik, rik, rk, pc, sc, rcs, ppk, pqr⟩, ret⟩
    cases rik <;> rfl
  rw [hm1 _ (by rfl), ← trFromGhost_model_snd x]
  have hfn : libsignalSessionCode.fnOff trFromName = num% (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") := by simp only [arm64_norm]
  generalize hentry : (tripleRatchetProgAtExt img.base ext).fnAddr trFromName = entry at hpc_f
  unfold trFromSavedRegs
  apply SepWP.of_sepWP_inv (mid := s0.readReg64 .lr) hfl_f hsym_f
  tr_from_fetches img.base (Rust.withPanics ext) hfn hentry 0x0e8 8
  wp_steps
  examples_clear_fetches
  refine SepWP.fold (stackAt_trFrom_fold s0.sp s0) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hfl_ret hsym_ret
  refine SepWP.mono_pre (Entails.of_eq (by ac_rfl))
    (hdone _
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
      hfl_ret hsym_ret)

theorem SepWP.with_post {prog : Program} {pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (h : ∀ post', post' = post → SepWP prog pc s P post') :
    SepWP prog pc s P post := h post rfl

abbrev trFrom10cTail (img : Obj.Image) (A : RustAlloc) (x : TrFromGhost) (s0 : State) : SepProp :=
  (x.G.localIk.ptr ↦ₛ x.G.localIk.bytes) ∗
  vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
  memRegion (s0.sp - 496#64) 40 ∗
  stackAt (s0.sp - 496#64) dropVecChainStack ∗
  A.pool ∗
  vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
  vecU8Buf A x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
  memRegion x.ret 264 ∗
  logOff img ∗
  trFromSavedRegs s0.sp s0

theorem memRegion_33_sp_456 (sp : BitVec 64) :
    memRegion (sp - 456#64) 33 ⊢
      ∃∗ tag0 : BitVec 8, ∃∗ out32 : List (BitVec 8),
        ⌜out32.length = 32⌝ ∗ ((sp - 456#64) ↦₈ tag0) ∗ ((sp - 455#64) ↦ₛ out32) := by
  have h := memRegion_33_to_tag_and_32 (sp - 456#64)
  have h1 : sp - 456#64 + 1#64 = sp - 455#64 := by bv_omega
  rwa [h1] at h

theorem pubKey_unpack_sp_455 (sp : BitVec 64) {bs : List (BitVec 8)}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
     b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 : BitVec 8}
    {d28 : BitVec 32}
    (h : ∀ a : BitVec 64,
      (a ↦ₛ bs) =
        ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
         ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7) ∗
         ((a + 8#64) ↦₈ b8) ∗ ((a + 9#64) ↦₈ b9) ∗ ((a + 10#64) ↦₈ b10) ∗ ((a + 11#64) ↦₈ b11) ∗
         ((a + 12#64) ↦₈ b12) ∗ ((a + 13#64) ↦₈ b13) ∗ ((a + 14#64) ↦₈ b14) ∗
         ((a + 15#64) ↦₆₄ (b22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15)) ∗
         ((a + 23#64) ↦₃₂ (b26 ++ b25 ++ b24 ++ b23)) ∗
         ((a + 27#64) ↦₈ b27) ∗
         ((a + 28#64) ↦₃₂ d28))) :
    ((sp - 455#64) ↦ₛ bs) =
      (((sp - 455#64) ↦₈ b0) ∗ ((sp - 454#64) ↦₈ b1) ∗ ((sp - 453#64) ↦₈ b2) ∗ ((sp - 452#64) ↦₈ b3) ∗
       ((sp - 451#64) ↦₈ b4) ∗ ((sp - 450#64) ↦₈ b5) ∗ ((sp - 449#64) ↦₈ b6) ∗ ((sp - 448#64) ↦₈ b7) ∗
       ((sp - 447#64) ↦₈ b8) ∗ ((sp - 446#64) ↦₈ b9) ∗ ((sp - 445#64) ↦₈ b10) ∗ ((sp - 444#64) ↦₈ b11) ∗
       ((sp - 443#64) ↦₈ b12) ∗ ((sp - 442#64) ↦₈ b13) ∗ ((sp - 441#64) ↦₈ b14) ∗
       ((sp - 440#64) ↦₆₄ (b22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15)) ∗
       ((sp - 432#64) ↦₃₂ (b26 ++ b25 ++ b24 ++ b23)) ∗
       ((sp - 428#64) ↦₈ b27) ∗
       ((sp - 427#64) ↦₃₂ d28)) := by
  rw [h (sp - 455#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]

theorem trFrom_step_ac_to_244
    {img : Obj.Image}
    {ext : String → Option (State → State)}
    (A : RustAlloc) (x : TrFromGhost) (sg : SenderChainGhost) (sc : SenderChain)
    (s0 s : State) (F_tail : SepProp) (post : State → SepProp → Prop)
    (w_208 : BitVec 64) (b_200 : BitVec 8)
    (d_192 : BitVec 32) (h_188 : BitVec 16)
    (u_296 : BitVec 64) (u_288 u_284 : BitVec 32)
    {rk_b0 rk_b1 rk_b2 rk_b3 rk_b4 rk_b5 rk_b6 : BitVec 8}
    {rk_w7 rk_w15 rk_w23 : BitVec 64} {rk_b31 : BitVec 8}
    (hrk : ∀ a : BitVec 64,
      (a ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) =
        ((a ↦₈ rk_b0) ∗ ((a + 1#64) ↦₈ rk_b1) ∗ ((a + 2#64) ↦₈ rk_b2) ∗ ((a + 3#64) ↦₈ rk_b3) ∗
         ((a + 4#64) ↦₈ rk_b4) ∗ ((a + 5#64) ↦₈ rk_b5) ∗ ((a + 6#64) ↦₈ rk_b6) ∗
         ((a + 7#64) ↦₆₄ rk_w7) ∗ ((a + 15#64) ↦₆₄ rk_w15) ∗ ((a + 23#64) ↦₆₄ rk_w23) ∗
         ((a + 31#64) ↦₈ rk_b31)))
    (hsender_opt : x.G.sender = some sg)
    (hsc_opt : x.st.senderChain = some sc)
    (hclamp_sc : Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hsrk_cmn : (sg.srk.cap + 1#64 == 0#64) = false)
    (hck_cmn : (sg.ck.cap + 1#64 == 0#64) = false)
    (hcmn_chains : (x.G.chainsCap + 1#64 == 0#64) = false)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 172#64)
    (hrun : s.status = .Running) (halign : (s0.sp &&& 0xf#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = s0.sp - 456#64)
    (hx21 : s.readReg64 .x21 = rk_w15)
    (hx22 : s.readReg64 .x22 = rk_w7)
    (hx23 : s.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : s.readReg64 .x25 = 0#64)
    (hx26 : s.readReg64 .x26 = x.ss)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hsp : s.sp = s0.sp - 496#64)
    (hcont : ∀ s_244,
      img.FrozenLoaded s_244 → s_244.symtab = img.symtab →
      s_244.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 580#64 →
      s_244.status = .Running → s_244.trace = s0.trace →
      s_244.readReg64 .x0 = x.G.localIk.ptr →
      s_244.readReg64 .x1 = BitVec.ofNat 64 x.G.localIk.bytes.length →
      s_244.readReg64 .x8 = s0.sp - 160#64 →
      s_244.readReg64 .x19 = x.ret →
      s_244.readReg64 .x20 = x.G.pq.cap →
      s_244.readReg64 .x21 = x.G.pq.ptr →
      s_244.readReg64 .x22 = x.ss →
      s_244.readReg64 .x23 = 0x8000000000000014#64 →
      s_244.readReg64 .x24 = s0.sp - 184#64 →
      s_244.readReg64 .x25 = BitVec.ofNat 64 x.st.pqRatchetState.length →
      s_244.readReg64 .x29 = s0.sp - 96#64 →
      s_244.sp = s0.sp - 496#64 →
      calleeSavedVRegs s_244 = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s_244
        (((s0.sp - 456#64) ↦₆₄ x.G.chainsCap) ∗
         ((s0.sp - 448#64) ↦₆₄ x.G.chainsPtr) ∗
         ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
         ((s0.sp - 432#64) ↦ₛ optSenderChainBytes x.st.senderChain (List.replicate 100 0#8)) ∗
         ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) ∗
         ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
         ((s0.sp - 288#64) ↦₃₂ x.st.previousCounter) ∗
         ((s0.sp - 284#64) ↦₃₂ u_284) ∗
         memRegion (s0.sp - 280#64) 184 ∗
         sessionAfter208Frame A x.ss x.G x.st ∗
         F_tail)
        post) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (memRegion (s0.sp - 184#64) 24 ∗
       ((s0.sp - 456#64) ↦₈ 0#8) ∗
       ((s0.sp - 455#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       memRegion (s0.sp - 423#64) 127 ∗
       ((s0.sp - 296#64) ↦₆₄ u_296) ∗
       ((s0.sp - 288#64) ↦₃₂ u_288) ∗
       ((s0.sp - 284#64) ↦₃₂ u_284) ∗
       memRegion (s0.sp - 280#64) 24 ∗
       memRegion (s0.sp - 256#64) 24 ∗
       ((s0.sp - 232#64) ↦₆₄ rk_w23) ∗
       ((s0.sp - 224#64) ↦₈ rk_b31) ∗ memRegion (s0.sp - 223#64) 7 ∗
       ((s0.sp - 216#64) ↦₈ rk_b0) ∗ ((s0.sp - 215#64) ↦₈ rk_b1) ∗
       ((s0.sp - 214#64) ↦₈ rk_b2) ∗ ((s0.sp - 213#64) ↦₈ rk_b3) ∗
       ((s0.sp - 212#64) ↦₈ rk_b4) ∗ ((s0.sp - 211#64) ↦₈ rk_b5) ∗
       ((s0.sp - 210#64) ↦₈ rk_b6) ∗ memRegion (s0.sp - 209#64) 1 ∗
       ((s0.sp - 208#64) ↦₆₄ w_208) ∗
       ((s0.sp - 200#64) ↦₈ b_200) ∗ memRegion (s0.sp - 199#64) 7 ∗
       ((s0.sp - 192#64) ↦₃₂ d_192) ∗ ((s0.sp - 188#64) ↦₁₆ h_188) ∗ memRegion (s0.sp - 186#64) 2 ∗
       ((s0.sp - 160#64) ↦₆₄ x.G.chainsCap) ∗
       ((s0.sp - 152#64) ↦₆₄ x.G.chainsPtr) ∗
       ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
       memRegion (s0.sp - 136#64) 16 ∗
       memRegion (s0.sp - 120#64) 24 ∗
       sessionFromBase A x.ss x.G x.st ∗
       (x.ss ↦₆₄ x.G.localIk.cap) ∗ ((x.ss + 8#64) ↦₆₄ x.G.localIk.ptr) ∗
       ((x.ss + 16#64) ↦₆₄ BitVec.ofNat 64 x.G.localIk.bytes.length) ∗
       vecU8Rest A x.G.localIk.cap x.G.localIk.ptr x.G.localIk.bytes ∗
       ((x.ss + 48#64) ↦₆₄ x.G.root.cap) ∗ ((x.ss + 56#64) ↦₆₄ x.G.root.ptr) ∗
       ((x.ss + 64#64) ↦₆₄ 32#64) ∗
       (x.G.root.ptr ↦₈ rk_b0) ∗ ((x.G.root.ptr + 1#64) ↦₈ rk_b1) ∗
       ((x.G.root.ptr + 2#64) ↦₈ rk_b2) ∗ ((x.G.root.ptr + 3#64) ↦₈ rk_b3) ∗
       ((x.G.root.ptr + 4#64) ↦₈ rk_b4) ∗ ((x.G.root.ptr + 5#64) ↦₈ rk_b5) ∗
       ((x.G.root.ptr + 6#64) ↦₈ rk_b6) ∗ ((x.G.root.ptr + 7#64) ↦₆₄ rk_w7) ∗
       ((x.G.root.ptr + 15#64) ↦₆₄ rk_w15) ∗ ((x.G.root.ptr + 23#64) ↦₆₄ rk_w23) ∗
       ((x.G.root.ptr + 31#64) ↦₈ rk_b31) ∗
       vecU8Rest A x.G.root.cap x.G.root.ptr (CryptoGames.HMAC.keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 72#64) 0#64 8#64 [] ∗
       ((x.ss + 120#64) ↦₆₄ x.G.pq.cap) ∗ ((x.ss + 128#64) ↦₆₄ x.G.pq.ptr) ∗
       ((x.ss + 136#64) ↦₆₄ BitVec.ofNat 64 x.st.pqRatchetState.length) ∗
       senderChainFromFrame A x.ss sg sc ∗
       ((x.ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((x.ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
       ((x.ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
       (sg.srk.ptr ↦ₛ sg.srk.bytes) ∗
       ((x.ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ ((x.ss + 184#64) ↦₆₄ 32#64) ∗
       (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((x.ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((x.ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
       ((x.ss + 232#64) ↦₆₄ 32#64) ∗
       (sg.ck.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
       ((x.ss + 240#64) ↦₃₂ sc.chainKey.index) ∗
       ((x.ss + 332#64) ↦₃₂ x.st.previousCounter) ∗
       F_tail)
      post := by
  have hfn : libsignalSessionCode.fnOff trFromName = num% (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") := by simp only [arm64_norm]
  have hstep10c := @trFrom_step_10c_to_244 img ext
  open FromFetches in tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 0x0ac 3
  open FromFetches in tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 0x270 62
  clear hfn
  have _ := hsrk_cmn; have _ := hck_cmn
  dsimp only [tripleRatchetProgAtExt] at hpc hcont hstep10c ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr trFromName = entry
  examples_hide_fetches
  obtain ⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6, pk_b7,
          pk_b8, pk_b9, pk_b10, pk_b11, pk_b12, pk_b13, pk_b14, pk_b15,
          pk_b16, pk_b17, pk_b18, pk_b19, pk_b20, pk_b21, pk_b22, pk_b23,
          pk_b24, pk_b25, pk_b26, pk_b27, pk_d28, hpk1, hpk2⟩ :=
    exists_pubKey_split_of_length_32 sc.ratchetKey.publicKey.bytes.toList_length
  obtain ⟨sk_b0, sk_d1, sk_h5, sk_w7, sk_w15, sk_w23, sk_b31, hc0, hc31, hsk⟩ :=
    exists_privKey_split sc.ratchetKey.privateKey.bytes hclamp_sc
  obtain ⟨ck_d0, ck_b4, ck_b5, ck_b6, ck_b7, ck_b8, ck_b9, ck_b10, ck_b11,
          ck_b12, ck_b13, ck_b14, ck_b15, ck_b16, ck_b17, ck_b18, ck_b19,
          ck_b20, ck_b21, ck_b22, ck_w23, ck_b31, hck1, hck2⟩ :=
    exists_chainKey_split_of_length_32 (length_keyToBytes32 sc.chainKey.key)
  apply SepWP.of_sepWP_inv (mid := entry + bv% (268)) hfl hsym
  rw [stack_184_24_split_some s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun t_162 => SepWP.exists_elim fun t_164 => ?_
  refine SepWP.exists_elim fun t_166 => SepWP.exists_elim fun t_167 => ?_
  refine SepWP.exists_elim fun t_168 => SepWP.exists_elim fun t_169 => ?_
  refine SepWP.exists_elim fun t_170 => SepWP.exists_elim fun t_171 => ?_
  refine SepWP.exists_elim fun t_172 => SepWP.exists_elim fun t_173 => ?_
  refine SepWP.exists_elim fun t_174 => SepWP.exists_elim fun t_175 => ?_
  refine SepWP.exists_elim fun t_176 => SepWP.exists_elim fun t_177 => ?_
  refine SepWP.exists_elim fun t_178 => SepWP.exists_elim fun t_179 => ?_
  refine SepWP.exists_elim fun t_180 => SepWP.exists_elim fun t_181 => ?_
  refine SepWP.exists_elim fun t_182 => SepWP.exists_elim fun t_183 => ?_
  refine SepWP.exists_elim fun t_184 => ?_
  refine SepWP.fold (Entails.refl
      (((x.ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((x.ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
       ((x.ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
       ((x.ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ ((x.ss + 184#64) ↦₆₄ 32#64) ∗
       (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((x.ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((x.ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
       ((x.ss + 232#64) ↦₆₄ 32#64) ∗
       (sg.ck.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
       ((x.ss + 240#64) ↦₃₂ sc.chainKey.index))) (by sep_focus) ?_
  rw [pubKey_unpack_sp_455 s0.sp hpk1, hsk sg.priv.ptr, hck1 sg.ck.ptr]
  simp only [sepConj_assoc]
  wp_steps
  refine SepWP.fold (stack_456_160_fold_some s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (stack_184_24_fold_some s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  have hsk_fold :
      ((sg.priv.ptr ↦₈ sk_b0) ∗ ((sg.priv.ptr + 1#64) ↦₃₂ sk_d1) ∗
       ((sg.priv.ptr + 5#64) ↦₁₆ sk_h5) ∗ ((sg.priv.ptr + 7#64) ↦₆₄ sk_w7) ∗
       ((sg.priv.ptr + 15#64) ↦₆₄ sk_w15) ∗ ((sg.priv.ptr + 23#64) ↦₆₄ sk_w23) ∗
       ((sg.priv.ptr + 31#64) ↦₈ sk_b31)) ⊢
      (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) := by
    rw [hsk sg.priv.ptr]; exact Entails.refl _
  refine SepWP.fold hsk_fold (by sep_focus) ?_
  have hck_fold :
      ((sg.ck.ptr ↦₃₂ ck_d0) ∗
       ((sg.ck.ptr + 4#64) ↦₁₆ (ck_b5 ++ ck_b4)) ∗
       ((sg.ck.ptr + 6#64) ↦₈ ck_b6) ∗
       ((sg.ck.ptr + 7#64) ↦₆₄ (ck_b14 ++ ck_b13 ++ ck_b12 ++ ck_b11 ++ ck_b10 ++ ck_b9 ++ ck_b8 ++ ck_b7)) ∗
       ((sg.ck.ptr + 15#64) ↦₆₄ (ck_b22 ++ ck_b21 ++ ck_b20 ++ ck_b19 ++ ck_b18 ++ ck_b17 ++ ck_b16 ++ ck_b15)) ∗
       ((sg.ck.ptr + 23#64) ↦₆₄ ck_w23) ∗
       ((sg.ck.ptr + 31#64) ↦₈ ck_b31)) ⊢
      (sg.ck.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) := by
    rw [hck1 sg.ck.ptr]; exact Entails.refl _
  refine SepWP.fold hck_fold (by sep_focus) ?_
  have hsc_some_fold :
      (senderChainFromFrame A x.ss sg sc ∗
       ((x.ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((x.ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
       ((x.ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
       (sg.srk.ptr ↦ₛ sg.srk.bytes) ∗
       ((x.ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ ((x.ss + 184#64) ↦₆₄ 32#64) ∗
       (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((x.ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((x.ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
       ((x.ss + 232#64) ↦₆₄ 32#64) ∗
       (sg.ck.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
       ((x.ss + 240#64) ↦₃₂ sc.chainKey.index)) ⊢
      optSenderChainAt A (x.ss + 144#64) x.G.sender x.st.senderChain := by
    rw [hsender_opt, hsc_opt]
    exact optSenderChainAt_some_reassemble_from A x.ss sg sc
  refine SepWP.fold hsc_some_fold (by sep_focus) ?_
  have hrk_fold :
      ((x.G.root.ptr ↦₈ rk_b0) ∗ ((x.G.root.ptr + 1#64) ↦₈ rk_b1) ∗
       ((x.G.root.ptr + 2#64) ↦₈ rk_b2) ∗ ((x.G.root.ptr + 3#64) ↦₈ rk_b3) ∗
       ((x.G.root.ptr + 4#64) ↦₈ rk_b4) ∗ ((x.G.root.ptr + 5#64) ↦₈ rk_b5) ∗
       ((x.G.root.ptr + 6#64) ↦₈ rk_b6) ∗ ((x.G.root.ptr + 7#64) ↦₆₄ rk_w7) ∗
       ((x.G.root.ptr + 15#64) ↦₆₄ rk_w15) ∗ ((x.G.root.ptr + 23#64) ↦₆₄ rk_w23) ∗
       ((x.G.root.ptr + 31#64) ↦₈ rk_b31)) ⊢
      (x.G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) := by
    rw [hrk x.G.root.ptr]; exact Entails.refl _
  refine SepWP.fold hrk_fold (by sep_focus) ?_
  clear t_162 t_164 t_166 t_167 t_168 t_169 t_170 t_171 t_172 t_173 t_174 t_175
        t_176 t_177 t_178 t_179 t_180 t_181 t_182 t_183 t_184
        hpk1 hck1 hsk_fold hck_fold hsc_some_fold hrk_fold
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  intro hfl_10c hsym_10c
  refine SepWP.mono_pre (Entails.of_eq (by ac_rfl))
    (hstep10c
      (rx2 := pk_b27 ++ pk_b26 ++ pk_b25 ++ pk_b24 ++ pk_b23 ++ pk_b22 ++ pk_b21 ++ pk_b20)
      (rx3 := sk_b0.zeroExtend 64)
      (rx14 := sk_b31.zeroExtend 64)
      A x.ret x.ss x.G x.st s0 _ (s0.readReg64 .lr) F_tail post
      ck_w23 ck_b31 sk_d1 sk_h5 u_296 u_288 u_284
      hrk hcmn_chains hfl_10c hsym_10c
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun])
      halign
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; bv_kernel)
      (by simp only [arm64_norm]; revert hc0; bv_kernel)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; revert hc31; bv_kernel)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23])
      (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx29])
      (by simp only [arm64_norm, hsp])
      ?_)
  intro s_244 hfl_244 hsym_244 hpc_244 hrun_244 htr_244
    hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244 hvregs_244
  refine SepWP.fold
    (scRawCells_some_entails s0.sp sc (List.replicate 100 0#8) hpk2 hsk hck2)
    (by sep_focus) ?_
  rw [← hsc_opt]
  refine SepWP.mono_pre (Entails.of_eq (by ac_rfl))
    (hcont s_244 hfl_244 hsym_244 hpc_244 hrun_244 htr_244
      hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244
      (by simp only [arm64_norm, *]))

/-! ## Main theorem (`trFrom_ok`) -/

theorem trFrom_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hDeser : DeserializeOkExt img.base ext :=
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_ok img.base _)
    (hRemoteIk : RemoteIdentityKeyOkExt img A ext)
    (hDropSpe : DropSpeOkExt img A ext)
    (hDropVecChain : DropVecChainOkExt img.base A ext) :
    TrFromOkExt img A ext := by
  have hb_align : img.base &&& 0xfff#64 = 0#64 := base_aligned_of_loads himg
  have hdeser := deserialize_ok_at_from hDeser
  clear hDeser
  simp only [TrFromOkExt, Spec.inImage, trFromSpec]
  wp_init x s0
  have hfl0 : img.FrozenLoaded s0 := by assumption
  have hsym0 : s0.symtab = img.symtab := by assumption
  have hx0 : s0.readReg64 .x0 = x.ss := by assumption
  have hw1 : (s0.readReg64 .x1).setWidth 32 = 0#32 := by assumption
  have hx8 : s0.readReg64 .x8 = x.ret := by assumption
  apply SepWP.with_post; intro post_ok hpost_ok
  have hfn : libsignalSessionCode.fnOff trFromName = num% (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") := by simp only [arm64_norm]
  have hstep10c := @trFrom_step_10c_to_244 img ext
  have hstepac := @trFrom_step_ac_to_244 img ext
  have hstep244 := @trFrom_step_244_to_ret img A ext himg hA hRemoteIk hDropSpe hDropVecChain
  open FromFetches in tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 0x000 23
  open FromFetches in tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 0x05c 20
  open FromFetches in tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 0x108 1
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at hpc hdeser hstep10c hstepac hstep244 ⊢
  have hentry_pc : (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr trFromName = s0.pc := by
    simp only [arm64_norm, hpc]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr trFromName = entry
  examples_hide_fetches
  clear hpc
  have hpc : s0.pc = entry := hentry_pc.symm
  clear hentry_pc
  have halign0 : (s0.sp &&& 0xf#64 == 0#64) = true := by
    simpa only [State.spAligned] using hsp_align
  refine SepWP.mono_pre (sepConj_mono (sessionStateAt_expose_from A x.ss x.G x.st) (Entails.refl _)) ?_
  simp only [sepConj_assoc]
  refine SepWP.pure_elim fun ⟨hlik, hlik_toNat, hchains, hcmn_chains, _, hpq_ne, hsc_some⟩ => ?_
  refine SepWP.mono_pre (sepConj_mono (sessionFromFrame_expose_remoteIk A x.ss x.G x.st) (Entails.refl _)) ?_
  simp only [sepConj_assoc]
  refine SepWP.pure_elim fun hrik => ?_
  obtain ⟨rk_b0, rk_b1, rk_b2, rk_b3, rk_b4, rk_b5, rk_b6, rk_w7, rk_w15, rk_w23, rk_b31, hrk⟩ :=
    exists_rootKey_split_of_length_32 (length_keyToBytes32 x.st.rootKey)
  refine SepWP.fold (Entails.of_eq (stackAt_trFrom s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun r11 => SepWP.exists_elim fun r10 => ?_
  refine SepWP.exists_elim fun r9 => SepWP.exists_elim fun r8 => ?_
  refine SepWP.exists_elim fun r7 => SepWP.exists_elim fun r6 => ?_
  refine SepWP.exists_elim fun r5 => SepWP.exists_elim fun r4 => ?_
  refine SepWP.exists_elim fun r3 => SepWP.exists_elim fun r2 => ?_
  refine SepWP.exists_elim fun r1 => SepWP.exists_elim fun r0 => ?_
  refine SepWP.exists_elim fun u_144 => SepWP.exists_elim fun u_152 => ?_
  refine SepWP.exists_elim fun u_160 => SepWP.exists_elim fun u_284 => ?_
  refine SepWP.exists_elim fun u_288 => SepWP.exists_elim fun u_296 => ?_
  refine SepWP.fold (Entails.of_eq (stack_256_96_split s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun h_188 => SepWP.exists_elim fun d_192 => ?_
  refine SepWP.exists_elim fun b_200 => SepWP.exists_elim fun w_208 => ?_
  refine SepWP.exists_elim fun b_210 => SepWP.exists_elim fun b_211 => ?_
  refine SepWP.exists_elim fun b_212 => SepWP.exists_elim fun b_213 => ?_
  refine SepWP.exists_elim fun b_214 => SepWP.exists_elim fun b_215 => ?_
  refine SepWP.exists_elim fun b_216 => SepWP.exists_elim fun b_224 => ?_
  refine SepWP.exists_elim fun w_232 => ?_
  rw [hrk x.G.root.ptr]
  apply SepWP.of_sepWP_inv (mid := entry + bv% (92)) hfl0 hsym0
  wp_steps
  refine SepWP.fold (vecAt_nil_chains_0_8 A (x.ss + 72#64)) (by sep_focus) ?_
  have hsaved_fold :
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      trFromSavedRegs s0.sp s0 := Entails.refl _
  refine SepWP.fold hsaved_fold (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hfl_5c hsym_5c
  cases hsc_opt : x.st.senderChain with
  | none =>
    cases hsender_opt : x.G.sender with
    | some _ => simp [hsender_opt, hsc_opt] at hsc_some
    | none =>
      have hclamp_none : ∀ sc, x.st.senderChain = some sc →
          Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes := by
        intro _ h; rw [hsc_opt] at h; cases h
      have hsc_none_unfold :
          optSenderChainAt A (x.ss + 144#64) none none =
            (((x.ss + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.ss + 152#64) 96) := by
        dsimp only [optSenderChainAt, noneCap]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      have hsc_none_fold :
          (((x.ss + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.ss + 152#64) 96) ⊢
            optSenderChainAt A (x.ss + 144#64) x.G.sender x.st.senderChain := by
        rw [hsender_opt, hsc_opt, hsc_none_unfold]; exact Entails.refl _
      apply SepWP.of_sepWP_inv (mid := entry + bv% (268)) hfl_5c hsym_5c
      refine SepWP.fold (Entails.of_eq hsc_none_unfold) (by sep_focus) ?_
      wp_steps
      refine SepWP.fold hsc_none_fold (by sep_focus) ?_
      have hrk_fold :
          ((x.G.root.ptr ↦₈ rk_b0) ∗ ((x.G.root.ptr + 1#64) ↦₈ rk_b1) ∗
           ((x.G.root.ptr + 2#64) ↦₈ rk_b2) ∗ ((x.G.root.ptr + 3#64) ↦₈ rk_b3) ∗
           ((x.G.root.ptr + 4#64) ↦₈ rk_b4) ∗ ((x.G.root.ptr + 5#64) ↦₈ rk_b5) ∗
           ((x.G.root.ptr + 6#64) ↦₈ rk_b6) ∗ ((x.G.root.ptr + 7#64) ↦₆₄ rk_w7) ∗
           ((x.G.root.ptr + 15#64) ↦₆₄ rk_w15) ∗ ((x.G.root.ptr + 23#64) ↦₆₄ rk_w23) ∗
           ((x.G.root.ptr + 31#64) ↦₈ rk_b31)) ⊢
          (x.G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) := by
        rw [hrk x.G.root.ptr]; exact Entails.refl _
      refine SepWP.fold hrk_fold (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hfl_10c hsym_10c
      refine SepWP.mono_pre (Entails.of_eq (by unfold trFrom10cTail; ac_rfl))
        (hstep10c A x.ret x.ss x.G x.st s0 _ (s0.readReg64 .lr) (trFrom10cTail img A x s0) post_ok
          w_208 b_200 d_192 h_188 u_296 u_288 u_284
          hrk hcmn_chains hfl_10c hsym_10c
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          halign0
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          ?_)
      intro s_244 hfl_244 hsym_244 hpc_244 hrun_244 htr_244
        hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244 hvregs_244
      refine SepWP.fold (scRawCells_none_entails s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWP.exists_elim fun senderPad => ?_
      refine SepWP.pure_elim fun hpad => ?_
      rw [← hsc_opt]
      refine SepWP.mono_pre (Entails.of_eq (by unfold trFrom10cTail; ac_rfl))
        (hstep244
          x senderPad s0 s_244 post_ok u_284 hpad hclamp_none hchains hpq_ne hlik hlik_toNat hrik
          hfl_244 hsym_244 hpc_244 hrun_244 halign0 htr_244
          hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244
          (by simp only [arm64_norm, *])
          ?_)
      intro sf hpc_ret hrun_ret htr_ret hsp_ret hcs_ret _ _
      subst hpost_ok
      apply SepWP.done hpc_ret hrun_ret
      refine ⟨fun hm => ?_, hsp_ret, hcs_ret⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨afterTrFrom_decRel x.G, htr_ret⟩, hm⟩
  | some sc =>
    cases hsender_opt : x.G.sender with
    | none => simp [hsender_opt, hsc_opt] at hsc_some
    | some sg =>
      have hlog : logOff img = ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) := rfl
      apply SepWP.of_sepWP_inv (mid := entry + bv% (172)) hfl_5c hsym_5c
      refine SepWP.fold (optSenderChainAt_some_expose_from A x.ss sg sc) (by sep_focus) ?_
      simp only [sepConj_assoc]
      refine SepWP.pure_elim fun ⟨hsrk, hsrk_lt, hsrk_toNat, hclamp_sc, hsrk_cmn, hck_cmn⟩ => ?_
      have hclamp_some : ∀ sc', x.st.senderChain = some sc' →
          Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes := by
        intro sc' h; rw [hsc_opt] at h; cases h; exact hclamp_sc
      rw [stack_456_160_split_deser s0.sp, hlog]
      refine SepWP.fold (memRegion_33_to_tag_and_32 (s0.sp - 456#64)) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWP.exists_elim fun tag0 => SepWP.exists_elim fun out32 => ?_
      refine SepWP.pure_elim fun hout32_len => ?_
      wp_steps
      wp_apply
      rw [← hlog]
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hfl_ac hsym_ac
      refine SepWP.mono_pre (Entails.of_eq (by unfold trFrom10cTail; ac_rfl))
        (hstepac A x sg sc s0 _ (trFrom10cTail img A x s0) post_ok
          w_208 b_200 d_192 h_188 u_296 u_288 u_284
          hrk hsender_opt hsc_opt hclamp_sc hsrk_cmn hck_cmn hcmn_chains hfl_ac hsym_ac
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          halign0
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          ?_)
      intro s_244 hfl_244 hsym_244 hpc_244 hrun_244 htr_244
        hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244 hvregs_244
      have hpad : (List.replicate 100 0#8).length = 100 := by simp
      refine SepWP.mono_pre (Entails.of_eq (by unfold trFrom10cTail; ac_rfl))
        (hstep244
          x (List.replicate 100 0#8) s0 s_244 post_ok u_284 hpad hclamp_some hchains hpq_ne hlik hlik_toNat hrik
          hfl_244 hsym_244 hpc_244 hrun_244 halign0 htr_244
          hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244
          (by simp only [arm64_norm, *])
          ?_)
      intro sf hpc_ret hrun_ret htr_ret hsp_ret hcs_ret _ _
      subst hpost_ok
      apply SepWP.done hpc_ret hrun_ret
      refine ⟨fun hm => ?_, hsp_ret, hcs_ret⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨afterTrFrom_decRel x.G, htr_ret⟩, hm⟩

theorem trFrom_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : TripleRatchetHooks C A S abs)
    (hDeser : DeserializeOk img.base C ctl abs :=
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_ok img.base _)
    (hRemoteIk : RemoteIdentityKeyOk img C A ctl abs)
    (hDropSpe : DropSpeOk img C A ctl abs)
    (hDropVecChain : DropVecChainOk img.base C A ctl abs) :
    TrFromOk img C A ctl abs :=
  trFrom_ok_ext himg (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hS.alloc)
    hDeser hRemoteIk hDropSpe hDropVecChain

/-! ## Relocatable per-block proof (block 57) -/

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
  (withLsRoLoaded sepWP_seq_lscl_ro lscall_blk_ro)

theorem trFrom_step_ac_to_244_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (A : RustAlloc) (x : TrFromGhost) (sg : SenderChainGhost) (sc : SenderChain)
    (s0 s : State) (F_tail : SepProp) (post : State → SepProp → Prop)
    (w_208 : BitVec 64) (b_200 : BitVec 8)
    (d_192 : BitVec 32) (h_188 : BitVec 16)
    (u_296 : BitVec 64) (u_288 u_284 : BitVec 32)
    {rk_b0 rk_b1 rk_b2 rk_b3 rk_b4 rk_b5 rk_b6 : BitVec 8}
    {rk_w7 rk_w15 rk_w23 : BitVec 64} {rk_b31 : BitVec 8}
    (hrk : ∀ a : BitVec 64,
      (a ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) =
        ((a ↦₈ rk_b0) ∗ ((a + 1#64) ↦₈ rk_b1) ∗ ((a + 2#64) ↦₈ rk_b2) ∗ ((a + 3#64) ↦₈ rk_b3) ∗
         ((a + 4#64) ↦₈ rk_b4) ∗ ((a + 5#64) ↦₈ rk_b5) ∗ ((a + 6#64) ↦₈ rk_b6) ∗
         ((a + 7#64) ↦₆₄ rk_w7) ∗ ((a + 15#64) ↦₆₄ rk_w15) ∗ ((a + 23#64) ↦₆₄ rk_w23) ∗
         ((a + 31#64) ↦₈ rk_b31)))
    (hsender_opt : x.G.sender = some sg)
    (hsc_opt : x.st.senderChain = some sc)
    (hclamp_sc : Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hsrk_cmn : (sg.srk.cap + 1#64 == 0#64) = false)
    (hck_cmn : (sg.ck.cap + 1#64 == 0#64) = false)
    (hcmn_chains : (x.G.chainsCap + 1#64 == 0#64) = false)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_57).base + 172#64)
    (hrun : s.status = .Running) (halign : (s0.sp &&& 0xf#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = s0.sp - 456#64)
    (hx21 : s.readReg64 .x21 = rk_w15)
    (hx22 : s.readReg64 .x22 = rk_w7)
    (hx23 : s.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : s.readReg64 .x25 = 0#64)
    (hx26 : s.readReg64 .x26 = x.ss)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hsp : s.sp = s0.sp - 496#64)
    (hcont : ∀ s_244,
      LibsignalCodeLoaded lsmpl s_244.mem → LibsignalRoLoaded lsmpl s_244.mem →
      s_244.pc = (blkPl_57).base + 580#64 →
      s_244.status = .Running → s_244.trace = s0.trace →
      s_244.readReg64 .x0 = x.G.localIk.ptr →
      s_244.readReg64 .x1 = BitVec.ofNat 64 x.G.localIk.bytes.length →
      s_244.readReg64 .x8 = s0.sp - 160#64 →
      s_244.readReg64 .x19 = x.ret →
      s_244.readReg64 .x20 = x.G.pq.cap →
      s_244.readReg64 .x21 = x.G.pq.ptr →
      s_244.readReg64 .x22 = x.ss →
      s_244.readReg64 .x23 = 0x8000000000000014#64 →
      s_244.readReg64 .x24 = s0.sp - 184#64 →
      s_244.readReg64 .x25 = BitVec.ofNat 64 x.st.pqRatchetState.length →
      s_244.readReg64 .x29 = s0.sp - 96#64 →
      s_244.sp = s0.sp - 496#64 →
      calleeSavedVRegs s_244 = calleeSavedVRegs s →
      SepWP ((blkPC_57).rebase (blkPl_57).base H) (s0.readReg64 .lr) s_244
        (((s0.sp - 456#64) ↦₆₄ x.G.chainsCap) ∗
         ((s0.sp - 448#64) ↦₆₄ x.G.chainsPtr) ∗
         ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
         ((s0.sp - 432#64) ↦ₛ optSenderChainBytes x.st.senderChain (List.replicate 100 0#8)) ∗
         ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) ∗
         ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
         ((s0.sp - 288#64) ↦₃₂ x.st.previousCounter) ∗
         ((s0.sp - 284#64) ↦₃₂ u_284) ∗
         memRegion (s0.sp - 280#64) 184 ∗
         sessionAfter208Frame A x.ss x.G x.st ∗
         F_tail)
        post) :
    SepWP ((blkPC_57).rebase (blkPl_57).base H) (s0.readReg64 .lr) s
      (memRegion (s0.sp - 184#64) 24 ∗
       ((s0.sp - 456#64) ↦₈ 0#8) ∗
       ((s0.sp - 455#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       memRegion (s0.sp - 423#64) 127 ∗
       ((s0.sp - 296#64) ↦₆₄ u_296) ∗
       ((s0.sp - 288#64) ↦₃₂ u_288) ∗
       ((s0.sp - 284#64) ↦₃₂ u_284) ∗
       memRegion (s0.sp - 280#64) 24 ∗
       memRegion (s0.sp - 256#64) 24 ∗
       ((s0.sp - 232#64) ↦₆₄ rk_w23) ∗
       ((s0.sp - 224#64) ↦₈ rk_b31) ∗ memRegion (s0.sp - 223#64) 7 ∗
       ((s0.sp - 216#64) ↦₈ rk_b0) ∗ ((s0.sp - 215#64) ↦₈ rk_b1) ∗
       ((s0.sp - 214#64) ↦₈ rk_b2) ∗ ((s0.sp - 213#64) ↦₈ rk_b3) ∗
       ((s0.sp - 212#64) ↦₈ rk_b4) ∗ ((s0.sp - 211#64) ↦₈ rk_b5) ∗
       ((s0.sp - 210#64) ↦₈ rk_b6) ∗ memRegion (s0.sp - 209#64) 1 ∗
       ((s0.sp - 208#64) ↦₆₄ w_208) ∗
       ((s0.sp - 200#64) ↦₈ b_200) ∗ memRegion (s0.sp - 199#64) 7 ∗
       ((s0.sp - 192#64) ↦₃₂ d_192) ∗ ((s0.sp - 188#64) ↦₁₆ h_188) ∗ memRegion (s0.sp - 186#64) 2 ∗
       ((s0.sp - 160#64) ↦₆₄ x.G.chainsCap) ∗
       ((s0.sp - 152#64) ↦₆₄ x.G.chainsPtr) ∗
       ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
       memRegion (s0.sp - 136#64) 16 ∗
       memRegion (s0.sp - 120#64) 24 ∗
       sessionFromBase A x.ss x.G x.st ∗
       (x.ss ↦₆₄ x.G.localIk.cap) ∗ ((x.ss + 8#64) ↦₆₄ x.G.localIk.ptr) ∗
       ((x.ss + 16#64) ↦₆₄ BitVec.ofNat 64 x.G.localIk.bytes.length) ∗
       vecU8Rest A x.G.localIk.cap x.G.localIk.ptr x.G.localIk.bytes ∗
       ((x.ss + 48#64) ↦₆₄ x.G.root.cap) ∗ ((x.ss + 56#64) ↦₆₄ x.G.root.ptr) ∗
       ((x.ss + 64#64) ↦₆₄ 32#64) ∗
       (x.G.root.ptr ↦₈ rk_b0) ∗ ((x.G.root.ptr + 1#64) ↦₈ rk_b1) ∗
       ((x.G.root.ptr + 2#64) ↦₈ rk_b2) ∗ ((x.G.root.ptr + 3#64) ↦₈ rk_b3) ∗
       ((x.G.root.ptr + 4#64) ↦₈ rk_b4) ∗ ((x.G.root.ptr + 5#64) ↦₈ rk_b5) ∗
       ((x.G.root.ptr + 6#64) ↦₈ rk_b6) ∗ ((x.G.root.ptr + 7#64) ↦₆₄ rk_w7) ∗
       ((x.G.root.ptr + 15#64) ↦₆₄ rk_w15) ∗ ((x.G.root.ptr + 23#64) ↦₆₄ rk_w23) ∗
       ((x.G.root.ptr + 31#64) ↦₈ rk_b31) ∗
       vecU8Rest A x.G.root.cap x.G.root.ptr (CryptoGames.HMAC.keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 72#64) 0#64 8#64 [] ∗
       ((x.ss + 120#64) ↦₆₄ x.G.pq.cap) ∗ ((x.ss + 128#64) ↦₆₄ x.G.pq.ptr) ∗
       ((x.ss + 136#64) ↦₆₄ BitVec.ofNat 64 x.st.pqRatchetState.length) ∗
       senderChainFromFrame A x.ss sg sc ∗
       ((x.ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((x.ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
       ((x.ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
       (sg.srk.ptr ↦ₛ sg.srk.bytes) ∗
       ((x.ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ ((x.ss + 184#64) ↦₆₄ 32#64) ∗
       (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((x.ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((x.ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
       ((x.ss + 232#64) ↦₆₄ 32#64) ∗
       (sg.ck.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
       ((x.ss + 240#64) ↦₃₂ sc.chainKey.index) ∗
       ((x.ss + 332#64) ↦₃₂ x.st.previousCounter) ∗
       F_tail)
      post := by
  have hstep10c := @trFrom_step_10c_to_244_placed _ H
  have _ := hsrk_cmn; have _ := hck_cmn
  obtain ⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6, pk_b7,
          pk_b8, pk_b9, pk_b10, pk_b11, pk_b12, pk_b13, pk_b14, pk_b15,
          pk_b16, pk_b17, pk_b18, pk_b19, pk_b20, pk_b21, pk_b22, pk_b23,
          pk_b24, pk_b25, pk_b26, pk_b27, pk_d28, hpk1, hpk2⟩ :=
    exists_pubKey_split_of_length_32 sc.ratchetKey.publicKey.bytes.toList_length
  obtain ⟨sk_b0, sk_d1, sk_h5, sk_w7, sk_w15, sk_w23, sk_b31, hc0, hc31, hsk⟩ :=
    exists_privKey_split sc.ratchetKey.privateKey.bytes hclamp_sc
  obtain ⟨ck_d0, ck_b4, ck_b5, ck_b6, ck_b7, ck_b8, ck_b9, ck_b10, ck_b11,
          ck_b12, ck_b13, ck_b14, ck_b15, ck_b16, ck_b17, ck_b18, ck_b19,
          ck_b20, ck_b21, ck_b22, ck_w23, ck_b31, hck1, hck2⟩ :=
    exists_chainKey_split_of_length_32 (length_keyToBytes32 sc.chainKey.key)
  apply sepWP_seq_lscl_ro hcl hro (mid := (blkPl_57).base + 268#64)
  rw [stack_184_24_split_some s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun t_162 => SepWP.exists_elim fun t_164 => ?_
  refine SepWP.exists_elim fun t_166 => SepWP.exists_elim fun t_167 => ?_
  refine SepWP.exists_elim fun t_168 => SepWP.exists_elim fun t_169 => ?_
  refine SepWP.exists_elim fun t_170 => SepWP.exists_elim fun t_171 => ?_
  refine SepWP.exists_elim fun t_172 => SepWP.exists_elim fun t_173 => ?_
  refine SepWP.exists_elim fun t_174 => SepWP.exists_elim fun t_175 => ?_
  refine SepWP.exists_elim fun t_176 => SepWP.exists_elim fun t_177 => ?_
  refine SepWP.exists_elim fun t_178 => SepWP.exists_elim fun t_179 => ?_
  refine SepWP.exists_elim fun t_180 => SepWP.exists_elim fun t_181 => ?_
  refine SepWP.exists_elim fun t_182 => SepWP.exists_elim fun t_183 => ?_
  refine SepWP.exists_elim fun t_184 => ?_
  refine SepWP.fold (Entails.refl
      (((x.ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((x.ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
       ((x.ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
       ((x.ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ ((x.ss + 184#64) ↦₆₄ 32#64) ∗
       (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((x.ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((x.ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
       ((x.ss + 232#64) ↦₆₄ 32#64) ∗
       (sg.ck.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
       ((x.ss + 240#64) ↦₃₂ sc.chainKey.index))) (by sep_focus) ?_
  rw [pubKey_unpack_sp_455 s0.sp hpk1, hsk sg.priv.ptr, hck1 sg.ck.ptr]
  simp only [sepConj_assoc]
  wp_steps
  refine SepWP.fold (stack_456_160_fold_some s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (stack_184_24_fold_some s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  have hsk_fold :
      ((sg.priv.ptr ↦₈ sk_b0) ∗ ((sg.priv.ptr + 1#64) ↦₃₂ sk_d1) ∗
       ((sg.priv.ptr + 5#64) ↦₁₆ sk_h5) ∗ ((sg.priv.ptr + 7#64) ↦₆₄ sk_w7) ∗
       ((sg.priv.ptr + 15#64) ↦₆₄ sk_w15) ∗ ((sg.priv.ptr + 23#64) ↦₆₄ sk_w23) ∗
       ((sg.priv.ptr + 31#64) ↦₈ sk_b31)) ⊢
      (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) := by
    rw [hsk sg.priv.ptr]; exact Entails.refl _
  refine SepWP.fold hsk_fold (by sep_focus) ?_
  have hck_fold :
      ((sg.ck.ptr ↦₃₂ ck_d0) ∗
       ((sg.ck.ptr + 4#64) ↦₁₆ (ck_b5 ++ ck_b4)) ∗
       ((sg.ck.ptr + 6#64) ↦₈ ck_b6) ∗
       ((sg.ck.ptr + 7#64) ↦₆₄ (ck_b14 ++ ck_b13 ++ ck_b12 ++ ck_b11 ++ ck_b10 ++ ck_b9 ++ ck_b8 ++ ck_b7)) ∗
       ((sg.ck.ptr + 15#64) ↦₆₄ (ck_b22 ++ ck_b21 ++ ck_b20 ++ ck_b19 ++ ck_b18 ++ ck_b17 ++ ck_b16 ++ ck_b15)) ∗
       ((sg.ck.ptr + 23#64) ↦₆₄ ck_w23) ∗
       ((sg.ck.ptr + 31#64) ↦₈ ck_b31)) ⊢
      (sg.ck.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) := by
    rw [hck1 sg.ck.ptr]; exact Entails.refl _
  refine SepWP.fold hck_fold (by sep_focus) ?_
  have hsc_some_fold :
      (senderChainFromFrame A x.ss sg sc ∗
       ((x.ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((x.ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
       ((x.ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
       (sg.srk.ptr ↦ₛ sg.srk.bytes) ∗
       ((x.ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ ((x.ss + 184#64) ↦₆₄ 32#64) ∗
       (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((x.ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((x.ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
       ((x.ss + 232#64) ↦₆₄ 32#64) ∗
       (sg.ck.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
       ((x.ss + 240#64) ↦₃₂ sc.chainKey.index)) ⊢
      optSenderChainAt A (x.ss + 144#64) x.G.sender x.st.senderChain := by
    rw [hsender_opt, hsc_opt]
    exact optSenderChainAt_some_reassemble_from A x.ss sg sc
  refine SepWP.fold hsc_some_fold (by sep_focus) ?_
  have hrk_fold :
      ((x.G.root.ptr ↦₈ rk_b0) ∗ ((x.G.root.ptr + 1#64) ↦₈ rk_b1) ∗
       ((x.G.root.ptr + 2#64) ↦₈ rk_b2) ∗ ((x.G.root.ptr + 3#64) ↦₈ rk_b3) ∗
       ((x.G.root.ptr + 4#64) ↦₈ rk_b4) ∗ ((x.G.root.ptr + 5#64) ↦₈ rk_b5) ∗
       ((x.G.root.ptr + 6#64) ↦₈ rk_b6) ∗ ((x.G.root.ptr + 7#64) ↦₆₄ rk_w7) ∗
       ((x.G.root.ptr + 15#64) ↦₆₄ rk_w15) ∗ ((x.G.root.ptr + 23#64) ↦₆₄ rk_w23) ∗
       ((x.G.root.ptr + 31#64) ↦₈ rk_b31)) ⊢
      (x.G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) := by
    rw [hrk x.G.root.ptr]; exact Entails.refl _
  refine SepWP.fold hrk_fold (by sep_focus) ?_
  clear t_162 t_164 t_166 t_167 t_168 t_169 t_170 t_171 t_172 t_173 t_174 t_175
        t_176 t_177 t_178 t_179 t_180 t_181 t_182 t_183 t_184
        hpk1 hck1 hsk_fold hck_fold hsc_some_fold hrk_fold
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  intro hcl_10c hro_10c
  refine SepWP.mono_pre (Entails.of_eq (by ac_rfl))
    (hstep10c
      (rx2 := pk_b27 ++ pk_b26 ++ pk_b25 ++ pk_b24 ++ pk_b23 ++ pk_b22 ++ pk_b21 ++ pk_b20)
      (rx3 := sk_b0.zeroExtend 64)
      (rx14 := sk_b31.zeroExtend 64)
      A x.ret x.ss x.G x.st s0 _ (s0.readReg64 .lr) F_tail post
      ck_w23 ck_b31 sk_d1 sk_h5 u_296 u_288 u_284
      hrk hcmn_chains hcl_10c hro_10c
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) halign
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]; bv_kernel) (by simp only [arm64_norm]; revert hc0; bv_kernel)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; revert hc31; bv_kernel)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx29]) (by simp only [arm64_norm, hsp]) ?_)
  intro s_244 hcl_244 hro_244 hpc_244 hrun_244 htr_244
    hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244 hvregs_244
  refine SepWP.fold
    (scRawCells_some_entails s0.sp sc (List.replicate 100 0#8) hpk2 hsk hck2)
    (by sep_focus) ?_
  rw [← hsc_opt]
  refine SepWP.mono_pre (Entails.of_eq (by ac_rfl))
    (hcont s_244 hcl_244 hro_244 hpc_244 hrun_244 htr_244
      hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244
      (by simp only [arm64_norm, *]))

theorem trFrom_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hDeser : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec)
    (hRemoteIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (hDropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec A)))
    (hDropVecChain : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpec A))) :
    subroutine_ok ((blkPC_57).rebase (blkPl_57).base H)
      (blkPl_57).base (trFromPlacedSpec A) := by
  simp only [trFromPlacedSpec, withLsCodeLoaded, trFromRawPlacedSpec]
  wp_init x s0
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hro0 : LibsignalRoLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 .x0 = x.ss := by assumption
  have hw1 : (s0.readReg64 .x1).setWidth 32 = 0#32 := by assumption
  have hx8 : s0.readReg64 .x8 = x.ret := by assumption
  apply SepWP.with_post; intro post_ok hpost_ok
  have hstep10c := @trFrom_step_10c_to_244_placed _ H
  have hstepac := @trFrom_step_ac_to_244_placed _ H
  have hstep244 := @trFrom_step_244_to_ret_placed _ A H hdealloc hRemoteIk hDropSpe hDropVecChain
  have halign0 : (s0.sp &&& 0xf#64 == 0#64) = true := by
    simpa only [State.spAligned] using hsp_align
  refine SepWP.mono_pre (sepConj_mono (sessionStateAt_expose_from A x.ss x.G x.st) (Entails.refl _)) ?_
  simp only [sepConj_assoc]
  refine SepWP.pure_elim fun ⟨hlik, hlik_toNat, hchains, hcmn_chains, _, hpq_ne, hsc_some⟩ => ?_
  refine SepWP.mono_pre (sepConj_mono (sessionFromFrame_expose_remoteIk A x.ss x.G x.st) (Entails.refl _)) ?_
  simp only [sepConj_assoc]
  refine SepWP.pure_elim fun hrik => ?_
  obtain ⟨rk_b0, rk_b1, rk_b2, rk_b3, rk_b4, rk_b5, rk_b6, rk_w7, rk_w15, rk_w23, rk_b31, hrk⟩ :=
    exists_rootKey_split_of_length_32 (length_keyToBytes32 x.st.rootKey)
  refine SepWP.fold (Entails.of_eq (stackAt_trFrom s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun r11 => SepWP.exists_elim fun r10 => ?_
  refine SepWP.exists_elim fun r9 => SepWP.exists_elim fun r8 => ?_
  refine SepWP.exists_elim fun r7 => SepWP.exists_elim fun r6 => ?_
  refine SepWP.exists_elim fun r5 => SepWP.exists_elim fun r4 => ?_
  refine SepWP.exists_elim fun r3 => SepWP.exists_elim fun r2 => ?_
  refine SepWP.exists_elim fun r1 => SepWP.exists_elim fun r0 => ?_
  refine SepWP.exists_elim fun u_144 => SepWP.exists_elim fun u_152 => ?_
  refine SepWP.exists_elim fun u_160 => SepWP.exists_elim fun u_284 => ?_
  refine SepWP.exists_elim fun u_288 => SepWP.exists_elim fun u_296 => ?_
  refine SepWP.fold (Entails.of_eq (stack_256_96_split s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun h_188 => SepWP.exists_elim fun d_192 => ?_
  refine SepWP.exists_elim fun b_200 => SepWP.exists_elim fun w_208 => ?_
  refine SepWP.exists_elim fun b_210 => SepWP.exists_elim fun b_211 => ?_
  refine SepWP.exists_elim fun b_212 => SepWP.exists_elim fun b_213 => ?_
  refine SepWP.exists_elim fun b_214 => SepWP.exists_elim fun b_215 => ?_
  refine SepWP.exists_elim fun b_216 => SepWP.exists_elim fun b_224 => ?_
  refine SepWP.exists_elim fun w_232 => ?_
  rw [hrk x.G.root.ptr]
  apply sepWP_seq_lscl_ro hcl0 hro0 (mid := (blkPl_57).base + 92#64)
  wp_steps
  refine SepWP.fold (vecAt_nil_chains_0_8 A (x.ss + 72#64)) (by sep_focus) ?_
  have hsaved_fold :
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      trFromSavedRegs s0.sp s0 := Entails.refl _
  refine SepWP.fold hsaved_fold (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl_5c hro_5c
  cases hsc_opt : x.st.senderChain with
  | none =>
    cases hsender_opt : x.G.sender with
    | some _ => simp [hsender_opt, hsc_opt] at hsc_some
    | none =>
      have hclamp_none : ∀ sc, x.st.senderChain = some sc →
          Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes := by
        intro _ h; rw [hsc_opt] at h; cases h
      have hsc_none_unfold :
          optSenderChainAt A (x.ss + 144#64) none none =
            (((x.ss + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.ss + 152#64) 96) := by
        dsimp only [optSenderChainAt, noneCap]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      have hsc_none_fold :
          (((x.ss + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.ss + 152#64) 96) ⊢
            optSenderChainAt A (x.ss + 144#64) x.G.sender x.st.senderChain := by
        rw [hsender_opt, hsc_opt, hsc_none_unfold]; exact Entails.refl _
      apply sepWP_seq_lscl_ro hcl_5c hro_5c (mid := (blkPl_57).base + 268#64)
      refine SepWP.fold (Entails.of_eq hsc_none_unfold) (by sep_focus) ?_
      wp_steps
      refine SepWP.fold hsc_none_fold (by sep_focus) ?_
      have hrk_fold :
          ((x.G.root.ptr ↦₈ rk_b0) ∗ ((x.G.root.ptr + 1#64) ↦₈ rk_b1) ∗
           ((x.G.root.ptr + 2#64) ↦₈ rk_b2) ∗ ((x.G.root.ptr + 3#64) ↦₈ rk_b3) ∗
           ((x.G.root.ptr + 4#64) ↦₈ rk_b4) ∗ ((x.G.root.ptr + 5#64) ↦₈ rk_b5) ∗
           ((x.G.root.ptr + 6#64) ↦₈ rk_b6) ∗ ((x.G.root.ptr + 7#64) ↦₆₄ rk_w7) ∗
           ((x.G.root.ptr + 15#64) ↦₆₄ rk_w15) ∗ ((x.G.root.ptr + 23#64) ↦₆₄ rk_w23) ∗
           ((x.G.root.ptr + 31#64) ↦₈ rk_b31)) ⊢
          (x.G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) := by
        rw [hrk x.G.root.ptr]; exact Entails.refl _
      refine SepWP.fold hrk_fold (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl_10c hro_10c
      refine SepWP.mono_pre (Entails.of_eq (by unfold trFrom10cTailPlaced; ac_rfl))
        (hstep10c A x.ret x.ss x.G x.st s0 _ (s0.readReg64 .lr) (trFrom10cTailPlaced A x s0) post_ok
          w_208 b_200 d_192 h_188 u_296 u_288 u_284
          hrk hcmn_chains hcl_10c hro_10c
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign0
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_)
      intro s_244 hcl_244 hro_244 hpc_244 hrun_244 htr_244
        hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244 hvregs_244
      refine SepWP.fold (scRawCells_none_entails s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWP.exists_elim fun senderPad => ?_
      refine SepWP.pure_elim fun hpad => ?_
      rw [← hsc_opt]
      refine SepWP.mono_pre (Entails.of_eq (by unfold trFrom10cTailPlaced; ac_rfl))
        (hstep244
          x senderPad s0 s_244 post_ok u_284 hpad hclamp_none hchains hpq_ne hlik hlik_toNat hrik
          hcl_244 hro_244 hpc_244 hrun_244 halign0 htr_244
          hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244
          (by simp only [arm64_norm, *])
          ?_)
      intro sf hpc_ret hrun_ret htr_ret hsp_ret hcs_ret _ _
      subst hpost_ok
      apply SepWP.done hpc_ret hrun_ret
      refine ⟨fun hm => ?_, hsp_ret, hcs_ret⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨afterTrFrom_decRel x.G, htr_ret⟩, hm⟩
  | some sc =>
    cases hsender_opt : x.G.sender with
    | none => simp [hsender_opt, hsc_opt] at hsc_some
    | some sg =>
      apply sepWP_seq_lscl_ro hcl_5c hro_5c (mid := (blkPl_57).base + 172#64)
      apply sepWP_seq_lscl_ro hcl_5c hro_5c (mid := lsmpl.base 201)
      refine SepWP.fold (optSenderChainAt_some_expose_from A x.ss sg sc) (by sep_focus) ?_
      simp only [sepConj_assoc]
      refine SepWP.pure_elim fun ⟨hsrk, hsrk_lt, hsrk_toNat, hclamp_sc, hsrk_cmn, hck_cmn⟩ => ?_
      have hclamp_some : ∀ sc', x.st.senderChain = some sc' →
          Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes := by
        intro sc' h; rw [hsc_opt] at h; cases h; exact hclamp_sc
      rw [stack_456_160_split_deser s0.sp]
      refine SepWP.fold (memRegion_33_to_tag_and_32 (s0.sp - 456#64)) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWP.exists_elim fun tag0 => SepWP.exists_elim fun out32 => ?_
      refine SepWP.pure_elim fun hout32_len => ?_
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl_deser _hro_deser
      wp_call (lscall_blk (callerProg := (blkPC_57).rebase (blkPl_57).base H) hDeser hcl_deser)
        (sg.srk.ptr, sg.srk.bytes, sc.ratchetKey.publicKey,
         s0.sp - 456#64, tag0, out32)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl_ac hro_ac
      refine SepWP.mono_pre (Entails.of_eq (by unfold trFrom10cTailPlaced; ac_rfl))
        (hstepac A x sg sc s0 _ (trFrom10cTailPlaced A x s0) post_ok
          w_208 b_200 d_192 h_188 u_296 u_288 u_284
          hrk hsender_opt hsc_opt hclamp_sc hsrk_cmn hck_cmn hcmn_chains hcl_ac hro_ac
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign0
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) ?_)
      intro s_244 hcl_244 hro_244 hpc_244 hrun_244 htr_244
        hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244 hvregs_244
      have hpad : (List.replicate 100 0#8).length = 100 := by simp
      refine SepWP.mono_pre (Entails.of_eq (by unfold trFrom10cTailPlaced; ac_rfl))
        (hstep244
          x (List.replicate 100 0#8) s0 s_244 post_ok u_284 hpad hclamp_some hchains hpq_ne hlik hlik_toNat hrik
          hcl_244 hro_244 hpc_244 hrun_244 halign0 htr_244
          hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244
          (by simp only [arm64_norm, *])
          ?_)
      intro sf hpc_ret hrun_ret htr_ret hsp_ret hcs_ret _ _
      subst hpost_ok
      apply SepWP.done hpc_ret hrun_ret
      refine ⟨fun hm => ?_, hsp_ret, hcs_ret⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨afterTrFrom_decRel x.G, htr_ret⟩, hm⟩

theorem trFrom_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hRemoteIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (hDropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec A)))
    (hDropVecChain : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpec A))) :
    subroutine_ok ((blkPC_57).rebase (blkPl_57).base H)
      (blkPl_57).base (trFromPlacedSpec A) :=
  trFrom_placed_ok_of_contracts
    (ls_hook_ok_of_mem h_dealloc)
    (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_placed_ok H)
    hRemoteIk
    hDropSpe
    hDropVecChain

end ReceiveRatchetFrom

export ReceiveRatchetFrom
  (trFrom_ok_ext trFrom_ok
   trFromRawPlacedSpec trFromPlacedSpec
   trFrom_placed_ok_of_contracts trFrom_placed_ok)

end CryptoVerification.LibsignalTripleRatchet
