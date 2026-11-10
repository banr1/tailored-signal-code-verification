/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitE
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3Aux

/-!
# Stage P2 Substage P2.3

Proves CPS `stageP2_sub3_kits` and `stageP2_sub3_kits_ext` (`+0x1460 → +0x0d5c` on `Ok`, or
`+0x0998` Arm 2 on `kpkKit.getPoll` error) on `tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

set_option maxHeartbeats 1200000 in
/-- Kit-generic Substage P2.3 (`+0x1460 -> +0x0d5c` or `+0x0998` Arm 2) in CPS form:
polls `kpkKit.getPoll`, delegates `.error e` at `+0x0998` to `hErr`, and on `.ok r` drops/frees the
KPK future, deserializes the ML-KEM-1024 keypair (`kemKeyPairSerde`), frees the cloned record
buffers, allocates & drops the temporary `"missing pq ciphertext"` error, and reaches `+0x0d5c`. -/
theorem stageP2_sub3_kits_ext {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : StageP2ClosureHooks A img.base ext) (hPure : StageP2PureCallees4K P A F img ext)
    (kpkKit : KyberPreKeyStoreSpec A img.base) (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_kpk_poll : kpkKit.getPollStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
     v_98 v_a0 v_b0 u_4f8 u_500 u_90 u_a8 u_b8 u_c0 u_d0
     u_3d8 u_3e0 u_3e8 u_3f0 : BitVec 64)
    (kyberPreKeyId : BitVec 32) (b_4f1 : BitVec 8) (stKpk : kpkKit.KpkState)
    (hb : img.base &&& 0xfff#64 = 0#64) (hkyber_nz : kyberCtCap ≠ 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (henv : ∀ s1 : State, Steps (tripleRatchetProgAtExt img.base ext) s s1 →
      s1.trace = s.trace → kpkKit.envOk s1.fs.files)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hrec_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1460#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = kyberFutPtr) (hx1 : s.readReg64 .x1 = img.base + kpkKit.getFutVtOff)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0) (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hErr : ∀ (e : kpkKit.GetErr) (s2 : State),
      Steps (tripleRatchetProgAtExt img.base ext) s s2 →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      s2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x998#64 →
      s2.status = .Running → s2.sp = s.sp →
      s2.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.error e) →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x21 = v_b0 →
      s2.readReg64 .x23 = v_a0 → s2.readReg64 .x25 = s.readReg64 .x25 →
      s2.readReg64 .x26 = v_98 → s2.readReg64 .x27 = ctxPtr →
      s2.readReg64 .x28 = s.readReg64 .x28 → s2.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      img.FrozenLoaded s2 → s2.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s2
        (kpkGetPollOutAt kpkKit (s.sp + 0x3e0#64) (.error e) ∗
         kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 1#8 ∗
         kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
         ((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
         ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
         ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((img.base + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getPollOff)) ∗
         A.live kyberFutPtr kpkKit.getBoxSize 8 ∗ A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q Qp)
    (hOk : ∀ (r : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
      (pkBuf skBuf v90 privCap privPtr : BitVec 64) (sf : State),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      r.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      pkBuf ≠ 0#64 → skBuf ≠ 0#64 →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xd5c#64 →
      sf.status = .Running → sf.sp = s.sp →
      sf.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.ok r) →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = kyberCtCap → sf.readReg64 .x23 = v_a0 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = s.sp + 0xa90#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok r)) ∗
         (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
         (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
         ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗
         ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗
         memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
         ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
         ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((img.base + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getPollOff)) ∗
         A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
       ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getPollOff)) ∗
       A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
       kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 0#8 ∗
       kpkKit.storeAt kyberStorePtr stKpk ∗ A.pool ∗ stackAt s.sp stk ∗ Frame)
      Q Qp := by
  have hstep1 := p2_seg3a_ext_wp img.base ext s coroPtr ctxPtr kyberFutPtr
    (img.base + kpkKit.getFutVtOff) (img.base + kpkKit.getPollOff) u_4f8 u_500
    hpc hrun hx0 hx1 hx19 hx27
  refine p2_bind_sepWP_steps_frame_qpan hF hsym hstep1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, _, hx8_1, hx19_1, hx21_1, hx23_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_poll := p2_stackAt_split_of_le s.sp stk kpkKit.getPollStack hstk_kpk_poll hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll) (by sep_focus) ?_
  sep_norm
  refine p2_call_oom_steps_frame_qpan
    (x := (({ fut := kyberFutPtr, self := kyberStorePtr, out := s.sp + 0x3e0#64,
              id := kyberPreKeyId } : PreKeyPollCall), stKpk))
    hpan hF1 hsym1 (htr1 ▸ htr) hkpkOk.getPoll hpc1 hrun1 hsp1_al hx30_1
    (hsp1 ▸ p2_kpkGetPoll_pre_intro hF1 hsym1 (henv s1 hst01 htr1) hb hx0_1 hx8_1 hid_kpk)
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun s2 hst12 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  dsimp only [Spec.inImage, kitKpkGetPollSpecE, withEnvPre, kitKpkGetPollSpec]
  rcases hcs2 with ⟨hcs2_19, _, hcs2_21, _, hcs2_23, _, hcs2_25, hcs2_26, hcs2_27, hcs2_28,
    hcs2_29, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rw [hsp1]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.pure_elim fun ⟨hrel, htr2_1⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll.symm) (by sep_focus) ?_
  have htr2 : s2.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId ans := by rw [htr2_1, htr1]
  cases ans with
  | error e =>
    have herr := hErr e s2 (hst01.trans hst12) hrel hpc2 hrun2 hsp2 htr2
      (hcs2_19.trans hx19_1) (by rw [hcs2_21, hx21_1, hx21]) (by rw [hcs2_23, hx23_1, hx23])
      (hcs2_25.trans hx25_1) (by rw [hcs2_26, hx26_1, hx26]) (hcs2_27.trans hx27_1)
      (hcs2_28.trans hx28_1) (hcs2_29.trans hx29_1)
      (by rw [hvregs2_1, hvregs1, hvregs]) hF2 hsym2
    exact p2_sepWPp_weaken_eq herr (by sep_focus)
  | ok r =>
    dsimp only [kpkGetPollOutAt]
    simp only [sepConj_assoc]
    refine p2_sepWPp_pure_elim_frame (kpkKit.RecOk r) (by sep_focus) fun hrec_ok => ?_
    obtain ⟨kyberPubBytes, kyberPrivBytes, hpub_len, hpriv_len, hpub_eq, hpriv_eq⟩ :=
      hrec_wf r hrel hrec_ok
    refine SepWPp.weaken_frame (p2_signedPreKeyStructAt_unpack A (s.sp + 0x3e0#64) r.signedPreKey)
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun pubCap => SepWPp.exists_elim fun pubPtr =>
      SepWPp.exists_elim fun privCap => SepWPp.exists_elim fun privPtr =>
      SepWPp.exists_elim fun sigCap => SepWPp.exists_elim fun sigPtr =>
      SepWPp.exists_elim fun pad32 => ?_
    have hpub_bv : BitVec.ofNat 64 r.signedPreKey.publicKey.length = 1569#64 := by
      rw [hpub_eq]; simp [hpub_len]
    have hpriv_bv : BitVec.ofNat 64 r.signedPreKey.privateKey.length = 3169#64 := by
      rw [hpriv_eq]; simp [hpriv_len]
    rw [hpub_bv, hpriv_bv, hpub_eq, hpriv_eq]
    refine SepWPp.weaken_frame (p2_vecU8Buf_nonempty A pubCap pubPtr (8#8 :: kyberPubBytes) (by simp))
      (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpub_le, _, hpub_nz, hpub_ne2, hpub_ne1⟩ => ?_
    refine SepWPp.weaken_frame
      (p2_vecU8Buf_nonempty A privCap privPtr (8#8 :: kyberPrivBytes) (by simp))
      (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpriv_le, _, hpriv_nz, _, _⟩ => ?_
    have hstep3 := p2_seg3b_gen_wp img.base ext s2 coroPtr kyberFutPtr
      (img.base + kpkKit.getFutVtOff) (img.base + kpkKit.getFutDropOff)
      pubCap pubPtr privCap privPtr sigCap sigPtr
      v_98 v_a0 v_b0 u_90 v_98 v_a0 u_a8 v_b0 u_b8 u_d0
      hpc2 hrun2 hsp2_align hpub_ne2 (kpkKit.getFutDrop_ne_zero hb)
      (hcs2_19.trans hx19_1) (by rw [hcs2_21, hx21_1, hx21])
      (by rw [hcs2_23, hx23_1, hx23]) (by rw [hcs2_26, hx26_1, hx26])
    have hvt0 : (img.base + kpkKit.getFutVtOff) + 0x0#64 = img.base + kpkKit.getFutVtOff :=
      BitVec.add_zero _
    rw [hsp2, hvt0] at hstep3
    refine p2_bind_sepWP_steps_frame_qpan hF2 hsym2 hstep3 (by sep_focus)
      fun s3 hst23 hpc3 hrun3 hF3 hsym3 hregs3 => ?_
    rcases hregs3 with ⟨hsp3, htr3_2, _, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3,
      hx26_3, hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
    have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
    refine p2_call_nopanic_steps_frame (x := ()) (T := emp)
      hF3 hsym3 hkpkOk.getFutDrop hpc3 hrun3 hsp3_al hx30_3
      rfl ⟨hF3, hsym3⟩ (by sep_focus)
      (hnext := fun s4 hst34 hpc4 hrun4 hsp4_3 _ hcs4 hF4 hsym4 => ?_)
    dsimp only [Spec.inImage, LibsignalPublicApi.StoreSession.futDropSpec]
    refine SepWPp.pure_elim fun htr4_3 => ?_
    rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25, hcs4_26,
      hcs4_27, hcs4_28, hcs4_29, hvregs4_3⟩
    have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
    have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
    refine SepWPp.weaken_frame (kpkKit.getBoxAt_memRegion kyberFutPtr kyberStorePtr kyberPreKeyId 1#8)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame
      (p2_preKeyRecordOut64_tail_to_memRegion88 (s.sp + 0x3e0#64)
        pubCap pubPtr 1569#64 privCap privPtr 3169#64 sigCap sigPtr
        (BitVec.ofNat 64 r.signedPreKey.signature.length)
        r.signedPreKey.timestamp (pad32 ++ r.signedPreKey.id))
      (by sep_focus) ?_
    have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
      (Nat.le_trans p2_alloc_le_pure hstk_pure) hstk_lt
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
    have hstep5 := p2_seg3c_hooks_wp img.base ext hH s4 coroPtr ctxPtr kyberFutPtr
      (img.base + kpkKit.getFutVtOff) pubCap pubPtr privPtr sigPtr u_c0 kpkKit.getBoxSize
      hpc4 hrun4 hsp4_align hpub_ne1 kpkKit.getBoxSize_ne_zero kpkKit.getBoxSize_lt
      (hcs4_19.trans hx19_3) (hcs4_20.trans hx20_3) (hcs4_21.trans hx21_3)
      (hcs4_22.trans hx22_3) (hcs4_23.trans hx23_3) (hcs4_24.trans hx24_3)
      (by rw [hcs4_27, hx27_3, hcs2_27, hx27_1]) (hcs4_28.trans hx28_3)
    rw [hsp4] at hstep5
    refine p2_bind_sepWP_steps_frame_qpan hF4 hsym4 hstep5 (by sep_focus)
      fun s5 hst45 hpc5 hrun5 hF5 hsym5 hregs5 => ?_
    rcases hregs5 with ⟨hsp5, htr5_4, hx0_5, hx1_5, hx2_5, hx3_5, hx8_5, hx19_5, hx20_5, _,
      hx23_5, hx25_5, hx26_5, hx27_5, hx28_5, hx29_5, hx30_5, hvregs5_4⟩
    have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
    have hstk_kem1 := p2_stackAt_split_of_le s.sp stk (64 + allocHookStack)
      (Nat.le_trans p2_kemStack_le_pure hstk_pure) hstk_lt
    have hstk_kem2 := p2_stackAt_kemKeyPair_eq s.sp
    have hmr65_split := p2_memRegion_65_split_cells5 (s.sp + 0xa90#64)
    refine SepWPp.weaken_frame (Entails.of_eq hstk_kem1) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_kem2) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hmr65_split) (by sep_focus) ?_
    sep_norm
    have htr5_0 : s0.trace <+: s5.trace := by
      rw [htr5_4, htr4_3, htr3_2, htr2]; exact htr.trans (List.prefix_append _ _)
    refine p2_call_frame_frozen_oom_prefix_qpan hpan hF5 hsym5 htr5_0 hPure.kemKeyPairSerde
      hpc5 hrun5 hsp5_al hx30_5
      (x := (pubPtr, kyberPubBytes, privPtr, kyberPrivBytes, s.sp + 0xa90#64))
      (φ := s5.readReg64 .x0 = pubPtr ∧ s5.readReg64 .x1 = 0x621#64 ∧
        s5.readReg64 .x2 = privPtr ∧ s5.readReg64 .x3 = 0xc61#64 ∧
        s5.readReg64 .x8 = s.sp + 0xa90#64 ∧ kyberPubBytes.length = 1568 ∧
        kyberPrivBytes.length = 3168)
      (T := (pubPtr ↦ₛ (8#8 :: kyberPubBytes)) ∗ (privPtr ↦ₛ (8#8 :: kyberPrivBytes)) ∗
        cells (s.sp + 0xa90#64) 5 ∗
        (memRegion (s.sp - 4160#64) 64 ∗ stackAt s.sp allocHookStack) ∗ A.pool)
      (by dsimp only [kemKeyPairFromPubPrivOkSpec]; rw [hsp5])
      (And.intro hx0_5 (And.intro hx1_5 (And.intro hx2_5
        (And.intro hx3_5 (And.intro hx8_5 (And.intro hpub_len hpriv_len))))))
      (by sep_focus)
      (by intro _; rfl) (by intro _ _; rfl)
      fun s6 hpc6 hrun6 hsp6_5 _ hcs6 hF6 hsym6 hst56 => ?_
    dsimp only [kemKeyPairFromPubPrivOkSpec]
    rcases hcs6 with ⟨hcs6_19, hcs6_20, _, _, hcs6_23, _, hcs6_25, hcs6_26, hcs6_27, hcs6_28,
      hcs6_29, hvregs6_5⟩
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
    rw [hsp5,
        show (s.sp + 0xa90#64) + 8#64 = s.sp + 0xa98#64 by bv_omega,
        show (s.sp + 0xa90#64) + 16#64 = s.sp + 0xaa0#64 by bv_omega,
        show (s.sp + 0xa90#64) + 24#64 = s.sp + 0xaa8#64 by bv_omega,
        show (s.sp + 0xa90#64) + 32#64 = s.sp + 0xab0#64 by bv_omega]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun pkBuf => SepWPp.exists_elim fun skBuf => ?_
    refine SepWPp.pure_elim fun ⟨htr6_5, hpk_nz, hsk_nz⟩ => ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_kem2.symm) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_kem1.symm) (by sep_focus) ?_
    refine SepWPp.weaken_frame (p2_vecU8Buf_rejoin pubPtr pubCap (8#8 :: kyberPubBytes) hpub_le)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (p2_vecU8Buf_rejoin privPtr privCap (8#8 :: kyberPrivBytes) hpriv_le)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
    sep_norm
    have hst06 := hst01.trans (hst12.trans (hst23.trans (hst34.trans (hst45.trans hst56))))
    have hnext7 : ∀ (v90 : BitVec 64) (s7 : State),
        Steps (tripleRatchetProgAtExt img.base ext) s6 s7 →
        s7.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xd04#64 →
        s7.status = .Running → img.FrozenLoaded s7 → s7.symtab = img.symtab →
        s7.sp = s.sp ∧ s7.trace = s6.trace ∧
        s7.readReg64 .x0 = 21#64 ∧ s7.readReg64 .x1 = 1#64 ∧
        s7.readReg64 .x19 = coroPtr ∧ s7.readReg64 .x21 = msgPtr + 0x90#64 ∧
        s7.readReg64 .x22 = kyberCtCap ∧ s7.readReg64 .x23 = v_a0 ∧
        s7.readReg64 .x25 = s6.readReg64 .x25 ∧ s7.readReg64 .x26 = v_98 ∧
        s7.readReg64 .x27 = s6.readReg64 .x27 ∧ s7.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s7.readReg64 .x29 = s6.readReg64 .x29 ∧ calleeSavedVRegs s7 = calleeSavedVRegs s6 →
        SepWPp (tripleRatchetProgAtExt img.base ext) ret s7
          ((((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
            ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗ ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
            ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗ ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
            ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗ ((s.sp + 0x90#64) ↦₆₄ v90) ∗
            ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
            ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗
            A.pool ∗ stackAt s.sp allocHookStack ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap)) ∗
           (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok r)) ∗
            (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
            (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
            ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0xab8#64) 25 ∗
            memRegion (s.sp + 0x3e0#64) 88 ∗
            ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
            ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
            ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
            ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
            ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((img.base + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getPollOff)) ∗
            memRegion (s.sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗ Frame))
          Q Qp := by
      intro v90 s7 hst67 hpc7 hrun7 hF7 hsym7 hregs7
      rcases hregs7 with ⟨hsp7, htr7_6, hx0_7, hx1_7, hx19_7, hx21_7, hx22_7, hx23_7, hx25_7,
        hx26_7, hx27_7, hx28_7, hx29_7, hvregs7_6⟩
      refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
      have htr7 : s7.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.ok r) := by
        rw [htr7_6, htr6_5, htr5_4, htr4_3, htr3_2, htr2]
      have hvregs7 : calleeSavedVRegs s7 = calleeSavedVRegs s0 := by
        rw [hvregs7_6, hvregs6_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
      let TailFrame : SepProp :=
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok r)) ∗
        (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
        (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
        ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
        ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
        ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗
        ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗
        ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
        ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
        ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
        ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
        ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
        ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
        ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
        ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getPollOff)) ∗
        Frame
      have htail := stageP2_sub3_tail_kits_ext himg hH hPure hb hstk_pure hstk_lt
        s0 s7 ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xd5c#64)
        s.sp coroPtr pkBuf skBuf kyberCtCap TailFrame
        (fun sm Pm => SepWPp (tripleRatchetProgAtExt img.base ext) ret sm Pm Q Qp)
        hkyber_nz hF7 hsym7 hpc7 hrun7 hsp7 hsp_align (htr.trans ⟨_, htr7.symm⟩) hvregs7
        hx0_7 hx1_7 hx19_7 hx22_7
        (fun sf hst7f hpcf hrunf hspf htrf_7 hx19_f hx21_f hx22_f hx23_f hx25_f hx26_f hx27_f
             hx28_f hx29_f hvregsf hFf hsymf => by
          have hok := hOk r kyberPubBytes kyberPrivBytes pkBuf skBuf v90 privCap privPtr sf
            (hst06.trans (hst67.trans hst7f)) hrel hrec_ok hpub_len hpriv_len hpub_eq hpriv_eq
            hpk_nz hsk_nz hpcf hrunf hspf (htrf_7.trans htr7)
            hx19_f (hx21_f.trans hx21_7) hx22_f (hx23_f.trans hx23_7)
            (by rw [hx25_f, hx25_7, hcs6_25, hx25_5, hcs4_25, hx25_3, hcs2_25, hx25_1])
            (hx26_f.trans hx26_7)
            (by rw [hx27_f, hx27_7, hcs6_27, hx27_5])
            (hx28_f.trans hx28_7)
            (by rw [hx29_f, hx29_7, hcs6_29, hx29_5, hcs4_29, hx29_3, hcs2_29, hx29_1])
            hvregsf hFf hsymf
          refine SepWPp.done hpcf hrunf ?_
          dsimp only [TailFrame]
          exact p2_sepWPp_weaken_eq hok (by sep_focus))
      dsimp only [TailFrame] at htail
      exact p2_sepWPp_weaken_eq (p2_cut_qpan hpan htail) (by sep_focus)
    by_cases hsig : sigCap = 0#64
    · rw [hsig]
      refine SepWPp.weaken_frame (p2_vecU8Buf_zero A sigPtr r.signedPreKey.signature)
        (by sep_focus) ?_
      sep_norm
      have hstep7 := p2_seg3d1_sig0_hooks_wp img.base ext hH s6 coroPtr msgPtr
        pubCap pubPtr privCap privPtr sigPtr pkBuf skBuf kyberCtCap v_98 v_a0
        u_3d8 u_3e0 u_3e8 u_3f0 b_4f1
        hpc6 hrun6 hsp6_align hpub_nz hpriv_nz
        (hcs6_19.trans hx19_5) (hcs6_20.trans hx20_5) (hcs6_23.trans hx23_5) (hcs6_28.trans hx28_5)
      rw [hsp6] at hstep7
      exact p2_bind_sepWP_steps_frame_qpan hF6 hsym6 hstep7 (by sep_focus) (hnext7 0#64)
    · refine SepWPp.weaken_frame
        (p2_vecU8Buf_dealloc_nonzero A sigCap sigPtr r.signedPreKey.signature hsig)
        (by sep_focus) ?_
      sep_norm
      have hstep7 := p2_seg3d1_sigNz_hooks_wp img.base ext hH s6 coroPtr msgPtr
        pubCap pubPtr privCap privPtr sigCap sigPtr pkBuf skBuf kyberCtCap v_98 v_a0
        u_3d8 u_3e0 u_3e8 u_3f0 b_4f1
        hpc6 hrun6 hsp6_align hpub_nz hpriv_nz hsig
        (hcs6_19.trans hx19_5) (hcs6_20.trans hx20_5) (hcs6_23.trans hx23_5) (hcs6_28.trans hx28_5)
      rw [hsp6] at hstep7
      exact p2_bind_sepWP_steps_frame_qpan hF6 hsym6 hstep7 (by sep_focus) (hnext7 sigCap)

abbrev stageP2_sub3_kits_4k := @stageP2_sub3_kits_ext
abbrev stageP2_sub3_kits_hooks := @stageP2_sub3_kits_ext

theorem stageP2_sub3_kits {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext) (hPure : StageP2PureCallees P A F img ext)
    (kpkKit : KyberPreKeyStoreSpec A img.base) (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_kpk_poll : kpkKit.getPollStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
     v_98 v_a0 v_b0 u_4f8 u_500 u_90 u_a8 u_b8 u_c0 u_d0
     u_3d8 u_3e0 u_3e8 u_3f0 : BitVec 64)
    (kyberPreKeyId : BitVec 32) (b_4f1 : BitVec 8) (stKpk : kpkKit.KpkState)
    (hb : img.base &&& 0xfff#64 = 0#64) (hkyber_nz : kyberCtCap ≠ 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (henv : ∀ s1 : State, Steps (tripleRatchetProgAtExt img.base ext) s s1 →
      s1.trace = s.trace → kpkKit.envOk s1.fs.files)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hrec_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1460#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = kyberFutPtr) (hx1 : s.readReg64 .x1 = img.base + kpkKit.getFutVtOff)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0) (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hErr : ∀ (e : kpkKit.GetErr) (s2 : State),
      Steps (tripleRatchetProgAtExt img.base ext) s s2 →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      s2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x998#64 →
      s2.status = .Running → s2.sp = s.sp →
      s2.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.error e) →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x21 = v_b0 →
      s2.readReg64 .x23 = v_a0 → s2.readReg64 .x25 = s.readReg64 .x25 →
      s2.readReg64 .x26 = v_98 → s2.readReg64 .x27 = ctxPtr →
      s2.readReg64 .x28 = s.readReg64 .x28 → s2.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      img.FrozenLoaded s2 → s2.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s2
        (kpkGetPollOutAt kpkKit (s.sp + 0x3e0#64) (.error e) ∗
         kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 1#8 ∗
         kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
         ((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
         ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
         ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((img.base + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getPollOff)) ∗
         A.live kyberFutPtr kpkKit.getBoxSize 8 ∗ A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q Qp)
    (hOk : ∀ (r : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
      (pkBuf skBuf v90 privCap privPtr : BitVec 64) (sf : State),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      r.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      pkBuf ≠ 0#64 → skBuf ≠ 0#64 →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xd5c#64 →
      sf.status = .Running → sf.sp = s.sp →
      sf.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.ok r) →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = kyberCtCap → sf.readReg64 .x23 = v_a0 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = s.sp + 0xa90#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok r)) ∗
         (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
         (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
         ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗
         ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗
         memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
         ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
         ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((img.base + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getPollOff)) ∗
         A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
       ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getPollOff)) ∗
       A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
       kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 0#8 ∗
       kpkKit.storeAt kyberStorePtr stKpk ∗ A.pool ∗ stackAt s.sp stk ∗ Frame)
      Q Qp :=
  stageP2_sub3_kits_ext img ext himg (.of_allocContracts hA) hPure.to_4K
    kpkKit hkpkOk stk hstk_pure hstk_kpk_poll hstk_lt ret s0 s Frame Q (Qp := Qp) hpan
    coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
    v_98 v_a0 v_b0 u_4f8 u_500 u_90 u_a8 u_b8 u_c0 u_d0 u_3d8 u_3e0 u_3e8 u_3f0
    kyberPreKeyId b_4f1 stKpk hb hkyber_nz hF hsym henv hid_kpk hrec_wf
    hpc hrun hsp_align htr hvregs hx0 hx1 hx19 hx21 hx23 hx26 hx27 hErr hOk

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
