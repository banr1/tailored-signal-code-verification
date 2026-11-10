/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitE
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1

/-!
# Stage P2 Substage P2.2

Proves 4 KiB-stacked CPS `stageP2_sub2_kits_ext` (`+0x0f14 → +0x1460` on `Ok`, or `+0x0f38` Arm 1
on `spkKit.getPoll` error) on `tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderStore
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

theorem p2_sepWPp_weaken_eq {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hw : SepWPp prog target s P' Q Qp)
    (hP : P = P' ∗ emp) :
    SepWPp prog target s P Q Qp := by
  rw [hP, sepConj_emp]; exact hw

theorem p2_sepWPp_pure_elim_frame {prog : Program} {target : BitVec 64} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (φ : Prop)
    (hP : P = ⌜φ⌝ ∗ F)
    (h : φ → SepWPp prog target s F Q Qp) :
    SepWPp prog target s P Q Qp := by
  rw [hP]; exact SepWPp.pure_elim h

set_option maxHeartbeats 1200000 in
/-- Kit-generic Substage P2.2 (`+0x0f14 -> +0x1460` or `+0x0f38` Arm 1) in CPS form:
polls `spkKit.getPoll`, delegates `.error e` at `+0x0f38` to `hErr`, and on `.ok r` drops/frees the
SPK future, deserializes & clamps the Curve25519 SPK keypair, frees the cloned record buffers, and
invokes `kpkKit.getShim` reaching `+0x1460` (`hOk`). -/
theorem stageP2_sub2_kits_ext {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A img.base ext) (hPure : StageP2PureCallees4K P A F img ext)
    (spkKit : SignedPreKeyStoreSpec A img.base) (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A img.base) (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_spk_poll : spkKit.getPollStack ≤ stk) (hstk_kpk_shim : kpkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (coroPtr ctxPtr msgPtr spkStorePtr spkFutPtr kyberStorePtr kyberCtCap
     v_a0 v_b0 u_90 u_b8 u_d0 u_4f8 u_500 : BitVec 64)
    (spkId kyberPreKeyId : BitVec 32) (stSpk : spkKit.SpkState)
    (s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (henv : ∀ s1 : State, Steps (tripleRatchetProgAtExt img.base ext) s s1 →
      s1.trace = s.trace → spkKit.envOk s1.fs.files)
    (hid_spk : spkKit.idOk spkId)
    (hrec_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk spkId (.ok r) → spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
        spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xf14#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = spkFutPtr) (hx1 : s.readReg64 .x1 = img.base + spkKit.getFutVtOff)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hErr : ∀ (e : spkKit.GetErr) (s2 : State),
      Steps (tripleRatchetProgAtExt img.base ext) s s2 →
      spkKit.getRel stSpk spkId (.error e) →
      s2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xf38#64 →
      s2.status = .Running → s2.sp = s.sp →
      s2.trace = s.trace ++ spkKit.getEvs spkId (.error e) →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x21 = v_b0 →
      s2.readReg64 .x23 = v_a0 → s2.readReg64 .x25 = s.readReg64 .x25 →
      s2.readReg64 .x26 = coroPtr + 0x398#64 → s2.readReg64 .x27 = ctxPtr →
      s2.readReg64 .x28 = s.readReg64 .x28 → s2.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      img.FrozenLoaded s2 → s2.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s2
        (spkGetPollOutAt spkKit (s.sp + 0x3e0#64) (.error e) ∗
         spkKit.getBoxAt spkFutPtr spkStorePtr spkId 1#8 ∗
         spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk spkId (.error e)) ∗
         ((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
         bytes7At (s.sp + 0x930#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
         memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
         keyPair64UnalignedAt (coroPtr + 0x398#64) c0_init c1_init c2_init c3_init
           c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
           cw6_init c63_init ∗
         ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
         ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
         ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((img.base + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getPollOff)) ∗
         ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getShimOff)) ∗
         A.live spkFutPtr spkKit.getBoxSize 8 ∗ A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q Qp)
    (hOk : ∀ (r : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (v90 privCap privPtr sigPtr kyberFutPtr : BitVec 64)
      (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
      (w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp : BitVec 64)
      (sf : State),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      spkKit.getRel stSpk spkId (.ok r) → spkKit.RecOk r →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      r.signedPreKey.publicKey = 5#8 :: spkPubBytes → r.signedPreKey.privateKey = spkPrivBytes →
      (∀ a : BitVec 64, (a ↦ₛ spkPubBytes) =
        (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
          ((a + 24#64) ↦₆₄ u3_kp)) →
      (∀ a : BitVec 64, (a ↦ₛ clampBv8List spkPrivBytes) =
        (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
          ((a + 24#64) ↦₆₄ u7_kp)) →
      (∀ a : BitVec 64,
        bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗
        ((a + 7#64) ↦₆₄ w0) ∗ ((a + 15#64) ↦₆₄ w1) ∗ ((a + 23#64) ↦₆₄ w2) ∗ ((a + 31#64) ↦₆₄ w3) =
          (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
            ((a + 24#64) ↦₆₄ u3_kp) ∗ bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6) →
      (∀ a : BitVec 64,
        bytes7At a c0 c1 c2 c3 c4 c5 c6 ∗
        ((a + 7#64) ↦₆₄ w4) ∗ ((a + 15#64) ↦₆₄ w5) ∗ ((a + 23#64) ↦₆₄ w6) ∗ ((a + 31#64) ↦₈ b63) =
          (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
            ((a + 24#64) ↦₆₄ u7_kp)) →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1460#64 →
      sf.status = .Running → sf.sp = s.sp →
      sf.trace = s.trace ++ spkKit.getEvs spkId (.ok r) →
      sf.readReg64 .x0 = kyberFutPtr → sf.readReg64 .x1 = img.base + kpkKit.getFutVtOff →
      kyberFutPtr ≠ 0#64 → kyberFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x20 = sigPtr →
      sf.readReg64 .x21 = v_b0 → sf.readReg64 .x23 = v_a0 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = coroPtr + 0x398#64 → sf.readReg64 .x27 = ctxPtr →
      sf.readReg64 .x28 = s.sp + 0xa90#64 → sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk spkId (.ok r)) ∗
         A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
         kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 0#8 ∗
         ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (s.sp + 0x3e0#64) 88 ∗
         bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
         keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
         ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
         ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
         ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((img.base + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getPollOff)) ∗
         ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getShimOff)) ∗
         A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (s.sp + 0x3e0#64) 88 ∗
       bytes7At (s.sp + 0x930#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
       memRegion (s.sp + 0xa90#64) 65 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       keyPair64UnalignedAt (coroPtr + 0x398#64) c0_init c1_init c2_init c3_init
         c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
         cw6_init c63_init ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
       ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
       ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getPollOff)) ∗
       ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getShimOff)) ∗
       A.live spkFutPtr spkKit.getBoxSize 8 ∗
       spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗
       spkKit.storeAt spkStorePtr stSpk ∗ A.pool ∗ stackAt s.sp stk ∗ Frame)
      Q Qp := by
  have hstep1 := p2_seg2a_ext_wp img.base ext s coroPtr ctxPtr spkFutPtr
    (img.base + spkKit.getFutVtOff) (img.base + spkKit.getPollOff)
    (coroPtr + 0x398#64) v_a0 v_b0 u_4f8 u_500 hpc hrun hsp_align hx0 hx1 hx19
  refine p2_bind_sepWP_steps_frame_qpan hF hsym hstep1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, _, hx8_1, hx19_1, hx21_1, hx23_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_poll := p2_stackAt_split_of_le s.sp stk spkKit.getPollStack hstk_spk_poll hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll) (by sep_focus) ?_
  sep_norm
  refine p2_call_oom_steps_frame_qpan
    (x := (({ fut := spkFutPtr, self := spkStorePtr, out := s.sp + 0x3e0#64,
              id := spkId } : PreKeyPollCall), stSpk))
    hpan hF1 hsym1 (htr1 ▸ htr) hspkOk.getPoll hpc1 hrun1 hsp1_al hx30_1
    (hsp1 ▸ p2_spkGetPoll_pre_intro hF1 hsym1 (henv s1 hst01 htr1) hb hx0_1 hx8_1 hid_spk)
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun s2 hst12 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  dsimp only [Spec.inImage, kitSpkGetPollSpecE, withEnvPre, kitSpkGetPollSpec]
  rcases hcs2 with ⟨hcs2_19, _, hcs2_21, _, hcs2_23, _, hcs2_25, hcs2_26, hcs2_27, hcs2_28,
    hcs2_29, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rw [hsp1]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.pure_elim fun ⟨hrel, htr2_1⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll.symm) (by sep_focus) ?_
  have htr2 : s2.trace = s.trace ++ spkKit.getEvs spkId ans := by rw [htr2_1, htr1]
  cases ans with
  | error e =>
    have herr := hErr e s2 (hst01.trans hst12) hrel hpc2 hrun2 hsp2 htr2
      (hcs2_19.trans hx19_1) (hcs2_21.trans hx21_1) (hcs2_23.trans hx23_1)
      (hcs2_25.trans hx25_1) (hcs2_26.trans hx26_1) (hcs2_27.trans hx27_1)
      (hcs2_28.trans hx28_1) (hcs2_29.trans hx29_1)
      (by rw [hvregs2_1, hvregs1, hvregs]) hF2 hsym2
    exact p2_sepWPp_weaken_eq herr (by sep_focus)
  | ok r =>
    dsimp only [spkGetPollOutAt]
    simp only [sepConj_assoc]
    refine p2_sepWPp_pure_elim_frame (spkKit.RecOk r) (by sep_focus) fun hrec_ok => ?_
    obtain ⟨spkPubBytes, spkPrivBytes, hpub_len, hpriv_len, hpub_eq, hpriv_eq⟩ :=
      hrec_wf r hrel hrec_ok
    refine SepWPp.weaken_frame (p2_signedPreKeyStructAt_unpack A (s.sp + 0x3e0#64) r.signedPreKey)
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun pubCap => SepWPp.exists_elim fun pubPtr =>
      SepWPp.exists_elim fun privCap => SepWPp.exists_elim fun privPtr =>
      SepWPp.exists_elim fun sigCap => SepWPp.exists_elim fun sigPtr =>
      SepWPp.exists_elim fun pad32 => ?_
    have hpub_bv : BitVec.ofNat 64 r.signedPreKey.publicKey.length = 33#64 := by
      rw [hpub_eq]; simp [hpub_len]
    have hpriv_bv : BitVec.ofNat 64 r.signedPreKey.privateKey.length = 32#64 := by
      rw [hpriv_eq, hpriv_len]
    rw [hpub_bv, hpriv_bv, hpub_eq, hpriv_eq]
    refine SepWPp.weaken_frame (p2_vecU8Buf_nonempty A pubCap pubPtr (5#8 :: spkPubBytes) (by simp))
      (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpub_le, _, hpub_nz, hpub_ne2, hpub_ne1⟩ => ?_
    refine SepWPp.weaken_frame (p2_vecU8Buf_nonempty A privCap privPtr spkPrivBytes (by omega))
      (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpriv_le, _, hpriv_nz, _, _⟩ => ?_
    have hstep3 := p2_seg2b_gen_wp img.base ext s2 coroPtr spkFutPtr
      (img.base + spkKit.getFutVtOff) (img.base + spkKit.getFutDropOff)
      pubCap pubPtr privCap privPtr sigCap sigPtr
      (coroPtr + 0x398#64) v_a0 v_b0 u_90 (coroPtr + 0x398#64) v_a0 v_b0 u_b8 u_d0
      hpc2 hrun2 hsp2_align hpub_ne2 (spkKit.getFutDrop_ne_zero hb)
      (hcs2_19.trans hx19_1) (hcs2_21.trans hx21_1) (hcs2_23.trans hx23_1) (hcs2_26.trans hx26_1)
    have hvt0 : (img.base + spkKit.getFutVtOff) + 0x0#64 = img.base + spkKit.getFutVtOff :=
      BitVec.add_zero _
    rw [hsp2, hvt0] at hstep3
    refine p2_bind_sepWP_steps_frame_qpan hF2 hsym2 hstep3 (by sep_focus)
      fun s3 hst23 hpc3 hrun3 hF3 hsym3 hregs3 => ?_
    rcases hregs3 with ⟨hsp3, htr3_2, _, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3,
      hx26_3, hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
    have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
    refine p2_call_nopanic_steps_frame (x := ()) (T := emp)
      hF3 hsym3 hspkOk.getFutDrop hpc3 hrun3 hsp3_al hx30_3
      rfl ⟨hF3, hsym3⟩ (by sep_focus)
      (hnext := fun s4 hst34 hpc4 hrun4 hsp4_3 _ hcs4 hF4 hsym4 => ?_)
    dsimp only [Spec.inImage, LibsignalPublicApi.StoreSession.futDropSpec]
    refine SepWPp.pure_elim fun htr4_3 => ?_
    rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25, hcs4_26,
      hcs4_27, hcs4_28, hcs4_29, hvregs4_3⟩
    have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
    have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
    refine SepWPp.weaken_frame (spkKit.getBoxAt_memRegion spkFutPtr spkStorePtr spkId 1#8)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame
      (p2_preKeyRecordOut64_tail_to_memRegion88 (s.sp + 0x3e0#64)
        pubCap pubPtr 33#64 privCap privPtr 32#64 sigCap sigPtr
        (BitVec.ofNat 64 r.signedPreKey.signature.length)
        r.signedPreKey.timestamp (pad32 ++ r.signedPreKey.id))
      (by sep_focus) ?_
    have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
      (Nat.le_trans p2_alloc_le_pure hstk_pure) hstk_lt
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
    have hstep5 := p2_seg2c_hooks_wp img.base ext hH s4 coroPtr spkFutPtr
      (img.base + spkKit.getFutVtOff) pubCap pubPtr privPtr sigPtr spkKit.getBoxSize
      hpc4 hrun4 hsp4_align hpub_ne1 spkKit.getBoxSize_ne_zero spkKit.getBoxSize_lt
      (hcs4_19.trans hx19_3) (hcs4_20.trans hx20_3) (hcs4_21.trans hx21_3)
      (hcs4_22.trans hx22_3) (hcs4_23.trans hx23_3) (hcs4_24.trans hx24_3)
      (hcs4_26.trans hx26_3) (hcs4_28.trans hx28_3)
    rw [hsp4] at hstep5
    refine p2_bind_sepWP_steps_frame_qpan hF4 hsym4 hstep5 (by sep_focus)
      fun s5 hst45 hpc5 hrun5 hF5 hsym5 hregs5 => ?_
    rcases hregs5 with ⟨hsp5, htr5_4, hx0_5, hx1_5, hx2_5, hx3_5, hx8_5, hx19_5, hx20_5, hx22_5,
      _, hx25_5, _, hx27_5, hx28_5, hx29_5, hx30_5, hvregs5_4⟩
    have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
    have hstk_kp1 := p2_stackAt_split_of_le s.sp stk 176
      (Nat.le_trans p2_kp176_le_pure hstk_pure) hstk_lt
    have hstk_kp2 := stackAt_176_keypair_eq s.sp
    refine SepWPp.weaken_frame (Entails.of_eq hstk_kp1) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_kp2) (by sep_focus) ?_
    sep_norm
    refine p2_call_nopanic_steps_frame
      (x := (pubPtr, spkPubBytes, privPtr, spkPrivBytes, s.sp + 0xa90#64))
      (T := (pubPtr ↦ₛ (5#8 :: spkPubBytes)) ∗ (privPtr ↦ₛ spkPrivBytes) ∗
        memRegion (s.sp + 0xa90#64) 65 ∗ cells (s.sp - 176#64) 8 ∗ cells (s.sp - 112#64) 14)
      hF5 hsym5 hPure.curveKeyPairSerde hpc5 hrun5 hsp5_al hx30_5
      (by dsimp only [curveKeyPairSerdeOkSpec]; rw [hsp5])
      (And.intro hx0_5 (And.intro hx1_5 (And.intro hx2_5
        (And.intro hx3_5 (And.intro hx8_5 (And.intro hpub_len hpriv_len))))))
      (by sep_focus)
      (hnext := fun s6 hst56 hpc6 hrun6 hsp6_5 _ hcs6 hF6 hsym6 => ?_)
    dsimp only [curveKeyPairSerdeOkSpec]
    rcases hcs6 with ⟨hcs6_19, hcs6_20, _, hcs6_22, _, _, hcs6_25, _, hcs6_27, hcs6_28, hcs6_29,
      hvregs6_5⟩
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
    rw [hsp5, show (s.sp + 0xa90#64) + 1#64 = s.sp + 0xa91#64 by bv_omega,
      show (s.sp + 0xa90#64) + 33#64 = s.sp + 0xab1#64 by bv_omega]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htr6_5 => ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_kp2.symm) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_kp1.symm) (by sep_focus) ?_
    have hclamp_len : (clampBv8List spkPrivBytes).length = 32 := clampBv8List_length hpriv_len
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b63, c0, c1, c2, c3, c4, c5, c6,
      w0, w1, w2, w3, w4, w5, w6, u0_kp, u1_kp, u2_kp, u3_kp, u4_kp, u5_kp, u6_kp, u7_kp,
      hpk_words, hsk_words, hkp64_eq, hkp_lo, hkp_hi⟩ := exists_keyPair64_decomp hpub_len hclamp_len
    have ha91_eq :
        ((s.sp + 0xa91#64) ↦ₛ spkPubBytes) ∗ ((s.sp + 0xab1#64) ↦ₛ clampBv8List spkPrivBytes) =
          keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 := by
      rw [show s.sp + 0xab1#64 = (s.sp + 0xa91#64) + 32#64 by bv_omega]
      exact hkp64_eq (s.sp + 0xa91#64)
    refine SepWPp.weaken_frame (Entails.of_eq ha91_eq) (by sep_focus) ?_
    refine SepWPp.weaken_frame (p2_vecU8Buf_rejoin pubPtr pubCap (5#8 :: spkPubBytes) hpub_le)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (p2_vecU8Buf_rejoin privPtr privCap spkPrivBytes hpriv_le)
      (by sep_focus) ?_
    have hmr88 : memRegion (s.sp + 0x3e0#64) 9 ∗ memRegion (s.sp + 0x3e9#64) 79 =
        memRegion (s.sp + 0x3e0#64) 88 :=
      (ProofLib.memRegion_split' (b := s.sp + 0x3e0#64) (n := 9) (k := 79)
        (b' := s.sp + 0x3e9#64) rfl (by bv_omega) (by decide)).symm
    refine SepWPp.weaken_frame (Entails.of_eq hmr88.symm) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (memRegion_9_sp3e0_eq s.sp)) (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun u_3e0 => ?_
    simp only [sepExists_sepConj_right, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun b_3e8 => ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
    sep_norm
    have hnext7 : ∀ (v90 : BitVec 64) (s7 : State),
        Steps (tripleRatchetProgAtExt img.base ext) s6 s7 →
        s7.pc = img.base + kpkKit.getShimOff → s7.status = .Running →
        img.FrozenLoaded s7 → s7.symtab = img.symtab →
        s7.sp = s.sp ∧ s7.trace = s6.trace ∧
        s7.readReg64 .x0 = kyberStorePtr ∧ s7.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧
        s7.readReg64 .x19 = coroPtr ∧ s7.readReg64 .x20 = sigPtr ∧
        s7.readReg64 .x21 = v_b0 ∧ s7.readReg64 .x22 = pubPtr ∧
        s7.readReg64 .x23 = v_a0 ∧ s7.readReg64 .x25 = s6.readReg64 .x25 ∧
        s7.readReg64 .x26 = coroPtr + 0x398#64 ∧ s7.readReg64 .x27 = s6.readReg64 .x27 ∧
        s7.readReg64 .x28 = s.sp + 0xa90#64 ∧ s7.readReg64 .x29 = s6.readReg64 .x29 ∧
        s7.readReg64 .x30 =
          (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1460#64 ∧
        calleeSavedVRegs s7 = calleeSavedVRegs s6 →
        SepWPp (tripleRatchetProgAtExt img.base ext) ret s7
          ((((s.sp + 0xa90#64) ↦₈ 0#8) ∗
            keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
            bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗
            keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
            ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ w6) ∗ ((s.sp + 0x3e8#64) ↦₈ b63) ∗
            A.pool ∗ stackAt s.sp allocHookStack ∗
            ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
            ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
            ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getShimOff))) ∗
           (memRegion (s.sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗
            memRegion (s.sp + 0x3e9#64) 79 ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
            ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
            ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
            ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
            ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((img.base + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getPollOff)) ∗
            spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk spkId (.ok r)) ∗ Frame))
          Q Qp := by
      intro v90 s7 hst67 hpc7 hrun7 hF7 hsym7 hregs7
      rcases hregs7 with ⟨hsp7, htr7_6, hx0_7, hx1_7, hx19_7, hx20_7, hx21_7, _, hx23_7, hx25_7,
        hx26_7, hx27_7, hx28_7, hx29_7, hx30_7, hvregs7_6⟩
      have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7] using hsp_align
      refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
      refine SepWPp.weaken_frame (Entails.of_eq ha91_eq.symm) (by sep_focus) ?_
      refine SepWPp.weaken_frame
        (sp_a90_65_entails_memRegion (s.sp + 0xa90#64) 0#8 spkPubBytes (clampBv8List spkPrivBytes)
          hpub_len hclamp_len)
        (by sep_focus) ?_
      refine SepWPp.weaken_frame (sp3e0_9_entails_memRegion s.sp w6 b63) (by sep_focus) ?_
      refine SepWPp.weaken_frame (Entails.of_eq hmr88) (by sep_focus) ?_
      have hstk_kpk := p2_stackAt_split_of_le s.sp stk kpkKit.getShimStack hstk_kpk_shim hstk_lt
      refine SepWPp.weaken_frame (Entails.of_eq hstk_kpk) (by sep_focus) ?_
      sep_norm
      have htr7 : s7.trace = s.trace ++ spkKit.getEvs spkId (.ok r) := by
        rw [htr7_6, htr6_5, htr5_4, htr4_3, htr3_2, htr2]
      have hx1_7_32 : s7.readReg32 .x1 = kyberPreKeyId := by
        change (s7.readReg64 .x1).setWidth 32 = kyberPreKeyId
        rw [hx1_7, p2_zext64_trunc32_id]
      refine p2_call_oom_steps_frame_qpan
        (x := ({ self := kyberStorePtr, id := kyberPreKeyId } : PreKeyShimCall))
        hpan hF7 hsym7 (htr.trans ⟨_, htr7.symm⟩) hkpkOk.getShim hpc7 hrun7 hsp7_al hx30_7
        (hsp7 ▸ p2_kpkGetShim_pre_intro hF7 hsym7 hb hx0_7 hx1_7_32)
        (by sep_focus) (fun _ => Entails.refl _)
        (hnext := fun sf hst7f hpcf hrunf hspf_7 _ hcsf hFf hsymf => ?_)
      dsimp only [Spec.inImage, kitKpkGetShimSpec]
      rcases hcsf with ⟨hcsf_19, hcsf_20, hcsf_21, _, hcsf_23, _, hcsf_25, hcsf_26, hcsf_27,
        hcsf_28, hcsf_29, hvregsf_7⟩
      rw [hsp7]
      sep_norm
      refine SepWPp.pure_elim fun ⟨hx1_f, hfut_nz, hfut_al, htrf_7⟩ => ?_
      refine SepWPp.weaken_frame (Entails.of_eq hstk_kpk.symm) (by sep_focus) ?_
      have hsteps_all :=
        hst01.trans (hst12.trans (hst23.trans (hst34.trans (hst45.trans (hst56.trans (hst67.trans hst7f))))))
      have hok := hOk r spkPubBytes spkPrivBytes v90 privCap privPtr sigPtr (sf.readReg64 .x0)
        b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6
        w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp sf
        hsteps_all hrel hrec_ok hpub_len hpriv_len hpub_eq hpriv_eq hpk_words hsk_words hkp_lo hkp_hi
        hpcf hrunf (hspf_7.trans hsp7) (by rw [htrf_7, htr7]) rfl hx1_f hfut_nz hfut_al
        (hcsf_19.trans hx19_7) (hcsf_20.trans hx20_7) (hcsf_21.trans hx21_7)
        (hcsf_23.trans hx23_7)
        (by rw [hcsf_25, hx25_7, hcs6_25, hx25_5, hcs4_25, hx25_3, hcs2_25, hx25_1])
        (hcsf_26.trans hx26_7)
        (by rw [hcsf_27, hx27_7, hcs6_27, hx27_5, hcs4_27, hx27_3, hcs2_27, hx27_1])
        (hcsf_28.trans hx28_7)
        (by rw [hcsf_29, hx29_7, hcs6_29, hx29_5, hcs4_29, hx29_3, hcs2_29, hx29_1])
        (by rw [hvregsf_7, hvregs7_6, hvregs6_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1,
          hvregs1, hvregs])
        hFf hsymf
      exact p2_sepWPp_weaken_eq hok (by sep_focus)
    by_cases hsig : sigCap = 0#64
    · rw [hsig]
      refine SepWPp.weaken_frame (p2_vecU8Buf_zero A sigPtr r.signedPreKey.signature)
        (by sep_focus) ?_
      sep_norm
      have hstep7 := p2_seg2d_sig0_hooks_wp img.base ext hH s6 coroPtr msgPtr
        pubCap pubPtr privCap privPtr sigPtr kyberCtCap kyberStorePtr kpkKit.kpk_vt
        (img.base + kpkKit.getShimOff) v_a0 v_b0 u_3e0 kyberPreKeyId
        b0 b1 b2 b3 b4 b5 b6 b63 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
        c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init b_3e8
        w0 w1 w2 w3 w4 w5 w6 cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
        hpc6 hrun6 hsp6_align hpub_nz hpriv_nz hkyber_nz
        (hcs6_19.trans hx19_5) (hcs6_20.trans hx20_5) (hcs6_22.trans hx22_5) (hcs6_28.trans hx28_5)
      rw [hsp6] at hstep7
      exact p2_bind_sepWP_steps_frame_qpan hF6 hsym6 hstep7 (by sep_focus) (hnext7 0#64)
    · refine SepWPp.weaken_frame
        (p2_vecU8Buf_dealloc_nonzero A sigCap sigPtr r.signedPreKey.signature hsig)
        (by sep_focus) ?_
      sep_norm
      have hstep7 := p2_seg2d_sigNz_hooks_wp img.base ext hH s6 coroPtr msgPtr
        pubCap pubPtr privCap privPtr sigCap sigPtr kyberCtCap kyberStorePtr kpkKit.kpk_vt
        (img.base + kpkKit.getShimOff) v_a0 v_b0 u_3e0 kyberPreKeyId
        b0 b1 b2 b3 b4 b5 b6 b63 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
        c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init b_3e8
        w0 w1 w2 w3 w4 w5 w6 cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
        hpc6 hrun6 hsp6_align hpub_nz hpriv_nz hsig hkyber_nz
        (hcs6_19.trans hx19_5) (hcs6_20.trans hx20_5) (hcs6_22.trans hx22_5) (hcs6_28.trans hx28_5)
      rw [hsp6] at hstep7
      exact p2_bind_sepWP_steps_frame_qpan hF6 hsym6 hstep7 (by sep_focus) (hnext7 sigCap)

abbrev stageP2_sub2_kits_4k := @stageP2_sub2_kits_ext
abbrev stageP2_sub2_kits_hooks := @stageP2_sub2_kits_ext

theorem stageP2_sub2_kits {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext) (hPure : StageP2PureCallees P A F img ext)
    (spkKit : SignedPreKeyStoreSpec A img.base) (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A img.base) (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_spk_poll : spkKit.getPollStack ≤ stk) (hstk_kpk_shim : kpkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (coroPtr ctxPtr msgPtr spkStorePtr spkFutPtr kyberStorePtr kyberCtCap
     v_a0 v_b0 u_90 u_b8 u_d0 u_4f8 u_500 : BitVec 64)
    (spkId kyberPreKeyId : BitVec 32) (stSpk : spkKit.SpkState)
    (s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (henv : ∀ s1 : State, Steps (tripleRatchetProgAtExt img.base ext) s s1 →
      s1.trace = s.trace → spkKit.envOk s1.fs.files)
    (hid_spk : spkKit.idOk spkId)
    (hrec_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk spkId (.ok r) → spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
        spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xf14#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = spkFutPtr) (hx1 : s.readReg64 .x1 = img.base + spkKit.getFutVtOff)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hErr : ∀ (e : spkKit.GetErr) (s2 : State),
      Steps (tripleRatchetProgAtExt img.base ext) s s2 →
      spkKit.getRel stSpk spkId (.error e) →
      s2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xf38#64 →
      s2.status = .Running → s2.sp = s.sp →
      s2.trace = s.trace ++ spkKit.getEvs spkId (.error e) →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x21 = v_b0 →
      s2.readReg64 .x23 = v_a0 → s2.readReg64 .x25 = s.readReg64 .x25 →
      s2.readReg64 .x26 = coroPtr + 0x398#64 → s2.readReg64 .x27 = ctxPtr →
      s2.readReg64 .x28 = s.readReg64 .x28 → s2.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      img.FrozenLoaded s2 → s2.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s2
        (spkGetPollOutAt spkKit (s.sp + 0x3e0#64) (.error e) ∗
         spkKit.getBoxAt spkFutPtr spkStorePtr spkId 1#8 ∗
         spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk spkId (.error e)) ∗
         ((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
         bytes7At (s.sp + 0x930#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
         memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
         keyPair64UnalignedAt (coroPtr + 0x398#64) c0_init c1_init c2_init c3_init
           c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
           cw6_init c63_init ∗
         ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
         ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
         ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((img.base + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getPollOff)) ∗
         ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getShimOff)) ∗
         A.live spkFutPtr spkKit.getBoxSize 8 ∗ A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q Qp)
    (hOk : ∀ (r : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (v90 privCap privPtr sigPtr kyberFutPtr : BitVec 64)
      (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
      (w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp : BitVec 64)
      (sf : State),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      spkKit.getRel stSpk spkId (.ok r) → spkKit.RecOk r →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      r.signedPreKey.publicKey = 5#8 :: spkPubBytes → r.signedPreKey.privateKey = spkPrivBytes →
      (∀ a : BitVec 64, (a ↦ₛ spkPubBytes) =
        (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
          ((a + 24#64) ↦₆₄ u3_kp)) →
      (∀ a : BitVec 64, (a ↦ₛ clampBv8List spkPrivBytes) =
        (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
          ((a + 24#64) ↦₆₄ u7_kp)) →
      (∀ a : BitVec 64,
        bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗
        ((a + 7#64) ↦₆₄ w0) ∗ ((a + 15#64) ↦₆₄ w1) ∗ ((a + 23#64) ↦₆₄ w2) ∗ ((a + 31#64) ↦₆₄ w3) =
          (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
            ((a + 24#64) ↦₆₄ u3_kp) ∗ bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6) →
      (∀ a : BitVec 64,
        bytes7At a c0 c1 c2 c3 c4 c5 c6 ∗
        ((a + 7#64) ↦₆₄ w4) ∗ ((a + 15#64) ↦₆₄ w5) ∗ ((a + 23#64) ↦₆₄ w6) ∗ ((a + 31#64) ↦₈ b63) =
          (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
            ((a + 24#64) ↦₆₄ u7_kp)) →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1460#64 →
      sf.status = .Running → sf.sp = s.sp →
      sf.trace = s.trace ++ spkKit.getEvs spkId (.ok r) →
      sf.readReg64 .x0 = kyberFutPtr → sf.readReg64 .x1 = img.base + kpkKit.getFutVtOff →
      kyberFutPtr ≠ 0#64 → kyberFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x20 = sigPtr →
      sf.readReg64 .x21 = v_b0 → sf.readReg64 .x23 = v_a0 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = coroPtr + 0x398#64 → sf.readReg64 .x27 = ctxPtr →
      sf.readReg64 .x28 = s.sp + 0xa90#64 → sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk spkId (.ok r)) ∗
         A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
         kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 0#8 ∗
         ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (s.sp + 0x3e0#64) 88 ∗
         bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
         keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
         ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
         ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
         ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((img.base + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getPollOff)) ∗
         ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getShimOff)) ∗
         A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (s.sp + 0x3e0#64) 88 ∗
       bytes7At (s.sp + 0x930#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
       memRegion (s.sp + 0xa90#64) 65 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       keyPair64UnalignedAt (coroPtr + 0x398#64) c0_init c1_init c2_init c3_init
         c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
         cw6_init c63_init ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
       ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
       ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getPollOff)) ∗
       ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getShimOff)) ∗
       A.live spkFutPtr spkKit.getBoxSize 8 ∗
       spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗
       spkKit.storeAt spkStorePtr stSpk ∗ A.pool ∗ stackAt s.sp stk ∗ Frame)
      Q Qp :=
  stageP2_sub2_kits_ext img ext (.of_allocContracts hA) hPure.to_4K
    spkKit hspkOk kpkKit hkpkOk stk hstk_pure hstk_spk_poll hstk_kpk_shim hstk_lt
    ret s0 s Frame Q (Qp := Qp) hpan coroPtr ctxPtr msgPtr spkStorePtr spkFutPtr kyberStorePtr kyberCtCap
    v_a0 v_b0 u_90 u_b8 u_d0 u_4f8 u_500 spkId kyberPreKeyId stSpk
    s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hb hF hsym henv hid_spk hrec_wf hkyber_nz hpc hrun hsp_align htr hvregs hx0 hx1 hx19 hErr hOk

private theorem extract56_8_0_s (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 0 8 = x.extractLsb' 56 8 := by
  ext i hi
  rw [BitVec.getElem_extractLsb', Nat.zero_add, BitVec.getLsbD_append]
  simp [hi]

private theorem extract56_8_hi_s (x y : BitVec 64) (k : Nat) (hk : 8 ≤ k) (hk2 : k + 8 ≤ 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' k 8 = y.extractLsb' (k - 8) 8 := by
  ext i hi
  have h1 : ¬ (k + i < 8) := by omega
  have h3 : k + i - 8 = k - 8 + i := by omega
  rw [BitVec.getElem_extractLsb', BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  simp [BitVec.getLsbD_extractLsb', h1, h3]; omega

theorem bytes7_word_shift_std3 (a x y : BitVec 64) :
    bytes7At a (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8) (x.extractLsb' 24 8)
      (x.extractLsb' 32 8) (x.extractLsb' 40 8) (x.extractLsb' 48 8) ∗
    ((a + 0x07#64) ↦₆₄ (y.extractLsb' 0 56 ++ x.extractLsb' 56 8)) =
    (a ↦₆₄ x) ∗ bytes7At (a + 0x08#64) (y.extractLsb' 0 8) (y.extractLsb' 8 8)
      (y.extractLsb' 16 8) (y.extractLsb' 24 8) (y.extractLsb' 32 8) (y.extractLsb' 40 8) (y.extractLsb' 48 8) := by
  simp only [bytes7At, pointsTo64, extract56_8_0_s, extract56_8_hi_s x y 8 (by decide) (by decide),
    extract56_8_hi_s x y 16 (by decide) (by decide), extract56_8_hi_s x y 24 (by decide) (by decide),
    extract56_8_hi_s x y 32 (by decide) (by decide), extract56_8_hi_s x y 40 (by decide) (by decide),
    extract56_8_hi_s x y 48 (by decide) (by decide), extract56_8_hi_s x y 56 (by decide) (by decide),
    Nat.reduceSub, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem keyPair39_eq_words4_bytes7_std3 (a ik0 ik1 ik2 ik3 ik4 : BitVec 64) :
    bytes7At a (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) ∗
    ((a + 0x07#64) ↦₆₄ (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)) ∗
    ((a + 0x0f#64) ↦₆₄ (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)) ∗
    ((a + 0x17#64) ↦₆₄ (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)) ∗
    ((a + 0x1f#64) ↦₆₄ (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)) =
    (a ↦₆₄ ik0) ∗ ((a + 0x08#64) ↦₆₄ ik1) ∗ ((a + 0x10#64) ↦₆₄ ik2) ∗ ((a + 0x18#64) ↦₆₄ ik3) ∗
    bytes7At (a + 0x20#64) (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8)
      (ik4.extractLsb' 24 8) (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) := by
  have h1 := bytes7_word_shift_std3 a ik0 ik1; have h2 := bytes7_word_shift_std3 (a + 0x08#64) ik1 ik2
  have h3 := bytes7_word_shift_std3 (a + 0x10#64) ik2 ik3; have h4 := bytes7_word_shift_std3 (a + 0x18#64) ik3 ik4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2 h3 h4
  rw [← sepConj_assoc, h1, sepConj_assoc, ← sepConj_assoc (bytes7At (a + 8#64) _ _ _ _ _ _ _), h2,
      sepConj_assoc, ← sepConj_assoc (bytes7At (a + 16#64) _ _ _ _ _ _ _), h3, sepConj_assoc, h4]

theorem keyPair32Hi_eq_words4_std3 (b ik4 ik5 ik6 ik7 : BitVec 64) :
    bytes7At b (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8) (ik4.extractLsb' 24 8)
      (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) ∗
    ((b + 0x07#64) ↦₆₄ (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)) ∗
    ((b + 0x0f#64) ↦₆₄ (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)) ∗
    ((b + 0x17#64) ↦₆₄ (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)) ∗ ((b + 0x1f#64) ↦₈ (ik7.extractLsb' 56 8)) =
    (b ↦₆₄ ik4) ∗ ((b + 0x08#64) ↦₆₄ ik5) ∗ ((b + 0x10#64) ↦₆₄ ik6) ∗ ((b + 0x18#64) ↦₆₄ ik7) := by
  have h1 := bytes7_word_shift_std3 b ik4 ik5; have h2 := bytes7_word_shift_std3 (b + 0x08#64) ik5 ik6
  have h3 := bytes7_word_shift_std3 (b + 0x10#64) ik6 ik7; have h4 := bytes7_byte_fold (b + 0x18#64) ik7
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2 h3 h4
  rw [← sepConj_assoc, h1, sepConj_assoc, ← sepConj_assoc (bytes7At (b + 8#64) _ _ _ _ _ _ _), h2,
      sepConj_assoc, ← sepConj_assoc (bytes7At (b + 16#64) _ _ _ _ _ _ _), h3, sepConj_assoc, h4]

theorem words8_eq_keyPair64UnalignedAt_std3 (a ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 : BitVec 64) :
    ((a ↦₆₄ ik0) ∗ ((a + 0x08#64) ↦₆₄ ik1) ∗ ((a + 0x10#64) ↦₆₄ ik2) ∗ ((a + 0x18#64) ↦₆₄ ik3) ∗
     ((a + 0x20#64) ↦₆₄ ik4) ∗ ((a + 0x28#64) ↦₆₄ ik5) ∗ ((a + 0x30#64) ↦₆₄ ik6) ∗ ((a + 0x38#64) ↦₆₄ ik7)) =
    keyPair64UnalignedAt a (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8)
      (ik0.extractLsb' 24 8) (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8)
      (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8) (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
      (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8) (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
      (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8) (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
      (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8) (ik7.extractLsb' 56 8) := by
  have hlo := keyPair39_eq_words4_bytes7_std3 a ik0 ik1 ik2 ik3 ik4
  have hhi := keyPair32Hi_eq_words4_std3 (a + 0x20#64) ik4 ik5 ik6 ik7
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhi; unfold keyPair64UnalignedAt; rw [← hhi]; symm
  calc _ = (bytes7At a (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) ∗
      ((a + 0x07#64) ↦₆₄ (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)) ∗
      ((a + 0x0f#64) ↦₆₄ (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)) ∗
      ((a + 0x17#64) ↦₆₄ (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)) ∗
      ((a + 0x1f#64) ↦₆₄ (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8))) ∗
      (((a + 0x27#64) ↦₆₄ (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)) ∗
      ((a + 0x2f#64) ↦₆₄ (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)) ∗
      ((a + 0x37#64) ↦₆₄ (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)) ∗
      ((a + 0x3f#64) ↦₈ (ik7.extractLsb' 56 8))) := by ac_rfl
    _ = _ := by rw [hlo]; ac_rfl

theorem memRegion64_entails_exists_keyPair64UnalignedAt_std3 (a : BitVec 64) :
    memRegion a 64 ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8, ∃∗ b4 : BitVec 8,
        ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8, ∃∗ b63 : BitVec 8,
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        keyPair64UnalignedAt a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 := by
  rw [ProofLib.memRegion_cells a 8 (by decide)]
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 => Entails.sepExists_elim
    fun u2 => Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u4 =>
    Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u6 => Entails.sepExists_elim fun u7 => ?_
  rw [words8_eq_keyPair64UnalignedAt_std3 a u0 u1 u2 u3 u4 u5 u6 u7]
  refine Entails.sepExists_right (u0.extractLsb' 0 8)
    (Entails.sepExists_right (u0.extractLsb' 8 8) (Entails.sepExists_right (u0.extractLsb' 16 8)
    (Entails.sepExists_right (u0.extractLsb' 24 8) (Entails.sepExists_right (u0.extractLsb' 32 8)
    (Entails.sepExists_right (u0.extractLsb' 40 8) (Entails.sepExists_right (u0.extractLsb' 48 8)
    (Entails.sepExists_right (u7.extractLsb' 56 8) (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.refl _)))))))))))))))

theorem coro798_64_entails_unaligned_std3 (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x798#64) 64 ⊢
      ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
      ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8,
      ∃∗ cw0 : BitVec 64, ∃∗ cw1 : BitVec 64, ∃∗ cw2 : BitVec 64, ∃∗ cw3 : BitVec 64,
      ∃∗ cw4 : BitVec 64, ∃∗ cw5 : BitVec 64, ∃∗ cw6 : BitVec 64, ∃∗ c63 : BitVec 8,
        bytes7At (coroPtr + 0x798#64) c0 c1 c2 c3 c4 c5 c6 ∗
        ((coroPtr + 0x79f#64) ↦₆₄ cw0) ∗ ((coroPtr + 0x7a7#64) ↦₆₄ cw1) ∗
        ((coroPtr + 0x7af#64) ↦₆₄ cw2) ∗ ((coroPtr + 0x7b7#64) ↦₆₄ cw3) ∗
        ((coroPtr + 0x7bf#64) ↦₆₄ cw4) ∗ ((coroPtr + 0x7c7#64) ↦₆₄ cw5) ∗
        ((coroPtr + 0x7cf#64) ↦₆₄ cw6) ∗ ((coroPtr + 0x7d7#64) ↦₈ c63) := by
  rw [ProofLib.memRegion_cells (coroPtr + 0x798#64) 8 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 =>
    Entails.sepExists_elim fun u2 => Entails.sepExists_elim fun u3 =>
    Entails.sepExists_elim fun u4 => Entails.sepExists_elim fun u5 =>
    Entails.sepExists_elim fun u6 => Entails.sepExists_elim fun u7 => ?_
  have hw := words8_eq_keyPair64UnalignedAt_std3 (coroPtr + 0x798#64) u0 u1 u2 u3 u4 u5 u6 u7
  unfold keyPair64UnalignedAt at hw
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hw
  rw [hw]
  exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.refl _)))))))))))))))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
