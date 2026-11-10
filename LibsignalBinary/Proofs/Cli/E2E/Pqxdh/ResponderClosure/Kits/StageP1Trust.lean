/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegTrustAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP1

/-!
# Stage P1 `is_trusted_identity` Step on Store Kits

Proves `stageP1_trust_call_wp_kit` (`img.base + ikit.trustShimOff → entry + 0x6e4#64`, generic
over `ans : Except Unit Bool`) and `stageP1_trust_ok_kit` (`→ entry + 0x868#64` for `ans = .ok
true`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

set_option maxHeartbeats 2800000 in
/-- Kit-generic Stage P1 Trust Call Block (`img.base + ikit.trustShimOff -> entry + 0x6e4#64`):
Executes the `is_trusted_identity` trait shim (`hikit.trustShim`), coroutine future setup
(`p1_seg5_wp`), poll closure (`hikit.trustPoll` with `logOff img` lent and returned), poll-output
read (`p1_seg6a_any_wp`), future drop (`hikit.trustFutDrop`), and box deallocation
(`p1_seg6_dealloc_wp`), stopping at the post-dealloc branch seam `entry + 0x6e4#64` for any
`ans : Except Unit Bool`. -/
theorem stageP1_trust_call_wp_kit {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {ikit : IdentityStoreSpec A img.base}
    {ist : ikit.IdState} {Q : Prop}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hA : AllocHooks A abs)
    (hikit : IdentityStoreKitOkI img ikit C ctl abs)
    (hstack_lt : trustCallStack ikit ≤ 2 ^ 64)
    (haddr_id : ikit.addrOk peer.val)
    (s0 s : State)
    (outPtr coroPtr ctxPtr msgPtr remoteAddrPtr
     idStorePtr
     u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s)
    (hfs : FsAt ikit.envOk Q (tripleRatchetProgAt img.base C ctl abs) s)
    (hpc : s.pc = img.base + ikit.trustShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hx0 : s.readReg64 .x0 = idStorePtr)
    (hx1 : s.readReg64 .x1 = remoteAddrPtr)
    (hx2 : s.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx30 : s.readReg64 .x30 =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64) s
      (((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
       ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
       logOff img ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt s.sp (trustCallStack ikit))
      (fun sm P_m =>
        (∃ ans : Except Unit Bool,
          ikit.trustRel ist peer.val remoteIdKey .receiving ans ∧
          sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans ∧
          sm.readReg64 .x20 = trustPollTag ans ∧
          (ans = .ok true → sm.readReg64 .x23 = 1#64) ∧
          (ans = .ok false → sm.readReg64 .x23 = 0#64) ∧
          (P_m ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              cells (coroPtr + 0x398#64) 2 ∗
              ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (s.sp + 0x3e0#64) 368 ∗
              ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
              ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
              (if ans.isOk then emp
               else ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ∗
              logOff img ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving ans) ∗
              protocolAddressAt A peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool ∗
              stackAt s.sp (trustCallStack ikit))) ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = coroPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        ImgCallInv img sm)
      (PanicOomProp s0) := by
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  have hdrop_nz : img.base + ikit.trustFutDropOff ≠ 0#64 := ikit.trustFutDrop_ne_zero hb
  have hbs_nz : BitVec.ofNat 64 ikit.trustBoxSize ≠ 0#64 := ikit.trustBoxSize_ne_zero
  have hbs_lt : ikit.trustBoxSize < 2 ^ 64 := ikit.trustBoxSize_lt
  have hx3_8 : (s.readReg64 .x3).setWidth 8 = 1#8 := by rw [hx3]; rfl
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_trustShim ikit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.call_oom_steps_frame
    (x := (({ self := idStorePtr, addrA := remoteAddrPtr,
              keyA := msgPtr + 0xc8#64 } : IdentityShimCall), 1#8))
    hinv htr hikit.trustShim hpc hrun hsp_al hx30
    (trustShim_pre_intro hinv hx0 hx1 hx2 hx3_8)
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s7 hsteps67 hpc7 hrun7 hsp7_s _ hcs7 hinv7 => ?_)
  dsimp only [Spec.inImage, kitTrustShimSpec]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_7, _, _, htr7_s⟩ => ?_
  have hfs7 : FsAt ikit.envOk Q (tripleRatchetProgAt img.base C ctl abs) s7 :=
    hfs.of_steps hsteps67 (evs := []) (by simpa using htr7_s) (fun _ => NoFsEv.nil)
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_trustShim ikit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hsp7_s]; exact hsp_align
  rcases hcs7 with ⟨hx19_cs7, _, hx21_cs7, _, _, _, _, hx26_cs7, hx27_cs7, _, hx29_cs7, _⟩
  have hx19_7 : s7.readReg64 .x19 = coroPtr := hx19_cs7.trans hx19
  have hx21_7 : s7.readReg64 .x21 = coroPtr + 0x390#64 := hx21_cs7.trans hx21
  have hx26_7 : s7.readReg64 .x26 = outPtr := hx26_cs7.trans hx26
  have hx27_7 : s7.readReg64 .x27 = ctxPtr := hx27_cs7.trans hx27
  have hstep8 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg5_wp
    img.base C ctl abs s7 coroPtr ctxPtr
    (s7.readReg64 .x0) (img.base + ikit.trustFutVtOff) (img.base + ikit.trustPollOff)
    u_398 u_3a0 u_c0
    hpc7 hrun7 hsp7_align rfl hx1_7 hx19_7 hx27_7
  rw [hsp7_s] at hstep8
  simp only [BitVec.add_assoc] at hstep8
  refine SepWPp.bind_sepWP_steps_frame hinv7 hstep8 (by sep_focus)
    fun s8 hsteps78 hpc8 hrun8 hinv8 hregs8 => ?_
  rcases hregs8 with ⟨hsp8_s, htr8_7, hx0_8, _, hx8_8, hx19_8, hx21_8, hx26_8, _, hx29_8, hx30_8⟩
  have hsp8_al : s8.spAligned = true := by simpa only [State.spAligned, hsp8_s] using hsp_align
  have htr8 : s0.trace <+: s8.trace := by
    rw [htr8_7, htr7_s]
    exact htr
  have hfs8 : FsAt ikit.envOk Q (tripleRatchetProgAt img.base C ctl abs) s8 :=
    hfs7.of_steps hsteps78 (evs := []) (by simpa using htr8_7) (fun _ => NoFsEv.nil)
  have hmr_3e0 : memRegion (s.sp + 0x3e0#64) 368 =
      memRegion (s.sp + 0x3e0#64) 48 ∗ memRegion (s.sp + 0x410#64) 320 :=
    ProofLib.memRegion_split' (b := s.sp + 0x3e0#64) (n := 48) (k := 320)
      (b' := s.sp + 0x410#64) rfl (by bv_omega) (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hmr_3e0) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_trustPoll ikit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.call_oom_steps_frame
    (x := (({ fut := s7.readReg64 .x0, out := s.sp + 0x3e0#64,
              call := { addrA := remoteAddrPtr, addr := peer,
                        keyA := msgPtr + 0xc8#64, key := remoteIdKey } } : IdentityPollCall),
           Direction.receiving, idStorePtr, ist))
    hinv8 htr8 hikit.trustPoll hpc8 hrun8 hsp8_al hx30_8
    (trustPoll_pre_intro hfs8.envOk_here hinv8 hsp8_s hx0_8 hx8_8 haddr_id)
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s9 _ hpc9 hrun9 hsp9_8 _ hcs9 hinv9 => ?_)
  dsimp only [kitTrustPollSpecI, Spec.inImage, withLogOff, kitTrustPollSpecE, withEnvPre,
    kitTrustPollSpec]
  rw [hsp8_s]
  sep_norm
  refine SepWPp.exists_elim fun ans => ?_
  refine SepWPp.pure_elim fun ⟨hrel, htr9_8⟩ => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_trustPoll ikit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  have hsp9_s : s9.sp = s.sp := hsp9_8.trans hsp8_s
  have hsp9_align : (s9.sp &&& 15#64 == 0#64) = true := by rw [hsp9_s]; exact hsp_align
  rcases hcs9 with ⟨hx19_cs9, _, hx21_cs9, _, _, _, _, hx26_cs9, _, _, hx29_cs9, _⟩
  have hx19_9 : s9.readReg64 .x19 = coroPtr := hx19_cs9.trans hx19_8
  have hx21_9 : s9.readReg64 .x21 = coroPtr + 0x390#64 :=
    by rw [hx21_cs9, hx21_8, hx21_7]
  have hx26_9 : s9.readReg64 .x26 = outPtr :=
    by rw [hx26_cs9, hx26_8, hx26_7]
  have hx29_9 : s9.readReg64 .x29 = s.readReg64 .x29 :=
    by rw [hx29_cs9, hx29_8, hx29_cs7]
  refine SepWPp.weaken_frame
    (trustPollOut_any_unpack img.base s.sp ans)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun b_3e8 =>
    SepWPp.exists_elim fun d_3e9 =>
    SepWPp.exists_elim fun h_3ed =>
    SepWPp.exists_elim fun b_3ef =>
    SepWPp.exists_elim fun w_3f0 =>
    SepWPp.exists_elim fun d_3f8 =>
    SepWPp.exists_elim fun d_3fc =>
    SepWPp.exists_elim fun w_400 =>
    SepWPp.exists_elim fun w_408 => ?_
  refine SepWPp.pure_elim fun ⟨hw_ne_neg3, hb_true, hb_false⟩ => ?_
  have hstep10 := p1_seg6a_any_wp
    img.base C ctl abs s9 coroPtr outPtr
    (s7.readReg64 .x0) (img.base + ikit.trustFutVtOff) (img.base + ikit.trustFutDropOff)
    (trustPollTag ans) w_3f0 w_400 w_408 u_a8 u_b0 u_b8 u_c8 u_d0
    d_3e9 d_3f8 d_3fc h_3ed b_3e8 b_3ef
    hw_ne_neg3 hpc9 hrun9 hsp9_align hdrop_nz hx19_9 hx21_9 hx26_9
  rw [hsp9_s, BitVec.add_zero] at hstep10
  refine SepWPp.bind_sepWP_steps_frame hinv9 hstep10 (by sep_focus)
    fun s10 _ hpc10 hrun10 hinv10 hregs10 => ?_
  rcases hregs10 with ⟨hsp10_s, htr10_9, _, hx19_10, hx20_10, hx21_10, hx23_10, hx25_10,
    _, hx29_10, hx30_10⟩
  have hsp10_al : s10.spAligned = true := by simpa only [State.spAligned, hsp10_s] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hmr_3e0.symm) (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    hinv10 hikit.trustFutDrop hpc10 hrun10 hsp10_al hx30_10
    (by simp [LibsignalPublicApi.StoreSession.futDropSpec]) True.intro (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s11 _ hpc11 hrun11 hsp11_10 _ hcs11 hinv11 => ?_)
  dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr11_10 => ?_
  have hsp11_s : s11.sp = s.sp := hsp11_10.trans hsp10_s
  have hsp11_align : (s11.sp &&& 15#64 == 0#64) = true := by rw [hsp11_s]; exact hsp_align
  rcases hcs11 with ⟨hx19_cs11, hx20_cs11, hx21_cs11, _, hx23_cs11, _, hx25_cs11, _, _, _,
    hx29_cs11, _⟩
  have hx19_11 : s11.readReg64 .x19 = coroPtr := hx19_cs11.trans hx19_10
  have hx20_11 : s11.readReg64 .x20 = trustPollTag ans := hx20_cs11.trans hx20_10
  have hx21_11 : s11.readReg64 .x21 = s7.readReg64 .x0 := hx21_cs11.trans hx21_10
  have hx23_11 : s11.readReg64 .x23 = b_3e8.zeroExtend 64 := hx23_cs11.trans hx23_10
  have hx25_11 : s11.readReg64 .x25 = img.base + ikit.trustFutVtOff := hx25_cs11.trans hx25_10
  have hx29_11 : s11.readReg64 .x29 = s.readReg64 .x29 :=
    by rw [hx29_cs11, hx29_10, hx29_9]
  refine SepWPp.weaken_frame
    (ikit.trustBoxAt_memRegion (s7.readReg64 .x0) idStorePtr remoteAddrPtr
      (msgPtr + 0xc8#64) 1#8 (directionByte .receiving))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (cells2_fold_398 coroPtr (s7.readReg64 .x0) (img.base + ikit.trustFutVtOff))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_alloc ikit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have hstep12 := p1_seg6_dealloc_wp
    (A := A) img.base C ctl abs hA s11
    coroPtr (s7.readReg64 .x0) (img.base + ikit.trustFutVtOff)
    (trustPollTag ans) (b_3e8.zeroExtend 64) ikit.trustBoxSize
    hpc11 hrun11 hsp11_align hbs_nz hbs_lt
    hx19_11 hx20_11 hx21_11 hx23_11 hx25_11
  rw [hsp11_s] at hstep12
  simp only [BitVec.add_assoc] at hstep12
  refine SepWPp.bind_sepWP_steps_frame hinv11 hstep12 (by sep_focus)
    fun sm _ hpcm hrunm hinvm hregsm => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_alloc ikit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcm hrunm ?_
  rcases hregsm with ⟨hspm_s, htrm_11, hx19_m, hx20_m, hx23_m, _, hx29_m⟩
  have htrm_s : sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans := by
    rw [htrm_11, htr11_10, htr10_9, htr9_8, htr8_7, htr7_s]
  have htrue_m : ans = .ok true → sm.readReg64 .x23 = 1#64 := fun ha => by
    rw [hx23_m, hb_true ha]; rfl
  have hfalse_m : ans = .ok false → sm.readReg64 .x23 = 0#64 := fun ha => by
    rw [hx23_m, hb_false ha]; rfl
  refine ⟨⟨ans, hrel, htrm_s, hx20_m, htrue_m, hfalse_m, ?_⟩,
    hspm_s, hx19_m, hx29_m.trans hx29_11, hinvm⟩
  refine Entails.sepExists_right (d_3fc.zeroExtend 64)
    (Entails.sepExists_right w_3f0
      (Entails.sepExists_right (d_3f8.zeroExtend 64) ?_))
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1600000 in
/-- Kit-generic Stage P1 Part B (`img.base + ikit.trustShimOff -> +0x0868`):
composing `stageP1_trust_call_wp_kit` (`-> +0x06e4`) with `p1_post_dealloc_true_wp` (`+0x06e4 -> +0x0868`). -/
theorem stageP1_trust_ok_kit {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {ikit : IdentityStoreSpec A img.base}
    {ist : ikit.IdState} {Q : Prop}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hA : AllocHooks A abs)
    (hikit : IdentityStoreKitOkI img ikit C ctl abs)
    (hstack_lt : trustCallStack ikit ≤ 2 ^ 64)
    (haddr_id : ikit.addrOk peer.val)
    (htrust_true : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok true)
    (s0 s : State)
    (outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt
     u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (b_4f2 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s)
    (hfs : FsAt ikit.envOk Q (tripleRatchetProgAt img.base C ctl abs) s)
    (hpc : s.pc = img.base + ikit.trustShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hx0 : s.readReg64 .x0 = idStorePtr)
    (hx1 : s.readReg64 .x1 = remoteAddrPtr)
    (hx2 : s.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx30 : s.readReg64 .x30 =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x868#64) s
      (processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
         spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
       ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       cells (coroPtr + 0x428#64) 8 ∗
       cells (coroPtr + 0x490#64) 4 ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
       ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
       logOff img ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt s.sp (trustCallStack ikit))
      (fun sf P_f =>
        ikit.trustRel ist peer.val remoteIdKey .receiving (.ok true) ∧
        sf.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok true) ∧
        (P_f ⊢
          ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
            processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
              spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
            processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
              spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
            cells (coroPtr + 0x398#64) 2 ∗
            ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
            ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
            ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
            ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
            memRegion (s.sp + 0x3e0#64) 368 ∗
            ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
            ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
            ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
            logOff img ∗
            ikit.identityAt idStorePtr (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok true)) ∗
            protocolAddressAt A peer remoteAddrPtr ∗
            ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
            A.pool ∗
            stackAt s.sp (trustCallStack ikit)) ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x8 = kyberStorePtr ∧
        sf.readReg64 .x9 = msgPtr ∧
        sf.readReg64 .x10 = kyberStoreVt ∧
        sf.readReg64 .x11 = preKeyStorePtr ∧
        sf.readReg64 .x12 = remoteAddrPtr ∧
        sf.readReg64 .x13 = preKeyStoreVt ∧
        sf.readReg64 .x14 = localAddrPtr ∧
        sf.readReg64 .x15 = idStorePtr ∧
        sf.readReg64 .x16 = ikit.id_vt ∧
        sf.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        sf.readReg64 .x22 = spkStorePtr ∧
        sf.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        sf.readReg64 .x24 = spkStoreVt ∧
        sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x28 = s.sp + 0xa90#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hcall := stageP1_trust_call_wp_kit (ist := ist)
    peer remoteIdKey hA hikit hstack_lt haddr_id
    s0 s outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hb hinv hfs hpc hrun hsp_align htr
    hx0 hx1 hx2 hx3 hx19 hx21 hx26 hx27 hx30
  have hcall_true := trust_call_wp_specialize_true htrust_true hcall
  refine SepWPp.bind_sepWPp_steps_frame hcall_true (by sep_focus)
    fun sm _ hpcm hrunm hregsm => ?_
  rcases hregsm with ⟨hrel, htrm, hx20_m, hx23_m, hspm, hx19_m, hx29_m, hinvm⟩
  have hsp_align_m : (sm.sp &&& 15#64 == 0#64) = true := by rw [hspm]; exact hsp_align
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  have hpost := p1_post_dealloc_true_wp
    img.base C ctl abs sm coroPtr
    msgPtr remoteAddrPtr localAddrPtr
    idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
    u_98 u_a0 b_4f2
    hpcm hrunm hsp_align_m hx19_m hx20_m hx23_m
  rw [hspm] at hpost
  refine SepWPp.ret_sepWP_steps_frame hinvm hpost (by sep_focus)
    fun sf _ _ _ hinvf hregsf => ?_
  rcases hregsf with ⟨hsp_f, htr_f, hx8_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx14_f,
    hx15_f, hx16_f, hx17_f, hx19_f, hx20_f, hx22_f, hx23_f, hx24_f, hx25_f, hx28_f, hx29_f⟩
  refine ⟨hrel, by rw [htr_f, htrm], ?_,
    hsp_f, hx8_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx14_f, hx15_f, hx16_f, hx17_f,
    hx19_f, hx20_f, hx22_f, hx23_f, hx24_f, hx25_f, hx28_f, hx29_f.trans hx29_m,
    hinvf.1, hinvf.2⟩
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
