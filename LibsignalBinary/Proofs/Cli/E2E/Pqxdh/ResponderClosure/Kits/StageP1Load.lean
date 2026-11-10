/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP1

/-!
# Stage P1 `load_session` Step on Store Kits

Proves `stageP1_load_ok_kit` (`img.base + kit.loadShimOff → img.base + ikit.trustShimOff`) for
both `opt = none` (empty session header at `coroPtr + 0xe0`) and `opt = some r` (loaded
`SessionRecord` satisfying `Scope r` moved into `coroPtr + 0xe0`).
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
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

set_option maxHeartbeats 3200000 in
/-- Kit-generic Stage P1 Part A (`img.base + kit.loadShimOff -> img.base + ikit.trustShimOff`). -/
theorem stageP1_load_ok_kit {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {Q : Prop}
    (peer : AddrGhost)
    (hA : AllocHooks A abs)
    (hkit : SessionOnlyKitOkS kit Scope C encRecord ctl abs)
    (hstack_lt : loadCallStack kit ≤ 2 ^ 64)
    (haddr_ss : kit.addrOk peer.val)
    (hload_ok : ∀ ans, kit.loadRel st peer.val ans → ans.isOk = true)
    (s0 s : State)
    (outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (b_390 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s)
    (hfs : FsAt kit.envOk Q (tripleRatchetProgAt img.base C ctl abs) s)
    (hpc : s.pc = img.base + kit.loadShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = sessStorePtr)
    (hx1 : s.readReg64 .x1 = remoteAddrPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64)
    (hx30 : s.readReg64 .x30 =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x130#64) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      (img.base + ikit.trustShimOff) s
      (decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       memRegion (s.sp + 0xd8#64) 348 ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
       ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
       ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
       ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
       kit.storeAt sessStorePtr st ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       A.pool ∗
       stackAt s.sp (loadCallStack kit))
      (fun s6 P_f =>
        (∃ opt : Option (SessionRecord (List (BitVec 8))),
          kit.loadRel st peer.val (.ok opt) ∧
          s6.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ∧
          (P_f ⊢
            decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
              preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
              kyberStorePtr kyberStoreVt rngPtr ∗
            p1LoadedRecordAt Scope A coroPtr opt ∗
            processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
              spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
            memRegion (s.sp + 0xd8#64) 348 ∗
            memRegion (s.sp + 0x3e0#64) 368 ∗
            ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
            ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
            ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
            ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
            kit.storeAt sessStorePtr st ∗
            protocolAddressAt A peer remoteAddrPtr ∗
            A.pool ∗
            stackAt s.sp (loadCallStack kit))) ∧
        s6.sp = s.sp ∧
        s6.readReg64 .x0 = idStorePtr ∧
        s6.readReg64 .x1 = remoteAddrPtr ∧
        s6.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s6.readReg64 .x3 = 1#64 ∧
        s6.readReg64 .x19 = coroPtr ∧
        s6.readReg64 .x21 = coroPtr + 0x390#64 ∧
        s6.readReg64 .x26 = outPtr ∧
        s6.readReg64 .x27 = ctxPtr ∧
        s6.readReg64 .x29 = s.readReg64 .x29 ∧
        s6.readReg64 .x30 =
          (tripleRatchetProgAt img.base C ctl abs).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64 ∧
        img.FrozenLoaded s6 ∧
        s6.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  have htr_pre : s0.trace <+: s.trace := htr ▸ List.prefix_refl _
  have hdrop_nz : img.base + kit.loadFutDropOff ≠ 0#64 := kit.loadFutDrop_ne_zero hb
  have hbs_nz : BitVec.ofNat 64 kit.loadBoxSize ≠ 0#64 := kit.loadBoxSize_ne_zero
  have hbs_lt : kit.loadBoxSize < 2 ^ 64 := kit.loadBoxSize_lt
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_loadShim kit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.call_oom_steps_frame
    (x := ({ self := sessStorePtr, addrA := remoteAddrPtr } : LoadShimCall))
    hinv htr_pre hkit.loadShim hpc hrun hsp_al hx30
    (loadShim_pre_intro hinv hx0 hx1)
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s1 hsteps01 hpc1 hrun1 hsp1 _ hcs1 hinv1 => ?_)
  dsimp only [Spec.inImage, kitLoadShimSpec]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_1, _, _, htr1⟩ => ?_
  have hfs1 : FsAt kit.envOk Q (tripleRatchetProgAt img.base C ctl abs) s1 :=
    hfs.of_steps hsteps01 (evs := []) (by simpa using htr1) (fun _ => NoFsEv.nil)
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_loadShim kit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  rcases hcs1 with ⟨hx19_cs1, _, _, _, _, hx24_cs1, hx25_cs1, hx26_cs1, hx27_cs1, hx28_cs1,
    hx29_cs1, _⟩
  have hx19_1 : s1.readReg64 .x19 = coroPtr := hx19_cs1.trans hx19
  have hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs1.trans hx24
  have hx25_1 : s1.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs1.trans hx25
  have hx26_1 : s1.readReg64 .x26 = outPtr := hx26_cs1.trans hx26
  have hx27_1 : s1.readReg64 .x27 = ctxPtr := hx27_cs1.trans hx27
  have hx28_1 : s1.readReg64 .x28 = s.sp + 0xa90#64 := hx28_cs1.trans hx28
  refine SepWPp.weaken_frame (Entails.of_eq (cells25_split2_eq coroPtr)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u2c8 => SepWPp.exists_elim fun u2d0 => ?_
  have hstep2 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg2_wp
    img.base C ctl abs s1 coroPtr ctxPtr
    (s1.readReg64 .x0) (img.base + kit.loadFutVtOff) (img.base + kit.loadPollOff) u2c8 u2d0
    hpc1 hrun1 rfl hx1_1 hx19_1 hx27_1
  simp only [BitVec.add_assoc] at hstep2
  refine SepWPp.bind_sepWP_steps_frame hinv1 hstep2 (by sep_focus)
    fun s2 hsteps12 hpc2 hrun2 hinv2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, hx0_2, _, hx8_2, hx19_2, hx21_2,
    hx24_2, hx25_2, hx26_2, hx27_2, _, hx29_2, hx30_2⟩
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_s] using hsp_align
  rw [hsp1] at hx8_2 hx21_2
  have htr2_pre : s0.trace <+: s2.trace := by
    rw [htr2_1, htr1, htr]
  have hfs2 : FsAt kit.envOk Q (tripleRatchetProgAt img.base C ctl abs) s2 :=
    hfs1.of_steps hsteps12 (evs := []) (by simpa using htr2_1) (fun _ => NoFsEv.nil)
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_loadPoll kit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.call_oom_steps_frame
    (x := (({ fut := s1.readReg64 .x0, out := s.sp + 0x3e0#64,
              addrA := remoteAddrPtr, addr := peer } : LoadPollCall),
           sessStorePtr, st))
    hinv2 htr2_pre hkit.loadPoll hpc2 hrun2 hsp2_al hx30_2
    (loadPoll_pre_intro hfs2.envOk_here hinv2 hsp2_s hx0_2 hx8_2 haddr_ss)
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s3 _ hpc3 hrun3 hsp3_2 _ hcs3 hinv3 => ?_)
  dsimp only [kitLoadPollSpecSE, withEnvPre, kitLoadPollSpecS]
  rw [hsp2_s]
  sep_norm
  refine SepWPp.exists_elim fun ans => ?_
  refine SepWPp.pure_elim fun ⟨hrel, htr3_2⟩ => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_loadPoll kit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2.trans hsp2_s
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  rcases hcs3 with ⟨hx19_cs3, _, hx21_cs3, _, _, hx24_cs3, hx25_cs3, hx26_cs3, hx27_cs3, _,
    hx29_cs3, _⟩
  have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
  have hx21_3 : s3.readReg64 .x21 = s3.sp + 0x3e0#64 := by rw [hx21_cs3, hx21_2, hsp3_s]
  have hx24_3 : s3.readReg64 .x24 = s3.sp + 0x370#64 := by rw [hx24_cs3, hx24_2, hx24_1, hsp3_s]
  have hx25_3 : s3.readReg64 .x25 = s3.sp + 0x210#64 := by rw [hx25_cs3, hx25_2, hx25_1, hsp3_s]
  have hx26_3 : s3.readReg64 .x26 = outPtr := by rw [hx26_cs3, hx26_2, hx26_1]
  have hx27_3 : s3.readReg64 .x27 = ctxPtr := by rw [hx27_cs3, hx27_2]
  have hx29_3 : s3.readReg64 .x29 = s.readReg64 .x29 := by rw [hx29_cs3, hx29_2, hx29_cs1]
  have hmr_d8 : memRegion (s.sp + 0xd8#64) 348 =
      memRegion (s.sp + 0xd8#64) 312 ∗ memRegion (s.sp + 0x210#64) 36 :=
    ProofLib.memRegion_split' (b := s.sp + 0xd8#64) (n := 312) (k := 36)
      (b' := s.sp + 0x210#64) rfl (by bv_omega) (by decide)
  rcases ans with ⟨⟨⟩⟩ | opt
  · exact absurd (hload_ok (.error ()) hrel) Bool.false_ne_true
  · cases opt with
    | none =>
      rw [show loadPollOutAtS Scope A img.base (s.sp + 0x3e0#64) (.ok none) =
        E2E.InMem.HashbrownBin.pollOptSessionRecordResultAt A (s.sp + 0x3e0#64) none from rfl]
      refine SepWPp.weaken_frame (Entails.of_eq (pollOptSessionRecordNone_split_eq A s.sp))
        (by sep_focus) ?_
      sep_norm
      refine SepWPp.exists_elim fun bs_418 => SepWPp.exists_elim fun d_414 =>
        SepWPp.exists_elim fun w_40c => SepWPp.exists_elim fun w_404 =>
        SepWPp.exists_elim fun w_3fc => SepWPp.exists_elim fun w_3f4 =>
        SepWPp.exists_elim fun d_3f0 => SepWPp.exists_elim fun w_3e8 => ?_
      refine SepWPp.weaken_frame (Entails.of_eq hmr_d8) (by sep_focus) ?_
      refine SepWPp.weaken_frame (Entails.of_eq (sp210_36_split_eq s.sp)) (by sep_focus) ?_
      sep_norm
      refine SepWPp.exists_elim fun u_230 => SepWPp.exists_elim fun u_228 =>
        SepWPp.exists_elim fun u_220 => SepWPp.exists_elim fun u_218 =>
        SepWPp.exists_elim fun u_210 => ?_
      refine SepWPp.weaken_frame (P₁ := ⌜bs_418.length = 312⌝) (P₂ := ⌜bs_418.length = 312⌝)
        (Entails.refl _) (by sep_focus) ?_
      refine SepWPp.pure_elim fun hbs312 => ?_
      have hstep4 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg3_wp
        img.base C ctl abs s3 coroPtr
        (s1.readReg64 .x0) (img.base + kit.loadFutVtOff) (img.base + kit.loadFutDropOff)
        w_3e8 w_3f4 w_3fc w_404 w_40c u_210 u_218 u_220 u_228
        d_3f0 d_414 u_230 bs_418
        hpc3 hrun3 hsp3_align hbs312 hdrop_nz hx19_3 hx21_3 hx24_3 hx25_3
      rw [hsp3_s, BitVec.add_zero] at hstep4
      refine SepWPp.bind_sepWP_steps_frame hinv3 hstep4 (by sep_focus)
        fun s4 _ hpc4 hrun4 hinv4 hregs4 => ?_
      rcases hregs4 with ⟨hsp4_s, htr4_3, _, hx19_4, hx21_4, _, hx23_4, hx24_4, _, hx26_4, hx27_4,
        _, hx29_4, hx30_4⟩
      have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_s] using hsp_align
      refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
        hinv4 hkit.loadFutDrop hpc4 hrun4 hsp4_al hx30_4
        (by simp [LibsignalPublicApi.StoreSession.futDropSpec]) True.intro (by sep_focus)
        (hoom_false := fun _ => rfl)
        (hnext := fun s5 _ hpc5 hrun5 hsp5_4 _ hcs5 hinv5 => ?_)
      dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
      refine SepWPp.pure_elim fun htr5_4 => ?_
      have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_s
      have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
      rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, hx23_cs5, hx24_cs5, _, hx26_cs5, hx27_cs5, _,
        hx29_cs5, _⟩
      have hx19_5 : s5.readReg64 .x19 = coroPtr := hx19_cs5.trans hx19_4
      have hx21_5 : s5.readReg64 .x21 = s1.readReg64 .x0 := hx21_cs5.trans hx21_4
      have hx23_5 : s5.readReg64 .x23 = 0xffffffffffffffff#64 := hx23_cs5.trans hx23_4
      have hx24_5 : s5.readReg64 .x24 = img.base + kit.loadFutVtOff := hx24_cs5.trans hx24_4
      have hx26_5 : s5.readReg64 .x26 = outPtr := by rw [hx26_cs5, hx26_4, hx26_3]
      have hx27_5 : s5.readReg64 .x27 = ctxPtr := by rw [hx27_cs5, hx27_4, hx27_3]
      have hx29_5 : s5.readReg64 .x29 = s.readReg64 .x29 := by rw [hx29_cs5, hx29_4, hx29_3]
      refine SepWPp.weaken_frame
        (kit.loadBoxAt_memRegion (s1.readReg64 .x0) sessStorePtr remoteAddrPtr 1#8)
        (by sep_focus) ?_
      refine SepWPp.weaken_frame
        (cells25_fold2 coroPtr (s1.readReg64 .x0) (img.base + kit.loadFutVtOff))
        (by sep_focus) ?_
      refine SepWPp.weaken_frame
        (Entails.of_eq (stack_loadCall_to_alloc kit s.sp hstack_lt))
        (by sep_focus) ?_
      sep_norm
      have hstep6 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg4_wp
        (A := A) img.base C ctl abs hA s5
        coroPtr (s1.readReg64 .x0) (img.base + kit.loadFutVtOff) (img.base + ikit.trustShimOff)
        msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr
        kit.loadBoxSize b_390
        hpc5 hrun5 hsp5_align hbs_nz hbs_lt hx19_5 hx21_5 hx23_5 hx24_5
      rw [hsp5_s] at hstep6
      simp only [BitVec.add_assoc] at hstep6
      refine SepWPp.bind_sepWP_steps_frame hinv5 hstep6 (by sep_focus)
        fun s6 _ hpc6 hrun6 hinv6 hregs6 => ?_
      refine SepWPp.weaken_frame
        (Entails.of_eq (stack_loadCall_to_alloc kit s.sp hstack_lt).symm)
        (by sep_focus) ?_
      refine SepWPp.done hpc6 hrun6 ?_
      rcases hregs6 with ⟨hsp6_s, htr6_5, hx0_6, hx1_6, hx2_6, hx3_6, hx19_6, hx21_6, _, hx26_6,
        hx27_6, _, hx29_6, hx30_6⟩
      have htr6_s : s6.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok none) := by
        rw [htr6_5, htr5_4, htr4_3, htr3_2, htr2_1, htr1]
      refine ⟨⟨none, hrel, htr6_s, ?_⟩, hsp6_s, hx0_6, hx1_6, hx2_6, hx3_6, hx19_6, hx21_6,
        hx26_6.trans hx26_5, hx27_6.trans hx27_5, hx29_6.trans hx29_5, hx30_6,
        hinv6.1, hinv6.2⟩
      dsimp only [p1LoadedRecordAt]
      sep_norm
      exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
    | some r =>
      refine SepWPp.weaken_frame
        (loadPollOut_some_unpack Scope A img.base s.sp r)
        (by sep_focus) ?_
      sep_norm
      refine SepWPp.exists_elim fun g =>
        SepWPp.exists_elim fun w4 =>
        SepWPp.exists_elim fun w5 =>
        SepWPp.exists_elim fun w6 =>
        SepWPp.exists_elim fun tail => ?_
      refine SepWPp.pure_elim fun ⟨hscope, hprev_lt, htail_inl, htail_len⟩ => ?_
      have hw_ne_neg3 : g.prevCap ≠ 0xfffffffffffffffd#64 := by bv_omega
      have hw_ne_neg2 : g.prevCap ≠ 0xfffffffffffffffe#64 := by bv_omega
      have hw_ne_neg1 : g.prevCap ≠ 0xffffffffffffffff#64 := by bv_omega
      refine SepWPp.weaken_frame (Entails.of_eq hmr_d8) (by sep_focus) ?_
      refine SepWPp.weaken_frame (Entails.of_eq (sp210_36_split_eq s.sp)) (by sep_focus) ?_
      sep_norm
      refine SepWPp.exists_elim fun u_230 => SepWPp.exists_elim fun u_228 =>
        SepWPp.exists_elim fun u_220 => SepWPp.exists_elim fun u_218 =>
        SepWPp.exists_elim fun u_210 => ?_
      have hstep4 := p1_load_some_seg3_wp
        img.base C ctl abs s3 coroPtr
        (s1.readReg64 .x0) (img.base + kit.loadFutVtOff) (img.base + kit.loadFutDropOff)
        g.prevCap g.prevPtr
        ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)
        (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)
        (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
        (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
        u_210 u_218 u_220 u_228
        ((0#64 : BitVec 64).extractLsb' 0 32) (w6.extractLsb' 32 32) u_230 tail
        hw_ne_neg3 hpc3 hrun3 hsp3_align htail_len hdrop_nz hx19_3 hx21_3 hx24_3 hx25_3
      rw [hsp3_s, BitVec.add_zero] at hstep4
      refine SepWPp.bind_sepWP_steps_frame hinv3 hstep4 (by sep_focus)
        fun s4 _ hpc4 hrun4 hinv4 hregs4 => ?_
      rcases hregs4 with ⟨hsp4_s, htr4_3, _, hx19_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4,
        hx26_4, hx27_4, hx28_4, hx29_4, hx30_4⟩
      have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_s] using hsp_align
      refine SepWPp.weaken_frame
        (sp3e0_368_fold s.sp g.prevCap g.prevPtr
          ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)
          (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)
          (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
          (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
          ((0#64 : BitVec 64).extractLsb' 0 32) (w6.extractLsb' 32 32) tail htail_len)
        (by sep_focus) ?_
      refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
        hinv4 hkit.loadFutDrop hpc4 hrun4 hsp4_al hx30_4
        (by simp [LibsignalPublicApi.StoreSession.futDropSpec]) True.intro (by sep_focus)
        (hoom_false := fun _ => rfl)
        (hnext := fun s5 _ hpc5 hrun5 hsp5_4 _ hcs5 hinv5 => ?_)
      dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
      refine SepWPp.pure_elim fun htr5_4 => ?_
      have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_s
      have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
      rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, hx22_cs5, hx23_cs5, hx24_cs5, hx25_cs5,
        hx26_cs5, hx27_cs5, hx28_cs5, hx29_cs5, _⟩
      have hx19_5 : s5.readReg64 .x19 = coroPtr := hx19_cs5.trans hx19_4
      have hx21_5 : s5.readReg64 .x21 = s1.readReg64 .x0 := hx21_cs5.trans hx21_4
      have hx22_5 : s5.readReg64 .x22 = ((0#64 : BitVec 64).extractLsb' 0 32).zeroExtend 64 :=
        hx22_cs5.trans hx22_4
      have hx23_5 : s5.readReg64 .x23 = g.prevCap := hx23_cs5.trans hx23_4
      have hx24_5 : s5.readReg64 .x24 = img.base + kit.loadFutVtOff := hx24_cs5.trans hx24_4
      have hx25_5 : s5.readReg64 .x25 = s5.sp + 0x210#64 := by rw [hx25_cs5, hx25_4, hsp5_s]
      have hx26_5 : s5.readReg64 .x26 = outPtr := by rw [hx26_cs5, hx26_4, hx26_3]
      have hx27_5 : s5.readReg64 .x27 = ctxPtr := by rw [hx27_cs5, hx27_4, hx27_3]
      have hx28_5 : s5.readReg64 .x28 = g.prevPtr := hx28_cs5.trans hx28_4
      have hx29_5 : s5.readReg64 .x29 = s.readReg64 .x29 := by rw [hx29_cs5, hx29_4, hx29_3]
      refine SepWPp.weaken_frame
        (kit.loadBoxAt_memRegion (s1.readReg64 .x0) sessStorePtr remoteAddrPtr 1#8)
        (by sep_focus) ?_
      refine SepWPp.weaken_frame
        (cells25_fold2 coroPtr (s1.readReg64 .x0) (img.base + kit.loadFutVtOff))
        (by sep_focus) ?_
      refine SepWPp.weaken_frame (coro_body336_split coroPtr) (by sep_focus) ?_
      sep_norm
      refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
        SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
        SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
        SepWPp.exists_elim fun c6 => ?_
      refine SepWPp.weaken_frame
        (Entails.of_eq (stack_loadCall_to_alloc kit s.sp hstack_lt))
        (by sep_focus) ?_
      sep_norm
      have hstep6 := p1_load_some_seg4_wp
        (A := A) img.base C ctl abs hA s5
        coroPtr (s1.readReg64 .x0) (img.base + kit.loadFutVtOff) (img.base + ikit.trustShimOff)
        msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr
        g.prevCap g.prevPtr
        ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)
        (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)
        (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
        (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
        c0 c1
        (c3.extractLsb' 0 32 ++ c2.extractLsb' 32 32)
        (c4.extractLsb' 0 32 ++ c3.extractLsb' 32 32)
        (c5.extractLsb' 0 32 ++ c4.extractLsb' 32 32)
        (c6.extractLsb' 0 32 ++ c5.extractLsb' 32 32)
        ((0#64 : BitVec 64).extractLsb' 0 32) (w6.extractLsb' 32 32)
        (c2.extractLsb' 0 32) (c6.extractLsb' 32 32)
        tail kit.loadBoxSize b_390
        hw_ne_neg2 hw_ne_neg1 htail_len
        hpc5 hrun5 hsp5_align hbs_nz hbs_lt
        hx19_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx28_5
      rw [hsp5_s] at hstep6
      simp only [BitVec.add_assoc] at hstep6
      refine SepWPp.bind_sepWP_steps_frame hinv5 hstep6 (by sep_focus)
        fun s6 _ hpc6 hrun6 hinv6 hregs6 => ?_
      refine SepWPp.weaken_frame
        (Entails.of_eq (stack_loadCall_to_alloc kit s.sp hstack_lt).symm)
        (by sep_focus) ?_
      refine SepWPp.weaken_frame
        (sp_d8_bytes_rejoin s.sp
          ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)
          (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)
          (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
          (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
          (w6.extractLsb' 32 32) tail htail_len)
        (by sep_focus) ?_
      refine SepWPp.weaken_frame
        (coro_e0_some_pack Scope A coroPtr g r w4 w5 w6 tail hscope htail_inl)
        (by sep_focus) ?_
      refine SepWPp.done hpc6 hrun6 ?_
      rcases hregs6 with ⟨hsp6_s, htr6_5, hx0_6, hx1_6, hx2_6, hx3_6, hx19_6, hx21_6, _, hx26_6,
        hx27_6, _, hx29_6, hx30_6⟩
      have htr6_s : s6.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok (some r)) := by
        rw [htr6_5, htr5_4, htr4_3, htr3_2, htr2_1, htr1]
      refine ⟨⟨some r, hrel, htr6_s, ?_⟩, hsp6_s, hx0_6, hx1_6, hx2_6, hx3_6, hx19_6, hx21_6,
        hx26_6.trans hx26_5, hx27_6.trans hx27_5, hx29_6.trans hx29_5, hx30_6,
        hinv6.1, hinv6.2⟩
      exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
