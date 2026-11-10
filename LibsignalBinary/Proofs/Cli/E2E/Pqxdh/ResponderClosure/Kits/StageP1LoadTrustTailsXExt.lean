/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitE
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExt

/-!
# Stage P1 Load and Trust Tail Lemmas on `tripleRatchetProgAtExt`

Post-poll deallocation tail lemmas for Stage P1 Part A (`load_session`) and Part B
(`is_trusted_identity`) on `tripleRatchetProgAtExt` under `AllocContractsX` and `AllocHooks`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

set_option maxHeartbeats 1200000 in
theorem stageP1_load_none_tail_x_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState}
    (peer : AddrGhost)
    (hAh : AllocHooks A ext)
    (hAc : AllocContractsX img A ext)
    (hkit : SessionOnlyKitOkSE kit Scope encRecord ext)
    (hext_stack : extHookStack ≤ loadCallStack kit)
    (hstack_lt : loadCallStack kit ≤ 2 ^ 64)
    (s0 s s3 : State)
    (loadFutPtr outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (b_390 : BitVec 8)
    (hdrop_nz : img.base + kit.loadFutDropOff ≠ 0#64)
    (hbs_nz : BitVec.ofNat 64 kit.loadBoxSize ≠ 0#64)
    (hbs_lt : kit.loadBoxSize < 2 ^ 64)
    (hrel : kit.loadRel st peer.val (.ok none))
    (htr3_s : s3.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok none))
    (hinv3 : ImgCallInv img s3)
    (hpc3 : s3.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x14c#64)
    (hrun3 : s3.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp3_s : s3.sp = s.sp)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx21_3 : s3.readReg64 .x21 = s3.sp + 0x3e0#64)
    (hx24_3 : s3.readReg64 .x24 = s3.sp + 0x370#64)
    (hx25_3 : s3.readReg64 .x25 = s3.sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx27_3 : s3.readReg64 .x27 = ctxPtr)
    (hx29_3 : s3.readReg64 .x29 = s.readReg64 .x29)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (img.base + ikit.trustShimOff) s3
      (((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ (img.base + kit.loadFutVtOff)) ∗
       cells (coroPtr + 0x2d8#64) 23 ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       memRegion (s.sp + 0xd8#64) 348 ∗
       loadPollOutAtS Scope A img.base (s.sp + 0x3e0#64) (.ok none) ∗
       A.live loadFutPtr kit.loadBoxSize 8 ∗
       kit.loadBoxAt loadFutPtr sessStorePtr remoteAddrPtr 1#8 ∗
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
          (tripleRatchetProgAtExt img.base ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64 ∧
        calleeSavedVRegs s6 = calleeSavedVRegs s ∧
        img.FrozenLoaded s6 ∧
        s6.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  have hmr_d8 : memRegion (s.sp + 0xd8#64) 348 =
      memRegion (s.sp + 0xd8#64) 312 ∗ memRegion (s.sp + 0x210#64) 36 :=
    ProofLib.memRegion_split' (b := s.sp + 0xd8#64) (n := 312) (k := 36)
      (b' := s.sp + 0x210#64) rfl (by bv_omega) (by decide)
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
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_ext kit s.sp hext_stack hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have hstep4 := p1_seg3_vregs_wp_ext (img := img) (A := A)
    ext hAc s3 hinv3 coroPtr
    loadFutPtr (img.base + kit.loadFutVtOff) (img.base + kit.loadFutDropOff)
    w_3e8 w_3f4 w_3fc w_404 w_40c u_210 u_218 u_220 u_228
    d_3f0 d_414 u_230 bs_418
    hpc3 hrun3 hsp3_align hbs312 hdrop_nz hx19_3 hx21_3 hx24_3 hx25_3
  rw [hsp3_s, BitVec.add_zero] at hstep4
  refine SepWPp.bind_sepWP_steps_frame hinv3 hstep4 (by sep_focus)
    fun s4 _ hpc4 hrun4 hinv4 hregs4 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_ext kit s.sp hext_stack hstack_lt).symm)
    (by sep_focus) ?_
  rcases hregs4 with ⟨hsp4_s, htr4_3, _, hx19_4, hx21_4, _, hx23_4, hx24_4, _, hx26_4, hx27_4,
    _, hx29_4, hx30_4, hvregs4_3⟩
  have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_s] using hsp_align
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    hinv4 hkit.loadFutDrop hpc4 hrun4 hsp4_al hx30_4
    (by dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s5 _ hpc5 hrun5 hsp5_4 _ hcs5 hinv5 => ?_)
  dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr5_4 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_s
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, hx23_cs5, hx24_cs5, _, hx26_cs5, hx27_cs5, _,
    hx29_cs5, hvregs_cs5⟩
  have hx19_5 : s5.readReg64 .x19 = coroPtr := hx19_cs5.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = loadFutPtr := hx21_cs5.trans hx21_4
  have hx23_5 : s5.readReg64 .x23 = 0xffffffffffffffff#64 := hx23_cs5.trans hx23_4
  have hx24_5 : s5.readReg64 .x24 = img.base + kit.loadFutVtOff := hx24_cs5.trans hx24_4
  have hx26_5 : s5.readReg64 .x26 = outPtr := by rw [hx26_cs5, hx26_4, hx26_3]
  have hx27_5 : s5.readReg64 .x27 = ctxPtr := by rw [hx27_cs5, hx27_4, hx27_3]
  have hx29_5 : s5.readReg64 .x29 = s.readReg64 .x29 := by rw [hx29_cs5, hx29_4, hx29_3]
  refine SepWPp.weaken_frame
    (kit.loadBoxAt_memRegion loadFutPtr sessStorePtr remoteAddrPtr 1#8)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (cells25_fold2 coroPtr loadFutPtr (img.base + kit.loadFutVtOff))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_alloc kit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have hstep6 := p1_seg4_vregs_wp_ext
    (A := A) img.base ext hAh s5
    coroPtr loadFutPtr (img.base + kit.loadFutVtOff) (img.base + ikit.trustShimOff)
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
    hx27_6, _, hx29_6, hx30_6, hvregs6_5⟩
  have htr6_s : s6.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok none) := by
    rw [htr6_5, htr5_4, htr4_3, htr3_s]
  have hvregs6_s : calleeSavedVRegs s6 = calleeSavedVRegs s := by
    rw [hvregs6_5, hvregs_cs5, hvregs4_3, hvregs3]
  refine ⟨⟨none, hrel, htr6_s, ?_⟩, hsp6_s, hx0_6, hx1_6, hx2_6, hx3_6, hx19_6, hx21_6,
    hx26_6.trans hx26_5, hx27_6.trans hx27_5, hx29_6.trans hx29_5, hx30_6, hvregs6_s,
    hinv6.1, hinv6.2⟩
  dsimp only [p1LoadedRecordAt]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP1_load_some_tail_x_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState}
    (peer : AddrGhost) (r : SessionRecord (List (BitVec 8)))
    (hAh : AllocHooks A ext)
    (hAc : AllocContractsX img A ext)
    (hkit : SessionOnlyKitOkSE kit Scope encRecord ext)
    (hext_stack : extHookStack ≤ loadCallStack kit)
    (hstack_lt : loadCallStack kit ≤ 2 ^ 64)
    (s0 s s3 : State)
    (loadFutPtr outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (b_390 : BitVec 8)
    (hdrop_nz : img.base + kit.loadFutDropOff ≠ 0#64)
    (hbs_nz : BitVec.ofNat 64 kit.loadBoxSize ≠ 0#64)
    (hbs_lt : kit.loadBoxSize < 2 ^ 64)
    (hrel : kit.loadRel st peer.val (.ok (some r)))
    (htr3_s : s3.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok (some r)))
    (hinv3 : ImgCallInv img s3)
    (hpc3 : s3.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x14c#64)
    (hrun3 : s3.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp3_s : s3.sp = s.sp)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx21_3 : s3.readReg64 .x21 = s3.sp + 0x3e0#64)
    (hx24_3 : s3.readReg64 .x24 = s3.sp + 0x370#64)
    (hx25_3 : s3.readReg64 .x25 = s3.sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx27_3 : s3.readReg64 .x27 = ctxPtr)
    (hx29_3 : s3.readReg64 .x29 = s.readReg64 .x29)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (img.base + ikit.trustShimOff) s3
      (((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ (img.base + kit.loadFutVtOff)) ∗
       cells (coroPtr + 0x2d8#64) 23 ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       memRegion (s.sp + 0xd8#64) 348 ∗
       loadPollOutAtS Scope A img.base (s.sp + 0x3e0#64) (.ok (some r)) ∗
       A.live loadFutPtr kit.loadBoxSize 8 ∗
       kit.loadBoxAt loadFutPtr sessStorePtr remoteAddrPtr 1#8 ∗
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
          (tripleRatchetProgAtExt img.base ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64 ∧
        calleeSavedVRegs s6 = calleeSavedVRegs s ∧
        img.FrozenLoaded s6 ∧
        s6.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  have hmr_d8 : memRegion (s.sp + 0xd8#64) 348 =
      memRegion (s.sp + 0xd8#64) 312 ∗ memRegion (s.sp + 0x210#64) 36 :=
    ProofLib.memRegion_split' (b := s.sp + 0xd8#64) (n := 312) (k := 36)
      (b' := s.sp + 0x210#64) rfl (by bv_omega) (by decide)
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
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_ext kit s.sp hext_stack hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have hstep4 := p1_load_some_seg3_vregs_wp_ext (img := img) (A := A)
    ext hAc s3 hinv3 coroPtr
    loadFutPtr (img.base + kit.loadFutVtOff) (img.base + kit.loadFutDropOff)
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
    hx26_4, hx27_4, hx28_4, hx29_4, hx30_4, hvregs4_3⟩
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
    (by dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s5 _ hpc5 hrun5 hsp5_4 _ hcs5 hinv5 => ?_)
  dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr5_4 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_s
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, hx22_cs5, hx23_cs5, hx24_cs5, hx25_cs5,
    hx26_cs5, hx27_cs5, hx28_cs5, hx29_cs5, hvregs_cs5⟩
  have hx19_5 : s5.readReg64 .x19 = coroPtr := hx19_cs5.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = loadFutPtr := hx21_cs5.trans hx21_4
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
    (kit.loadBoxAt_memRegion loadFutPtr sessStorePtr remoteAddrPtr 1#8)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (cells25_fold2 coroPtr loadFutPtr (img.base + kit.loadFutVtOff))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (coro_body336_split coroPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => ?_
  have hstep6 := p1_load_some_seg4_vregs_wp_ext
    (img := img) (A := A) ext hAh hAc s5 hinv5
    coroPtr loadFutPtr (img.base + kit.loadFutVtOff) (img.base + ikit.trustShimOff)
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
    (Entails.of_eq (stack_loadCall_to_ext kit s.sp hext_stack hstack_lt).symm)
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
    hx27_6, _, hx29_6, hx30_6, hvregs6_5⟩
  have htr6_s : s6.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok (some r)) := by
    rw [htr6_5, htr5_4, htr4_3, htr3_s]
  have hvregs6_s : calleeSavedVRegs s6 = calleeSavedVRegs s := by
    rw [hvregs6_5, hvregs_cs5, hvregs4_3, hvregs3]
  refine ⟨⟨some r, hrel, htr6_s, ?_⟩, hsp6_s, hx0_6, hx1_6, hx2_6, hx3_6, hx19_6, hx21_6,
    hx26_6.trans hx26_5, hx27_6.trans hx27_5, hx29_6.trans hx29_5, hx30_6, hvregs6_s,
    hinv6.1, hinv6.2⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP1_trust_call_tail_x_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {ikit : IdentityStoreSpec A img.base}
    {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey) (ans : Except Unit Bool)
    (hAh : AllocHooks A ext)
    (hikit : IdentityStoreKitOkIE img ikit ext)
    (hstack_lt : trustCallStack ikit ≤ 2 ^ 64)
    (s0 s s9 : State)
    (trustFutPtr outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr
     u_a8 u_b0 u_b8 u_c8 u_d0 : BitVec 64)
    (hdrop_nz : img.base + ikit.trustFutDropOff ≠ 0#64)
    (hbs_nz : BitVec.ofNat 64 ikit.trustBoxSize ≠ 0#64)
    (hbs_lt : ikit.trustBoxSize < 2 ^ 64)
    (hrel : ikit.trustRel ist peer.val remoteIdKey .receiving ans)
    (htr9_s : s9.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans)
    (hinv9 : ImgCallInv img s9)
    (hpc9 : s9.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x66c#64)
    (hrun9 : s9.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp9_s : s9.sp = s.sp)
    (hx19_9 : s9.readReg64 .x19 = coroPtr)
    (hx21_9 : s9.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26_9 : s9.readReg64 .x26 = outPtr)
    (hx29_9 : s9.readReg64 .x29 = s.readReg64 .x29)
    (hvregs9 : calleeSavedVRegs s9 = calleeSavedVRegs s) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64) s9
      (((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ (img.base + ikit.trustFutVtOff)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       trustPollOutAt img.base (s.sp + 0x3e0#64) ans ∗
       memRegion (s.sp + 0x410#64) 320 ∗
       ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
       ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
       logOff img ∗
       A.live trustFutPtr ikit.trustBoxSize 8 ∗
       ikit.trustBoxAt trustFutPtr idStorePtr remoteAddrPtr
         (msgPtr + 0xc8#64) 1#8 (directionByte .receiving) ∗
       ikit.identityAt idStorePtr
         (ikit.trustUpdate ist peer.val remoteIdKey .receiving ans) ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt s.sp (trustCallStack ikit))
      (fun sm P_m =>
        (∃ ans' : Except Unit Bool,
          ikit.trustRel ist peer.val remoteIdKey .receiving ans' ∧
          sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans' ∧
          sm.readReg64 .x20 = trustPollTag ans' ∧
          (ans' = .ok true → sm.readReg64 .x23 = 1#64) ∧
          (ans' = .ok false → sm.readReg64 .x23 = 0#64) ∧
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
              (if ans'.isOk then emp
               else ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ∗
              logOff img ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving ans') ∗
              protocolAddressAt A peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool ∗
              stackAt s.sp (trustCallStack ikit))) ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = coroPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        ImgCallInv img sm)
      (PanicOomProp s0) := by
  have hsp9_align : (s9.sp &&& 15#64 == 0#64) = true := by rw [hsp9_s]; exact hsp_align
  have hmr_3e0 : memRegion (s.sp + 0x3e0#64) 368 =
      memRegion (s.sp + 0x3e0#64) 48 ∗ memRegion (s.sp + 0x410#64) 320 :=
    ProofLib.memRegion_split' (b := s.sp + 0x3e0#64) (n := 48) (k := 320)
      (b' := s.sp + 0x410#64) rfl (by bv_omega) (by decide)
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
  have hstep10 := p1_seg6a_any_vregs_wp_ext
    img.base ext s9 coroPtr outPtr
    trustFutPtr (img.base + ikit.trustFutVtOff) (img.base + ikit.trustFutDropOff)
    (trustPollTag ans) w_3f0 w_400 w_408 u_a8 u_b0 u_b8 u_c8 u_d0
    d_3e9 d_3f8 d_3fc h_3ed b_3e8 b_3ef
    hw_ne_neg3 hpc9 hrun9 hsp9_align hdrop_nz hx19_9 hx21_9 hx26_9
  rw [hsp9_s, BitVec.add_zero] at hstep10
  refine SepWPp.bind_sepWP_steps_frame hinv9 hstep10 (by sep_focus)
    fun s10 _ hpc10 hrun10 hinv10 hregs10 => ?_
  rcases hregs10 with ⟨hsp10_s, htr10_9, _, hx19_10, hx20_10, hx21_10, hx23_10, hx25_10,
    _, hx29_10, hx30_10, hvregs10_9⟩
  have hsp10_al : s10.spAligned = true := by simpa only [State.spAligned, hsp10_s] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hmr_3e0.symm) (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    hinv10 hikit.trustFutDrop hpc10 hrun10 hsp10_al hx30_10
    (by dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s11 _ hpc11 hrun11 hsp11_10 _ hcs11 hinv11 => ?_)
  dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr11_10 => ?_
  have hsp11_s : s11.sp = s.sp := hsp11_10.trans hsp10_s
  have hsp11_align : (s11.sp &&& 15#64 == 0#64) = true := by rw [hsp11_s]; exact hsp_align
  rcases hcs11 with ⟨hx19_cs11, hx20_cs11, hx21_cs11, _, hx23_cs11, _, hx25_cs11, _, _, _,
    hx29_cs11, hvregs_cs11⟩
  have hx19_11 : s11.readReg64 .x19 = coroPtr := hx19_cs11.trans hx19_10
  have hx20_11 : s11.readReg64 .x20 = trustPollTag ans := hx20_cs11.trans hx20_10
  have hx21_11 : s11.readReg64 .x21 = trustFutPtr := hx21_cs11.trans hx21_10
  have hx23_11 : s11.readReg64 .x23 = b_3e8.zeroExtend 64 := hx23_cs11.trans hx23_10
  have hx25_11 : s11.readReg64 .x25 = img.base + ikit.trustFutVtOff := hx25_cs11.trans hx25_10
  have hx29_11 : s11.readReg64 .x29 = s.readReg64 .x29 :=
    by rw [hx29_cs11, hx29_10, hx29_9]
  refine SepWPp.weaken_frame
    (ikit.trustBoxAt_memRegion trustFutPtr idStorePtr remoteAddrPtr
      (msgPtr + 0xc8#64) 1#8 (directionByte .receiving))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (cells2_fold_398 coroPtr trustFutPtr (img.base + ikit.trustFutVtOff))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_alloc ikit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have hstep12 := p1_seg6_dealloc_vregs_wp_ext
    (A := A) img.base ext hAh s11
    coroPtr trustFutPtr (img.base + ikit.trustFutVtOff)
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
  rcases hregsm with ⟨hspm_s, htrm_11, hx19_m, hx20_m, hx23_m, _, hx29_m, hvregsm_11⟩
  have htrm_s : sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans := by
    rw [htrm_11, htr11_10, htr10_9, htr9_s]
  have hvregsm_s : calleeSavedVRegs sm = calleeSavedVRegs s := by
    rw [hvregsm_11, hvregs_cs11, hvregs10_9, hvregs9]
  have htrue_m : ans = .ok true → sm.readReg64 .x23 = 1#64 := fun ha => by
    rw [hx23_m, hb_true ha]; rfl
  have hfalse_m : ans = .ok false → sm.readReg64 .x23 = 0#64 := fun ha => by
    rw [hx23_m, hb_false ha]; rfl
  refine ⟨⟨ans, hrel, htrm_s, hx20_m, htrue_m, hfalse_m, ?_⟩,
    hspm_s, hx19_m, hx29_m.trans hx29_11, hvregsm_s, hinvm⟩
  refine Entails.sepExists_right (d_3fc.zeroExtend 64)
    (Entails.sepExists_right w_3f0
      (Entails.sepExists_right (d_3f8.zeroExtend 64) ?_))
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
