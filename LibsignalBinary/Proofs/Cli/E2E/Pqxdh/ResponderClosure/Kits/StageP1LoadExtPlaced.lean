/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExt
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrap
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlaced

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlaced

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

set_option maxHeartbeats 400000 in
theorem p1_seg2_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr loadFutPtr loadFutVt loadPollAddr u0 u1 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x130#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = loadFutPtr)
    (hx1 : s.readReg64 .x1 = loadFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (stageP1ProgPlaced ext) loadPollAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ u0) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ u1) ∗
       ((loadFutVt + 0x18#64) ↦₆₄ᵣ loadPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
          ((loadFutVt + 0x18#64) ↦₆₄ᵣ loadPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = loadFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x14c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = loadFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = loadFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩


set_option maxHeartbeats 1200000 in
theorem stageP1_load_ok_kit_x_ext_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64}
    {ikit : IdentityStoreSpec A 0#64}
    {st : kit.StoreState} {Q : Prop}
    (peer : AddrGhost)
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpySpecX))
    (hkit_shim : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadShimOff)
      (StoreKit.withLsRoCl lsmpl (kitLoadShimSpec kit)))
    (hkit_poll : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadPollOff)
      (StoreKit.withLsRoCl lsmpl (StoreKit.kitLoadPollPlacedSpecSE kit Scope encRecord)))
    (hkit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropSpec))
    (hext_stack : extHookStack ≤ loadCallStack kit)
    (hstack_lt : loadCallStack kit ≤ 2 ^ 64)
    (haddr_ss : kit.addrOk peer.val)
    (hload_ok : ∀ ans, kit.loadRel st peer.val ans → ans.isOk = true)
    (s0 s : State)
    (outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (b_390 : BitVec 8)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsAt kit.envOk Q (stageP1ProgPlaced ext) s)
    (hpc : s.pc = 0#64 + kit.loadShimOff)
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
    (hx30 : s.readReg64 .x30 = stageP1EntryPlaced + 0x130#64) :
    SepWPp (stageP1ProgPlaced ext)
      (0#64 + ikit.trustShimOff) s
      (cells (coroPtr + 0x2c8#64) 25 ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       memRegion (s.sp + 0xd8#64) 348 ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
       ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
       ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
       ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
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
            ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
            ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
            ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
            ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
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
        s6.readReg64 .x30 = stageP1EntryPlaced + 0x650#64 ∧
        calleeSavedVRegs s6 = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem)
      (PanicOomProp s0) := by
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  have htr_pre : s0.trace <+: s.trace := htr ▸ List.prefix_refl _
  have hdrop_nz : 0#64 + kit.loadFutDropOff ≠ 0#64 := kit.loadFutDrop_ne_zero rfl
  have hbs_nz : BitVec.ofNat 64 kit.loadBoxSize ≠ 0#64 := kit.loadBoxSize_ne_zero
  have hbs_lt : kit.loadBoxSize < 2 ^ 64 := kit.loadBoxSize_lt
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_loadShim kit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  refine call_oom_rocl_steps_frame_placed
    (x := ({ self := sessStorePtr, addrA := remoteAddrPtr } : LoadShimCall))
    hcrl htr_pre hkit_shim hpc hrun hsp_al hx30
    (loadShim_pre_intro_placed hx0 hx1)
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s1 hsteps01 hpc1 hrun1 hsp1 _ hcs1 hcrl1 => ?_)
  dsimp only [kitLoadShimSpec]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_1, _, _, htr1⟩ => ?_
  have hfs1 : FsAt kit.envOk Q (stageP1ProgPlaced ext) s1 :=
    hfs.of_steps hsteps01 (evs := []) (by simpa using htr1) (fun _ => NoFsEv.nil)
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_loadShim kit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  rcases hcs1 with ⟨hx19_cs1, _, _, _, _, hx24_cs1, hx25_cs1, hx26_cs1, hx27_cs1, hx28_cs1,
    hx29_cs1, hvregs_cs1⟩
  have hx19_1 : s1.readReg64 .x19 = coroPtr := hx19_cs1.trans hx19
  have hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs1.trans hx24
  have hx25_1 : s1.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs1.trans hx25
  have hx26_1 : s1.readReg64 .x26 = outPtr := hx26_cs1.trans hx26
  have hx27_1 : s1.readReg64 .x27 = ctxPtr := hx27_cs1.trans hx27
  have hx28_1 : s1.readReg64 .x28 = s.sp + 0xa90#64 := hx28_cs1.trans hx28
  refine SepWPp.weaken_frame (Entails.of_eq (cells25_split2_eq coroPtr)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u2c8 => SepWPp.exists_elim fun u2d0 => ?_
  have hstep2 := p1_seg2_vregs_wp_ext_placed ext s1 coroPtr ctxPtr
    (s1.readReg64 .x0) (0#64 + kit.loadFutVtOff) (0#64 + kit.loadPollOff) u2c8 u2d0
    hpc1 hrun1 rfl hx1_1 hx19_1 hx27_1
  simp only [BitVec.add_assoc] at hstep2
  refine bind_sepWP_steps_frame_placed hcrl1 hstep2 (by sep_focus)
    fun s2 hsteps12 hpc2 hrun2 hcrl2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, hx0_2, _, hx8_2, hx19_2, hx21_2,
    hx24_2, hx25_2, hx26_2, hx27_2, _, hx29_2, hx30_2, hvregs2_1⟩
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_s] using hsp_align
  rw [hsp1] at hx8_2 hx21_2
  have htr2_pre : s0.trace <+: s2.trace := by
    rw [htr2_1, htr1, htr]
  have hfs2 : FsAt kit.envOk Q (stageP1ProgPlaced ext) s2 :=
    hfs1.of_steps hsteps12 (evs := []) (by simpa using htr2_1) (fun _ => NoFsEv.nil)
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_loadPoll kit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  refine call_oom_rocl_steps_frame_placed
    (x := (({ fut := s1.readReg64 .x0, out := s.sp + 0x3e0#64,
              addrA := remoteAddrPtr, addr := peer } : LoadPollCall),
           sessStorePtr, st))
    hcrl2 htr2_pre hkit_poll hpc2 hrun2 hsp2_al hx30_2
    (loadPoll_pre_intro_placed hfs2.envOk_here hsp2_s hx0_2 hx8_2 haddr_ss)
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s3 _ hpc3 hrun3 hsp3_2 _ hcs3 hcrl3 => ?_)
  dsimp only [StoreKit.kitLoadPollPlacedSpecSE, withEnvPre, StoreKit.kitLoadPollPlacedSpecS]
  rw [hsp2_s]
  sep_norm
  refine SepWPp.exists_elim fun ans => ?_
  refine SepWPp.pure_elim fun ⟨hrel, htr3_2⟩ => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_loadPoll kit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2.trans hsp2_s
  rcases hcs3 with ⟨hx19_cs3, _, hx21_cs3, _, _, hx24_cs3, hx25_cs3, hx26_cs3, hx27_cs3, _,
    hx29_cs3, hvregs_cs3⟩
  have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
  have hx21_3 : s3.readReg64 .x21 = s3.sp + 0x3e0#64 := by rw [hx21_cs3, hx21_2, hsp3_s]
  have hx24_3 : s3.readReg64 .x24 = s3.sp + 0x370#64 := by rw [hx24_cs3, hx24_2, hx24_1, hsp3_s]
  have hx25_3 : s3.readReg64 .x25 = s3.sp + 0x210#64 := by rw [hx25_cs3, hx25_2, hx25_1, hsp3_s]
  have hx26_3 : s3.readReg64 .x26 = outPtr := by rw [hx26_cs3, hx26_2, hx26_1]
  have hx27_3 : s3.readReg64 .x27 = ctxPtr := by rw [hx27_cs3, hx27_2]
  have hx29_3 : s3.readReg64 .x29 = s.readReg64 .x29 := by rw [hx29_cs3, hx29_2, hx29_cs1]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s := by
    rw [hvregs_cs3, hvregs2_1, hvregs_cs1]
  have htr3_s : s3.trace = s.trace ++ kit.loadEvs encRecord peer.val ans := by
    rw [htr3_2, htr2_1, htr1]
  rcases ans with ⟨⟨⟩⟩ | opt
  · exact absurd (hload_ok (.error ()) hrel) Bool.false_ne_true
  · cases opt with
    | none =>
      have htail := stageP1_load_none_tail_x_ext_placed (Scope := Scope) (ikit := ikit)
        peer hdealloc hmemcpy hkit_drop hext_stack hstack_lt s0 s s3
        (s1.readReg64 .x0) outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr idStorePtr preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr b_390
        hdrop_nz hbs_nz hbs_lt hrel htr3_s hcrl3 hpc3 hrun3 hsp_align hsp3_s
        hx19_3 hx21_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 hvregs3
      simp only [BitVec.add_assoc] at htail
      exact sepWPp_perm_pre htail (by sep_focus)
    | some r =>
      have htail := stageP1_load_some_tail_x_ext_placed (Scope := Scope) (ikit := ikit)
        peer r hdealloc hmemcpy hkit_drop hext_stack hstack_lt s0 s s3
        (s1.readReg64 .x0) outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr idStorePtr preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr b_390
        hdrop_nz hbs_nz hbs_lt hrel htr3_s hcrl3 hpc3 hrun3 hsp_align hsp3_s
        hx19_3 hx21_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 hvregs3
      simp only [BitVec.add_assoc] at htail
      exact sepWPp_perm_pre htail (by sep_focus)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlaced
