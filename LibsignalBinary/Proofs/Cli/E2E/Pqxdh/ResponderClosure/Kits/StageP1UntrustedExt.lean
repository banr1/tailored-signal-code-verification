/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitE
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Untrusted
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAuxTrap
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedTrap
import LibsignalBinary.Proofs.Common.StringCloneFlat
import LibsignalBinary.Proofs.Common.StringCloneFlatX
import LibsignalBinary.Proofs.FnOffEq

/-!
# Stage P1 Untrusted-Identity Error Exit on `tripleRatchetProgAtExt`

Lifts `stageP1_untrusted_err_ok_kit_trap` (`entry + 0x6e4#64 → s0.readReg64 .x30`) to
`tripleRatchetProgAtExt img.base ext`, preserving `calleeSavedVRegs`.
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
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

theorem stringClone_withPanics_ext (A : RustAlloc) (ext : String → Option (State → State))
    (hSC : HookSat ext stringCloneHookName (stringCloneSpec A)) :
    HookSat (Rust.withPanics ext) stringCloneHookName (stringCloneSpec A) := by
  have hnp : Rust.isPanicSymbol stringCloneHookName = false := by
    simp [stringCloneHookName, Rust.isPanicSymbol]
  unfold HookSat Rust.withPanics
  rw [hnp]
  exact hSC

set_option maxHeartbeats 1200000 in
theorem stageP1_untrusted_err_ok_kit_ext {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {abs ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (hAh : AllocHooks A abs)
    (hT : TrapsOnly (trTrapProgAt img.base C abs) (tripleRatchetProgAtExt img.base ext))
    (hstack_lt : untrustedErrCallStack ≤ 2 ^ 64)
    (s0 s : State)
    (outPtr coroPtr msgPtr remoteAddrPtr sessStorePtr idStorePtr : BitVec 64)
    (b_2c0 b_390 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s)
    (hpc : s.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 0#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
       p1LoadedRecordAt Scope A coroPtr opt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       cells (s.sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗
       logOff img ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr
         (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt s.sp untrustedErrCallStack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          ((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          memRegion (s.sp + 0x3e0#64) 368 ∗
          cells (s.sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
          logOff img ∗
          kit.storeAt sessStorePtr st ∗
          ikit.identityAt idStorePtr
            (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
          protocolAddressAt A peer remoteAddrPtr ∗
          ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
          A.pool ∗
          stackAt s.sp untrustedErrCallStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hfn_cl := fnAddr_trTrap_eq_ext img.base C abs ext
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
  have hfn_sc := fnAddr_trTrap_eq_ext img.base C abs ext stringCloneHookName
  have hstep1 := SepWP.of_trapsOnly hT (p1_untrusted_to_clone_vregs_wp_trap img.base C abs s
    coroPtr remoteAddrPtr (by rwa [hfn_cl]) hrun hsp_align hx19 hx20 hx23)
  rw [hfn_sc, hfn_cl] at hstep1
  refine SepWPp.bind_sepWP_steps_frame hinv hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx8_1, hx19_1, hx21_1, hx25_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have htr1_pre : s0.trace <+: s1.trace := htr1 ▸ htr
  refine SepWPp.weaken_frame (memRegion_368_untrusted_entails s.sp) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun pad => ?_
  refine SepWPp.pure_elim fun hpad => ?_
  have haddr_eq :
      protocolAddressAt A peer remoteAddrPtr =
        vecGhostAt A peer.name remoteAddrPtr ∗
          ((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗
          memRegion (remoteAddrPtr + 0x19#64) 7 := rfl
  refine SepWPp.weaken_frame (Entails.of_eq haddr_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_ext s.sp hstack_lt))
    (by sep_focus) ?_
  have hclone : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr stringCloneHookName) (stringCloneSpec A) := by
    rw [← hfn_sc]
    exact subroutine_ok.of_trapsOnly hT
      (LibsignalBinary.Proofs.Common.StringCloneFlat.stringClone_trTrapProgAt_ok
        img.base C A abs hAh)
  refine SepWPp.call_oom_steps_frame
    (x := (remoteAddrPtr, s.sp + 0x3e0#64, peer.name))
    (P_spec := vecGhostAt A peer.name remoteAddrPtr ∗ memRegion (s.sp + 0x3e0#64) 24 ∗
      A.pool ∗ stackAt s1.sp extHookStack)
    hinv1 htr1_pre hclone hpc1 hrun1 hsp1_al hx30_1
    (stringClone_pre_intro hx0_1 hx8_1)
    (by rw [hsp1]; sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [stringCloneSpec]
  rw [hsp1]
  sep_norm
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_ext s.sp hstack_lt).symm)
    (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, _, _, _, hx25_cs2, _, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = remoteAddrPtr := hx21_cs2.trans hx21_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hsp2_s]
  refine SepWPp.weaken_frame (vecU8_unpack_3e0 A s.sp peer.name.bytes) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (coroPtr + 0x250#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (s.sp + 0xa90#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq s.sp)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u390 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u370 => ?_
  have hw4_ex : ∃ devWord : BitVec 64, peer.device :: pad = unpack64 devWord := by
    rcases pad with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, _ | _⟩⟩⟩⟩⟩⟩⟩ <;>
      try simp at hpad
    exact ⟨p7 ++ p6 ++ p5 ++ p4 ++ p3 ++ p2 ++ p1 ++ peer.device,
      (unpack64_pack64 peer.device p1 p2 p3 p4 p5 p6 p7).symm⟩
  obtain ⟨devWord, hw4⟩ := hw4_ex
  have hlog_eq :
      logOff img =
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hstep3 := SepWP.of_trapsOnly hT (p1_untrusted_post_clone_vregs_wp_trap img.base C abs s2
    coroPtr remoteAddrPtr outPtr cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord
    u250 u258 u260 u268 u270 u278
    ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390
    d0 b_390 peer pad
    hb hw4 (by rwa [hfn_cl]) hrun2 hsp2_align hx19_2 hx21_2 hx25_2)
  rw [hsp2_s, hfn_cl] at hstep3
  refine SepWPp.bind_sepWP_steps_frame hinv2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hinv3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_s, htr3_2, hx19_3, hx22_3, hx25_3, hx26_3, hx28_3, _, hvregs3_2⟩
  refine SepWPp.weaken_frame
    (cells_3e0_entails_memRegion_368 s.sp cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord)
    (by sep_focus) ?_
  have hc250 := cells6_fold (coroPtr + 0x250#64)
    0x800000000000000c#64 cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord (s2.readReg64 .x27)
  repeat (simp only [BitVec.add_assoc] at hc250); repeat (simp only [BitVec.reduceAdd] at hc250)
  refine SepWPp.weaken_frame hc250 (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (sp_a90_rejoin s.sp 0x800000000000000c#64 cap ptr
      (BitVec.ofNat 64 peer.name.bytes.length) devWord (s2.readReg64 .x27))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq haddr_eq.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  have hdrop_ret := SepWPp.of_trapsOnly hT (p1_err_drop_and_return_vregs_wp_trap
    (Scope := Scope)
    hAh hstack_lt opt s0 s3 s.sp coroPtr outPtr cap ptr devWord (s2.readReg64 .x27) b_2c0
    peer pad hpad hw4 hinv3 hsp3_s (by rwa [hfn_cl]) hrun3 hsp_align
    hx19_3 hx22_3 hx25_3 hx26_3 hx28_3)
  refine SepWPp.bind_sepWPp_steps_frame hdrop_ret (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hspf, htrf_3, hcs_f, hvregsf_3, hinvf⟩
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s.trace := by
    rw [htrf_3, htr3_2, htr2_1, htr1]
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s := by
    rw [hvregsf_3, hvregs3_2, hvregs_cs2, hvregs1]
  refine ⟨htr_full, ?_, hspf, hcs_f, hvregs_full, hinvf.1, hinvf.2⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP1_untrusted_from_trust_ext {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {abs ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (hAh : AllocHooks A abs)
    (hT : TrapsOnly (trTrapProgAt img.base C abs) (tripleRatchetProgAtExt img.base ext))
    (hikit : IdentityStoreKitOkIE img ikit ext)
    (hstack_lt : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64)
    (haddr_id : ikit.addrOk peer.val)
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (s0 s6 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt
     u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv6 : ImgCallInv img s6)
    (hfs6_ikit : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet) (tripleRatchetProgAtExt img.base ext) s6)
    (hpc6 : s6.pc = img.base + ikit.trustShimOff)
    (hrun6 : s6.status = .Running)
    (hsp6_eq : s6.sp = sp)
    (hsp_saved : sp + 0xcd0#64 = s0.sp)
    (hsp6_align : (s6.sp &&& 15#64 == 0#64) = true)
    (htr6_pre : s0.trace <+: s6.trace)
    (hx0_6 : s6.readReg64 .x0 = idStorePtr)
    (hx1_6 : s6.readReg64 .x1 = remoteAddrPtr)
    (hx2_6 : s6.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3_6 : s6.readReg64 .x3 = 1#64)
    (hx19_6 : s6.readReg64 .x19 = coroPtr)
    (hx21_6 : s6.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26_6 : s6.readReg64 .x26 = outPtr)
    (hx27_6 : s6.readReg64 .x27 = ctxPtr)
    (hx30_6 : s6.readReg64 .x30 =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s6
      (p1LoadedRecordAt Scope A coroPtr opt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
         spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
       ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt s0.sp s0 ∗
       memRegion outPtr 48 ∗
       ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
       ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
       logOff img ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt sp (stageP1UntrustedCallStack kit ikit))
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
            memRegion (coroPtr + 0xe0#64) 368 ∗
            cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
              spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            cells (coroPtr + 0x398#64) 2 ∗
            ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
            ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
            ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
            memRegion (sp + 0x370#64) 36 ∗
            memRegion (sp + 0x3e0#64) 368 ∗
            cells (sp + 0xa90#64) 6 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
            ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
            ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
            ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
            logOff img ∗
            kit.storeAt sessStorePtr st ∗
            ikit.identityAt idStorePtr
              (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
            protocolAddressAt A peer remoteAddrPtr ∗
            ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
            A.pool ∗
            stackAt sp (stageP1UntrustedCallStack kit ikit)) ∧
        ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
        sf.trace = s6.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
        sf.sp = s0.sp ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s6 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hp1_le : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hstack_lt
  have herr_le : untrustedErrCallStack ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hstack_lt
  have htrust_le : trustCallStack ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hp1_le
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hp1_le))
    (by sep_focus) ?_
  sep_norm
  have htrust_raw := stageP1_trust_call_wp_kit_ext (ist := ist)
    peer remoteIdKey hAh hT hikit htrust_le haddr_id s0 s6
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hb hinv6 hfs6_ikit hpc6 hrun6 hsp6_align htr6_pre
    hx0_6 hx1_6 hx2_6 hx3_6 hx19_6 hx21_6 hx26_6 hx27_6 hx30_6
  have htrust := trust_call_wp_specialize_false_prog htrust_false htrust_raw
  rw [hsp6_eq] at htrust
  simp only [BitVec.add_assoc] at htrust
  refine SepWPp.bind_sepWPp_steps_frame htrust (by sep_focus)
    fun sm _ hpcm hrunm hregsm => ?_
  rcases hregsm with ⟨hrel_trust, htrm, hx20_m, hx23_m, hspm, hx19_m, _, hvregsm, hinvm⟩
  have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hspm, ← hsp6_eq]; exact hsp6_align
  have htrm_pre : s0.trace <+: sm.trace := by
    rcases htr6_pre with ⟨pre, hpre⟩
    exact ⟨pre ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok false),
      by rw [htrm, ← hpre, List.append_assoc]⟩
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hp1_le).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_err kit ikit sp hstack_lt))
    (by sep_focus) ?_
  unfold processPrekeyInnerInitAt
  sep_norm
  have herr := stageP1_untrusted_err_ok_kit_ext
    (Scope := Scope) (kit := kit) (ikit := ikit) (st := st) (ist := ist)
    peer remoteIdKey opt hAh hT herr_le s0 sm
    outPtr coroPtr msgPtr remoteAddrPtr sessStorePtr idStorePtr
    0#8 0#8
    hb hinvm hpcm hrunm hspm_align htrm_pre hx19_m hx20_m hx23_m
  rw [hspm, hsp_saved] at herr
  have herr_re := SepWPp.mono_run herr fun sf P_f h =>
    let ⟨htrf, hent, hregs⟩ := h
    And.intro hent (And.intro htrf hregs)
  refine SepWPp.bind_sepWPp_steps_frame herr_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcs_f, hvregsf_m, hFf, hsymf⟩
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_err kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨?_, hrel_trust, htrf.trans htrm, hspf, hcs_f, hvregsf_m.trans hvregsm, hFf, hsymf⟩
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  rw [hsp_saved]
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
private theorem p1_err_drop_and_return_vregs_wp_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hA : AllocHooks A ext)
    (hstack_lt : untrustedErrCallStack ≤ 2 ^ 64)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (s0 s3 : State) (sp coroPtr outPtr cap ptr devWord u_278 : BitVec 64)
    (b_2c0 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hpad : pad.length = 7)
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hinv3 : ImgCallInv img s3)
    (hsp3_s : s3.sp = sp)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64)
    (hrun3 : s3.status = .Running)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx22_3 : s3.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64)
    (hx25_3 : s3.readReg64 .x25 = sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx28_3 : s3.readReg64 .x28 = 0x800000000000000c#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s3
      (p1LoadedRecordAt Scope A coroPtr opt ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       SegUntrusted.vecU8Buf A cap ptr peer.name.bytes ∗
       ((sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((sp + 0x378#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
       ((sp + 0x388#64) ↦₆₄ (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
       ((sp + 0x390#64) ↦₃₂ u_278.extractLsb' 32 32) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp untrustedErrCallStack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp untrustedErrCallStack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s3.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s3 ∧
        ImgCallInv img sf)
      (PanicOomProp s0) := by
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_dropSS sp hstack_lt))
    (by sep_focus) ?_
  have hdrop := p1_err_drop_record_core_wp (Scope := Scope) (Qp := PanicOomProp s0)
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.drop_session_structure3_of_allocHooks_ext
      (A := A) (b := img.base) (ext := ext) hA)
    opt s3 coroPtr hinv3 hpc3 hrun3 hsp3_align hx19_3
  rw [hsp3_s] at hdrop
  refine SepWPp.bind_sepWPp_steps_frame hdrop (by sep_focus)
    fun s4 _ hpc4 hrun4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_s, htr4_3, hx19_4, hx22_4, hx25_4, hx26_4, hx28_4, hvregs4_3, hinv4⟩
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4_s]; exact hsp_align
  sep_norm
  refine SepWPp.exists_elim fun prevCap => SepWPp.exists_elim fun prevPtr => ?_
  refine SepWPp.pure_elim fun hprev_lt => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_dropSS sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_alloc sp hstack_lt))
    (by sep_focus) ?_
  have hret := p1_err_tail_prev_core_wp (Qp := PanicOomProp s0)
    (dealloc_ok_at_ext img.base A ext hA
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
      (num% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))
      (by
        unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName deallocName
        fnoff_eq))
    s0 s4 sp coroPtr outPtr
    prevCap prevPtr cap ptr devWord u_278 b_2c0 peer pad
    hprev_lt hpad hw4 hinv4 hsp4_s hpc4 hrun4 hsp4_align
    hx19_4 (hx22_4.trans hx22_3) (hx25_4.trans hx25_3)
    (hx26_4.trans hx26_3) (hx28_4.trans hx28_3)
  refine SepWPp.bind_sepWPp_steps_frame hret (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hspf, htrf_4, hcs_f, hvregsf_4, hinvf⟩
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_alloc sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨?_, hspf, htrf_4.trans htr4_3, hcs_f, hvregsf_4.trans hvregs4_3, hinvf⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP1_untrusted_err_ok_kit_x_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    {errStk : Nat}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (hAc : AllocContractsX img A ext)
    (hAh : AllocHooks A ext)
    (herr_ext2 : 2 * extHookStack ≤ errStk)
    (herr_base : untrustedErrCallStack ≤ errStk)
    (hstack_lt : errStk ≤ 2 ^ 64)
    (s0 s : State)
    (outPtr coroPtr msgPtr remoteAddrPtr sessStorePtr idStorePtr : BitVec 64)
    (b_2c0 b_390 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s)
    (hpc : s.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 0#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
       p1LoadedRecordAt Scope A coroPtr opt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       cells (s.sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗
       logOff img ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr
         (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt s.sp errStk)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          ((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          memRegion (s.sp + 0x3e0#64) 368 ∗
          cells (s.sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
          logOff img ∗
          kit.storeAt sessStorePtr st ∗
          ikit.identityAt idStorePtr
            (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
          protocolAddressAt A peer remoteAddrPtr ∗
          ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
          A.pool ∗
          stackAt s.sp errStk) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have herr_base_lt : untrustedErrCallStack ≤ 2 ^ 64 := Nat.le_trans herr_base hstack_lt
  have hstep1 := p1_untrusted_to_clone_vregs_wp_ext img.base ext s
    coroPtr remoteAddrPtr hpc hrun hsp_align hx19 hx20 hx23
  refine SepWPp.bind_sepWP_steps_frame hinv hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx8_1, hx19_1, hx21_1, hx25_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have htr1_pre : s0.trace <+: s1.trace := htr1 ▸ htr
  refine SepWPp.weaken_frame (memRegion_368_untrusted_entails s.sp) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun pad => ?_
  refine SepWPp.pure_elim fun hpad => ?_
  have haddr_eq :
      protocolAddressAt A peer remoteAddrPtr =
        vecGhostAt A peer.name remoteAddrPtr ∗
          ((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗
          memRegion (remoteAddrPtr + 0x19#64) 7 := rfl
  refine SepWPp.weaken_frame (Entails.of_eq haddr_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_split_of_le s.sp errStk (2 * extHookStack) herr_ext2 hstack_lt))
    (by sep_focus) ?_
  have hclone :=
    LibsignalBinary.Proofs.Common.StringCloneFlatX.stringClone2x_inImage_of_allocContractsX hAc
  refine SepWPp.call_oom_steps_frame
    (x := (remoteAddrPtr, s.sp + 0x3e0#64, peer.name))
    (P_spec := vecGhostAt A peer.name remoteAddrPtr ∗ memRegion (s.sp + 0x3e0#64) 24 ∗
      A.pool ∗ stackAt s1.sp (2 * extHookStack))
    hinv1 htr1_pre hclone hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [Spec.inImage,
        LibsignalBinary.Proofs.Common.StringCloneFlatX.stringCloneSpecWithStack]
      exact Entails.pure_right hinv1 (Entails.pure_right ⟨hx0_1, hx8_1⟩ (Entails.refl _)))
    (by rw [hsp1]; sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [Spec.inImage,
    LibsignalBinary.Proofs.Common.StringCloneFlatX.stringCloneSpecWithStack]
  rw [hsp1]
  sep_norm
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_split_of_le s.sp errStk (2 * extHookStack) herr_ext2 hstack_lt).symm)
    (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, _, _, _, hx25_cs2, _, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = remoteAddrPtr := hx21_cs2.trans hx21_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hsp2_s]
  refine SepWPp.weaken_frame (vecU8_unpack_3e0 A s.sp peer.name.bytes) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (coroPtr + 0x250#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (s.sp + 0xa90#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq s.sp)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u390 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u370 => ?_
  have hw4_ex : ∃ devWord : BitVec 64, peer.device :: pad = unpack64 devWord := by
    rcases pad with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, _ | _⟩⟩⟩⟩⟩⟩⟩ <;>
      try simp at hpad
    exact ⟨p7 ++ p6 ++ p5 ++ p4 ++ p3 ++ p2 ++ p1 ++ peer.device,
      (unpack64_pack64 peer.device p1 p2 p3 p4 p5 p6 p7).symm⟩
  obtain ⟨devWord, hw4⟩ := hw4_ex
  have hlog_eq :
      logOff img =
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hstep3 := p1_untrusted_post_clone_vregs_wp_ext img.base ext s2
    coroPtr remoteAddrPtr outPtr cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord
    u250 u258 u260 u268 u270 u278
    ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390
    d0 b_390 peer pad
    hb hw4 hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx25_2
  rw [hsp2_s] at hstep3
  refine SepWPp.bind_sepWP_steps_frame hinv2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hinv3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_s, htr3_2, hx19_3, hx22_3, hx25_3, hx26_3, hx28_3, _, hvregs3_2⟩
  refine SepWPp.weaken_frame
    (cells_3e0_entails_memRegion_368 s.sp cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord)
    (by sep_focus) ?_
  have hc250 := cells6_fold (coroPtr + 0x250#64)
    0x800000000000000c#64 cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord (s2.readReg64 .x27)
  repeat (simp only [BitVec.add_assoc] at hc250); repeat (simp only [BitVec.reduceAdd] at hc250)
  refine SepWPp.weaken_frame hc250 (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (sp_a90_rejoin s.sp 0x800000000000000c#64 cap ptr
      (BitVec.ofNat 64 peer.name.bytes.length) devWord (s2.readReg64 .x27))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq haddr_eq.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_split_of_le s.sp errStk untrustedErrCallStack herr_base hstack_lt))
    (by sep_focus) ?_
  have hdrop_ret := p1_err_drop_and_return_vregs_wp_ext
    (Scope := Scope)
    hAh herr_base_lt opt s0 s3 s.sp coroPtr outPtr cap ptr devWord (s2.readReg64 .x27) b_2c0
    peer pad hpad hw4 hinv3 hsp3_s hpc3 hrun3 hsp_align
    hx19_3 hx22_3 hx25_3 hx26_3 hx28_3
  refine SepWPp.bind_sepWPp_steps_frame hdrop_ret (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hspf, htrf_3, hcs_f, hvregsf_3, hinvf⟩
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_split_of_le s.sp errStk untrustedErrCallStack herr_base hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s.trace := by
    rw [htrf_3, htr3_2, htr2_1, htr1]
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s := by
    rw [hvregsf_3, hvregs3_2, hvregs_cs2, hvregs1]
  refine ⟨htr_full, ?_, hspf, hcs_f, hvregs_full, hinvf.1, hinvf.2⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP1_untrusted_from_trust_x_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (hAc : AllocContractsX img A ext)
    (hAh : AllocHooks A ext)
    (hikit : IdentityStoreKitOkIE img ikit ext)
    (hstack_lt : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64)
    (hext_load : 2 * extHookStack ≤ loadCallStack kit)
    (haddr_id : ikit.addrOk peer.val)
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (s0 s6 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt
     u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv6 : ImgCallInv img s6)
    (hfs6_ikit : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet) (tripleRatchetProgAtExt img.base ext) s6)
    (hpc6 : s6.pc = img.base + ikit.trustShimOff)
    (hrun6 : s6.status = .Running)
    (hsp6_eq : s6.sp = sp)
    (hsp_saved : sp + 0xcd0#64 = s0.sp)
    (hsp6_align : (s6.sp &&& 15#64 == 0#64) = true)
    (htr6_pre : s0.trace <+: s6.trace)
    (hx0_6 : s6.readReg64 .x0 = idStorePtr)
    (hx1_6 : s6.readReg64 .x1 = remoteAddrPtr)
    (hx2_6 : s6.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3_6 : s6.readReg64 .x3 = 1#64)
    (hx19_6 : s6.readReg64 .x19 = coroPtr)
    (hx21_6 : s6.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26_6 : s6.readReg64 .x26 = outPtr)
    (hx27_6 : s6.readReg64 .x27 = ctxPtr)
    (hx30_6 : s6.readReg64 .x30 =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s6
      (p1LoadedRecordAt Scope A coroPtr opt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
         spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
       ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt s0.sp s0 ∗
       memRegion outPtr 48 ∗
       ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
       ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
       logOff img ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt sp (stageP1UntrustedCallStack kit ikit))
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
            memRegion (coroPtr + 0xe0#64) 368 ∗
            cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
              spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            cells (coroPtr + 0x398#64) 2 ∗
            ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
            ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
            ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
            memRegion (sp + 0x370#64) 36 ∗
            memRegion (sp + 0x3e0#64) 368 ∗
            cells (sp + 0xa90#64) 6 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
            ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
            ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
            ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
            logOff img ∗
            kit.storeAt sessStorePtr st ∗
            ikit.identityAt idStorePtr
              (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
            protocolAddressAt A peer remoteAddrPtr ∗
            ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
            A.pool ∗
            stackAt sp (stageP1UntrustedCallStack kit ikit)) ∧
        ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
        sf.trace = s6.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
        sf.sp = s0.sp ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s6 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hp1_le : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hstack_lt
  have herr_ext2 : 2 * extHookStack ≤ stageP1UntrustedCallStack kit ikit :=
    Nat.le_trans hext_load (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have herr_base : untrustedErrCallStack ≤ stageP1UntrustedCallStack kit ikit :=
    Nat.le_max_right _ _
  have htrust_le : trustCallStack ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hp1_le
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hp1_le))
    (by sep_focus) ?_
  sep_norm
  have htrust_raw := stageP1_trust_call_wp_kit_x_ext (ist := ist)
    peer remoteIdKey hAh hikit htrust_le haddr_id s0 s6
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hb hinv6 hfs6_ikit hpc6 hrun6 hsp6_align htr6_pre
    hx0_6 hx1_6 hx2_6 hx3_6 hx19_6 hx21_6 hx26_6 hx27_6 hx30_6
  have htrust := trust_call_wp_specialize_false_prog htrust_false htrust_raw
  rw [hsp6_eq] at htrust
  simp only [BitVec.add_assoc] at htrust
  refine SepWPp.bind_sepWPp_steps_frame htrust (by sep_focus)
    fun sm _ hpcm hrunm hregsm => ?_
  rcases hregsm with ⟨hrel_trust, htrm, hx20_m, hx23_m, hspm, hx19_m, _, hvregsm, hinvm⟩
  have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hspm, ← hsp6_eq]; exact hsp6_align
  have htrm_pre : s0.trace <+: sm.trace := by
    rcases htr6_pre with ⟨pre, hpre⟩
    exact ⟨pre ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok false),
      by rw [htrm, ← hpre, List.append_assoc]⟩
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hp1_le).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  unfold processPrekeyInnerInitAt
  sep_norm
  have herr := stageP1_untrusted_err_ok_kit_x_ext
    (Scope := Scope) (kit := kit) (ikit := ikit) (st := st) (ist := ist)
    (errStk := stageP1UntrustedCallStack kit ikit)
    peer remoteIdKey opt hAc hAh herr_ext2 herr_base hstack_lt s0 sm
    outPtr coroPtr msgPtr remoteAddrPtr sessStorePtr idStorePtr
    0#8 0#8
    hb hinvm hpcm hrunm hspm_align htrm_pre hx19_m hx20_m hx23_m
  rw [hspm, hsp_saved] at herr
  have herr_re := SepWPp.mono_run herr fun sf P_f h =>
    let ⟨htrf, hent, hregs⟩ := h
    And.intro hent (And.intro htrf hregs)
  refine SepWPp.bind_sepWPp_steps_frame herr_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcs_f, hvregsf_m, hFf, hsymf⟩
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨?_, hrel_trust, htrf.trans htrm, hspf, hcs_f, hvregsf_m.trans hvregsm, hFf, hsymf⟩
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  rw [hsp_saved]
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
