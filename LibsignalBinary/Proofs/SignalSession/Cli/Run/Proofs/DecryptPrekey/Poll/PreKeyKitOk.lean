/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitE
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitStk
import LibsignalBinary.Proofs.RecordCodecs.SignedAssembly
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOneX
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExt
import LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWord
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShims
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll

/-!
# CLI PreKey, SignedPreKey, and KyberPreKey `StoreKitOkImgE` Bundles

Assembles `PreKeyStoreKitOkImgE` and `SignedPreKeyStoreKitOkImgE` from the verified CLI store shims
and polls, parameterized by the record-decoder contracts (`preKeyDeserializeSpec` and
`decodeKyberPreKeySpec`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.Store

/-! ## 1. Entry-Address Rewrites (`fnAddr` → `b + Off`) & Future Drop -/

section FnAddr
variable {b : BitVec 64} {ext : String → Option (State → State)}

theorem cliPkGetShim_fnAddr :
    (tripleRatchetProgAtExt b ext).fnAddr pkGetShimName = b + cliPkGetShimOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, pkGetShim_fnOff, cliPkGetShimOff]

theorem cliPkGetPoll_fnAddr :
    (tripleRatchetProgAtExt b ext).fnAddr pkGetPollName = b + cliPkGetPollOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, pkGetPoll_fnOff, cliPkGetPollOff]

theorem cliPkRemoveShim_fnAddr :
    (tripleRatchetProgAtExt b ext).fnAddr pkRemoveShimName = b + cliPkRemoveShimOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, pkRemoveShim_fnOff, cliPkRemoveShimOff]

theorem cliPkRemovePoll_fnAddr :
    (tripleRatchetProgAtExt b ext).fnAddr pkRemovePollName = b + cliPkRemovePollOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, pkRemovePoll_fnOff, cliPkRemovePollOff]

theorem cliSpkGetShim_fnAddr :
    (tripleRatchetProgAtExt b ext).fnAddr spkGetShimName = b + cliSpkGetShimOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, spkGetShim_fnOff, cliSpkGetShimOff]

theorem cliSpkGetPoll_fnAddr :
    (tripleRatchetProgAtExt b ext).fnAddr spkGetPollName = b + cliSpkGetPollOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, spkGetPoll_fnOff, cliSpkGetPollOff]

theorem cliKpkGetShim_fnAddr :
    (tripleRatchetProgAtExt b ext).fnAddr kpkGetShimName = b + cliKpkGetShimOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, kpkGetShim_fnOff, cliKpkGetShimOff]

theorem cliKpkGetPoll_fnAddr :
    (tripleRatchetProgAtExt b ext).fnAddr kpkGetPollName = b + cliKpkGetPollOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, kpkGetPoll_fnOff, cliKpkGetPollOff]

theorem cliKpkMarkShim_fnAddr :
    (tripleRatchetProgAtExt b ext).fnAddr kpkMarkShimName = b + cliKpkMarkShimOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, kpkMarkShim_fnOff, cliKpkMarkShimOff]

end FnAddr

theorem cliIdFutDrop_inImage_ext {img : Obj.Image} {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + cliIdFutDropOff)
      (futDropSpec.inImage img) :=
  subroutine_ok_withEnvPre cliIdFutDrop_ok_ext (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab)

/-! ## 2. Shared Shim Consequence Helpers -/

theorem pkShim_conseq {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {addr vtOff : BitVec 64} {stk : Nat}
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext) addr (pkShimSpec vtOff A img stk)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) addr
      (Spec.inImage
        { pre := fun (x : PreKeyShimCall) (s : State) =>
            ⌜(img.base &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id⌝ ∗
              A.pool ∗ stackAt s.sp stk
          post := fun x s0 sf =>
            ⌜sf.readReg64 .x1 = img.base + vtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live (sf.readReg64 .x0) 16 8 ∗ pkBoxAt (sf.readReg64 .x0) x.self x.id 0#8 ∗
              A.pool ∗ stackAt s0.sp stk
          onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
        img) := by
  refine subroutine_ok_map_panic h fun x R (s0 : State) hpre => ?_
  dsimp only [Spec.inImage, pkShimSpec] at hpre ⊢
  have h1 : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id⌝ ∗
        (A.pool ∗ stackAt s0.sp stk ∗ R)) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at h1; obtain ⟨hfl, h1⟩ := h1
  rw [satisfies_pure_sepConj] at h1; obtain ⟨⟨_, hx0, hx1⟩, hsp⟩ := h1
  have hm : s0.mem ⊨ (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id⌝ ∗ A.pool ∗ stackAt s0.sp stk)) ∗ R := by
    have h2 : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id⌝ ∗
          (A.pool ∗ stackAt s0.sp stk ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx1⟩, hsp⟩
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h2
  exact ⟨⟨x.self, x.id⟩, R, hm, fun _ hp => hp, fun _ hp => hp⟩

theorem kpkMarkShim_conseq {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {addr : BitVec 64} {stk : Nat}
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext) addr (kpkMarkShimSpec A img stk)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) addr
      (Spec.inImage
        { pre := fun (x : KyberMarkShimCall) (s : State) =>
            ⌜(img.base &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧
              s.readReg32 .x2 = x.signedId ∧ s.readReg64 .x3 = x.baseKeyA⌝ ∗
              A.pool ∗ stackAt s.sp stk
          post := fun x s0 sf =>
            ⌜sf.readReg64 .x1 = img.base + cliKpkMarkFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live (sf.readReg64 .x0) 32 8 ∗
              kpkMarkBoxAt (sf.readReg64 .x0) x.self x.baseKeyA x.id x.signedId 0#8 ∗
              A.pool ∗ stackAt s0.sp stk
          onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
        img) := by
  refine subroutine_ok_map_panic h fun x R (s0 : State) hpre => ?_
  dsimp only [Spec.inImage, kpkMarkShimSpec] at hpre ⊢
  have h1 : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id ∧
        s0.readReg32 .x2 = x.signedId ∧ s0.readReg64 .x3 = x.baseKeyA⌝ ∗
        (A.pool ∗ stackAt s0.sp stk ∗ R)) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at h1; obtain ⟨hfl, h1⟩ := h1
  rw [satisfies_pure_sepConj] at h1; obtain ⟨⟨_, hx0, hx1, hx2, hx3⟩, hsp⟩ := h1
  have hm : s0.mem ⊨ (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id ∧
        s0.readReg32 .x2 = x.signedId ∧ s0.readReg64 .x3 = x.baseKeyA⌝ ∗
        A.pool ∗ stackAt s0.sp stk)) ∗ R := by
    have h2 : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id ∧
          s0.readReg32 .x2 = x.signedId ∧ s0.readReg64 .x3 = x.baseKeyA⌝ ∗
          (A.pool ∗ stackAt s0.sp stk ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx1, hx2, hx3⟩, hsp⟩
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h2
  exact ⟨⟨x.self, x.id, x.signedId, x.baseKeyA⟩, R, hm, fun _ hp => hp, fun _ hp => hp⟩

/-! ## 3. `PreKeyStoreKitOkImgE` and `SignedPreKeyStoreKitOkImgE` -/

/-- Generic `PreKeyStoreKitOkImgE` assembly for `cliPreKeyStoreSpec`, leaving only
`hPkDec` (`PreKeyRecord::deserialize`) and the stack bounds `hs1..hs4` open. -/
theorem cliPkKitOkImgE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {pid : BitVec 32} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hPkDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName)
      (preKeyDeserializeSpec A img))
    (hs1 : (cliKitStk ⟨readStk⟩).pkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).pkGetPoll ≤ s2)
    (hs3 : (cliKitStk ⟨readStk⟩).pkRemoveShim ≤ s3)
    (hs4 : (cliKitStk ⟨readStk⟩).pkRemovePoll ≤ s4) :
    PreKeyStoreKitOkImgE img
      (cliPreKeyStoreSpec A img.base rd F0 cliWrOk pid s1 s2 s3 s4) ext := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := base_aligned himg
  have hC : AllocContractsX img A ext := hh.alloc
  have hDecimal := Decimal.decimal_ok_of_deps
    (reserve_ok hh (Nat.le_refl doReserveStackX)) (Nat.le_refl SessKit.decNeed) hb
  have hGet := Get.dirGet_ok_of_deps (pathOk := cliWrOk) himg (fun _ hp => hp.2) hC
    hh.memcpyRO hh.bcmp (path_ok himg hh (Nat.le_refl pathNeed))
    hRead hh.fs (Nat.le_refl (RunBudgets.dirGetNeed ⟨readStk⟩)) hb
  have hGrow := GrowOne.growOneDir_ok_x hC (Nat.le_refl SessKit.growOneDirNeed) hb
  have hPut := Put.dirPut_ok_of_deps hC hh.bcmp hGrow (Nat.le_refl SessKit.dirPutNeed) hb
  have hDropW := DropSpeWord.dropSpeWord_ok himg hC
  refine ⟨?_, ?_, cliIdFutDrop_inImage_ext, ?_, ?_, cliIdFutDrop_inImage_ext⟩
  · -- getShim
    have h := PkShims.pkGetShim_ok_of_deps hC hs1 hb
    rw [cliPkGetShim_fnAddr] at h
    exact pkShim_conseq h
  · -- getPoll
    have h := PkGetPoll.pkGetPoll_ok_of_deps hC hDecimal hGet hPkDec hDropW hh.fs hs2 hb
    rw [cliPkGetPoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨⟨fut, out, self, id⟩, st0⟩ R s0 hpre
    dsimp only [kitPreKeyGetPollSpecE, Spec.inImage, withEnvPre, kitPreKeyGetPollSpec,
      cliPreKeyStoreSpec, cliPkStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          id = pid⌝ ∗
        (⌜CliPkInv rd F0 cliWrOk pid st0⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt A self st0 ∗ memRegion out 56 ∗
          A.pool ∗ stackAt s0.sp s2 ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, hid⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
    subst hid
    have hm_hop : s0.mem ⊨ (pkGetPollSpec rd cliWrOk A img s2).pre ⟨fut, out, self, id, st0⟩ s0 ∗ R := by
      dsimp only [pkGetPollSpec, pkGetPollSpecOf, Spec.inImage]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk cliWrOk st0 id ∧ PkSizeOk rd s0.fs.files st0 id⌝ ∗
          (pkBoxAt fut self id 0#8 ∗ dirAt A self st0 ∗ memRegion out 56 ∗
            A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx8, hinv.nameOk, hfiles ▸ hinv.sizeOk⟩, hsp⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨fut, out, self, id, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
    intro sf hpost
    dsimp only [pkGetPollSpec, pkGetPollSpecOf, Spec.inImage] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨pa, ⟨hpa, htr⟩, hm⟩ := hpost
    rw [hfiles] at hpa; subst hpa
    have hm' := Satisfies.mono
      (sepConj_mono_left (pkGetAnsAt_entails_pollOut A img.base rd F0 cliWrOk id s1 s2 s3 s4 st0 id out)) hm
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hm'
    obtain ⟨ans, hrel, hm'⟩ := hm'
    dsimp only [kitPreKeyGetPollSpecE, Spec.inImage, withEnvPre, kitPreKeyGetPollSpec]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ans, ?_⟩
    have hstore :
        (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).storeAt self
          ((cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).getUpdate st0 id ans) =
        (⌜CliPkInv rd F0 cliWrOk id st0⌝ ∗ dirAt A self st0) := rfl
    have hstk : (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).getPollStack = s2 := rfl
    have hbox : (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).getBoxAt fut self id 1#8 =
        pkBoxAt fut self id 1#8 := rfl
    rw [hstore, hstk, hbox]
    have hgoal : sf.mem ⊨
        ⌜(cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).getRel st0 id ans ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliPkInv rd F0 cliWrOk id st0⌝ ∗
          (preKeyGetPollOutAt (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4) out ans ∗
            pkBoxAt fut self id 1#8 ∗ dirAt A self st0 ∗ A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  · -- removeShim
    have h := PkShims.pkRemoveShim_ok_of_deps hC hs3 hb
    rw [cliPkRemoveShim_fnAddr] at h
    exact pkShim_conseq h
  · -- removePoll
    have h := PkRemovePoll.pkRemovePoll_ok_of_deps hC hDecimal hGet hPut hh.fs hs4 hb
    rw [cliPkRemovePoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨⟨fut, out, self, id⟩, st0⟩ R s0 hpre
    dsimp only [kitPreKeyRemovePollSpecE, Spec.inImage, withEnvPre, kitPreKeyRemovePollSpec,
      cliPreKeyStoreSpec, cliPkStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          id = pid⌝ ∗
        (⌜CliPkInv rd F0 cliWrOk pid st0⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt A self st0 ∗ memRegion out 48 ∗
          A.pool ∗ stackAt s0.sp s4 ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, hid⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
    subst hid
    have hm_hop : s0.mem ⊨ (pkRemovePollSpec rd cliWrOk A img s4).pre ⟨fut, out, self, id, st0⟩ s0 ∗ R := by
      dsimp only [pkRemovePollSpec, Spec.inImage]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk cliWrOk st0 id ∧ st0.changed.length < 2 ^ 32⌝ ∗
          (pkBoxAt fut self id 0#8 ∗ dirAt A self st0 ∗ memRegion out 48 ∗
            A.pool ∗ stackAt s0.sp s4 ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx8, hinv.nameOk, hinv.oneLt.1⟩, hsp⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨fut, out, self, id, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
    intro sf hpost
    dsimp only [pkRemovePollSpec, Spec.inImage] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨res, ⟨hres, htr⟩, hm⟩ := hpost
    rw [hfiles] at hres; subst hres
    have hm' := Satisfies.mono
      (sepConj_mono_left (pkRemoveOutAt_entails_pollOut A img.base rd F0 cliWrOk id s1 s2 s3 s4 st0 id out)) hm
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hm'
    obtain ⟨ans, ⟨hrel, heq2⟩, hm'⟩ := hm'
    rw [heq2] at hm'
    dsimp only [kitPreKeyRemovePollSpecE, Spec.inImage, withEnvPre, kitPreKeyRemovePollSpec]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ans, ?_⟩
    have hstore :
        (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).storeAt self
          ((cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).removeUpdate st0 id ans) =
        (⌜CliPkInv rd F0 cliWrOk id
            (_root_.CryptoVerification.SignalSession.Cli.removePreKey rd F0 st0 id).2⌝ ∗
          dirAt A self (_root_.CryptoVerification.SignalSession.Cli.removePreKey rd F0 st0 id).2) := rfl
    have hstk : (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).removePollStack = s4 := rfl
    have hbox : (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).removeBoxAt fut self id 1#8 =
        pkBoxAt fut self id 1#8 := rfl
    rw [hstore, hstk, hbox]
    have hgoal : sf.mem ⊨
        ⌜(cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4).removeRel st0 id ans ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliPkInv rd F0 cliWrOk id
            (_root_.CryptoVerification.SignalSession.Cli.removePreKey rd F0 st0 id).2⌝ ∗
          (preKeyRemovePollOutAt (cliPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2 s3 s4) out ans ∗
            dirAt A self (_root_.CryptoVerification.SignalSession.Cli.removePreKey rd F0 st0 id).2 ∗
            pkBoxAt fut self id 1#8 ∗ A.pool ∗ stackAt s0.sp s4 ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hinv.removePreKey, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal

/-- Generic `SignedPreKeyStoreKitOkImgE` assembly for `cliSignedPreKeyStoreSpec`, leaving only
`hKpkDec` (`decode_kyber_pre_key`) and the stack bounds `hs1, hs2` open. -/
theorem cliSpkKitOkImgE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {sid : BitVec 32} {readStk s1 s2 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hKpkDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeKyberPreKeySpec A img))
    (hs1 : (cliKitStk ⟨readStk⟩).spkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).spkGetPoll ≤ s2) :
    SignedPreKeyStoreKitOkImgE img
      (cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk sid s1 s2) ext := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := base_aligned himg
  have hC : AllocContractsX img A ext := hh.alloc
  have hDecimal := Decimal.decimal_ok_of_deps
    (reserve_ok hh (Nat.le_refl doReserveStackX)) (Nat.le_refl SessKit.decNeed) hb
  have hGet := Get.dirGet_ok_of_deps (pathOk := cliWrOk) himg (fun _ hp => hp.2) hC
    hh.memcpyRO hh.bcmp (path_ok himg hh (Nat.le_refl pathNeed))
    hRead hh.fs (Nat.le_refl (RunBudgets.dirGetNeed ⟨readStk⟩)) hb
  have hDropW := DropSpeWord.dropSpeWord_ok himg hC
  have hSpkDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeSignedPreKeySpec A img) :=
    SignedAssembly.decodeSignedPreKeySpec_eq A img ▸ hKpkDec
  refine ⟨?_, ?_, cliIdFutDrop_inImage_ext⟩
  · -- getShim
    have h := PkShims.spkGetShim_ok_of_deps hC hs1 hb
    rw [cliSpkGetShim_fnAddr] at h
    exact pkShim_conseq h
  · -- getPoll
    have h := SpkGetPoll.spkGetPoll_ok_of_deps hC hDecimal hGet hSpkDec hDropW hh.fs hs2 hb
    rw [cliSpkGetPoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨⟨fut, out, self, id⟩, st0⟩ R (s0 : State) hpre
    dsimp only [kitSpkGetPollSpecE, Spec.inImage, withEnvPre, kitSpkGetPollSpec,
      cliSignedPreKeyStoreSpec, cliSpkStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          id = sid⌝ ∗
        (⌜CliSpkInv rd F0 cliWrOk sid st0⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt A self st0 ∗ memRegion out 88 ∗
          A.pool ∗ stackAt s0.sp s2 ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, hid⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
    subst hid
    have hm_hop : s0.mem ⊨ (spkGetPollSpec rd cliWrOk A img s2).pre ⟨fut, out, self, id, st0⟩ s0 ∗ R := by
      dsimp only [spkGetPollSpec, pkGetPollSpecOf, Spec.inImage]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk cliWrOk st0 id ∧ PkSizeOk rd s0.fs.files st0 id⌝ ∗
          (pkBoxAt fut self id 0#8 ∗ dirAt A self st0 ∗ memRegion out 88 ∗
            A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx8, hinv.nameOk, hfiles ▸ hinv.sizeOk⟩, hsp⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨fut, out, self, id, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
    intro sf hpost
    dsimp only [spkGetPollSpec, pkGetPollSpecOf, Spec.inImage] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨pa, ⟨hpa, htr⟩, hm⟩ := hpost
    rw [hfiles] at hpa; subst hpa
    have hm' := Satisfies.mono
      (sepConj_mono_left (spkAnsAt_entails_pollOut A img.base rd F0 cliWrOk id s1 s2 st0 id out)) hm
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hm'
    obtain ⟨ans, hrel, hm'⟩ := hm'
    dsimp only [kitSpkGetPollSpecE, Spec.inImage, withEnvPre, kitSpkGetPollSpec]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ans, ?_⟩
    have hstore :
        (cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2).storeAt self
          ((cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2).getUpdate st0 id ans) =
        (⌜CliSpkInv rd F0 cliWrOk id st0⌝ ∗ dirAt A self st0) := rfl
    have hstk : (cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2).getPollStack = s2 := rfl
    have hbox : (cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2).getBoxAt fut self id 1#8 =
        pkBoxAt fut self id 1#8 := rfl
    rw [hstore, hstk, hbox]
    have hgoal : sf.mem ⊨
        ⌜(cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2).getRel st0 id ans ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliSpkInv rd F0 cliWrOk id st0⌝ ∗
          (spkGetPollOutAt (cliSignedPreKeyStoreSpec A img.base rd F0 cliWrOk id s1 s2) out ans ∗
            pkBoxAt fut self id 1#8 ∗ dirAt A self st0 ∗ A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
