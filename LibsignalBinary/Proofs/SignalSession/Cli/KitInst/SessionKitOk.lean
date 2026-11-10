/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOneX
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExt
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadShim
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollX
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShim

/-!
# CLI `SessionOnlyKitOkSE` Assembly

Assembles `MessageDecrypt.SessionOnlyKitOkSE` for `cliSessionStoreSpec` from the `SessionFiles`
shim, poll, and `futDrop` contracts over an arbitrary allocator, `ReadRule`, initial file table,
`SessionRecord` scope, and external-hook map.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst.SessKit

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.Store
open CryptoVerification.SignalSession.Cli.MainHops

/-! ## Stack bounds -/

abbrev decNeed : Nat := 10 * 0x50 + doReserveStackX
abbrev addrTextNeed : Nat := 0x70 + max (max doReserveStackX extHookStack) decNeed
abbrev growOneDirNeed : Nat := 0x40 + finishGrowStackX
abbrev dirPutNeed : Nat := 0x60 + max growOneDirNeed extHookStack
abbrev loadShimNeed : Nat := 0x20 + extHookStack
abbrev storeShimNeed : Nat := 0x30 + extHookStack
abbrev loadPollNeed (readStk : Nat) : Nat :=
  0x350 + max (max addrTextNeed (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩))
    (max E2E.Record.recDeserializeStack extHookStack)
abbrev storePollNeedX : Nat :=
  0xd0 + max (max addrTextNeed Proofs.libsignal.Hooks2.serializeStackX) (max dirPutNeed extHookStack)

/-! ## Separation-logic rearrangement helpers -/

private theorem poll_pre_entails {p1 p2 p3 q1 q2 : Prop} {box dir rest : SepProp}
    (hq : p1 → p2 → p3 → q1 ∧ q2) :
    ⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest) ⊢
      ⌜q1⌝ ∗ (⌜q2⌝ ∗ box ∗ dir ∗ rest) := by
  have hperm :
      ⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest) =
        ⌜p1⌝ ∗ (⌜p2⌝ ∗ (⌜p3⌝ ∗ (box ∗ dir ∗ rest))) := by
    ac_rfl
  rw [hperm]
  apply Entails.pure_left; intro hp1
  apply Entails.pure_left; intro hp2
  apply Entails.pure_left; intro hp3
  obtain ⟨hq1, hq2⟩ := hq hp1 hp2 hp3
  exact Entails.pure_right hq1 (Entails.pure_right hq2 (Entails.refl _))

private theorem storePoll_pre_entails {fl p1 p2 p3 q : Prop} {box dir rest : SepProp}
    (hq : p1 → p2 → p3 → q) :
    ⌜fl⌝ ∗ (⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest)) ⊢
      ⌜fl⌝ ∗ (⌜q⌝ ∗ box ∗ dir ∗ rest) := by
  apply Entails.pure_left; intro hfl
  refine Entails.pure_right hfl ?_
  have hperm :
      ⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest) =
        ⌜p1⌝ ∗ (⌜p2⌝ ∗ (⌜p3⌝ ∗ (box ∗ dir ∗ rest))) := by
    ac_rfl
  rw [hperm]
  apply Entails.pure_left; intro hp1
  apply Entails.pure_left; intro hp2
  apply Entails.pure_left; intro hp3
  exact Entails.pure_right (hq hp1 hp2 hp3) (Entails.refl _)

private theorem extract_pure3 {p1 p2 p3 : Prop} {box dir rest R : SepProp} {m : Memory}
    (hm : m ⊨ (⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest)) ∗ R) :
    p1 ∧ p2 ∧ p3 := by
  have hperm :
      (⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest)) ∗ R =
        ⌜p1⌝ ∗ (⌜p2⌝ ∗ (⌜p3⌝ ∗ (box ∗ dir ∗ rest ∗ R))) := by
    ac_rfl
  rw [hperm, satisfies_pure_sepConj] at hm
  obtain ⟨hp1, hm⟩ := hm
  rw [satisfies_pure_sepConj] at hm
  obtain ⟨hp2, hm⟩ := hm
  rw [satisfies_pure_sepConj] at hm
  exact ⟨hp1, hp2, hm.1⟩

private theorem extract_storePoll_pure {fl p1 p2 p3 : Prop} {box dir rest R : SepProp} {m : Memory}
    (hm : m ⊨ (⌜fl⌝ ∗ (⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest))) ∗ R) :
    p1 ∧ p2 ∧ p3 := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact extract_pure3 hm.2

private theorem loadPoll_post_sat {α β : Type} {p : α → β → Prop} {q : β → Prop}
    {inv : Prop} {out1 out2 : β → SepProp} {box1 dir tail R : SepProp} {m : Memory}
    (hinv : inv)
    (hstep : ∀ g a, p g a → q a ∧ (out1 a ⊢ out2 a))
    (hm : m ⊨ ((∃∗ g : α, ∃∗ a : β, ⌜p g a⌝ ∗ out1 a) ∗ box1 ∗ dir ∗ tail) ∗ R) :
    m ⊨ (∃∗ a : β, ⌜q a⌝ ∗ box1 ∗ (⌜inv⌝ ∗ dir) ∗ out2 a ∗ tail) ∗ R := by
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨g, hm⟩ := hm
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hm⟩ := hm
  have hperm1 :
      ((⌜p g a⌝ ∗ out1 a) ∗ (box1 ∗ dir ∗ tail)) ∗ R =
        ⌜p g a⌝ ∗ ((box1 ∗ dir ∗ out1 a ∗ tail) ∗ R) := by
    ac_rfl
  rw [hperm1, satisfies_pure_sepConj] at hm
  obtain ⟨hpga, hm⟩ := hm
  obtain ⟨hqa, hout⟩ := hstep g a hpga
  refine Satisfies.sepExists_intro a ?_
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hqa, Satisfies.mono (sepConj_mono_left ?_) hm⟩
  exact sepConj_mono_right
    (sepConj_mono (Entails.pure_right hinv (Entails.refl dir)) (sepConj_mono_left hout))

private theorem storePoll_post_sat {p : Prop} {q : Except Unit Unit → Prop} {inv' : Prop}
    {box1 dir0 outA outB tail R : SepProp}
    {storeAt' outAt' : Except Unit Unit → SepProp} {m : Memory}
    (hq : p → q (.ok ())) (hinv' : inv')
    (hstore : storeAt' (.ok ()) = ⌜inv'⌝ ∗ dir0)
    (hout : outAt' (.ok ()) = outA ∗ outB)
    (hm : m ⊨ (⌜p⌝ ∗ box1 ∗ dir0 ∗ outA ∗ outB ∗ tail) ∗ R) :
    m ⊨ (∃∗ ans : Except Unit Unit,
          ⌜q ans⌝ ∗ box1 ∗ storeAt' ans ∗ outAt' ans ∗ tail) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨hp, hm⟩ := hm
  refine Satisfies.sepExists_intro (.ok ()) ?_
  rw [hstore, hout, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hq hp, Satisfies.mono (sepConj_mono_left ?_) hm⟩
  rw [← sepConj_assoc outA outB tail]
  exact sepConj_mono_right (sepConj_mono_left (Entails.pure_right hinv' (Entails.refl dir0)))

/-! ## Kit assembly -/

/-- Assemble `SessionOnlyKitOkSE` for `cliSessionStoreSpec` from `RunHooks`, `read_file`,
`SessionRecord::deserialize`, and `SessionRecord::serialize` contracts. -/
theorem cliSessKitOkSE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooks img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordDeserializeName)
      (sessDeserializeSpec Scope A img))
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((Proofs.libsignal.Hooks2.serializeCanonSpecX A).inImage img))
    (hs1 : loadShimNeed ≤ s1) (hs2 : loadPollNeed readStk ≤ s2)
    (hs3 : storeShimNeed ≤ s3) (hs4 : storePollNeedX ≤ s4) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliSessionStoreSpec A img.base rd F0 cliWrOk Scope peer s1 s2 s3 s4)
      Scope E2E.Record.encodeRecord ext := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := RunSkeleton.base_aligned himg
  have hC : AllocContractsX img A ext := hh.alloc
  have hRes := RunSkeleton.reserve_ok hh (Nat.le_refl doReserveStackX)
  have hDec := Decimal.decimal_ok_of_deps hRes (Nat.le_refl decNeed) hb
  have hAddr := AddressText.addressText_ok_of_deps hC hRes hDec (Nat.le_refl addrTextNeed) hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- loadShim
    have h := LoadShim.sessLoadShim_ok_of_deps hC hs1 hb
    rw [cliSessLoadShim_fnAddr] at h
    exact h
  · -- loadPoll
    have hGet := Get.dirGet_ok_of_deps (pathOk := cliWrOk) himg (fun _ hp => hp.2) hC
      hh.memcpyRO hh.bcmp (RunSkeleton.path_ok himg hh (Nat.le_refl RunSkeleton.pathNeed))
      hRead hh.fs (Nat.le_refl (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩)) hb
    have h := LoadPoll.sessLoadPoll_ok_of_deps hC hAddr hGet hDeser hh.fs hs2 hb
    rw [cliSessLoadPoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨call, self, d⟩ R s0 hpre
    obtain ⟨hfiles, ⟨_, _, _, _, haddr⟩, hinv⟩ := extract_pure3 hpre
    have hname : call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    refine ⟨⟨call, self, d⟩, R, ?_, ?_, fun _ hpan => hpan⟩
    · exact Satisfies.mono
        (sepConj_mono_left
          (poll_pre_entails fun hfiles' ⟨hfl, hsym, hx0, hx8, haddr'⟩ hinv' =>
            ⟨⟨hfl, hsym⟩, hx0, hx8, hname ▸ hinv'.nameLt, haddr' ▸ hinv'.textLt, hinv'.pathLt,
              haddr' ▸ hinv'.pathOk, fun bs hbs => by
                rw [hfiles', haddr'] at hbs
                obtain ⟨bs₀, hget₀, hwf₀⟩ := hinv'.getOk
                rw [hget₀] at hbs
                cases hbs
                exact hwf₀⟩))
        hpre
    · intro sf hpost
      refine loadPoll_post_sat hinv (fun gr ans ⟨⟨hgr, htr⟩, hans⟩ => ?_) hpost
      rw [hfiles, haddr] at hgr
      obtain ⟨bs₀, hget₀, _⟩ := hinv.getOk
      rw [hget₀] at hgr
      subst hgr
      refine ⟨⟨⟨bs₀, haddr.symm ▸ hget₀, hans⟩, by
        show sf.trace = s0.trace ++ []
        rw [List.append_nil]
        exact htr⟩, ?_⟩
      cases bs₀ with
      | nil =>
        have hans' : ans = .ok none := hans
        subst hans'
        exact Entails.refl _
      | cons b bs =>
        obtain ⟨r, hans', _, hsc⟩ := hans
        subst hans'
        exact Entails.pure_right hsc (Entails.refl _)
  · -- loadFutDrop
    exact cliIdFutDrop_ok_ext
  · -- storeShim
    have h := StoreShim.sessStoreShim_ok_of_deps hC hs3 hb
    rw [cliSessStoreShim_fnAddr] at h
    exact h
  · -- storePoll
    have hGrow := GrowOne.growOneDir_ok_x hC (Nat.le_refl growOneDirNeed) hb
    have hPut := Put.dirPut_ok_of_deps hC hh.bcmp hGrow (Nat.le_refl dirPutNeed) hb
    have h := StorePollX.sessStorePoll_ok_of_depsX hC hAddr hSer hPut hs4 hb
    rw [cliSessStorePoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨call, self, d⟩ R s0 hpre
    obtain ⟨_, ⟨_, _, hrec, haddr⟩, hinv⟩ := extract_storePoll_pure hpre
    have hname : call.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    refine ⟨⟨call, self, d⟩, R, ?_, ?_, fun _ hpan => hpan⟩
    · exact Satisfies.mono
        (sepConj_mono_left
          (storePoll_pre_entails fun _ ⟨hx0, hx8, hrec', _⟩ hinv' =>
            ⟨hx0, hx8, hname ▸ hinv'.nameLt, hrec'.2, hinv'.changedLt.1⟩))
        hpre
    · intro sf hpost
      exact storePoll_post_sat
        (fun htr => ⟨rfl, by
          show sf.trace = s0.trace ++ []
          rw [List.append_nil]
          exact htr⟩)
        (cliSessionStoreSpec_storeUpdate_inv (ans := .ok ()) hinv haddr hrec)
        rfl rfl hpost
  · -- storeFutDrop
    exact cliIdFutDrop_ok_ext

/-- Variant of `cliSessKitOkSE` taking minimal hook contracts and pool-threaded
`sessDeserializeExtSpec`. -/
theorem cliSessKitOkSE_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {roStk readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk))
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordDeserializeName)
      (sessDeserializeExtSpec Scope A img))
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((Proofs.libsignal.Hooks2.serializeCanonSpecX A).inImage img))
    (hs1 : loadShimNeed ≤ s1) (hs2 : loadPollNeed readStk ≤ s2)
    (hs3 : storeShimNeed ≤ s3) (hs4 : storePollNeedX ≤ s4)
    (hro : roStk ≤ extHookStack := by decide) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliSessionStoreSpec A img.base rd F0 cliWrOk Scope peer s1 s2 s3 s4)
      Scope E2E.Record.encodeRecord ext := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := RunSkeleton.base_aligned himg
  have hRes := cliDoReserve_ok hC (Nat.le_refl doReserveStackX)
  have hDec := Decimal.decimal_ok_of_deps hRes (Nat.le_refl decNeed) hb
  have hAddr := AddressText.addressText_ok_of_deps hC hRes hDec (Nat.le_refl addrTextNeed) hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- loadShim
    have h := LoadShim.sessLoadShim_ok_of_deps hC hs1 hb
    rw [cliSessLoadShim_fnAddr] at h
    exact h
  · -- loadPoll
    have hPath := Path.path_ok_of_deps_withStack hC hRO hRes
      (Nat.le_refl RunSkeleton.pathNeed) hb hro
    have hGet := Get.dirGet_ok_of_deps_withStack (pathOk := cliWrOk) himg (fun _ hp => hp.2) hC
      hRO hBcmp hPath hRead hFs (Nat.le_refl (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩)) hb hro
    have h := LoadPoll.sessLoadPoll_ok_of_deps_ext hC hAddr hGet hDeser hFs hs2 hb
    rw [cliSessLoadPoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨call, self, d⟩ R s0 hpre
    obtain ⟨hfiles, ⟨_, _, _, _, haddr⟩, hinv⟩ := extract_pure3 hpre
    have hname : call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    refine ⟨⟨call, self, d⟩, R, ?_, ?_, fun _ hpan => hpan⟩
    · exact Satisfies.mono
        (sepConj_mono_left
          (poll_pre_entails fun hfiles' ⟨hfl, hsym, hx0, hx8, haddr'⟩ hinv' =>
            ⟨⟨hfl, hsym⟩, hx0, hx8, hname ▸ hinv'.nameLt, haddr' ▸ hinv'.textLt, hinv'.pathLt,
              haddr' ▸ hinv'.pathOk, fun bs hbs => by
                rw [hfiles', haddr'] at hbs
                obtain ⟨bs₀, hget₀, hwf₀⟩ := hinv'.getOk
                rw [hget₀] at hbs
                cases hbs
                exact hwf₀⟩))
        hpre
    · intro sf hpost
      refine loadPoll_post_sat hinv (fun gr ans ⟨⟨hgr, htr⟩, hans⟩ => ?_) hpost
      rw [hfiles, haddr] at hgr
      obtain ⟨bs₀, hget₀, _⟩ := hinv.getOk
      rw [hget₀] at hgr
      subst hgr
      refine ⟨⟨⟨bs₀, haddr.symm ▸ hget₀, hans⟩, by
        show sf.trace = s0.trace ++ []
        rw [List.append_nil]
        exact htr⟩, ?_⟩
      cases bs₀ with
      | nil =>
        have hans' : ans = .ok none := hans
        subst hans'
        exact Entails.refl _
      | cons b bs =>
        obtain ⟨r, hans', _, hsc⟩ := hans
        subst hans'
        exact Entails.pure_right hsc (Entails.refl _)
  · -- loadFutDrop
    exact cliIdFutDrop_ok_ext
  · -- storeShim
    have h := StoreShim.sessStoreShim_ok_of_deps hC hs3 hb
    rw [cliSessStoreShim_fnAddr] at h
    exact h
  · -- storePoll
    have hGrow := GrowOne.growOneDir_ok_x hC (Nat.le_refl growOneDirNeed) hb
    have hPut := Put.dirPut_ok_of_deps hC hBcmp hGrow (Nat.le_refl dirPutNeed) hb
    have h := StorePollX.sessStorePoll_ok_of_depsX hC hAddr hSer hPut hs4 hb
    rw [cliSessStorePoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨call, self, d⟩ R s0 hpre
    obtain ⟨_, ⟨_, _, hrec, haddr⟩, hinv⟩ := extract_storePoll_pure hpre
    have hname : call.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    refine ⟨⟨call, self, d⟩, R, ?_, ?_, fun _ hpan => hpan⟩
    · exact Satisfies.mono
        (sepConj_mono_left
          (storePoll_pre_entails fun _ ⟨hx0, hx8, hrec', _⟩ hinv' =>
            ⟨hx0, hx8, hname ▸ hinv'.nameLt, hrec'.2, hinv'.changedLt.1⟩))
        hpre
    · intro sf hpost
      exact storePoll_post_sat
        (fun htr => ⟨rfl, by
          show sf.trace = s0.trace ++ []
          rw [List.append_nil]
          exact htr⟩)
        (cliSessionStoreSpec_storeUpdate_inv (ans := .ok ()) hinv haddr hrec)
        rfl rfl hpost
  · -- storeFutDrop
    exact cliIdFutDrop_ok_ext

theorem cliSessKitOkSE_ext_of_hooks {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordDeserializeName)
      (sessDeserializeExtSpec Scope A img))
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((Proofs.libsignal.Hooks2.serializeCanonSpecX A).inImage img))
    (hs1 : loadShimNeed ≤ s1) (hs2 : loadPollNeed readStk ≤ s2)
    (hs3 : storeShimNeed ≤ s3) (hs4 : storePollNeedX ≤ s4) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliSessionStoreSpec A img.base rd F0 cliWrOk Scope peer s1 s2 s3 s4)
      Scope E2E.Record.encodeRecord ext :=
  cliSessKitOkSE_of_deps himg hh.alloc hh.memcpyRO hh.bcmp hh.fs hRead hDeser hSer
    hs1 hs2 hs3 hs4

end CryptoVerification.SignalSession.Cli.KitInst.SessKit
