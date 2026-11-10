/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitE
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitStk
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOneX
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.PreKeyKitOk
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShims

/-!
# CLI KyberPreKey `StoreKitOkImgE` Bundle

Extends `KyberMarkFit.CliKpkInv` with `get_kyber_pre_key` preconditions (`CliKpkInvFull`), proves
closure under `kpkMarkOf`, defines `cliKpkStoreSpecFull`, and assembles `KyberPreKeyStoreKitOkImgE`.
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

/-! ## 1. Full Kyber Store Invariant (`get_kyber_pre_key` + `mark_kyber_pre_key_used`) -/

private theorem keyName_ne_baseKeysName (id : BitVec 32) : keyName id ≠ baseKeysName id := by
  intro h
  have hlen := congrArg List.length h
  have h10 : (utf8 ".base-keys").length = 10 := by decide +kernel
  rw [baseKeysName, List.length_append, h10] at hlen
  omega

/-- Full Kyber store invariant combining `CliKpkInv` (`mark_kyber_pre_key_used` preconditions) with
`kpkGetPollSpec`'s `lastResort` name bound and `< 2^32` file-size bounds on both directories. -/
structure CliKpkInvFull (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (g : KyberGhost) : Prop where
  markInv : CliKpkInv rd F0 pathOk kid ksid kbk g
  lastNameOk : PkNameOk pathOk g.lastResort kid
  oneSizeOk : PkSizeOk rd F0 g.oneTime kid
  lastSizeOk : PkSizeOk rd F0 g.lastResort kid

theorem CliKpkInvFull.mark {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey} {g : KyberGhost}
    (h : CliKpkInvFull rd F0 pathOk kid ksid kbk g) :
    CliKpkInvFull rd F0 pathOk kid ksid kbk (kpkMarkOf rd F0 g kid ksid kbk).2 := by
  refine ⟨h.markInv.mark, ?_, ?_, ?_⟩
  · unfold kpkMarkOf
    rcases g.oneTime.get rd F0 (keyName kid) with _ | _ | ⟨_, _⟩
    · exact h.lastNameOk
    · rcases g.lastResort.get rd F0 (baseKeysName kid) with _ | seen
      · exact h.lastNameOk
      · dsimp only
        split
        · exact h.lastNameOk
        · split <;> exact h.lastNameOk
    · exact h.lastNameOk
  · unfold kpkMarkOf
    rcases g.oneTime.get rd F0 (keyName kid) with _ | _ | ⟨_, _⟩
    · exact h.oneSizeOk
    · rcases g.lastResort.get rd F0 (baseKeysName kid) with _ | seen
      · exact h.oneSizeOk
      · dsimp only
        split
        · exact h.oneSizeOk
        · split <;> exact h.oneSizeOk
    · intro bs hbs
      rw [DirGhost.get_put_self] at hbs
      cases hbs
      decide
  · unfold kpkMarkOf
    rcases g.oneTime.get rd F0 (keyName kid) with _ | _ | ⟨_, _⟩
    · exact h.lastSizeOk
    · rcases g.lastResort.get rd F0 (baseKeysName kid) with _ | seen
      · exact h.lastSizeOk
      · dsimp only
        split
        · exact h.lastSizeOk
        · split
          · exact h.lastSizeOk
          · intro bs hbs
            rw [DirGhost.get_put_ne rd F0 g.lastResort (keyName_ne_baseKeysName kid)] at hbs
            exact h.lastSizeOk bs hbs
    · exact h.lastSizeOk

def cliKpkStoreAtFull (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (kid ksid : BitVec 32) (kbk : PublicKey)
    (self : BitVec 64) (g : KyberGhost) : SepProp :=
  ⌜CliKpkInvFull rd F0 pathOk kid ksid kbk g⌝ ∗ dirAt A self g.oneTime ∗
    dirAt A (self + 0x28#64) g.lastResort

/-- `cliKyberPreKeyStoreSpec` with `storeAt := cliKpkStoreAtFull`, sharing all vtable, box, error,
and relation fields definitionally with `cliKyberPreKeyStoreSpec`. -/
def cliKpkStoreSpecFull (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (kid ksid : BitVec 32) (kbk : PublicKey)
    (getShimStk getPollStk markShimStk markPollStk : Nat) : KyberPreKeyStoreSpec A b :=
  { cliKyberPreKeyStoreSpec A b rd F0 pathOk kid ksid kbk
      getShimStk getPollStk markShimStk markPollStk with
    storeAt := cliKpkStoreAtFull A rd F0 pathOk kid ksid kbk }

theorem cliKpkStoreSpecFull_quiet {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (s1 s2 s3 s4 : Nat) :
    (cliKpkStoreSpecFull A b rd F0 pathOk kid ksid kbk s1 s2 s3 s4).Quiet :=
  cliKpkStoreSpec_quiet (A := A) (b := b) rd F0 pathOk kid ksid kbk
    (cliKpkGetSide A rd F0 pathOk kid) s1 s2 s3 s4 pkBoxAt_memRegion kpkMarkBoxAt_memRegion

theorem cliKpkStoreSpecFull_vtablesOk {A : RustAlloc} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (s1 s2 s3 s4 : Nat) :
    KyberPreKeyVtablesOk img
      (cliKpkStoreSpecFull A img.base rd F0 pathOk kid ksid kbk s1 s2 s3 s4) where
  getSlot := cliKpkGetSlot_ok himg
  markSlot := cliKpkMarkSlot_ok himg
  getFutDrop := (cliKpkGetFutVt_ok himg).drop
  getFutSize := (cliKpkGetFutVt_ok himg).size
  getFutAlign := (cliKpkGetFutVt_ok himg).align
  getFutPoll := (cliKpkGetFutVt_ok himg).poll
  markFutDrop := (cliKpkMarkFutVt_ok himg).drop
  markFutSize := (cliKpkMarkFutVt_ok himg).size
  markFutAlign := (cliKpkMarkFutVt_ok himg).align
  markFutPoll := (cliKpkMarkFutVt_ok himg).poll

theorem cliKpkStoreSpecFull_getRel_error_iff {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (s1 s2 s3 s4 : Nat)
    (g : KyberGhost) (id : BitVec 32) :
    (∃ e, (cliKpkStoreSpecFull A b rd F0 pathOk kid ksid kbk s1 s2 s3 s4).getRel g id (.error e)) ↔
      g.get rd F0 id = .error () :=
  cliKpk_getRel_error_iff (A := A) rd F0 pathOk kid g id

theorem cliKpkStoreSpecFull_getRel_ok_iff {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (s1 s2 s3 s4 : Nat)
    (g : KyberGhost) (id : BitVec 32) (r : KyberPreKeyRecord) :
    (cliKpkStoreSpecFull A b rd F0 pathOk kid ksid kbk s1 s2 s3 s4).getRel g id (.ok r) ↔
      g.get rd F0 id = .ok r :=
  cliKpk_getRel_ok_iff (A := A) rd F0 pathOk kid g id r

/-! ## 2. Sret Layout Bridge for `mark_kyber_pre_key_used` -/

private theorem cliMarkErr_of_parts' (A : RustAlloc) (out : BitVec 64) (ans : KpkMarkAns)
    (bs : List (BitVec 8)) (w4 w5 : BitVec 64) (tail : SepProp)
    (htail : tail ⊢ match ans with
      | .readErr => ⌜w5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗ (w4 ↦ᵣ utf8 "read")
      | _ => emp)
    (hne : ans ≠ .ok) :
    ((out ↦₆₄ match ans with | .reused => speWord 24 | _ => speWord 1) ∗
      vecU8 A (out + 8#64) bs ∗
      ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5) ∗ tail) ⊢
    ∃∗ r : Except CliKpkMarkErr Unit,
      ⌜(match r with | .ok () => ans = .ok | .error e => ans = e.ans)⌝ ∗
        unitSpePollOutAt (cliKpkMarkErrSpec A) out r := by
  unfold vecU8 vecU8At vecHeader
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun cap => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun ptr => ?_
  let e : CliKpkMarkErr :=
    { ans := ans, ne_ok := hne, cap := cap, ptr := ptr,
      len := BitVec.ofNat 64 bs.length, w4 := w4, w5 := w5 }
  refine Entails.sepExists_right (.error e) (Entails.pure_right rfl ?_)
  dsimp only [unitSpePollOutAt, speErrAt, speWordsAt, cliKpkMarkErrSpec, e]
  have h10 : out + 8#64 + 8#64 = out + 0x10#64 := by bv_omega
  have h18 : out + 8#64 + 16#64 = out + 0x18#64 := by bv_omega
  rw [h10, h18]
  set bufHeap : SepProp :=
    if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
  set w0Term : SepProp := out ↦₆₄ match ans with | .reused => speWord 24 | _ => speWord 1
  have hvec :
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ bufHeap ⊢
        ∃∗ bs' : List (BitVec 8),
          ⌜BitVec.ofNat 64 bs'.length = BitVec.ofNat 64 bs.length ∧
            bs'.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs') ∗
             memRegion (ptr + BitVec.ofNat 64 bs'.length) (cap.toNat - bs'.length)) := by
    refine Entails.pure_left fun ⟨hlen, hcap, hptr⟩ => ?_
    refine Entails.sepExists_right bs ?_
    exact Entails.pure_right ⟨rfl, hlen, hcap, hptr⟩ (Entails.refl _)
  refine Entails.trans (Entails.of_eq (show _ =
    ((w0Term ∗ ((out + 0x08#64) ↦₆₄ cap) ∗ ((out + 0x10#64) ↦₆₄ ptr) ∗
        ((out + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5)) ∗
      ((⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ bufHeap) ∗ tail)) by ac_rfl)) ?_
  cases ans <;> exact sepConj_mono_right (sepConj_mono hvec htail)

private theorem cliKpkMarkOut_entails' (A : RustAlloc) (out : BitVec 64) (a : KpkMarkAns) :
    kpkMarkOutAt A out a ⊢
      ∃∗ ans : Except CliKpkMarkErr Unit,
        ⌜(match ans with | .ok () => a = .ok | .error e => a = e.ans)⌝ ∗
          unitSpePollOutAt (cliKpkMarkErrSpec A) out ans := by
  rcases a with _ | _ | _ | _
  · exact Entails.sepExists_right (.ok ()) (Entails.pure_right rfl (Entails.refl _))
  · dsimp only [kpkMarkOutAt, speAt, strRefAt]
    have e1 : out + asm64% spePayloadOff = out + 8#64 := by bv_omega
    have e2 : out + asm64% speInvalidStateFnOff = out + 0x20#64 := by bv_omega
    have e3 : out + 0x20#64 + asm64% boxSliceLenOff = out + 0x28#64 := by bv_omega
    rw [e1, e2, e3, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun p => ?_
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (cliMarkErr_of_parts' A out .readErr bs p
        (BitVec.ofNat 64 (utf8 "read").length) (p ↦ᵣ utf8 "read")
        (Entails.pure_right rfl (Entails.refl _)) (by nofun))
  · dsimp only [kpkMarkOutAt, strSpeAt]
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
          (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w4 => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    rw [← sepConj_emp ((out + 0x28#64) ↦₆₄ w5)]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (cliMarkErr_of_parts' A out .malformed bs w4 w5 emp (Entails.refl _) (by nofun))
  · dsimp only [kpkMarkOutAt, strSpeAt]
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
          (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w4 => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    rw [← sepConj_emp ((out + 0x28#64) ↦₆₄ w5)]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (cliMarkErr_of_parts' A out .reused bs w4 w5 emp (Entails.refl _) (by nofun))

/-! ## 3. `KyberPreKeyStoreKitOkImgE` Assembly -/

/-- Generic `KyberPreKeyStoreKitOkImgE` assembly for `cliKpkStoreSpecFull`, leaving only
`hKpkDec` (`decode_kyber_pre_key`) and the stack bounds `hs1..hs4` open. -/
theorem cliKpkKitOkImgE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {kid ksid : BitVec 32} {kbk : PublicKey}
    {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hKpkDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeKyberPreKeySpec A img))
    (hs1 : (cliKitStk ⟨readStk⟩).kpkGetShim ≤ s1)
    (hs2 : (cliKitStk ⟨readStk⟩).kpkGetPoll ≤ s2)
    (hs3 : (cliKitStk ⟨readStk⟩).kpkMarkShim ≤ s3)
    (hs4 : (cliKitStk ⟨readStk⟩).kpkMarkPoll ≤ s4) :
    KyberPreKeyStoreKitOkImgE img
      (cliKpkStoreSpecFull A img.base rd F0 cliWrOk kid ksid kbk s1 s2 s3 s4) ext := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := base_aligned himg
  have hC : AllocContractsX img A ext := hh.alloc
  have hDecimal := Decimal.decimal_ok_of_deps
    (reserve_ok hh (Nat.le_refl doReserveStackX)) (Nat.le_refl SessKit.decNeed) hb
  have hGet := Get.dirGet_ok_of_deps (pathOk := cliWrOk) himg (fun _ hp => hp.2) hC
    hh.memcpyRO hh.bcmp (path_ok himg hh (Nat.le_refl pathNeed))
    hRead hh.fs (Nat.le_refl (RunBudgets.dirGetNeed ⟨readStk⟩)) hb
  have hGrow := GrowOne.growOneDir_ok_x hC (Nat.le_refl SessKit.growOneDirNeed) hb
  have hPut := Put.dirPut_ok_of_deps hC hh.bcmp hGrow (Nat.le_refl SessKit.dirPutNeed) hb
  refine ⟨?_, ?_, cliIdFutDrop_inImage_ext, ?_, ?_, cliIdFutDrop_inImage_ext⟩
  · -- getShim
    have h := PkShims.kpkGetShim_ok_of_deps hC hs1 hb
    rw [cliKpkGetShim_fnAddr] at h
    exact pkShim_conseq h
  · -- getPoll
    have h := KpkGetPoll.kpkGetPoll_ok_of_deps hC hDecimal hGet hKpkDec hh.fs hs2 hb
    rw [cliKpkGetPoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨⟨fut, out, self, id⟩, st0⟩ R (s0 : State) hpre
    dsimp only [kitKpkGetPollSpecE, Spec.inImage, withEnvPre, kitKpkGetPollSpec,
      cliKpkStoreSpecFull, cliKyberPreKeyStoreSpec, cliKpkStoreSpec, cliKpkGetSide,
      cliKpkStoreAtFull] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          id = kid⌝ ∗
        (⌜CliKpkInvFull rd F0 cliWrOk kid ksid kbk st0⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt A self st0.oneTime ∗
          dirAt A (self + 0x28#64) st0.lastResort ∗ memRegion out 88 ∗
          A.pool ∗ stackAt s0.sp s2 ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, hid⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
    subst hid
    have hm_hop : s0.mem ⊨ (kpkGetPollSpec rd cliWrOk A img s2).pre ⟨fut, out, self, id, st0⟩ s0 ∗ R := by
      dsimp only [kpkGetPollSpec, Spec.inImage]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk cliWrOk st0.oneTime id ∧ PkNameOk cliWrOk st0.lastResort id ∧
            PkSizeOk rd s0.fs.files st0.oneTime id ∧ PkSizeOk rd s0.fs.files st0.lastResort id⌝ ∗
          (pkBoxAt fut self id 0#8 ∗ dirAt A self st0.oneTime ∗
            dirAt A (self + 0x28#64) st0.lastResort ∗ memRegion out 88 ∗
            A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hinv.markInv.nameOk, hinv.lastNameOk,
          hfiles ▸ hinv.oneSizeOk, hfiles ▸ hinv.lastSizeOk⟩, hsp⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨fut, out, self, id, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
    intro sf hpost
    dsimp only [kpkGetPollSpec, Spec.inImage] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨pa, ⟨hpa, htr⟩, hm⟩ := hpost
    rw [hfiles] at hpa; subst hpa
    have hm' := Satisfies.mono
      (sepConj_mono_left (kpkAnsAt_entails_pollOut A img.base rd F0 cliWrOk id ksid kbk
        s1 s2 s3 s4 pkBoxAt_memRegion kpkMarkBoxAt_memRegion st0 id out)) hm
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hm'
    obtain ⟨ans, hrel, hm'⟩ := hm'
    dsimp only [kitKpkGetPollSpecE, Spec.inImage, withEnvPre, kitKpkGetPollSpec]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ans, ?_⟩
    have hstore :
        (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id ksid kbk s1 s2 s3 s4).storeAt self
          ((cliKpkStoreSpecFull A img.base rd F0 cliWrOk id ksid kbk s1 s2 s3 s4).getUpdate st0 id ans) =
        (⌜CliKpkInvFull rd F0 cliWrOk id ksid kbk st0⌝ ∗
          dirAt A self st0.oneTime ∗ dirAt A (self + 0x28#64) st0.lastResort) := rfl
    have hstk :
        (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id ksid kbk s1 s2 s3 s4).getPollStack = s2 := rfl
    have hbox :
        (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id ksid kbk s1 s2 s3 s4).getBoxAt fut self id 1#8 =
        pkBoxAt fut self id 1#8 := rfl
    have hout :
        kpkGetPollOutAt (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id ksid kbk s1 s2 s3 s4) out ans =
        kpkGetPollOutAt
          (cliKpkStoreSpec A img.base rd F0 cliWrOk id ksid kbk (cliKpkGetSide A rd F0 cliWrOk id)
            s1 s2 s3 s4 pkBoxAt_memRegion kpkMarkBoxAt_memRegion)
          out ans := by cases ans <;> rfl
    rw [hstore, hstk, hbox, hout]
    have hgoal : sf.mem ⊨
        ⌜(cliKpkStoreSpecFull A img.base rd F0 cliWrOk id ksid kbk s1 s2 s3 s4).getRel st0 id ans ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliKpkInvFull rd F0 cliWrOk id ksid kbk st0⌝ ∗
          (kpkGetPollOutAt
              (cliKpkStoreSpec A img.base rd F0 cliWrOk id ksid kbk (cliKpkGetSide A rd F0 cliWrOk id)
                s1 s2 s3 s4 pkBoxAt_memRegion kpkMarkBoxAt_memRegion)
              out ans ∗
            pkBoxAt fut self id 1#8 ∗ dirAt A self st0.oneTime ∗
            dirAt A (self + 0x28#64) st0.lastResort ∗ A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  · -- markShim
    have h := PkShims.kpkMarkShim_ok_of_deps hC hs3 hb
    rw [cliKpkMarkShim_fnAddr] at h
    exact kpkMarkShim_conseq h
  · -- markPoll
    have h := KpkMarkPoll.kpkMarkPoll_ok_of_deps himg hC hh.bcmp hDecimal hGet hPut hh.fs hs4 hb
    rw [cliKpkMarkPoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨⟨fut, out, self, baseKeyA, id, sid, bk⟩, st0⟩ R (s0 : State) hpre
    dsimp only [kitKpkMarkPollSpecE, Spec.inImage, withEnvPre, kitKpkMarkPollSpec,
      cliKpkStoreSpecFull, cliKyberPreKeyStoreSpec, cliKpkStoreSpec, cliKpkStoreAtFull] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          (id = kid ∧ sid = ksid ∧ bk = kbk)⌝ ∗
        (⌜CliKpkInvFull rd F0 cliWrOk kid ksid kbk st0⌝ ∗
        (kpkMarkBoxAt fut self baseKeyA id sid 0#8 ∗ dirAt A self st0.oneTime ∗
          dirAt A (self + 0x28#64) st0.lastResort ∗ memRegion out 48 ∗
          (baseKeyA ↦ₛ bk.bytes.toList) ∗ A.pool ∗ stackAt s0.sp s4 ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, hid, hsid, hbk⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
    subst hid; subst hsid; subst hbk
    have hm_hop : s0.mem ⊨
        (kpkMarkPollSpec rd cliWrOk A img s4).pre ⟨fut, out, self, baseKeyA, id, sid, bk, st0⟩ s0 ∗ R := by
      dsimp only [kpkMarkPollSpec, Spec.inImage]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            PkNameOk cliWrOk st0.oneTime id ∧ KpkBaseKeysOk cliWrOk st0.lastResort id ∧
            KpkSeenOk rd s0.fs.files st0.lastResort id sid bk ∧
            st0.oneTime.changed.length < 2 ^ 32 ∧ st0.lastResort.changed.length < 2 ^ 32⌝ ∗
          (kpkMarkBoxAt fut self baseKeyA id sid 0#8 ∗ dirAt A self st0.oneTime ∗
            dirAt A (self + 0x28#64) st0.lastResort ∗ (baseKeyA ↦ₛ bk.bytes.toList) ∗
            memRegion out 48 ∗ A.pool ∗ stackAt s0.sp s4 ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hinv.markInv.nameOk, hinv.markInv.baseOk,
          hfiles ▸ hinv.markInv.seenOk, hinv.markInv.oneLt.1, hinv.markInv.lastLt.1⟩,
          Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hsp⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨fut, out, self, baseKeyA, id, sid, bk, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
    intro sf hpost
    dsimp only [kpkMarkPollSpec, Spec.inImage] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨res, ⟨hres, htr⟩, hm⟩ := hpost
    rw [hfiles] at hres; subst hres
    set m := kpkMarkOf rd F0 st0 id sid bk
    have hm' := Satisfies.mono (sepConj_mono_left (cliKpkMarkOut_entails' A out m.1)) hm
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hm'
    obtain ⟨ans, hrel, hm'⟩ := hm'
    dsimp only [kitKpkMarkPollSpecE, Spec.inImage, withEnvPre, kitKpkMarkPollSpec]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ans, ?_⟩
    have hstore :
        (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id sid bk s1 s2 s3 s4).storeAt self
          ((cliKpkStoreSpecFull A img.base rd F0 cliWrOk id sid bk s1 s2 s3 s4).markUpdate
            st0 id sid bk ans) =
        (⌜CliKpkInvFull rd F0 cliWrOk id sid bk m.2⌝ ∗
          dirAt A self m.2.oneTime ∗ dirAt A (self + 0x28#64) m.2.lastResort) := rfl
    have hout :
        kpkMarkPollOutAt (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id sid bk s1 s2 s3 s4) out ans =
        unitSpePollOutAt (cliKpkMarkErrSpec A) out ans := rfl
    have hstk :
        (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id sid bk s1 s2 s3 s4).markPollStack = s4 := rfl
    have hbox :
        (cliKpkStoreSpecFull A img.base rd F0 cliWrOk id sid bk s1 s2 s3 s4).markBoxAt
          fut self baseKeyA id sid 1#8 =
        kpkMarkBoxAt fut self baseKeyA id sid 1#8 := rfl
    rw [hstore, hout, hstk, hbox]
    have hgoal : sf.mem ⊨
        ⌜(cliKpkStoreSpecFull A img.base rd F0 cliWrOk id sid bk s1 s2 s3 s4).markRel
            st0 id sid bk ans ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliKpkInvFull rd F0 cliWrOk id sid bk m.2⌝ ∗
          (unitSpePollOutAt (cliKpkMarkErrSpec A) out ans ∗
            dirAt A self m.2.oneTime ∗ dirAt A (self + 0x28#64) m.2.lastResort ∗
            kpkMarkBoxAt fut self baseKeyA id sid 1#8 ∗
            (baseKeyA ↦ₛ bk.bytes.toList) ∗ A.pool ∗ stackAt s0.sp s4 ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hinv.mark, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
