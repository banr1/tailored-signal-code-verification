/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed CLI `KyberPreKeyFiles` Mark-Side Store Specification

Relocatable `[LibsignalPlacement]` instantiation of `cliKpkStoreSpec` and its mark-poll bridge.
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs

private theorem cliMarkErr_of_parts (A : RustAlloc) (out : BitVec 64)
    (ans : KpkMarkAns)
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
    { ans := ans
      ne_ok := hne
      cap := cap
      ptr := ptr
      len := BitVec.ofNat 64 bs.length
      w4 := w4
      w5 := w5 }
  refine Entails.sepExists_right (.error e) (Entails.pure_right rfl ?_)
  dsimp only [unitSpePollOutAt, speErrAt, speWordsAt, cliKpkMarkErrSpec, e]
  have h10 : out + 8#64 + 8#64 = out + 0x10#64 := by bv_omega
  have h18 : out + 8#64 + 16#64 = out + 0x18#64 := by bv_omega
  rw [h10, h18]
  set bufHeap : SepProp :=
    if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
  set w0Term : SepProp :=
    out ↦₆₄ match ans with | .reused => speWord 24 | _ => speWord 1
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

private theorem cliKpkMarkOut_entails (A : RustAlloc) (out : BitVec 64) (a : KpkMarkAns) :
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
      (cliMarkErr_of_parts A out .readErr bs p
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
      (cliMarkErr_of_parts A out .malformed bs w4 w5 emp (Entails.refl _) (by nofun))
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
      (cliMarkErr_of_parts A out .reused bs w4 w5 emp (Entails.refl _) (by nofun))

/-- Relocatable `KyberPreKeyStoreSpec` for CLI `KyberPreKeyFiles` at base `0#64`. -/
abbrev cliKpkStoreSpecPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (kid ksid : BitVec 32) (kbk : PublicKey)
    (G : CliKpkGetSide) (getShimStk getPollStk markShimStk markPollStk : Nat)
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32) :
    KyberPreKeyStoreSpec A 0#64 :=
  { cliKpkStoreSpec A 0#64 rd F0 pathOk kid ksid kbk G
      getShimStk getPollStk markShimStk markPollStk hGetBox hMarkBox with
    kpk_vt := lsρ cliKyberPreKeyVtSym
    getShimOff := lsmpl.base 611
    getFutVtOff := lsρ kpkGetFutVtSym
    getPollOff := lsmpl.base 576
    getFutDropOff := lsDropOffPlaced
    markShimOff := lsmpl.base 613
    markFutVtOff := lsρ kpkMarkFutVtSym
    markPollOff := lsmpl.base 578
    markFutDropOff := lsDropOffPlaced
    getFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    markFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

/-- Lift `kpkMarkPollSpecPlaced` to `withLsCodeRoLoaded lsmpl (kitKpkMarkPollSpecE ...)`. -/
theorem cliKpkStoreSpecPlaced_markPoll [LibsignalPlacement] {A : RustAlloc} {prog : Program}
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (hhop : subroutine_ok prog (lsmpl.base 578)
      (kpkMarkPollSpecPlaced rd pathOk A s4)) :
    subroutine_ok prog (lsmpl.base 578)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (kitKpkMarkPollSpecE (cliKpkStoreSpecPlaced A rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
          hGetBox hMarkBox))) := by
  let kit := cliKpkStoreSpecPlaced A rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre1⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  have hpre2 :
      s0.mem ⊨ ⌜s0.fs.files = F0⌝ ∗ ((kitKpkMarkPollSpec kit).pre
        (⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0) s0 ∗ R) := by
    change s0.mem ⊨ (⌜s0.fs.files = F0⌝ ∗ (kitKpkMarkPollSpec kit).pre
      (⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0) s0) ∗ R at hpre1
    simpa only [sepConj_assoc] using hpre1
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨hfiles, hpre3⟩ := hpre2
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        (kid' = kid ∧ ksid' = ksid ∧ kbk' = kbk)⌝ ∗
      kpkMarkBoxAt fut self baseKeyA kid' ksid' 0#8 ∗
      (⌜CliKpkInv rd F0 pathOk kid ksid kbk st0⌝ ∗ dirAt A self st0.oneTime ∗
        dirAt A (self + 0x28#64) st0.lastResort) ∗
      memRegion out 48 ∗
      (baseKeyA ↦ₛ kbk'.bytes.toList) ∗
      A.pool ∗ stackAt s0.sp s4) ∗ R at hpre3
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
  obtain ⟨⟨_, hx0, hx8, hxid, hxsid, hxbk⟩, hpre4⟩ := hpre3
  rw [hxid, hxsid, hxbk] at hpre4 ⊢
  have hpre5 :
      s0.mem ⊨ ⌜CliKpkInv rd F0 pathOk kid ksid kbk st0⌝ ∗
        (kpkMarkBoxAt fut self baseKeyA kid ksid 0#8 ∗
          dirAt A self st0.oneTime ∗ dirAt A (self + 0x28#64) st0.lastResort ∗
          (baseKeyA ↦ₛ kbk.bytes.toList) ∗ memRegion out 48 ∗
          A.pool ∗ stackAt s0.sp s4 ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre4
  rw [satisfies_pure_sepConj] at hpre5
  obtain ⟨hinv, hspatial⟩ := hpre5
  let xg : KpkMarkPollGhost := ⟨fut, out, self, baseKeyA, kid, ksid, kbk, st0⟩
  have hpre_hop : s0.mem ⊨ (kpkMarkPollSpecPlaced rd pathOk A s4).pre xg s0 ∗ R := by
    dsimp only [kpkMarkPollSpecPlaced, LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hinv.nameOk, hinv.baseOk, hfiles ▸ hinv.seenOk,
      hinv.oneLt.1, hinv.lastLt.1⟩, ?_⟩
    simpa only [sepConj_assoc] using hspatial
  refine subroutine_ok.mono_outcome hhop xg R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    show (kpkMarkPollSpecPlaced rd pathOk A s4).post xg s0 sf ⊢
      (kitKpkMarkPollSpec kit).post (⟨fut, out, self, baseKeyA, kid, ksid, kbk⟩, st0) s0 sf
    dsimp only [kpkMarkPollSpecPlaced, kitKpkMarkPollSpec, kit, cliKpkStoreSpecPlaced,
      cliKpkStoreSpec, cliKpkStoreAt, kpkMarkPollOutAt, xg]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun res => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hres, htr⟩ => ?_
    rw [hfiles] at hres
    subst hres
    set m := kpkMarkOf rd F0 st0 kid ksid kbk
    refine Entails.trans
      (Entails.of_eq (show _ =
        kpkMarkOutAt A out m.1 ∗
          (dirAt A self m.2.oneTime ∗ dirAt A (self + 0x28#64) m.2.lastResort ∗
            kpkMarkBoxAt fut self baseKeyA kid ksid 1#8 ∗
            (baseKeyA ↦ₛ kbk.bytes.toList) ∗ A.pool ∗ stackAt s0.sp s4) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (cliKpkMarkOut_entails A out m.1)) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ans => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hrel => ?_
    refine Entails.sepExists_right ans ?_
    refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr⟩ ?_
    exact Entails.trans (Entails.pure_right hinv.mark (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

end CryptoVerification.SignalSession.Cli.KitInst
