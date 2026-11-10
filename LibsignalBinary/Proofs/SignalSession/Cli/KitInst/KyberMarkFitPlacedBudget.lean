/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import ProofLib.SepLogic.WP -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Placed Budgeted `KyberPreKeyFiles` Store Kit

Establishes the sret entailment `kpkMarkOutAt ⊢ unitSpePollOutAt`, the budget-threaded mark-poll
bridge on Block `578`, shim and `futDrop` contracts on Blocks `611`, `613`, and `547`, and full
`KyberPreKeyStoreKitPlacedOk` assembly for `cliKpkStoreSpecPlaced`.
-/

@[expose] public section
set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt speWord strRefAt utf8)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles KyberMarkShimCall PreKeyShimCall extract_withLsCodeRoLoaded kpkMarkPollOutAt
   ls_subroutine_ok_rocl_of_block speErrAt speWordsAt unitSpePollOutAt
   withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.SignalSession (lsDropOffPlaced_eq)
open CryptoVerification.SignalSession.Cli
  (KpkMarkAns KpkMarkPollGhost KyberGhost ReadRule dirAt kpkGetFutVtSym
   kpkMarkBoxAt kpkMarkFutVtSym kpkMarkOf kpkMarkOutAt pkBoxAt strSpeAt)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPC_547 blkPl_547 lsProg_547 lsProg_576 lsProg_578 lsProg_611 lsProg_613)
open CryptoVerification.SignalSession.Cli.KitInst
  (CliKpkGetSide CliKpkInv CliKpkMarkErr cliKpkMarkErrSpec cliKpkStoreAt
   cliKpkStoreSpec cliKpkStoreSpecPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
  (KyberPreKeyStoreBudgetEnv kitKpkGetPollSpecE kitKpkGetShimSpec kitKpkMarkPollSpec
   kitKpkMarkPollSpecE kitKpkMarkShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (KyberPreKeyStoreKitPlacedOk ls_futDrop_ok_of_block)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced kpkMarkPollSpecPlaced kpkMarkShimSpecPlaced pkShimSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget
  (kpkGetShim_placed_ok_of_deps kpkMarkShim_placed_ok_of_deps)

/-! ## Sret layout entailment -/

private theorem cliMarkErr_of_parts (A : RustAlloc) (out : BitVec 64)
    (ans : KpkMarkAns)
    (bs : List (BitVec 8)) (w4 w5 : BitVec 64) (tail : SepProp)
    (htail : tail ⊢ match ans with
      | .readErr => ⌜w5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗ (w4 ↦ᵣ utf8 "read")
      | _ => emp)
    (hne : ans ≠ .ok) :
    ((out ↦₆₄ match ans with | .reused => speWord 24 | _ => speWord 1) ∗
      vecU8 A (out + 8#64) bs ∗
      ((out + 32#64) ↦₆₄ w4) ∗ ((out + 40#64) ↦₆₄ w5) ∗ tail) ⊢
    ∃∗ r : Except CliKpkMarkErr Unit,
      ⌜(match r with | .ok () => ans = .ok | .error e => ans = e.ans)⌝ ∗
        unitSpePollOutAt (cliKpkMarkErrSpec A) out r := by
  unfold vecU8 vecU8At
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun cap => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun ptr => ?_
  rw [sepConj_left_comm (vecHeader (out + 8#64) cap ptr (BitVec.ofNat 64 bs.length)),
      sepConj_assoc (⌜_⌝), sepConj_left_comm (out ↦₆₄ _)]
  refine Entails.pure_left fun ⟨hlen, hcap, hptr⟩ => ?_
  unfold vecHeader
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
  have h10 : out + 8#64 + 8#64 = out + 16#64 := by bv_omega
  have h18 : out + 8#64 + 16#64 = out + 24#64 := by bv_omega
  rw [h10, h18]
  set bufHeap : SepProp :=
    if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
  set w0Term : SepProp :=
    out ↦₆₄ match ans with | .reused => speWord 24 | _ => speWord 1
  have hvec :
      bufHeap ⊢
        ∃∗ bs' : List (BitVec 8),
          ⌜BitVec.ofNat 64 bs'.length = BitVec.ofNat 64 bs.length ∧
            bs'.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs') ∗
             memRegion (ptr + BitVec.ofNat 64 bs'.length) (cap.toNat - bs'.length)) :=
    Entails.sepExists_right bs (Entails.pure_right ⟨rfl, hlen, hcap, hptr⟩ (Entails.refl _))
  refine Entails.trans (Entails.of_eq (show _ =
    ((w0Term ∗ ((out + 8#64) ↦₆₄ cap) ∗ ((out + 16#64) ↦₆₄ ptr) ∗
        ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((out + 32#64) ↦₆₄ w4) ∗ ((out + 40#64) ↦₆₄ w5)) ∗
      (bufHeap ∗ tail)) by
    sep_ac_rfl)) ?_
  cases ans <;> exact sepConj_mono_right (sepConj_mono hvec htail)

/-- `kpkMarkOutAt A out a` entails `unitSpePollOutAt (cliKpkMarkErrSpec A) out ans` with matching
answer projection. -/
theorem cliKpkMarkOut_entails (A : RustAlloc) (out : BitVec 64) (a : KpkMarkAns) :
    kpkMarkOutAt A out a ⊢
      ∃∗ ans : Except CliKpkMarkErr Unit,
        ⌜(match ans with | .ok () => a = .ok | .error e => a = e.ans)⌝ ∗
          unitSpePollOutAt (cliKpkMarkErrSpec A) out ans := by
  rcases a with _ | _ | _ | _
  · exact Entails.sepExists_right (.ok ()) (Entails.pure_right rfl (Entails.refl _))
  · dsimp only [kpkMarkOutAt, speAt, strRefAt]
    have e3 : out + 32#64 + 8#64 = out + 40#64 := by bv_omega
    rw [e3, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun p => ?_
    have hpart := cliMarkErr_of_parts A out .readErr bs p
      (BitVec.ofNat 64 (utf8 "read").length) (p ↦ᵣ utf8 "read")
      (Entails.pure_right rfl (Entails.refl _)) (by nofun)
    refine Entails.trans ?_ hpart
    exact Entails.of_eq (by dsimp only; sep_ac_rfl)
  · dsimp only [kpkMarkOutAt, strSpeAt]
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [ProofLib.memRegion_split' (b := out + 32#64) (n := 8) (k := 8)
          (b' := out + 40#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w4 => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    rw [← sepConj_emp ((out + 40#64) ↦₆₄ w5)]
    have hpart := cliMarkErr_of_parts A out .malformed bs w4 w5 emp (Entails.refl _) (by nofun)
    refine Entails.trans ?_ hpart
    exact Entails.of_eq (by dsimp only)
  · dsimp only [kpkMarkOutAt, strSpeAt]
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [ProofLib.memRegion_split' (b := out + 32#64) (n := 8) (k := 8)
          (b' := out + 40#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w4 => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    rw [← sepConj_emp ((out + 40#64) ↦₆₄ w5)]
    have hpart := cliMarkErr_of_parts A out .reused bs w4 w5 emp (Entails.refl _) (by nofun)
    refine Entails.trans ?_ hpart
    exact Entails.of_eq (by dsimp only)

/-! ## Budget envelope and mark-poll bridge -/

def cliKpkStoreBudgetEnvPlaced [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    {G : CliKpkGetSide} {s1 s2 s3 s4 : Nat}
    {hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16}
    {hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32}
    (GetEnv : KyberGhost → BitVec 32 → List AllocEvent → Prop)
    (MarkEnv : KyberGhost → BitVec 32 → BitVec 32 → PublicKey → List AllocEvent → Prop) :
    KyberPreKeyStoreBudgetEnv
      (cliKpkStoreSpecPlaced A rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox) where
  getPollEnv := GetEnv
  markPollEnv := MarkEnv

/-- Lift budgeted `kpkMarkPollSpecPlaced` on Block `578` to `kitKpkMarkPollSpecE` under envelope
inclusion `hEnv`. -/
theorem cliKpkStoreSpecPlaced_markPoll_of_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program}
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop)
    (kitEnv : KyberPreKeyStoreBudgetEnv
      (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox))
    (hEnv : ∀ fut out self baseKeyA st0 evs,
      MarkEnv F0 ⟨fut, out, self, baseKeyA, kid, ksid, kbk, st0⟩ evs →
        kitEnv.markPollEnv st0 kid ksid kbk evs)
    (hhop : subroutine_ok prog (lsmpl.base 578)
      (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4)) :
    subroutine_ok prog (lsmpl.base 578)
      (withLsCodeRoLoaded lsmpl
        (kitKpkMarkPollSpecE M A lim
          (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
            hGetBox hMarkBox)
          kitEnv)) := by
  let kit :=
    cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  have hpre2 :
      s0.mem ⊨ ⌜s0.fs.files = F0⌝ ∗ ((kitKpkMarkPollSpec M A lim kit kitEnv).pre
        (⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0, st) s0 ∗ R) := by
    change s0.mem ⊨ (⌜s0.fs.files = F0⌝ ∗ (kitKpkMarkPollSpec M A lim kit kitEnv).pre
      (⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0, st) s0) ∗ R at hpre1
    simpa only [sepConj_assoc] using hpre1
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨hfiles, hpre3⟩ := hpre2
  change s0.mem ⊨
    (⌜(0#64 &&& 4095#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        (kid' = kid ∧ ksid' = ksid ∧ kbk' = kbk) ∧
        FitsEnv M lim st (kitEnv.markPollEnv st0 kid' ksid' kbk')⌝ ∗
      kpkMarkBoxAt fut self baseKeyA kid' ksid' 0#8 ∗
      (⌜CliKpkInv rd F0 pathOk kid ksid kbk st0⌝ ∗ dirAt A.repAlloc self st0.oneTime ∗
        dirAt A.repAlloc (self + 40#64) st0.lastResort) ∗
      memRegion out 48 ∗
      (baseKeyA ↦ₛ kbk'.bytes.toList) ∗
      A.pool lim st s0 ∗ stackAt s0.sp s4) ∗ R at hpre3
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
  obtain ⟨⟨_, hx0, hx8, ⟨hxid, hxsid, hxbk⟩, hfit_kit⟩, hpre4⟩ := hpre3
  rw [hxid, hxsid, hxbk] at hfit_kit hpre4 ⊢
  have hpre5 :
      s0.mem ⊨ ⌜CliKpkInv rd F0 pathOk kid ksid kbk st0⌝ ∗
        (kpkMarkBoxAt fut self baseKeyA kid ksid 0#8 ∗
          dirAt A.repAlloc self st0.oneTime ∗ dirAt A.repAlloc (self + 40#64) st0.lastResort ∗
          (baseKeyA ↦ₛ kbk.bytes.toList) ∗ memRegion out 48 ∗
          A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) := by
    refine Satisfies.mono ?_ hpre4
    exact Entails.of_eq (by sep_ac_rfl)
  rw [satisfies_pure_sepConj] at hpre5
  obtain ⟨hinv, hspatial⟩ := hpre5
  let xg : KpkMarkPollGhost := ⟨fut, out, self, baseKeyA, kid, ksid, kbk, st0⟩
  have hfit_hop : FitsEnv M lim st (MarkEnv s0.fs.files xg) := fun evs hm => by
    rw [hfiles] at hm
    exact hfit_kit evs (hEnv fut out self baseKeyA st0 evs hm)
  have hpre_hop : s0.mem ⊨ (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4).pre (xg, st) s0 ∗ R := by
    dsimp only [kpkMarkPollSpecPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hinv.nameOk, hinv.baseOk, hfiles ▸ hinv.seenOk,
      hinv.oneLt.1, hinv.lastLt.1, hfit_hop⟩, ?_⟩
    simpa only [sepConj_assoc] using hspatial
  refine subroutine_ok.mono_outcome hhop (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    show (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4).post (xg, st) s0 sf ⊢
      (kitKpkMarkPollSpec M A lim kit kitEnv).post
        (⟨fut, out, self, baseKeyA, kid, ksid, kbk⟩, st0, st) s0 sf
    dsimp only [kpkMarkPollSpecPlaced, kitKpkMarkPollSpec, kit, cliKpkStoreSpecPlaced,
      cliKpkStoreSpec, cliKpkStoreAt, kpkMarkPollOutAt, xg]
    refine Entails.sepExists_elim fun evs => ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun res => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hres, htr, hmenv⟩ => ?_
    rw [hfiles] at hres hmenv
    subst hres
    have hkenv : kitEnv.markPollEnv st0 kid ksid kbk evs :=
      hEnv fut out self baseKeyA st0 evs hmenv
    set m := kpkMarkOf rd F0 st0 kid ksid kbk
    refine Entails.trans
      (Entails.of_eq (show _ =
        kpkMarkOutAt A.repAlloc out m.1 ∗
          (dirAt A.repAlloc self m.2.oneTime ∗ dirAt A.repAlloc (self + 40#64) m.2.lastResort ∗
            kpkMarkBoxAt fut self baseKeyA kid ksid 1#8 ∗
            (baseKeyA ↦ₛ kbk.bytes.toList) ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp s4) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (cliKpkMarkOut_entails A.repAlloc out m.1)) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ans => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hrel => ?_
    refine Entails.sepExists_right ans ?_
    refine Entails.sepExists_right evs ?_
    refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hkenv⟩ ?_
    refine Entails.trans ?_
      (Entails.of_eq (show
        ⌜CliKpkInv rd F0 pathOk kid ksid kbk m.2⌝ ∗
          (unitSpePollOutAt (cliKpkMarkErrSpec A.repAlloc) out ans ∗
            (dirAt A.repAlloc self m.2.oneTime ∗ dirAt A.repAlloc (self + 40#64) m.2.lastResort ∗
              kpkMarkBoxAt fut self baseKeyA kid ksid 1#8 ∗
              (baseKeyA ↦ₛ kbk.bytes.toList) ∗ A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp s4)) = _ by sep_ac_rfl))
    exact Entails.pure_right hinv.mark (Entails.refl _)
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem cliKpkStoreSpecPlaced_markPoll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program}
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (GetEnv : KyberGhost → BitVec 32 → List AllocEvent → Prop)
    (MarkEnv0 : FsFiles → KyberGhost → BitVec 32 → BitVec 32 → PublicKey →
      List AllocEvent → Prop)
    (hhop : subroutine_ok prog (lsmpl.base 578)
      (kpkMarkPollSpecPlaced rd pathOk A lim
        (fun F xg evs => MarkEnv0 F xg.kg xg.id xg.signedId xg.baseKey evs) s4)) :
    subroutine_ok prog (lsmpl.base 578)
      (withLsCodeRoLoaded lsmpl
        (kitKpkMarkPollSpecE M A lim
          (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
            hGetBox hMarkBox)
          (cliKpkStoreBudgetEnvPlaced GetEnv (MarkEnv0 F0)))) :=
  cliKpkStoreSpecPlaced_markPoll_of_env G hGetBox hMarkBox
    (fun F xg evs => MarkEnv0 F xg.kg xg.id xg.signedId xg.baseKey evs)
    (cliKpkStoreBudgetEnvPlaced GetEnv (MarkEnv0 F0))
    (fun _ _ _ _ _ _ hm => hm) hhop

theorem cliKpkStoreSpecPlaced_markPoll_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop)
    (kitEnv : KyberPreKeyStoreBudgetEnv
      (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox))
    (hEnv : ∀ fut out self baseKeyA st0 evs,
      MarkEnv F0 ⟨fut, out, self, baseKeyA, kid, ksid, kbk, st0⟩ evs →
        kitEnv.markPollEnv st0 kid ksid kbk evs)
    (hhop : subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4))
    (hblk : callerBlk < 619 := by decide) :
    let kit :=
      cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox
    subroutine_ok callerProg (0#64 + kit.markPollOff)
      (withLsRoCl lsmpl (kitKpkMarkPollSpecE M A lim kit kitEnv)) := by
  intro kit
  have hcallee :=
    cliKpkStoreSpecPlaced_markPoll_of_env G hGetBox hMarkBox MarkEnv kitEnv hEnv hhop
  have hrocl :=
    ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 578)
      hcallee hblk (by decide) (by decide)
  simpa only [kit, cliKpkStoreSpecPlaced, BitVec.zero_add] using hrocl

/-! ## Shims, `futDrop`, and `KyberPreKeyStoreKitPlacedOk` assembly -/

theorem cliKpkGetShim_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (hC : AllocContractsXCliPlaced A lim H)
    (hs1 : 32 + extHookStack ≤ s1) :
    subroutine_ok (lsProg_611 H) (lsmpl.base 611)
      (withLsCodeRoLoaded lsmpl
        (kitKpkGetShimSpec M A lim
          (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
            hGetBox hMarkBox))) := by
  let kit :=
    cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox
  have hshim := kpkGetShim_placed_ok_of_deps (stk := s1) hC hs1
  refine subroutine_ok.of_codeLoaded fun ⟨⟨self, id⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜(0#64 &&& 4095#64) = 0#64 ∧ s0.readReg64 .x0 = self ∧ s0.readReg32 .x1 = id ∧
        FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗
      A.pool lim st s0 ∗ stackAt s0.sp s1) ∗ R at hpre1
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨_, hx0, hx1, hfit⟩, hpool⟩ := hpre1
  have hpre_shim :
      s0.mem ⊨ (pkShimSpecPlaced kpkGetFutVtSym A lim s1).pre (⟨self, id⟩, st) s0 ∗ R := by
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hfit⟩, by simpa only [sepConj_assoc] using hpool⟩
  refine subroutine_ok.mono_outcome hshim (⟨self, id⟩, st) R s0 hpc hrun hpre_shim hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, kitKpkGetShimSpec, kit, cliKpkStoreSpecPlaced, cliKpkStoreSpec]
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded] at hpost
    simpa only [BitVec.zero_add] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem cliKpkGetShim_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (hC : AllocContractsXCliPlaced A lim H)
    (hs1 : 32 + extHookStack ≤ s1)
    (hblk : callerBlk < 619 := by decide) :
    let kit :=
      cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox
    subroutine_ok callerProg (0#64 + kit.getShimOff)
      (withLsRoCl lsmpl (kitKpkGetShimSpec M A lim kit)) := by
  intro kit
  have hrocl :=
    ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 611)
      (cliKpkGetShim_placed_ok (rd := rd) (F0 := F0) (pathOk := pathOk)
        (kid := kid) (ksid := ksid) (kbk := kbk) G
        (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) hGetBox hMarkBox hC hs1)
      hblk (by decide) (by decide)
  have hoff : 0#64 + kit.getShimOff = lsmpl.base 611 := by
    dsimp only [kit, cliKpkStoreSpecPlaced]
    exact BitVec.zero_add _
  rw [hoff]
  exact hrocl

theorem cliKpkMarkShim_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (hC : AllocContractsXCliPlaced A lim H)
    (hs3 : 48 + extHookStack ≤ s3) :
    subroutine_ok (lsProg_613 H) (lsmpl.base 613)
      (withLsCodeRoLoaded lsmpl
        (kitKpkMarkShimSpec M A lim
          (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
            hGetBox hMarkBox))) := by
  let kit :=
    cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox
  have hshim := kpkMarkShim_placed_ok_of_deps (stk := s3) hC hs3
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨self, id, signedId, baseKeyA⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜(0#64 &&& 4095#64) = 0#64 ∧ s0.readReg64 .x0 = self ∧ s0.readReg32 .x1 = id ∧
        s0.readReg32 .x2 = signedId ∧ s0.readReg64 .x3 = baseKeyA ∧
        FitsEnv M lim st (BoxAllocEnv 32)⌝ ∗
      A.pool lim st s0 ∗ stackAt s0.sp s3) ∗ R at hpre1
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨_, hx0, hx1, hx2, hx3, hfit⟩, hpool⟩ := hpre1
  have hpre_shim :
      s0.mem ⊨
        (kpkMarkShimSpecPlaced A lim s3).pre (⟨self, id, signedId, baseKeyA⟩, st) s0 ∗ R := by
    dsimp only [kpkMarkShimSpecPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hfit⟩, by simpa only [sepConj_assoc] using hpool⟩
  refine subroutine_ok.mono_outcome hshim (⟨self, id, signedId, baseKeyA⟩, st) R s0 hpc hrun
    hpre_shim hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, kitKpkMarkShimSpec, kit, cliKpkStoreSpecPlaced, cliKpkStoreSpec]
    dsimp only [kpkMarkShimSpecPlaced, withLsCodeRoLoaded] at hpost
    simpa only [BitVec.zero_add] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem cliKpkMarkShim_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (hC : AllocContractsXCliPlaced A lim H)
    (hs3 : 48 + extHookStack ≤ s3)
    (hblk : callerBlk < 619 := by decide) :
    let kit :=
      cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox
    subroutine_ok callerProg (0#64 + kit.markShimOff)
      (withLsRoCl lsmpl (kitKpkMarkShimSpec M A lim kit)) := by
  intro kit
  have hrocl :=
    ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 613)
      (cliKpkMarkShim_placed_ok (rd := rd) (F0 := F0) (pathOk := pathOk)
        (kid := kid) (ksid := ksid) (kbk := kbk) G
        (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) hGetBox hMarkBox hC hs3)
      hblk (by decide) (by decide)
  have hoff : 0#64 + kit.markShimOff = lsmpl.base 613 := by
    dsimp only [kit, cliKpkStoreSpecPlaced]
    exact BitVec.zero_add _
  rw [hoff]
  exact hrocl

section FutDrop

attribute [local irreducible] Program.fetch Program.externAt?

theorem cliKpkFutDrop_block_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (lsProg_547 H) (lsmpl.base 547) futDropBudgetSpec := by
  dsimp only [lsProg_547, futDropBudgetSpec]
  change subroutine_ok ((blkPC_547).rebase (blkPl_547).base H) (blkPl_547).base _
  wp_init x s0
  wp_steps
  wp_done

end FutDrop

theorem cliKpkFutDrop_rocl_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H] (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 547) (withLsRoCl lsmpl futDropBudgetSpec) :=
  ls_futDrop_ok_of_block (callerProg := callerProg) (cliKpkFutDrop_block_placed_ok H)
    hi (by decide) (by decide)

/-- Assemble `KyberPreKeyStoreKitPlacedOk` for `cliKpkStoreSpecPlaced` from
`AllocContractsXCliPlaced` and the Block `576`/`578` poll contracts. -/
theorem cliKpkStorePlacedOk_of_polls [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop)
    (kitEnv : KyberPreKeyStoreBudgetEnv
      (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hC : AllocContractsXCliPlaced A lim H)
    (hs1 : 32 + extHookStack ≤ s1)
    (hs3 : 48 + extHookStack ≤ s3)
    (hGetPoll : subroutine_ok (lsProg_576 H) (lsmpl.base 576)
      (withLsCodeRoLoaded lsmpl
        (kitKpkGetPollSpecE M A lim
          (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
            hGetBox hMarkBox)
          kitEnv)))
    (hEnv : ∀ fut out self baseKeyA st0 evs,
      MarkEnv F0 ⟨fut, out, self, baseKeyA, kid, ksid, kbk, st0⟩ evs →
        kitEnv.markPollEnv st0 kid ksid kbk evs)
    (hMarkPoll : subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv s4)) :
    KyberPreKeyStoreKitPlacedOk A lim
      (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox)
      kitEnv H where
  getShim hblk := cliKpkGetShim_rocl_placed_ok G hGetBox hMarkBox hC hs1 hblk
  getPoll {callerProg} {callerBlk} _ hblk := by
    have hoff :
        0#64 +
          (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
            hGetBox hMarkBox).getPollOff =
          lsmpl.base 576 := by
      dsimp only [cliKpkStoreSpecPlaced]
      exact BitVec.zero_add _
    rw [hoff]
    exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 576)
      hGetPoll hblk (by decide) (by decide)
  getFutDrop {callerProg} {callerBlk} _ hblk := by
    have hoff :
        0#64 +
          (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
            hGetBox hMarkBox).getFutDropOff =
          lsmpl.base 547 := by
      dsimp only [cliKpkStoreSpecPlaced]
      rw [BitVec.zero_add]
      exact lsDropOffPlaced_eq hDropNz
    rw [hoff]
    exact cliKpkFutDrop_rocl_placed_ok (callerProg := callerProg) (i := callerBlk) (H := H) hblk
  markShim hblk := cliKpkMarkShim_rocl_placed_ok G hGetBox hMarkBox hC hs3 hblk
  markPoll hblk :=
    cliKpkStoreSpecPlaced_markPoll_rocl G hGetBox hMarkBox MarkEnv kitEnv hEnv hMarkPoll hblk
  markFutDrop {callerProg} {callerBlk} _ hblk := by
    have hoff :
        0#64 +
          (cliKpkStoreSpecPlaced A.repAlloc rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
            hGetBox hMarkBox).markFutDropOff =
          lsmpl.base 547 := by
      dsimp only [cliKpkStoreSpecPlaced]
      rw [BitVec.zero_add]
      exact lsDropOffPlaced_eq hDropNz
    rw [hoff]
    exact cliKpkFutDrop_rocl_placed_ok (callerProg := callerProg) (i := callerBlk) (H := H) hblk

end LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlacedBudget
