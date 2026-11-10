/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BridgeReloc
public import LibsignalBinary.Proofs.RecordCodecs.Deps
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommon
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import all Init.Data.String.Defs

/-!
# Store Poll Helpers (`[LibsignalPlacement]`)

Read-only `.rodata` string witnesses (`"identity-key-pair"`, `"registration-id"`, `"malformed file"`),
layout bridges, and cell-oriented callee wrappers (`Dir::get` Block `589`, `__rust_dealloc`, and
`IdentityKeyPair::try_from` Block `84`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs

/-! ## Layout Predicate Bridges -/

theorem idOwnFutBoxAtPlaced_eq (box self : BitVec 64) (st : BitVec 8) :
    idOwnFutBoxAtPlaced box self st = idOwnFutBoxAt box self st := rfl

theorem idKeyPairOutAtPlaced_eq (A : RustAlloc) (out : BitVec 64)
    (ans : Except Unit IdentityKeyPair) :
    idKeyPairOutAtPlaced A out ans = idKeyPairOutAt A out ans := by
  cases ans <;> rfl

theorem idRegIdOutAtPlaced_eq (A : RustAlloc) (out : BitVec 64)
    (ans : Except Unit (BitVec 32)) :
    idRegIdOutAtPlaced A out ans = idRegIdOutAt A out ans := by
  cases ans <;> rfl

/-! ## Symbolic `.rodata` Strings -/

abbrev idKpFileNameSym : String := "libsignal_cli:.rodata..Lanon.17"
abbrev idRegIdFileNameSym : String := "libsignal_cli:.rodata..Lanon.13"
abbrev malformedFileStrSym : String := "libsignal_cli:.rodata..Lanon.67"

theorem rodata_idKpFileName_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (lsρ idKpFileNameSym ↦ᵣ utf8 "identity-key-pair") ∗ P :=
  lsro_slice_intro hro (by lsro_addr) (by decide +kernel) hP

theorem rodata_regId_and_malformed_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    ∃ w0 wTail : BitVec 64,
      m ⊨ ((lsρ idRegIdFileNameSym ↦ᵣ utf8 "registration-id") ∗
        (lsρ malformedFileStrSym ↦₆₄ᵣ w0) ∗
        ((lsρ malformedFileStrSym + 6#64) ↦₆₄ᵣ wTail)) ∗ P := by
  let bs0 : List (BitVec 8) := (utf8 "malformed file").take 8
  let bs6 : List (BitVec 8) := (utf8 "malformed file").drop 6
  have hlen0 : bs0.length = 8 := by decide +kernel
  have hlen6 : bs6.length = 8 := by decide +kernel
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 hlen0
  obtain ⟨wTail, hwt⟩ := exists_unpack64_of_length_8 hlen6
  have hchk0 : lsroSliceCheck malformedFileStrSym 0 (unpack64 w0) = true := by
    rw [← hw0]; decide +kernel
  have hchk6 : lsroSliceCheck malformedFileStrSym 6 (unpack64 wTail) = true := by
    rw [← hwt]; decide +kernel
  refine ⟨w0, wTail, ?_⟩
  have s1 := lsro64_intro hro (addr := lsρ malformedFileStrSym + 6#64)
    (by lsro_addr) hchk6 hP
  have s2 := lsro64_intro hro (addr := lsρ malformedFileStrSym)
    (by lsro_addr) hchk0 s1
  have s3 := lsro_slice_intro hro (addr := lsρ idRegIdFileNameSym)
    (by lsro_addr) (bs := utf8 "registration-id") (by decide +kernel) s2
  simpa only [sepConj_assoc] using s3

/-! ## Cell-Oriented Callee Wrappers -/

def dirGetRawSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) : Spec DirGetGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.self ∧ s.readReg64 .x2 = x.nameA ∧
      (s.readReg64 .x3).toNat = x.name.length ∧ x.name.length < 2 ^ 32 ∧
      x.dir.path.length < 2 ^ 32 ∧ pathOk (pathOf x.dir.path x.name)⌝ ∗
      dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
      memRegion x.ret 48 ∗ stackAt s.sp stk ∗ A.pool
  post := fun x s0 sf =>
    (∃∗ r : Except Unit (List (BitVec 8)),
      ⌜r = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace⌝ ∗
        getResultAt A x.ret r) ∗
      dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
      stackAt s0.sp stk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem dirGetRo_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (dirGetRawSpec rd pathOk A getStk)))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (dirGetRoCellsSpec rd pathOk A calleeStk)) := by
  intro ⟨ret, self, dir, nameA, name, fsp⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl0, hpre⟩ := LibsignalPublicApi.StoreKit.extract_withLsRoCl hpre
  simp only [dirGetRoCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hnl, hpl, hpok⟩, hmem⟩
  subst hfsp
  rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let callG : DirGetGhost := ⟨ret, self, dir, nameA, name, true⟩
  have hif : (if true = true then (nameA ↦ᵣ name) else (nameA ↦ₛ name)) = (nameA ↦ᵣ name) := rfl
  have hpre0 : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (dirGetRawSpec rd pathOk A getStk)).pre callG s0 ∗ (stkRem ∗ R) := by
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, dirGetRawSpec,
      SpqrV1.ChainProofs.bytesAt, callG, stkRem]
    rw [hif]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnl, hpl, hpok⟩, ?_⟩
    convert hmem using 1; ac_rfl
  rcases hGet callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, dirGetRawSpec, dirGetRoCellsSpec,
      SpqrV1.ChainProofs.bytesAt, callG] at hq ⊢
    rw [hif] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hcrlf, hq⟩
    refine ⟨hcrlf, ?_⟩
    rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, dirGetRawSpec, dirGetRoCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, dirGetRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, dirGetRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem deallocAt_cells_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hi : i < 619 := by decide)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (Store.IdTrustPoll.Helpers.deallocVecBufSpec A calleeStk)) := by
  have hDealloc : subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (rustDeallocExternSpecWithStack A extHookStack)) :=
    ls_subroutine_ok_rocl_of_block (callerProg := prog) hC.dealloc hi
  intro ⟨bPtr, bCap, bs, fsp⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl0, hpre⟩ := LibsignalPublicApi.StoreKit.extract_withLsRoCl hpre
  simp only [Store.IdTrustPoll.Helpers.deallocVecBufSpec, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hlen, hlt, hnz⟩, hmem⟩
  subst hfsp
  rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi] at hmem
  dsimp only [Store.IdTrustPoll.Helpers.vecU8BufRest] at hmem
  simp only [hnz, ↓reduceIte] at hmem
  have hreg :
      (bPtr ↦ₛ bs) ∗ memRegion (bPtr + BitVec.ofNat 64 bs.length) (bCap.toNat - bs.length) ⊢
      memRegion bPtr bCap.toNat := by
    have hsplit : memRegion bPtr bCap.toNat =
        memRegion bPtr bs.length ∗
        memRegion (bPtr + BitVec.ofNat 64 bs.length) (bCap.toNat - bs.length) := by
      have heq : bCap.toNat = bs.length + (bCap.toNat - bs.length) := by omega
      conv_lhs => rw [heq]
      rw [memRegion_split bPtr bs.length (bCap.toNat - bs.length) (by omega)]
    rw [hsplit]
    exact sepConj_mono_left (IsBlock.entails_memRegion (IsBlock.pointsToBytes bPtr bs))
  have hlay : LayoutOk bCap.toNat 1 := ⟨by bv_omega, ⟨0, rfl⟩, by omega⟩
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hmem_reg : s0.mem ⊨
      memRegion bPtr bCap.toNat ∗
      (A.live bPtr bCap.toNat 1 ∗ A.pool ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left hreg) ?_
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hpre0 : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (rustDeallocExternSpecWithStack A extHookStack)).pre
        (bPtr, bCap.toNat, 1) s0 ∗ (stkRem ∗ R) := by
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, rustDeallocExternSpecWithStack]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by rw [hx1], by rw [hx2]; rfl, hlay⟩, ?_⟩
    convert hmem_reg using 1; ac_rfl
  rcases hDealloc (bPtr, bCap.toNat, 1) (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, rustDeallocExternSpecWithStack,
      Store.IdTrustPoll.Helpers.deallocVecBufSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hcrlf, hq⟩
    refine ⟨hcrlf, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, rustDeallocExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, rustDeallocExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, rustDeallocExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

def ikpTryFromCellsPlacedSpec [LibsignalPlacement] (A : RustAlloc) (calleeStk : Nat) :
    Spec IkpTryFromCellsGhost where
  pre := fun (bytesA, bytes, ret, fsp) s =>
    ⌜s.readReg64 .x0 = bytesA ∧ (s.readReg64 .x1).toNat = bytes.length ∧
      bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = ret ∧ s.sp = fsp⌝ ∗
      (bytesA ↦ₛ bytes) ∗ memRegion ret 72 ∗ FromRecordCallees.lsLogOff ∗
      stackAt fsp calleeStk ∗ A.pool
  post := fun (bytesA, bytes, ret, fsp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      RecordCodecsBinary.identityKeyPairResultAt A ret
        (RecordCodecs.IdentityKeyPair.tryFrom bytes) ∗
      (bytesA ↦ₛ bytes) ∗ FromRecordCallees.lsLogOff ∗ stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem ikpTryFrom_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 84)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (RecordCodecsBinary.identityKeyPairTryFromRawSpec A)))
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 84)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (ikpTryFromCellsPlacedSpec A calleeStk)) := by
  intro ⟨bytesA, bytes, ret, fsp⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl0, hpre⟩ := LibsignalPublicApi.StoreKit.extract_withLsRoCl hpre
  simp only [ikpTryFromCellsPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hblt, hx8, hfsp⟩, hmem⟩
  subst hfsp
  rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk)
    (calleeStk - smallRootStack)
  let callG : RecordCodecsBinary.DecodeGhost := ⟨bytesA, bytes, ret⟩
  have hpre0 : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (RecordCodecsBinary.identityKeyPairTryFromRawSpec A)).pre
        callG s0 ∗ (stkRem ∗ R) := by
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
      RecordCodecsBinary.identityKeyPairTryFromRawSpec, callG, stkRem]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hblt, hx8⟩, ?_⟩
    convert hmem using 1; ac_rfl
  rcases hDec callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
      RecordCodecsBinary.identityKeyPairTryFromRawSpec,
      ikpTryFromCellsPlacedSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hcrlf, hq⟩
    refine ⟨hcrlf, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
      RecordCodecsBinary.identityKeyPairTryFromRawSpec, ikpTryFromCellsPlacedSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
      RecordCodecsBinary.identityKeyPairTryFromRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
      RecordCodecsBinary.identityKeyPairTryFromRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon
