/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.MainCodeSym
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCallees
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` `kem::Key<Public>::deserialize` (Block `590`)

Proves `cliKemDeserialize_placed_ok` on Block `590` (calling `KeyKind::key_length` at Block `110`)
and transfers it to any caller block `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617 instIsLsBlockProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunProofs.KemDeserializeHelpers

/-- Mangled symbol for `alloc::alloc::handle_alloc_error` in the libsignal object. -/
abbrev lsHandleAllocErrorSymCli : String :=
  "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error"

/-- Relocatable `[LibsignalPlacement]` counterpart of `cliKemDeserializeSpec` (Block `590`). -/
def cliKemDeserializeSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) :
    Spec KemDeserializeGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (cliKemDeserializeSpec A stk)

section KemDeserializePlacedHelpers

private theorem stackAt_kemDeser_placed (sp : BitVec 64) :
    stackAt sp cliKemDeserStack =
      stackAt (sp - 48#64) extHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗
        ((sp - 32#64) ↦₆₄ v2) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
        ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
  have h1 := ProofLib.stackAt_split_cells sp 16384 6 (by decide)
  have hsum : 16384 + 8 * 6 = cliKemDeserStack := by decide
  rw [hsum] at h1
  change stackAt sp cliKemDeserStack =
    stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 at h1
  have hc6 : cells (sp - 48#64) 6 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗
        ((sp - 32#64) ↦₆₄ v2) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
        ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
    cells_unfold
  rw [h1, hc6]

private theorem memRegion_24_split_8_16_placed (r : BitVec 64) :
    memRegion r 24 = (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗ memRegion (r + 8#64) 16 := by
  rw [show (24 : Nat) = 8 + 16 by rfl, ProofLib.memRegion_split r 8 16 (by decide),
    ProofLib.memRegion_eight]

private theorem memRegion_24_split_badType_placed (r : BitVec 64) :
    memRegion r 24 =
      (∃∗ b1 : BitVec 8, ∃∗ w0 : BitVec 64,
        (r ↦₆₄ w0) ∗ ((r + 8#64) ↦₈ b1) ∗ memRegion (r + 9#64) 15) := by
  rw [memRegion_24_split_8_16_placed r,
    show (16 : Nat) = 1 + 15 by rfl,
    ProofLib.memRegion_split (r + 8#64) 1 15 (by decide),
    ProofLib.memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_24_split_badLen_placed (r : BitVec 64) :
    memRegion r 24 =
      (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (r ↦₆₄ w0) ∗ ((r + 8#64) ↦₆₄ w1) ∗ memRegion (r + 16#64) 8) := by
  rw [memRegion_24_split_8_16_placed r,
    show (16 : Nat) = 8 + 8 by rfl,
    ProofLib.memRegion_split (r + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_24_cells_placed (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem pull_alloc_pure_placed (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

private theorem ofNat_beq_zero_false_placed {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem ofNat_ne_1569_placed {n : Nat} (hne : n ≠ 1569) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 1569#64 := by
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 1569 at ht
  omega

private theorem byte_zext32_ne8_placed {t : BitVec 8} (ht : t ≠ 0x08#8) :
    t.zeroExtend 32 ≠ 8#32 := by
  intro h
  apply ht
  apply BitVec.eq_of_toNat_eq
  have hlt : t.toNat < 256 := t.isLt
  have hn := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : t.toNat < 2 ^ 32)] at hn
  exact hn

private theorem byte_zext64_ne8_placed {t : BitVec 8} (ht : t ≠ 0x08#8) :
    t.zeroExtend 64 ≠ 8#64 := by
  intro h
  apply ht
  apply BitVec.eq_of_toNat_eq
  have hlt : t.toNat < 256 := t.isLt
  have hn := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : t.toNat < 2 ^ 64)] at hn
  exact hn

private theorem ok_post_entails_placed (A : RustAlloc) (r buf : BitVec 64) (key : List (BitVec 8))
    (hlen : key.length = kemPkLen) (hbuf : buf ≠ 0#64) :
    (r ↦₆₄ 0xfffffffffffffffe#64) ∗ ((r + 8#64) ↦₆₄ buf) ∗ ((r + 16#64) ↦₆₄ 1568#64) ∗
      A.live buf 1568 1 ∗ (buf ↦ₛ key) ⊢
      kemDeserResAt A r (.ok key) := by
  have hne : key ≠ [] := by
    intro h; rw [h] at hlen; simp [kemPkLen] at hlen
  unfold kemDeserResAt
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right buf ?_
  unfold boxU8At
  have hoff : (r + 8#64 + asm64% boxSliceLenOff) = r + 16#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (buf ≠ 0 ∧ 1568 < 2 ^ 63) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hbuf, by decide⟩⟩
  rw [hoff, hlen]
  dsimp only [kemPkLen]
  simp only [hne, ↓reduceIte, hpure, pure_true, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

private theorem sepExists_mono_bv64_placed {P Q : BitVec 64 → SepProp}
    (h : ∀ v, P v ⊢ Q v) : (∃∗ v, P v) ⊢ (∃∗ v, Q v) :=
  Entails.sepExists_mono h

private theorem sepWPp_ok_ret_placed {prog : Program} {s s0 : State} {P R : SepProp}
    {Tail : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {Qp : State → SepProp → Prop} {A : RustAlloc} {r : BitVec 64} (buf : BitVec 64)
    {key : List (BitVec 8)} (hlen : key.length = kemPkLen) (hbuf : buf ≠ 0#64)
    (h : SepWP prog (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ∃∗ x0, ∃∗ x1, ∃∗ x2, ∃∗ x3, ∃∗ x4, ∃∗ x5,
            ⌜sf.trace = s0.trace⌝ ∗
              ((r ↦₆₄ 0xfffffffffffffffe#64) ∗ ((r + 8#64) ↦₆₄ buf) ∗
                ((r + 16#64) ↦₆₄ 1568#64) ∗ A.live buf 1568 1 ∗ (buf ↦ₛ key)) ∗
              Tail x0 x1 x2 x3 x4 x5)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    SepWPp prog (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ∃∗ x0, ∃∗ x1, ∃∗ x2, ∃∗ x3, ∃∗ x4, ∃∗ x5,
            ⌜sf.trace = s0.trace⌝ ∗
              kemDeserResAt A r (.ok key) ∗
              Tail x0 x1 x2 x3 x4 x5)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  have h1 := SepWPp.of_sepWP_ret (Qp := Qp) h
  intro R' hm hL
  rcases h1 R' hm hL with ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq, hsp, hcs⟩ | hpan | hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, ?_, hsp, hcs⟩⟩
    intro hm_pf
    refine Satisfies.mono ?_ (hq hm_pf)
    exact sepExists_mono_bv64_placed fun x0 => sepExists_mono_bv64_placed fun x1 =>
      sepExists_mono_bv64_placed fun x2 => sepExists_mono_bv64_placed fun x3 =>
        sepExists_mono_bv64_placed fun x4 => sepExists_mono_bv64_placed fun x5 =>
          sepConj_mono_right (sepConj_mono_left (ok_post_entails_placed A r buf key hlen hbuf))
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

private def cliMemcpyBytesAtSpecPlaced (ro : Bool) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length ∧
     bs.length ≤ 2 ^ 64⌝ ∗
    memRegion dst bs.length ∗
    SpqrV1.ChainProofs.bytesAt ro src bs ∗
    stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    SpqrV1.ChainProofs.bytesAt ro src bs ∗
    stackAt s0.sp extHookStack

private theorem cliMemcpy_bytesAt_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (ro : Bool) :
    subroutine_ok (lsProg_590 H) (lsρ memcpyName)
      (withLsRoCl lsmpl (cliMemcpyBytesAtSpecPlaced ro)) := by
  cases ro
  · have hmc := @ls_subroutine_ok_rocl_of_block _ _ (lsProg_590 H) (lsProg_617 H) 590 617 H
      (instIsLsBlockProg_590 H) (instIsLsBlockProg_617 H) (lsρ memcpyName) _
      (hA.session_memcpy_region extHookStack (Nat.le_refl _) (by decide))
      _ _ _ _ (by decide) (by decide) (by decide)
    refine subroutine_ok_mono hmc ?_ ?_
    · intro ⟨dst, src, bs⟩ R s0 hpre
      obtain ⟨hcrl, hrest⟩ := extract_withLsRoCl hpre
      dsimp only [withLsRoCl, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
      dsimp only [cliMemcpyBytesAtSpecPlaced, SpqrV1.ChainProofs.bytesAt_false] at hrest
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcrl, ?_⟩
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hrest ⊢
      exact ⟨⟨hrest.1.1, hrest.1.2.1, hrest.1.2.2.1⟩, hrest.2⟩
    · intro ⟨dst, src, bs⟩ R s0 sf hpost
      simpa only [withLsRoCl, cliMemcpyBytesAtSpecPlaced, withStack, sessionMemcpyRegionSpec,
        memcpyRegionSpec, SpqrV1.ChainProofs.bytesAt_false, sepConj_assoc] using hpost
  · have hmc_plain : subroutine_ok (lsProg_590 H) (lsρ memcpyName)
        SpqrV1.Alloc.sessionMemcpyRegionROSpec :=
      ls_hook_ok_ultra_of_mem (prog := lsProg_590 H) (i := 590)
        (hprog := instIsLsBlockProg_590 H) hRO
    have hmc := subroutine_ok_rocl_of_plain (pl := lsmpl) hmc_plain
    intro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal hL
    have hpre' : s0.mem ⊨ (withLsRoCl lsmpl SpqrV1.Alloc.sessionMemcpyRegionROSpec).pre
        (dst, src, bs) s0 ∗ (stackAt s0.sp extHookStack ∗ R) := by
      obtain ⟨hcrl, hrest⟩ := extract_withLsRoCl hpre
      dsimp only [withLsRoCl, SpqrV1.Alloc.sessionMemcpyRegionROSpec]
      dsimp only [cliMemcpyBytesAtSpecPlaced, SpqrV1.ChainProofs.bytesAt_true] at hrest
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcrl, ?_⟩
      simpa only [sepConj_assoc] using hrest
    rcases hmc (dst, src, bs) (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hal hL with
      ⟨sf, hs, hout⟩
    refine ⟨sf, hs, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [withLsRoCl, cliMemcpyBytesAtSpecPlaced, SpqrV1.Alloc.sessionMemcpyRegionROSpec,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc] using hpost
    · simp only [SpqrV1.Alloc.sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [SpqrV1.Alloc.sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [SpqrV1.Alloc.sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1

private def cliMemcpy1568SpecPlaced (ro : Bool) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     s0.readReg64 .x2 = 1568#64 ∧
     bs.length = 1568⌝ ∗
    memRegion dst 1568 ∗
    SpqrV1.ChainProofs.bytesAt ro src bs ∗
    stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    SpqrV1.ChainProofs.bytesAt ro src bs ∗
    stackAt s0.sp extHookStack

private theorem cliMemcpy1568_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (ro : Bool) :
    subroutine_ok (lsProg_590 H) (lsρ memcpyName)
      (withLsRoCl lsmpl (cliMemcpy1568SpecPlaced ro)) := by
  refine subroutine_ok_mono (cliMemcpy_bytesAt_placed_ok hA hRO ro) ?_ ?_
  · intro ⟨dst, src, bs⟩ R s0 hpre
    obtain ⟨hcrl, hrest⟩ := extract_withLsRoCl hpre
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hrest
    simp only [cliMemcpy1568SpecPlaced, cliMemcpyBytesAtSpecPlaced]
    apply Entails.pure_left
    rintro ⟨hx0, hx1, hx2, hlen⟩
    rw [hx2, hlen]
    exact Entails.pure_right ⟨hx0, hx1, rfl, by decide⟩ (Entails.refl _)
  · intro ⟨dst, src, bs⟩ R s0 sf hpost
    simpa only [withLsRoCl, cliMemcpy1568SpecPlaced, cliMemcpyBytesAtSpecPlaced, sepConj_assoc]
      using hpost

set_option maxHeartbeats 1600000 in
theorem cliKemDeserialize_exact_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hpanic : H lsHandleAllocErrorSymCli = some Rust.panicked) :
    subroutine_ok (lsProg_590 H) (blkPl_590).base
      (cliKemDeserializeSpecPlaced A cliKemDeserStack) := by
  unfold cliKemDeserializeSpecPlaced LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
    cliKemDeserializeSpec
  simp only [stackAt_kemDeser_placed, sepExists_sepConj_right, sepExists_sepConj_left, sepConj_assoc]
  have h110 : IsLsBlockProg
      ((CryptoVerification.blkPC_110).rebase (CryptoVerification.blkPl_110).base H) 110 H :=
    inferInstance
  have hkeylen : subroutine_ok (lsProg_590 H) (lsmpl.base 110)
      (withLsRoCl lsmpl E2E.Pqxdh.kemPublicKeyLengthSpec) :=
    @ls_subroutine_ok_rocl_of_plain _ _ (lsProg_590 H) _ 590 110 H
      (instIsLsBlockProg_590 H) h110 (CryptoVerification.blkPl_110).base _
      (E2E.Pqxdh.kemPublicKeyLength_placed_ok H) _ _ _ _ (by decide) (by decide) (by decide)
  have hshim : subroutine_ok (lsProg_590 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (withStack sessionShimSpec extHookStack)) :=
    @ls_subroutine_ok_rocl_of_block _ _ (lsProg_590 H) (lsProg_617 H) 590 617 H
      (instIsLsBlockProg_590 H) (instIsLsBlockProg_617 H) (lsρ lsRustNoAllocShimSymCli) _
      (hA.shim extHookStack (Nat.le_refl _) (by decide)) _ _ _ _ (by decide) (by decide) (by decide)
  have halloc : subroutine_ok (lsProg_590 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustAllocSpecWithStack A extHookStack)) :=
    @ls_subroutine_ok_rocl_of_block _ _ (lsProg_590 H) (lsProg_617 H) 590 617 H
      (instIsLsBlockProg_590 H) (instIsLsBlockProg_617 H) (lsρ lsRustAllocSymCli) _
      hA.alloc _ _ _ _ (by decide) (by decide) (by decide)
  have hmc_any := cliMemcpy1568_placed_ok hA hRO
  have hpanic_at : (lsProg_590 H).externAt? (lsρ lsHandleAllocErrorSymCli) = some Rust.panicked :=
    (ls_externAt?_of_mem (prog := lsProg_590 H) (i := 590)
      (hprog := instIsLsBlockProg_590 H) (sym := lsHandleAllocErrorSymCli)).trans hpanic
  clear hA hRO hpanic h110
  dsimp only [lsProg_590, ite_true] at hkeylen hshim halloc hmc_any hpanic_at ⊢
  wpp_init x s0
  obtain ⟨r, ro, p, bs⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  cases bs with
  | nil =>
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, kemPkDeserialize, kemDeserResAt,
      memRegion_24_split_8_16_placed r, sepExists_sepConj_left, sepConj_assoc] at *
    refine SepWPp.exists_elim fun w0 => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  | cons t rest =>
    have hlen_lt63 : (t :: rest).length < 2 ^ 63 := ‹_›
    have hlen_lt64 : rest.length + 1 < 2 ^ 64 := by simp at hlen_lt63; omega
    have hne0 : (BitVec.ofNat 64 (rest.length + 1) == 0#64) = false :=
      ofNat_beq_zero_false_placed (by omega) hlen_lt64
    by_cases ht : t = 0x08#8
    · subst ht
      simp only [kemPkDeserialize, ne_eq, not_true_eq_false, ↓reduceIte]
      by_cases hrlen : rest.length = kemPkLen
      · have hrlen_keep : rest.length = kemPkLen := hrlen
        have hrlen1568 : rest.length = 1568 := hrlen
        have hx2_eq : BitVec.ofNat 64 (rest.length + 1) = 1569#64 := by rw [hrlen1568]
        rw [List.length_cons] at *
        try rw [hx2_eq] at *
        simp only [hrlen, not_true_eq_false, ↓reduceIte,
          memRegion_24_cells_placed r, sepExists_sepConj_left, sepConj_assoc]
        refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
          SepWPp.exists_elim fun w2 => ?_
        have hlay : LayoutOk 1568 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
        have hpow : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
        have hmcall := hmc_any ro
        cases ro
        · simp only [SpqrV1.ChainProofs.bytesAt_false, ProofLib.pointsToBytes_cons,
            sepConj_assoc] at hmcall ⊢
          apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
            (mid := lsmpl.base 110) hcrl0
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl1, hro1⟩
          wp_apply using hkeylen
          apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
            (mid := lsρ lsRustNoAllocShimSymCli) ‹_›
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl2, hro2⟩
          wp_apply using hshim
          apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
            (mid := lsρ lsRustAllocSymCli) ‹_›
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl3, hro3⟩
          wp_apply using halloc
          by_cases hoom : sf_2.readReg64 Reg.x0 = 0
          · have hoom64 : sf_2.readReg64 Reg.x0 = 0#64 := hoom
            simp only [hoom, ite_true]
            rw [pull_alloc_pure_placed]
            refine SepWPp.pure_elim fun htrace => ?_
            apply SepWPp.of_sepWP (mid := lsρ lsHandleAllocErrorSymCli)
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) hpanic_at fun hm => ?_
            simpa only [sepConj_assoc] using
              allowPanic_panicked
                (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
          · simp only [hoom, ite_false, sepConj_assoc]
            have hoom_beq : (sf_2.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
            rw [pull_alloc_pure_placed]
            refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
            have htr_sf2 : sf_2.trace = s0.trace := by
              rw [htr2]; simp only [wp_norm, arm64_norm, *]
            apply sepWPp_ok_ret_placed (sf_2.readReg64 Reg.x0) hrlen_keep hoom
            apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ memcpyName) ‹_›
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            rintro ⟨hcl4, hro4⟩
            wp_apply using hmcall
            wp_steps
            wp_done
        · simp only [SpqrV1.ChainProofs.bytesAt_true, ProofLib.pointsToBytesRO_cons,
            sepConj_assoc] at hmcall ⊢
          apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
            (mid := lsmpl.base 110) hcrl0
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl1, hro1⟩
          wp_apply using hkeylen
          apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
            (mid := lsρ lsRustNoAllocShimSymCli) ‹_›
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl2, hro2⟩
          wp_apply using hshim
          apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
            (mid := lsρ lsRustAllocSymCli) ‹_›
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl3, hro3⟩
          wp_apply using halloc
          by_cases hoom : sf_2.readReg64 Reg.x0 = 0
          · have hoom64 : sf_2.readReg64 Reg.x0 = 0#64 := hoom
            simp only [hoom, ite_true]
            rw [pull_alloc_pure_placed]
            refine SepWPp.pure_elim fun htrace => ?_
            apply SepWPp.of_sepWP (mid := lsρ lsHandleAllocErrorSymCli)
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) hpanic_at fun hm => ?_
            simpa only [sepConj_assoc] using
              allowPanic_panicked
                (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
          · simp only [hoom, ite_false, sepConj_assoc]
            have hoom_beq : (sf_2.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
            rw [pull_alloc_pure_placed]
            refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
            have htr_sf2 : sf_2.trace = s0.trace := by
              rw [htr2]; simp only [wp_norm, arm64_norm, *]
            apply sepWPp_ok_ret_placed (sf_2.readReg64 Reg.x0) hrlen_keep hoom
            apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ memcpyName) ‹_›
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            rintro ⟨hcl4, hro4⟩
            wp_apply using hmcall
            wp_steps
            wp_done
      · have hne1569 : BitVec.ofNat 64 (rest.length + 1) ≠ 1569#64 :=
          ofNat_ne_1569_placed (by simp [kemPkLen] at hrlen; omega) hlen_lt64
        have hbeq1569 : (BitVec.ofNat 64 (rest.length + 1) == 1569#64) = false :=
          beq_false_of_ne hne1569
        rw [List.length_cons] at *
        simp only [hrlen, not_false_eq_true, ↓reduceIte, kemDeserResAt,
          memRegion_24_split_badLen_placed r, sepExists_sepConj_left, sepConj_assoc]
        refine SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w0 => ?_
        apply SepWPp.of_sepWP_ret
        cases ro
        · simp only [SpqrV1.ChainProofs.bytesAt_false, ProofLib.pointsToBytes_cons, sepConj_assoc]
          apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro
            (mid := lsmpl.base 110) hcrl0
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl1, hro1⟩
          wp_apply using hkeylen
          wp_steps
          wp_done
        · simp only [SpqrV1.ChainProofs.bytesAt_true, ProofLib.pointsToBytesRO_cons, sepConj_assoc]
          apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro
            (mid := lsmpl.base 110) hcrl0
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl1, hro1⟩
          wp_apply using hkeylen
          wp_steps
          wp_done
    · have hne32 := byte_zext32_ne8_placed ht
      have hne64 := byte_zext64_ne8_placed ht
      have hsub32 : t.zeroExtend 32 - 8#32 ≠ 0#32 := by bv_omega
      have hsub64 : t.zeroExtend 64 - 8#64 ≠ 0#64 := by bv_omega
      have hbeq_sub32 : (t.zeroExtend 32 - 8#32 == 0#32) = false := beq_false_of_ne hsub32
      have hbeq8_32 : (t.zeroExtend 32 == 8#32) = false := beq_false_of_ne hne32
      have hbeq8_64 : (t.zeroExtend 64 == 8#64) = false := beq_false_of_ne hne64
      rw [List.length_cons] at *
      simp only [kemPkDeserialize, ne_eq, ht, not_false_eq_true, ↓reduceIte,
        kemDeserResAt, memRegion_24_split_badType_placed r, sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun b1 => SepWPp.exists_elim fun w0 => ?_
      apply SepWPp.of_sepWP_ret
      cases ro
      · simp only [SpqrV1.ChainProofs.bytesAt_false, ProofLib.pointsToBytes_cons, sepConj_assoc]
        wp_steps
        wp_done
      · simp only [SpqrV1.ChainProofs.bytesAt_true, ProofLib.pointsToBytesRO_cons, sepConj_assoc]
        wp_steps
        wp_done

end KemDeserializePlacedHelpers

/-- `kem::Key<Public>::deserialize` (Block `590`) satisfies `cliKemDeserializeSpecPlaced`. -/
theorem cliKemDeserialize_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hpanic : H lsHandleAllocErrorSymCli = some Rust.panicked)
    (stk : Nat) (hstk : 48 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_590 H) (blkPl_590).base
      (cliKemDeserializeSpecPlaced A stk) := by
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliKemDeserStack))
    (cliKemDeserialize_exact_placed_ok hA hRO hpanic) ?_ ?_ ?_ (fun _ _ _ _ => rfl)
  · intro x s0
    dsimp only [cliKemDeserializeSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      cliKemDeserializeSpec]
    rw [stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by ac_rfl)
  · intro x s0 sf
    dsimp only [cliKemDeserializeSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      cliKemDeserializeSpec]
    rw [stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by ac_rfl)
  · intro _ s0 sf
    dsimp only [cliKemDeserializeSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      cliKemDeserializeSpec]
    rw [sepConj_assoc]
    exact sepConj_mono_right (entails_anyHeap _)

/-- Cross-block transfer of `cliKemDeserialize_placed_ok` to any caller block `i < 619`
(e.g. `run` at Block `579`). -/
theorem cliKemDeserialize_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hpanic : H lsHandleAllocErrorSymCli = some Rust.panicked)
    (stk : Nat) (hstk : 48 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_590).base
      (cliKemDeserializeSpecPlaced A stk) := by
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_590 H) i 590 H
    hcaller (instIsLsBlockProg_590 H) (blkPl_590).base _
    (cliKemDeserialize_placed_ok hA hRO hpanic stk hstk hstk64)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

end CryptoVerification.SignalSession.Cli.RunProofs
