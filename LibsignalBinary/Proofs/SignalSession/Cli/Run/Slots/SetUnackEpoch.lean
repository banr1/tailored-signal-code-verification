/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.E2E.Bin.SendSegsCommon
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Bin CryptoVerification.E2E.HooksE
open CryptoVerification.E2E.Run
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.InMem
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit Initiator.bv_sub_add_lit' BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_send sp_setMem_setPC_pre_send
  readReg64_setPC_pre_send readReg64_setMem_setPC_pre_send
  readReg32_setPC_pre_send readReg32_setMem_setPC_pre_send
  readReg_setPC_pre_send readReg_setMem_setPC_pre_send
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
  conditionHolds_mi_subsPState64 conditionHolds_pl_subsPState64
  conditionHolds_hi_addsPState64
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64
attribute [local arm64_norm, local wp_norm]
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_32 bv_add_neg_36
  CryptoVerification.E2E.Pqxdh.TopLevel.bv_add_neg_0x60
  bv_add_neg_728 bv_add_neg_828 bv_add_neg_864 bv_add_neg_904 bv_add_neg_944
  bv_add_neg_1000 bv_add_neg_1032 bv_add_neg_1048 bv_add_neg_1056 bv_add_neg_1068 bv_add_neg_1072
    bv_add_neg_1116 bv_add_neg_1144
  bv_add_neg_1444 bv_add_neg_2088 bv_add_neg_2108 bv_add_neg_2132 bv_add_neg_2400
  bv_add_neg_2536 bv_add_neg_2684 bv_add_neg_0xb20 bv_add_neg_3032
  bv_add_bl_0x123d0 bv_add_bl_0x17490 bv_add_bl_0x49e80
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32 ProofLib.reduceStateReadReg
attribute [-arm64_norm]
  SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  SpqrV1.Kdf.HkdfToSliceProof.read8_write64_264_271
  SpqrV1.Kdf.HkdfToSliceProof.read8_write64_408_415
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint

/-!
# `SessionState::set_unacknowledged_pre_key_message` at `UNIX_EPOCH`

Verifies `SessionState::set_unacknowledged_pre_key_message` when `now = UNIX_EPOCH` (`x5 = 0`,
`w6 = 0`) against `setUnackPreKeyMsgExactStackEpochSpec` on `trTrapProgAt` and `cliExterns W`, and
against the 16-KiB `setUnackPreKeyMsgExtStackEpochSpec` under `CliExternsOk P A ext`.

## 1. `UNIX_EPOCH` stack specification (`setUnackPreKeyMsgExactStackEpochSpec`)
-/

def setUnackPreKeyMsgExactStackEpochSpec (A : RustAlloc) (img : Obj.Image) :
    Spec Pqxdh.TopLevel.SetUnackExactGhost :=
  { Pqxdh.TopLevel.setUnackPreKeyMsgExactStackSpec A img with
    pre := fun g s =>
      ⌜s.readReg64 .x5 = 0#64 ∧ (s.readReg64 .x6).setWidth 32 = 0#32⌝ ∗
        (Pqxdh.TopLevel.setUnackPreKeyMsgExactStackSpec A img).pre g s }

/-! ## 2. Stub and layout helpers -/

private theorem sessionShim_hookOk_std3 : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

private theorem hookSat_trTrap_std3 {α : Type} (C : Crypto)
    (abs : String → Option (State → State)) {sym : String} {spec : Spec α}
    (heq : trTrapExterns C abs sym = abs sym)
    (h : HookSat abs sym spec) :
    HookSat (trTrapExterns C abs) sym spec := by
  unfold HookSat at *; rwa [heq]

private theorem shim_ok_at_trap_std3 (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  hook_ok_at (hname := shimName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, shimName])
    ⟨_, rfl, sessionShim_hookOk_std3⟩

private theorem alloc_ok_at_trap_std3 (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : CryptoVerification.RustHeap.AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  hook_ok_at (hname := allocName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, allocName])
    (hookSat_trTrap_std3 C abs rfl hA.alloc)

private theorem dealloc_ok_at_trap_std3 (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : CryptoVerification.RustHeap.AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  hook_ok_at (hname := deallocName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, deallocName])
    (hookSat_trTrap_std3 C abs rfl hA.dealloc)

private theorem session_memcpy_region_ok_at_trap_std3 (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) sessionMemcpyRegionSpec :=
  hook_ok_at (hname := memcpyName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memcpyName])
    ⟨_, rfl, LibsignalTripleRatchet.hookMemcpy_region_trace_ok⟩

private theorem durationSinceEpochAlloc_ok_at_trap_std3 {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hTime : HookSat absHooks E2E.durationSinceName durationSinceEpochAllocSpec)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff E2E.durationSinceName) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr name + BitVec.ofNat 64 k)
      durationSinceEpochAllocSpec :=
  hook_ok_at (hname := E2E.durationSinceName) rfl hk
    (by rw [(ls_stub% "<std::time::SystemTime>::duration_since")]; decide)
    (fun H => by
      rw [(ls_stub% "<std::time::SystemTime>::duration_since")]
      exact (ls_hook% "<std::time::SystemTime>::duration_since") H)
    (by simp [Rust.isPanicSymbol, E2E.durationSinceName])
    (hookSat_trTrap_std3 C absHooks rfl hTime)

private theorem panic_at_handle_error_trap_std3 (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff handleErrorName) :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_panicSymbol (hname := handleErrorName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, handleErrorName])

private theorem memRegion_33_cells_epoch (a : BitVec 64) :
    memRegion a 33 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗
      (∃∗ u0 : BitVec 64, (a + 1#64) ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (a + 9#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (a + 17#64) ↦₆₄ u2) ∗
      (∃∗ u3 : BitVec 64, (a + 25#64) ↦₆₄ u3) := by
  rw [ProofLib.memRegion_split a 1 32 (by decide),
    ProofLib.memRegion_split (a + 1#64) 8 24 (by decide),
    ProofLib.memRegion_split (a + 1#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 1#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem bytesToBv8_encodeEC_epoch (bs : Initiator.Bytes) :
    Initiator.bytesToBv8 (Initiator.encodeEC bs) = 5#8 :: Initiator.bytesToBv8 bs := rfl

private def ecPubKeySerializeRawSpec' (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × Initiator.Bytes) where
  pre := fun (keyPtr, keyBytes) s =>
    ⌜s.readReg64 .x0 = keyPtr ∧ keyBytes.length = 32⌝ ∗ (keyPtr ↦ₛ Initiator.bytesToBv8 keyBytes) ∗
      stackAt (s.sp - 32#64) RustHeap.allocHookStack ∗
    cells (s.sp - 32#64) 4 ∗ A.pool
  post := fun (keyPtr, keyBytes) s0 sf =>
    ∃∗ slicePtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = slicePtr ∧ sf.readReg64 .x1 = 33#64 ∧
        slicePtr ≠ 0⌝ ∗
      (keyPtr ↦ₛ Initiator.bytesToBv8 keyBytes) ∗
      (slicePtr ↦ₛ Initiator.bytesToBv8 (Initiator.encodeEC keyBytes)) ∗
        A.live slicePtr 33 1 ∗
      stackAt (s0.sp - 32#64) RustHeap.allocHookStack ∗ cells (s0.sp - 32#64) 4 ∗ A.pool
  onPanic := rustPanicOnOom img

private theorem ecPubKeySerializeRawSpec'_eq (A : RustAlloc) (img : Obj.Image) :
    ecPubKeySerializeRawSpec' A img = ecPubKeySerializeRawSpec A img := rfl

private theorem hook_shim_at_hooks_std3 (b : BitVec 64)
    (hooks : String → Option (State → State))
    (hShim : HookSat hooks shimName CliExt.shimSpec) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (tripleRatchetProgAtExt b hooks)
      ((tripleRatchetProgAtExt b hooks).fnAddr name + BitVec.ofNat 64 k) CliExt.shimSpec :=
  hook_ok_at (hname := shimName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, shimName]) hShim

private theorem hook_alloc_at_hooks_std3 (b : BitVec 64) (A : RustAlloc)
    (hooks : String → Option (State → State))
    (hAlloc : HookSat hooks allocName (rustAllocSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName) :
    subroutine_ok (tripleRatchetProgAtExt b hooks)
      ((tripleRatchetProgAtExt b hooks).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  hook_ok_at (hname := allocName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, allocName]) hAlloc

private theorem panic_at_handle_error_hooks_std3 (b : BitVec 64)
    (hooks : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff handleErrorName) :
    (tripleRatchetProgAtExt b hooks).externAt?
      ((tripleRatchetProgAtExt b hooks).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_panicSymbol (hname := handleErrorName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, handleErrorName])

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
private theorem ecPubKeySerializeRaw_ok_hooks {A : RustAlloc} {img : Obj.Image}
    {hooks : String → Option (State → State)}
    (hShim : HookSat hooks shimName CliExt.shimSpec)
    (hAlloc : HookSat hooks allocName (rustAllocSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base hooks)
      ((tripleRatchetProgAtExt img.base hooks).fnAddr ecPubKeySerializeSym)
      (ecPubKeySerializeRawSpec' A img) := by
  unfold ecPubKeySerializeRawSpec' rustPanicOnOom
  simp only [bytesToBv8_encodeEC_epoch]
  cells_unfold
  have hshim := hook_shim_at_hooks_std3 img.base hooks hShim ecPubKeySerializeSym
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := hook_alloc_at_hooks_std3 img.base A hooks hAlloc ecPubKeySerializeSym
    (num% (ls_off% "__rustc::__rust_alloc" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "__rustc::__rust_alloc")])
  have hpanic := panic_at_handle_error_hooks_std3 img.base hooks ecPubKeySerializeSym
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hShim hAlloc
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff ecPubKeySerializeSym = 0x3e2c4 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics hooks) hfn 0x3e2c4 84
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics hooks)).fnAddr ecPubKeySerializeSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics hooks)).fnAddr ecPubKeySerializeSym = entry
  examples_hide_fetches
  obtain ⟨keyPtr, keyBytes⟩ := g
  dsimp only at *
  have hlen_key : keyBytes.length = 32 := ‹_›
  have hlen_bv : (Initiator.bytesToBv8 keyBytes).length = 32 := by
    simp [Initiator.bytesToBv8, hlen_key]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hlen_bv
  rw [hpk_cells keyPtr]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 32#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine Initiator.sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x3e2c4))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (Initiator.allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
        ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_33_cells_epoch, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u0 =>
      SepWPp.exists_elim fun u1 => SepWPp.exists_elim fun u2 =>
      SepWPp.exists_elim fun u3 => ?_
    refine Initiator.sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [pointsToBytes_cons, hpk_cells, BitVec.add_assoc, BitVec.reduceAdd]
    wp_done

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_neg1_1_true_epoch :
    ConditionHolds CondCode.LT (subsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ite_zero64_epoch (b : Bool) : (if b = true then 0#64 else 0#64) = 0#64 := by
  cases b <;> rfl

private theorem memRegion_16_split_64_epoch (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) := by
  rw [ProofLib.memRegion_split a 8 8 (by decide), ProofLib.memRegion_eight a,
    ProofLib.memRegion_eight (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem memRegion_24_split_64_epoch (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]

private theorem pointsTo64_triple_entails_memRegion24_epoch (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion_24_split_64_epoch a]
  exact Entails.sepExists_right w2 (Entails.sepExists_right w1
    (Entails.sepExists_right w0 (Entails.refl _)))

private theorem memRegion_40_unack_split_epoch (statePtr : BitVec 64) :
    memRegion (statePtr + 0x100#64) 40 =
      (∃∗ w100 : BitVec 64, (statePtr + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (statePtr + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 32, (statePtr + 0x110#64) ↦₃₂ w110) ∗
      (∃∗ w114 : BitVec 32, (statePtr + 0x114#64) ↦₃₂ w114) ∗
      (∃∗ w118 : BitVec 64, (statePtr + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (statePtr + 0x120#64) ↦₃₂ w120) ∗
      memRegion (statePtr + 0x124#64) 4 := by
  rw [ProofLib.memRegion_split (statePtr + 0x100#64) 8 32 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64) 4 20 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64) 4 16 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 8 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64) 4 4
      (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_four, ProofLib.memRegion_four,
    ProofLib.memRegion_eight, ProofLib.memRegion_four]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_setUnack_call_epoch (sp : BitVec 64) :
    stackAt (sp - 144#64) (RustHeap.allocHookStack + 32) =
      stackAt (sp - 176#64) RustHeap.allocHookStack ∗ cells (sp - 176#64) 4 := by
  have h1 := ProofLib.stackAt_split_cells (sp - 144#64) RustHeap.allocHookStack 4 (by decide)
  have h2 : sp - 144#64 - BitVec.ofNat 64 (8 * 4) = sp - 176#64 := by bv_arith
  rw [h2] at h1
  exact h1

private theorem stackAt_setUnack_hooks_epoch (sp : BitVec 64) :
    stackAt (sp - 176#64) RustHeap.allocHookStack ∗ cells (sp - 176#64) 4 =
      memRegion (sp - 4272#64) 32 ∗ stackAt (sp - 144#64) RustHeap.allocHookStack := by
  rw [← stackAt_setUnack_call_epoch sp]
  have h1 := Initiator.stackAt_split_top (sp - 144#64) 32 RustHeap.allocHookStack (by decide)
  have h2 : (32 + RustHeap.allocHookStack : Nat) = RustHeap.allocHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (32 + RustHeap.allocHookStack) = 4128#64 := rfl
  have h4 : sp - 144#64 - 4128#64 = sp - 4272#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

private theorem pointsToBytes_entails_memRegion_33_epoch (p : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 33) : (p ↦ₛ bs) ⊢ memRegion p 33 := by
  rw [← h]; exact ProofLib.pointsToBytes_entails_memRegion p bs

private theorem cells_pre_unfold_18_epoch (sp : BitVec 64) :
    cells (sp - 144#64) 18 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
       ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
       ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64,
       ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c14 : BitVec 64,
       ∃∗ c15 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c17 : BitVec 64,
        ((sp - 144#64) ↦₆₄ c0) ∗ ((sp - 136#64) ↦₆₄ c1) ∗ ((sp - 128#64) ↦₆₄ c2) ∗
        ((sp - 120#64) ↦₆₄ c3) ∗ ((sp - 112#64) ↦₆₄ c4) ∗ ((sp - 104#64) ↦₆₄ c5) ∗
        ((sp - 96#64) ↦₆₄ c6) ∗ ((sp - 88#64) ↦₆₄ c7) ∗ ((sp - 80#64) ↦₆₄ c8) ∗
        ((sp - 72#64) ↦₆₄ c9) ∗ ((sp - 64#64) ↦₆₄ c10) ∗ ((sp - 56#64) ↦₆₄ c11) ∗
        ((sp - 48#64) ↦₆₄ c12) ∗ ((sp - 40#64) ↦₆₄ c13) ∗ ((sp - 32#64) ↦₆₄ c14) ∗
        ((sp - 24#64) ↦₆₄ c15) ∗ ((sp - 16#64) ↦₆₄ c16) ∗ ((sp - 8#64) ↦₆₄ c17)) := by
  cells_unfold

private theorem fnAddr_ecPubKeySerialize_from_setUnack_trap (b : BitVec 64)
    (C : Crypto) (absHooks : String → Option (State → State)) :
    (trTrapProgAt b C absHooks).fnAddr ecPubKeySerializeSym =
      (trTrapProgAt b C absHooks).fnAddr setUnackPreKeyMsgSym + 180268#64 := by
  simp only [trTrapProgAt, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x12298,
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4, BitVec.add_assoc]
  rfl

/-! ## 3. Exact-stack proofs (`_trap`, `_ok`, `_cli`) -/

private def setUnackPreKeyMsgEpochAtSpec (totalStk : Nat) (A : RustAlloc) (img : Obj.Image) :
    Spec Pqxdh.TopLevel.SetUnackExactGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x5 = 0#64 ∧ (s.readReg64 .x6).setWidth 32 = 0#32⌝ ∗
      (⌜s.readReg64 .x0 = g.statePtr ∧
        (s.readReg64 .x1).setWidth 32 = g.optOpkTag ∧
        (s.readReg64 .x2).setWidth 32 = g.optOpkVal ∧
        (s.readReg64 .x3).setWidth 32 = g.spkId ∧
        s.readReg64 .x4 = g.baseKeyPtr ∧
        g.baseKeyBytes.length = 32⌝ ∗
      (g.baseKeyPtr ↦ₛ Initiator.bytesToBv8 g.baseKeyBytes) ∗
      ((g.statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.statePtr + 0x100#64) 40 ∗
      stackAt (s.sp - 144#64) totalStk ∗
      cells (s.sp - 144#64) 18 ∗
      A.pool)
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (g.baseKeyPtr ↦ₛ Initiator.bytesToBv8 g.baseKeyBytes) ∗
    Initiator.vecU8 A (g.statePtr + 0xf8#64) (Initiator.bytesToBv8 (encodeEC g.baseKeyBytes)) ∗
    ((g.statePtr + 0x110#64) ↦₃₂ g.optOpkTag) ∗
    ((g.statePtr + 0x114#64) ↦₃₂ g.optOpkVal) ∗
    ((g.statePtr + 0x118#64) ↦₆₄ 0#64) ∗
    ((g.statePtr + 0x120#64) ↦₃₂ g.spkId) ∗
    memRegion (g.statePtr + 0x124#64) 4 ∗
    stackAt (s0.sp - 144#64) totalStk ∗
    cells (s0.sp - 144#64) 18 ∗
    A.pool
  onPanic := rustPanicOnOom img

private theorem hookOk_cliMemcpy_of_region_std3 {h : State → State}
    (hh : HookOk h sessionMemcpyRegionSpec) : HookOk h CliExt.memcpySpec := by
  intro x R s0 hrun hpre hsp
  rcases x with ⟨dst, src, bs⟩
  dsimp only [CliExt.memcpySpec, libcMemcpySpec] at hpre
  simp only [sepConj_assoc] at hpre
  obtain ⟨hkf, hsym, hout⟩ :=
    hh (dst, src, bs) (stackAt s0.sp CliExt.memHookStack ∗ R) s0 hrun
      (by dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
          simpa only [sepConj_assoc] using hpre)
      hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemcpyRegionSpec] at hpost
    dsimp only [CliExt.memcpySpec]
    simpa only [sepConj_assoc] using hpost
  · refine False.elim ?_
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hpan
    exact ((satisfies_pure_sepConj _ _ _).mp (by simpa only [sepConj_assoc] using hpan.2)).1
  · refine False.elim ?_
    rcases hex with ⟨_, _, hex2⟩
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hex2
    exact ((satisfies_pure_sepConj _ _ _).mp (by simpa only [sepConj_assoc] using hex2)).1
  · refine False.elim ?_
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hoom
    exact ((satisfies_pure_sepConj _ _ _).mp (by simpa only [sepConj_assoc] using hoom.2)).1

private theorem hook_dealloc_at_hooks_std3 (b : BitVec 64) (A : RustAlloc)
    (hooks : String → Option (State → State))
    (hDealloc : HookSat hooks deallocName (rustDeallocSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName) :
    subroutine_ok (tripleRatchetProgAtExt b hooks)
      ((tripleRatchetProgAtExt b hooks).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  hook_ok_at (hname := deallocName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, deallocName]) hDealloc

private theorem hook_memcpy_at_hooks_std3 (b : BitVec 64)
    (hooks : String → Option (State → State))
    (hMemcpy : HookSat hooks memcpyName CliExt.memcpySpec) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (tripleRatchetProgAtExt b hooks)
      ((tripleRatchetProgAtExt b hooks).fnAddr name + BitVec.ofNat 64 k) CliExt.memcpySpec :=
  hook_ok_at (hname := memcpyName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memcpyName]) hMemcpy

private theorem hook_durationSince_at_hooks_std3 (b : BitVec 64) (timeStk : Nat)
    (hooks : String → Option (State → State))
    (hTime : HookSat hooks E2E.durationSinceName (durationSinceEpochAtSpec timeStk))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff E2E.durationSinceName) :
    subroutine_ok (tripleRatchetProgAtExt b hooks)
      ((tripleRatchetProgAtExt b hooks).fnAddr name + BitVec.ofNat 64 k)
      (durationSinceEpochAtSpec timeStk) :=
  hook_ok_at (hname := E2E.durationSinceName) rfl hk
    (by rw [(ls_stub% "<std::time::SystemTime>::duration_since")]; decide)
    (fun H => by
      rw [(ls_stub% "<std::time::SystemTime>::duration_since")]
      exact (ls_hook% "<std::time::SystemTime>::duration_since") H)
    (by simp [Rust.isPanicSymbol, E2E.durationSinceName]) hTime

private theorem fnAddr_ecPubKeySerialize_from_setUnack_hooks (b : BitVec 64)
    (hooks : String → Option (State → State)) :
    (tripleRatchetProgAtExt b hooks).fnAddr ecPubKeySerializeSym =
      (tripleRatchetProgAtExt b hooks).fnAddr setUnackPreKeyMsgSym + 180268#64 := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x12298,
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4, BitVec.add_assoc]
  rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 3200000 in
private theorem setUnackPreKeyMsg_epoch_ok_hooks {A : RustAlloc} {img : Obj.Image}
    {hooks : String → Option (State → State)} {totalStk timeStk : Nat}
    {F_call F_4k F_time : BitVec 64 → SepProp}
    (hShim : HookSat hooks shimName CliExt.shimSpec)
    (hAlloc : HookSat hooks allocName (rustAllocSpec A))
    (hDealloc : HookSat hooks deallocName (rustDeallocSpec A))
    (hMemcpy : HookSat hooks memcpyName CliExt.memcpySpec)
    (hTime : HookSat hooks E2E.durationSinceName (durationSinceEpochAtSpec timeStk))
    (h_call : ∀ sp, stackAt (sp - 144#64) totalStk =
      F_call sp ∗ stackAt (sp - 176#64) RustHeap.allocHookStack ∗ cells (sp - 176#64) 4)
    (h_after_ser : ∀ sp, F_call sp ∗
        stackAt (sp - 176#64) RustHeap.allocHookStack ∗ cells (sp - 176#64) 4 =
      F_4k sp ∗ stackAt (sp - 144#64) RustHeap.allocHookStack)
    (h_to_time : ∀ sp, F_4k sp ∗ stackAt (sp - 144#64) RustHeap.allocHookStack =
      F_time sp ∗ stackAt (sp - 144#64) timeStk) :
    subroutine_ok (tripleRatchetProgAtExt img.base hooks)
      ((tripleRatchetProgAtExt img.base hooks).fnAddr setUnackPreKeyMsgSym)
      (setUnackPreKeyMsgEpochAtSpec totalStk A img) := by
  unfold setUnackPreKeyMsgEpochAtSpec rustPanicOnOom
  have hser :
      subroutine_ok (tripleRatchetProgAtExt img.base hooks)
        ((tripleRatchetProgAtExt img.base hooks).fnAddr setUnackPreKeyMsgSym + 180268#64)
        (ecPubKeySerializeRawSpec' A img) :=
    (fnAddr_ecPubKeySerialize_from_setUnack_hooks img.base hooks).symm ▸
      ecPubKeySerializeRaw_ok_hooks (img := img) hShim hAlloc
  have hshim := hook_shim_at_hooks_std3 img.base hooks hShim setUnackPreKeyMsgSym
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x12298))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x12298,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := hook_alloc_at_hooks_std3 img.base A hooks hAlloc setUnackPreKeyMsgSym
    (num% (ls_off% "__rustc::__rust_alloc" - 0x12298))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x12298,
      (ls_stub% "__rustc::__rust_alloc")])
  have hmemcpy := hook_memcpy_at_hooks_std3 img.base hooks hMemcpy setUnackPreKeyMsgSym
    (num% (ls_off% "memcpy" - 0x12298))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x12298,
      (ls_stub% "memcpy")])
  have htime := hook_durationSince_at_hooks_std3 img.base timeStk hooks hTime setUnackPreKeyMsgSym
    (num% (ls_off% "<std::time::SystemTime>::duration_since" - 0x12298))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x12298,
      (ls_stub% "<std::time::SystemTime>::duration_since")])
  have hdealloc := hook_dealloc_at_hooks_std3 img.base A hooks hDealloc setUnackPreKeyMsgSym
    (num% (ls_off% "__rustc::__rust_dealloc" - 0x12298))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x12298,
      (ls_stub% "__rustc::__rust_dealloc")])
  have hpanic := panic_at_handle_error_hooks_std3 img.base hooks setUnackPreKeyMsgSym
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x12298))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x12298,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hShim hAlloc hDealloc hMemcpy hTime
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff setUnackPreKeyMsgSym = 0x12298 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x12298
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.setUnackPreKeyMsg img.base
    (Rust.withPanics hooks) hfn 0x12298 312
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics hooks)).fnAddr setUnackPreKeyMsgSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hser hshim halloc hmemcpy htime hdealloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics hooks)).fnAddr setUnackPreKeyMsgSym = entry
  examples_hide_fetches
  obtain ⟨statePtr, optOpkTag, optOpkVal, spkId, baseKeyPtr, baseKeyBytes⟩ := g
  dsimp only at *
  have hx5 : s0.readReg64 (.gpr 5#5) = 0#64 := ‹_›
  have hx6 : (s0.readReg64 (.gpr 6#5)).setWidth 32 = 0#32 := ‹_›
  have hx6_ext : (s0.readReg64 (.gpr 6#5)).extractLsb' 0 32 = 0#32 := by
    ext i hi
    have := congrArg (fun v => v[i]) hx6
    simpa using this
  have hlen_base : baseKeyBytes.length = 32 := ‹_›
  subst h_3 h_4 h_5 h_6 h_7
  have hlen_enc : (Initiator.bytesToBv8 (Initiator.encodeEC baseKeyBytes)).length = 33 := by
    change (5#8 :: Initiator.bytesToBv8 baseKeyBytes).length = 33
    simp [Initiator.bytesToBv8, hlen_base]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  rw [memRegion_40_unack_split_epoch (s0.readReg64 (.gpr 0#5))]
  rw (occs := .pos [1]) [cells_pre_unfold_18_epoch s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 => SepWPp.exists_elim fun c2 => ?_
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  rw (occs := .pos [1]) [h_call s0.sp]
  rw [pointsTo64_split32' (s0.sp - 128#64)]
  simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  apply SepWPp.of_sepWP (mid := entry + 180268#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 4#5), baseKeyBytes)) hser
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [State.spAligned, arm64_norm, hsp_align])
    (ret_pc := entry + 64#64) (by wp_norm_lhs)
    (by dsimp only [ecPubKeySerializeRawSpec']; simp only [arm64_norm, BitVec.sub_sub,
      BitVec.reduceAdd]; rfl)
    hlen_base
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ hm => by
      dsimp only [ecPubKeySerializeRawSpec', rustPanicOnOom] at hm
      rw [← sepConj_assoc]
      exact allowPanic_frame (by simp only [allocFailedIn, arm64_norm]; exact id) hm)
    (fun sm hpcm hrunm hspm hcsm => ?_)
  simp only [arm64_norm] at hspm
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm
  rcases hcsm with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, _⟩
  simp only [arm64_norm] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29
  clear hpre
  dsimp only [ecPubKeySerializeRawSpec']
  simp only [arm64_norm, BitVec.sub_sub, BitVec.reduceAdd,
    sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun slicePtr => ?_
  refine SepWPp.pure_left fun ⟨htr_sm, hx0_sm, hx1_sm, hne_slice⟩ => ?_
  apply SepWPp.of_sepWP (mid := entry + 116#64)
  apply Initiator.SepWP.replace_pre (by sep_focus) (Entails.of_eq (h_after_ser s0.sp))
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true]
    refine Initiator.sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x12298))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm =>
      ⟨Initiator.allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm]; rw [htrace,
        ‹sf.trace = sm.trace›, htr_sm]),
        Arm64.Satisfies.mono (sepConj_mono_left (ent_anyHeap _)) hm⟩
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine Initiator.sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    have hsp1 : sf_1.sp = s0.sp - 144#64 := by
      rw [‹sf_1.sp = sf.sp›, ‹sf.sp = sm.sp›, hspm]
    rw [‹sf.sp = sm.sp›, hspm, ← hlen_enc]
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), slicePtr,
      Initiator.bytesToBv8 (Initiator.encodeEC baseKeyBytes))
    rw [hsp1]
    wp_steps
    have h136_eq : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_arith
    have h136_12 : s0.sp - 136#64 + 12#64 = s0.sp - 124#64 := by bv_arith
    have h120_8 : s0.sp - 120#64 + 8#64 = s0.sp - 112#64 := by bv_arith
    have h120_16 : s0.sp - 120#64 + 16#64 = s0.sp - 104#64 := by bv_arith
    have h124_ent : ∀ v, ((s0.sp - 124#64) ↦₃₂ v) ⊢ memRegion (s0.sp - 136#64 + 12#64) 4 := by
      intro v; rw [h136_12]; exact pointsTo32_entails_memRegion (s0.sp - 124#64) v
    rw [← h136_eq]
    apply Initiator.SepWP.replace_pre (by sep_focus) (h124_ent _)
    apply Initiator.SepWP.replace_pre (by sep_focus)
      (h120_8 ▸ h120_16 ▸ pointsTo64_triple_entails_memRegion24_epoch (s0.sp - 120#64) _ _ _)
    apply Initiator.SepWP.replace_pre (by sep_focus) (Entails.of_eq (h_to_time s0.sp))
    have hsp2 : sf_2.sp = s0.sp - 144#64 := by rw [‹sf_2.sp = sf_1.sp›, hsp1]
    wp_call htime (s0.sp - 136#64, s0.sp - 120#64)
    rw [hsp2]
    apply Initiator.SepWP.replace_pre (by sep_focus) (Entails.of_eq (h_to_time s0.sp).symm)
    rw [memRegion_16_split_64_epoch (s0.sp - 136#64), h136_eq]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists
    wp_steps
    apply Initiator.SepWP.replace_pre (by sep_focus)
      (pointsToBytes_entails_memRegion_33_epoch slicePtr _ hlen_enc)
    rw [← hsp2, ← ‹sf_3.sp = sf_2.sp›]
    wp_call hdealloc (slicePtr, 33, 1)
    wp_steps
    apply Initiator.SepWP.replace_pre (by sep_focus)
      (Entails.of_eq ((h_call s0.sp).trans (h_after_ser s0.sp)).symm)
    clear h_call h_after_ser h_to_time
    simp only [ite_self, *] at *
    dsimp only [Initiator.vecU8]
    rw [cells_pre_unfold_18_epoch s0.sp]
    wp_done

private theorem sessionShimSpec_eq_cliExt : sessionShimSpec = CliExt.shimSpec := by
  unfold sessionShimSpec CliExt.shimSpec
  rfl

private theorem setUnackPreKeyMsgEpochAtSpec_exact (A : RustAlloc) (img : Obj.Image) :
    setUnackPreKeyMsgEpochAtSpec (RustHeap.allocHookStack + 32) A img =
      setUnackPreKeyMsgExactStackEpochSpec A img := by
  unfold setUnackPreKeyMsgEpochAtSpec setUnackPreKeyMsgExactStackEpochSpec
    Pqxdh.TopLevel.setUnackPreKeyMsgExactStackSpec
  rfl

theorem setUnackPreKeyMsg_exact_stack_epoch_ok_trap {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hA : CryptoVerification.RustHeap.AllocHooks A absHooks)
    (hTime : HookSat absHooks E2E.durationSinceName durationSinceEpochAllocSpec) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr setUnackPreKeyMsgSym)
      (setUnackPreKeyMsgExactStackEpochSpec A img) := by
  dsimp only [tripleRatchetProgAt_eq_tripleRatchetProgAtExt_trap]
  exact Eq.mp
    (congrArg
      (subroutine_ok (tripleRatchetProgAtExt img.base (trTrapExterns C absHooks))
        ((tripleRatchetProgAtExt img.base (trTrapExterns C absHooks)).fnAddr setUnackPreKeyMsgSym))
      (setUnackPreKeyMsgEpochAtSpec_exact A img))
    (setUnackPreKeyMsg_epoch_ok_hooks
      (A := A) (img := img)
      (hooks := trTrapExterns C absHooks)
      (totalStk := RustHeap.allocHookStack + 32)
      (timeStk := RustHeap.allocHookStack)
      (F_call := fun _ => emp)
      (F_4k := fun sp => memRegion (sp - 4272#64) 32)
      (F_time := fun sp => memRegion (sp - 4272#64) 32)
      ⟨_, rfl, Eq.mp (congrArg (HookOk hookNoop) sessionShimSpec_eq_cliExt) sessionShim_hookOk_std3⟩
      (hookSat_trTrap_std3 C absHooks rfl hA.alloc)
      (hookSat_trTrap_std3 C absHooks rfl hA.dealloc)
      ⟨_, rfl, hookOk_cliMemcpy_of_region_std3 LibsignalTripleRatchet.hookMemcpy_region_trace_ok⟩
      (hookSat_trTrap_std3 C absHooks rfl hTime)
      (fun sp => by rw [emp_sepConj]; exact stackAt_setUnack_call_epoch sp)
      (fun sp => by rw [emp_sepConj]; exact stackAt_setUnack_hooks_epoch sp)
      (fun _ => rfl))

theorem setUnackPreKeyMsg_exact_stack_epoch_ok {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hA : CryptoVerification.RustHeap.AllocHooks A absHooks)
    (hTime : HookSat absHooks E2E.durationSinceName durationSinceEpochAllocSpec) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr setUnackPreKeyMsgSym)
      (setUnackPreKeyMsgExactStackEpochSpec A img) := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl absHooks).fnAddr setUnackPreKeyMsgSym]
  exact subroutine_ok_kit_of_trTrap
    (setUnackPreKeyMsg_exact_stack_epoch_ok_trap hA hTime)

private theorem cliHookNames_nodup_std3 : cliHookNames.Nodup := by
  unfold cliHookNames
  decide

private theorem cliHookNames_notPanic_epoch_std3 :
    cliHookNames.all (fun n => !E2E.isImagePanicSymbol n) = true := by
  rw [List.all_eq_true]
  intro n hn
  simp only [cliHookNames, E2E.compress512Name, E2E.toEdwardsName, E2E.compressName, E2E.edNegName,
    E2E.torsionFreeName, E2E.dsmbName, E2E.scalarModName, E2E.scalarWideName,
    E2E.kemEncapsName, E2E.kemDecapsName,
    LibsignalSpqrV1.mlkemFromSeedName, LibsignalSpqrV1.mlkemPk1Name,
    LibsignalSpqrV1.mlkemPk2Name, LibsignalSpqrV1.mlkemEncaps1Name,
    LibsignalSpqrV1.mlkemEncaps2Name, LibsignalSpqrV1.mlkemDecapsName,
    LibsignalSpqrV1.mlkemValidatePkName, LibsignalSpqrV1.libcruxHmacName,
    SignalSession.readFileName, SignalSession.writeFileName,
    SignalSession.readStdinName, SignalSession.writeStdoutName,
    List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [E2E.isImagePanicSymbol, Rust.isPanicSymbol, E2E.extraImagePanicNames]

private theorem cliExterns_row_std3 (W : CliHooks) {n : String} {h : State → State}
    (hm : (n, h) ∈ cliHookTable W) : cliExterns W n = some h := by
  have hn : n ∈ cliHookNames := by
    rw [← cliHookNames_eq W]
    exact List.mem_map.mpr ⟨(n, h), hm, rfl⟩
  have hp : E2E.isImagePanicSymbol n = false := by
    have := List.all_eq_true.mp cliHookNames_notPanic_epoch_std3 n hn
    simpa using this
  unfold cliExterns
  rw [withCliPanics_of_isImagePanicSymbol_false _ hp]
  exact lookup_of_mem_nodup _ n h (by rw [cliHookNames_eq W]; exact cliHookNames_nodup_std3) hm

private theorem cliExterns_none_std3 (W : CliHooks) {n : String} (hn : n ∉ cliHookNames)
    (hp : E2E.isImagePanicSymbol n = false) : cliExterns W n = none := by
  unfold cliExterns
  rw [withCliPanics_of_isImagePanicSymbol_false _ hp]
  exact lookup_of_not_mem _ n (by rw [cliHookNames_eq W]; exact hn)

private theorem cliExterns_durationSinceEpochAlloc_std3 (W : CliHooks) :
    HookSat (cliExterns W) E2E.durationSinceName durationSinceEpochAllocSpec :=
  ⟨durationSinceExactHook, cliExterns_row_std3 W (durationSince_row W),
    durationSinceExactHook_epoch_alloc_ok⟩

private theorem cliExterns_agree_std3 (W : CliHooks) (ctl : BitVec 64) {n : String}
    (hn : n ≠ rngFillName) :
    Rust.withPanics (tripleRatchetExterns W.C ctl (cliExterns W)) n =
      Rust.withPanics (cliExterns W) n := by
  rw [withPanics_cliExterns]
  by_cases hp : Rust.isPanicSymbol n = true
  · have hpC : isCliPanicSymbol n = true := isCliPanicSymbol_of_isPanicSymbol hp
    unfold cliExterns withCliPanics
    simp [Rust.withPanics, hp, hpC]
  · simp only [Rust.withPanics, hp, Bool.false_eq_true, ↓reduceIte]
    by_cases hk : n ∈ kitOwnNames
    · simp only [kitOwnNames, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
      simp [tripleRatchetExterns, CryptoVerification.LibsignalSession.sessionExterns,
        dhName, pubFromSecretName, staticDropName, sharedDropName, rngFillName, noHookNames] <;>
      first
        | (unfold cliExterns withCliPanics
           simp [isCliPanicSymbol, E2E.isImagePanicSymbol, E2E.extraImagePanicNames,
             deadCliHashbrownPanicNames]; done)
        | (refine (cliExterns_row_std3 W ?_).symm
           simp [cliHookTable])
        | (refine (cliExterns_none_std3 W ?_ ?_).symm
           · unfold cliHookNames; decide
           · simp [E2E.isImagePanicSymbol, Rust.isPanicSymbol, E2E.extraImagePanicNames])
    · exact tripleRatchetExterns_of_not_mem W.C ctl (cliExterns W) hk hn

private theorem trapsOnly_trTrap_cli_std3 (b : BitVec 64) (W : CliHooks) :
    TrapsOnly (trTrapProgAt b W.C (cliExterns W)) (tripleRatchetProgAtExt b (cliExterns W)) := by
  refine TrapsOnly.rebase libsignalSessionCode b ?_
  intro n
  by_cases hr : n = rngFillName
  · subst hr
    by_cases hp : Rust.isPanicSymbol rngFillName = true
    · left; simp [Rust.withPanics, hp]
    · right
      refine ⟨rngTrap, ?_, rngTrap_isTrap⟩
      simp [Rust.withPanics, trTrapExterns, ProofLib.Variant.trapAt, hp]
  · left
    rw [withPanics_trTrap_ne W.C (cliExterns W) hr]
    exact cliExterns_agree_std3 W 0#64 hr

private theorem subroutine_ok_cli_of_trTrap_std3 {α : Type} {b : BitVec 64} {W : CliHooks}
    {name : String} {spec : Spec α}
    (h : subroutine_ok (trTrapProgAt b W.C (cliExterns W))
      ((trTrapProgAt b W.C (cliExterns W)).fnAddr name) spec) :
    subroutine_ok (tripleRatchetProgAtExt b (cliExterns W))
      ((tripleRatchetProgAtExt b (cliExterns W)).fnAddr name) spec := by
  rw [← (trapsOnly_trTrap_cli_std3 b W).fnAddr name]
  exact subroutine_ok.of_trapsOnly (trapsOnly_trTrap_cli_std3 b W) h

theorem setUnackPreKeyMsg_exact_stack_epoch_ok_cli {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (hA : CryptoVerification.RustHeap.AllocHooks A (cliExterns W)) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr setUnackPreKeyMsgSym)
      (setUnackPreKeyMsgExactStackEpochSpec A img) :=
  subroutine_ok_cli_of_trTrap_std3
    (setUnackPreKeyMsg_exact_stack_epoch_ok_trap (C := W.C) (absHooks := cliExterns W)
      hA (cliExterns_durationSinceEpochAlloc_std3 W))

/-! ## 4. Contract-backed generalization (`CliExternsOk`, 16-KiB stack) -/

/-- 16-KiB (`extHookStack + 32`) stack generalization of `setUnackPreKeyMsgExactStackEpochSpec`,
sizing the stack budget for `CliExt.durationSinceEpochSpec` (`extHookStack = 16384`). -/
def setUnackPreKeyMsgExtStackEpochSpec (A : RustAlloc) (img : Obj.Image) :
    Spec Pqxdh.TopLevel.SetUnackExactGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x5 = 0#64 ∧ (s.readReg64 .x6).setWidth 32 = 0#32⌝ ∗
      (⌜s.readReg64 .x0 = g.statePtr ∧
        (s.readReg64 .x1).setWidth 32 = g.optOpkTag ∧
        (s.readReg64 .x2).setWidth 32 = g.optOpkVal ∧
        (s.readReg64 .x3).setWidth 32 = g.spkId ∧
        s.readReg64 .x4 = g.baseKeyPtr ∧
        g.baseKeyBytes.length = 32⌝ ∗
      (g.baseKeyPtr ↦ₛ Initiator.bytesToBv8 g.baseKeyBytes) ∗
      ((g.statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.statePtr + 0x100#64) 40 ∗
      stackAt (s.sp - 144#64) (extHookStack + 32) ∗
      cells (s.sp - 144#64) 18 ∗
      A.pool)
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (g.baseKeyPtr ↦ₛ Initiator.bytesToBv8 g.baseKeyBytes) ∗
    Initiator.vecU8 A (g.statePtr + 0xf8#64) (Initiator.bytesToBv8 (encodeEC g.baseKeyBytes)) ∗
    ((g.statePtr + 0x110#64) ↦₃₂ g.optOpkTag) ∗
    ((g.statePtr + 0x114#64) ↦₃₂ g.optOpkVal) ∗
    ((g.statePtr + 0x118#64) ↦₆₄ 0#64) ∗
    ((g.statePtr + 0x120#64) ↦₃₂ g.spkId) ∗
    memRegion (g.statePtr + 0x124#64) 4 ∗
    stackAt (s0.sp - 144#64) (extHookStack + 32) ∗
    cells (s0.sp - 144#64) 18 ∗
    A.pool
  onPanic := rustPanicOnOom img

private theorem cliExternsWith_eq_of_mem_std3 {ext : String → Option (State → State)} {n : String}
    (hn : n ∈ cliHookNames) :
    cliExternsWith ext n = ext n := by
  have hp : E2E.isImagePanicSymbol n = false := by
    have := List.all_eq_true.mp cliHookNames_notPanic_epoch_std3 n hn
    simpa using this
  exact withCliPanics_of_isImagePanicSymbol_false ext hp

private theorem hookSat_cliExternsWith_std3 {α : Type} {ext : String → Option (State → State)}
    {n : String} {spec : Spec α} (hn : n ∈ cliHookNames) (h : HookSat ext n spec) :
    HookSat (cliExternsWith ext) n spec := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, (cliExternsWith_eq_of_mem_std3 hn).trans hf, hok⟩

/-- Stub `subroutine_ok` for `<std::time::SystemTime>::duration_since` on
`tripleRatchetProgAtExt img.base (cliExternsWith ext)` directly from `hOk.durationSince`. -/
theorem durationSince_ok_cliExternsWith {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (img : Obj.Image) (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr E2E.durationSinceName)
      CliExt.durationSinceEpochSpec := by
  have h1 := hook_ok_at (P := libsignalSessionCode) (b := img.base)
    (hooks := cliExternsWith ext) (name := E2E.durationSinceName)
    (hname := E2E.durationSinceName) (k := 0)
    (ls_stub% "<std::time::SystemTime>::duration_since")
    (Nat.add_zero _)
    (by decide)
    (ls_hook% "<std::time::SystemTime>::duration_since")
    (by simp [Rust.isPanicSymbol, E2E.durationSinceName])
    (hookSat_cliExternsWith_std3 (by decide) hOk.durationSince)
  simpa only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h1

private theorem stackAt_ext_split_exact_epoch (sp : BitVec 64) :
    stackAt (sp - 144#64) (extHookStack + 32) =
      memRegion (sp - 16560#64) 12288 ∗
        stackAt (sp - 144#64) (RustHeap.allocHookStack + 32) := by
  have h1 := Initiator.stackAt_split_top (sp - 144#64) 12288 (RustHeap.allocHookStack + 32)
    (by decide)
  have h2 : (12288 + (RustHeap.allocHookStack + 32) : Nat) = extHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (12288 + (RustHeap.allocHookStack + 32)) = 16416#64 := rfl
  have h4 : sp - 144#64 - 16416#64 = sp - 16560#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

private theorem stackAt_setUnack_ext_call (sp : BitVec 64) :
    stackAt (sp - 144#64) (extHookStack + 32) =
      memRegion (sp - 16560#64) 12288 ∗
        stackAt (sp - 176#64) RustHeap.allocHookStack ∗ cells (sp - 176#64) 4 := by
  rw [stackAt_ext_split_exact_epoch sp, stackAt_setUnack_call_epoch sp]

private theorem stackAt_setUnack_ext_4k (sp : BitVec 64) :
    stackAt (sp - 144#64) (extHookStack + 32) =
      memRegion (sp - 16560#64) 12320 ∗ stackAt (sp - 144#64) RustHeap.allocHookStack := by
  have h1 := Initiator.stackAt_split_top (sp - 144#64) 12320 RustHeap.allocHookStack (by decide)
  have h2 : (12320 + RustHeap.allocHookStack : Nat) = extHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (12320 + RustHeap.allocHookStack) = 16416#64 := rfl
  have h4 : sp - 144#64 - 16416#64 = sp - 16560#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

private theorem stackAt_setUnack_ext_16k (sp : BitVec 64) :
    stackAt (sp - 144#64) (extHookStack + 32) =
      memRegion (sp - 16560#64) 32 ∗ stackAt (sp - 144#64) extHookStack := by
  have h1 := Initiator.stackAt_split_top (sp - 144#64) 32 extHookStack (by decide)
  have h2 : (32 + extHookStack : Nat) = extHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (32 + extHookStack) = 16416#64 := rfl
  have h4 : sp - 144#64 - 16416#64 = sp - 16560#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

private theorem stackAt_setUnack_ext_after_ser (sp : BitVec 64) :
    memRegion (sp - 16560#64) 12288 ∗
        stackAt (sp - 176#64) RustHeap.allocHookStack ∗ cells (sp - 176#64) 4 =
      memRegion (sp - 16560#64) 12320 ∗ stackAt (sp - 144#64) RustHeap.allocHookStack :=
  (stackAt_setUnack_ext_call sp).symm.trans (stackAt_setUnack_ext_4k sp)

private theorem stackAt_setUnack_ext_4k_to_16k (sp : BitVec 64) :
    memRegion (sp - 16560#64) 12320 ∗ stackAt (sp - 144#64) RustHeap.allocHookStack =
      memRegion (sp - 16560#64) 32 ∗ stackAt (sp - 144#64) extHookStack :=
  (stackAt_setUnack_ext_4k sp).symm.trans (stackAt_setUnack_ext_16k sp)

private theorem durationSinceEpochAtSpec_ext_eq :
    durationSinceEpochAtSpec extHookStack = CliExt.durationSinceEpochSpec := by
  unfold durationSinceEpochAtSpec CliExt.durationSinceEpochSpec
  rfl

private theorem setUnackPreKeyMsgEpochAtSpec_ext (A : RustAlloc) (img : Obj.Image) :
    setUnackPreKeyMsgEpochAtSpec (extHookStack + 32) A img =
      setUnackPreKeyMsgExtStackEpochSpec A img := by
  unfold setUnackPreKeyMsgEpochAtSpec setUnackPreKeyMsgExtStackEpochSpec
  rfl

/-- `SessionState::set_unacknowledged_pre_key_message` meets `setUnackPreKeyMsgExtStackEpochSpec`
(`extHookStack + 32` stack) directly on `tripleRatchetProgAtExt img.base (cliExternsWith ext)`
under `CliExternsOk P A ext`. -/
theorem setUnackPreKeyMsg_ext_stack_epoch_ok {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr setUnackPreKeyMsgSym)
      (setUnackPreKeyMsgExtStackEpochSpec A img) := by
  exact Eq.mp
    (congrArg
      (subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr setUnackPreKeyMsgSym))
      (setUnackPreKeyMsgEpochAtSpec_ext A img))
    (setUnackPreKeyMsg_epoch_ok_hooks
      (A := A) (img := img)
      (hooks := cliExternsWith ext)
      (totalStk := extHookStack + 32)
      (timeStk := extHookStack)
      (F_call := fun sp => memRegion (sp - 16560#64) 12288)
      (F_4k := fun sp => memRegion (sp - 16560#64) 12320)
      (F_time := fun sp => memRegion (sp - 16560#64) 32)
      (hookSat_cliExternsWith_std3 (by decide) hOk.shim)
      (hookSat_cliExternsWith_std3 (by decide) hOk.alloc.alloc)
      (hookSat_cliExternsWith_std3 (by decide) hOk.alloc.dealloc)
      (hookSat_cliExternsWith_std3 (by decide) hOk.memcpy)
      (Eq.mp
        (congrArg (HookSat (cliExternsWith ext) E2E.durationSinceName)
          durationSinceEpochAtSpec_ext_eq.symm)
        (hookSat_cliExternsWith_std3 (by decide) hOk.durationSince))
      stackAt_setUnack_ext_call
      stackAt_setUnack_ext_after_ser
      stackAt_setUnack_ext_4k_to_16k)

end CryptoVerification.SignalSession.Cli.Slots
