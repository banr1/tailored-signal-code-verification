/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2HelpersPlaced
public meta import Lean
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Frame
import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonCalleesExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.Disproof.Basic

/-!
# `signal_session::run` Placed Arm `R2` Shared Steps

Relocatable (`[LibsignalPlacement]`) stack-frame equalities, shared cleanup tails
(`r2p_free_peer_reject`, `r2p_free_peer_join`, `r2p_free_me_peer_join`), error arm (`r2p_err_arm`),
and message copy/free sub-steps on Block `579` (`runProgPlaced H`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunSkeleton CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.LibsignalProtoCodec

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero r2p_vregs_0 r2p_vregs_1 r2p_vregs_2

def r2_localGaps (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x10#64) (0x1d0 - 0x10) ∗
  memRegion (fsp + 0x1e0#64) (0x208 - 0x1e0) ∗
  memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
  memRegion (fsp + 0x2a8#64) (0x320 - 0x2a8) ∗
  memRegion (fsp + 0x340#64) (0x4d0 - 0x340) ∗
  memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
  memRegion (fsp + 0x1848#64) (0x23b0 - 0x1848) ∗
  memRegion (fsp + 0x23d0#64) (0x29f0 - 0x23d0)

theorem r2_tail_split_220 (fsp : BitVec 64) :
    memRegion (fsp + 0x220#64) (runLocalBytes - 0x220) =
      memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x320#64) 32 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗
      memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗
      (memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
       memRegion (fsp + 0x2a8#64) (0x320 - 0x2a8) ∗
       memRegion (fsp + 0x340#64) (0x4d0 - 0x340) ∗
       memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
       memRegion (fsp + 0x1848#64) (0x23b0 - 0x1848) ∗
       memRegion (fsp + 0x23d0#64) (0x29f0 - 0x23d0)) := by
  dsimp only [runLocalBytes]
  rw [ProofLib.memRegion_split' (b := fsp + 0x220#64) (n := 0x2a0 - 0x220) (k := 0x29f0 - 0x2a0)
        (b' := fsp + 0x2a0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x2a0#64) (n := 8) (k := 0x29f0 - 0x2a8)
        (b' := fsp + 0x2a8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x2a8#64) (n := 0x320 - 0x2a8) (k := 0x29f0 - 0x320)
        (b' := fsp + 0x320#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x320#64) (n := 32) (k := 0x29f0 - 0x340)
        (b' := fsp + 0x340#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x340#64) (n := 0x4d0 - 0x340) (k := 0x29f0 - 0x4d0)
        (b' := fsp + 0x4d0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x4d0#64) (n := 248) (k := 0x29f0 - 0x5c8)
        (b' := fsp + 0x5c8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x5c8#64) (n := 0x1750 - 0x5c8) (k := 0x29f0 - 0x1750)
        (b' := fsp + 0x1750#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1750#64) (n := 248) (k := 0x29f0 - 0x1848)
        (b' := fsp + 0x1848#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1848#64) (n := 0x23b0 - 0x1848) (k := 0x29f0 - 0x23b0)
        (b' := fsp + 0x23b0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x23b0#64) (n := 32) (k := 0x29f0 - 0x23d0)
        (b' := fsp + 0x23d0#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem r2_locals_some_eq (fsp : BitVec 64) (p1d0 : SepProp) :
    runLocals fsp [(0x1d0, 16, p1d0)] =
      memRegion fsp 16 ∗ p1d0 ∗ memRegion (fsp + 0x208#64) 24 ∗
      memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp := by
  dsimp only [runLocals, runLocalsFrom, runLocalBytes]
  have hf0 : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
  have hf1e0 : fsp + BitVec.ofNat 64 (0x1d0 + 16) = fsp + 0x1e0#64 := by bv_omega
  rw [hf0, hf1e0,
      ProofLib.memRegion_split' (b := fsp) (n := 16) (k := 0x1d0 - 0x10)
        (b' := fsp + 0x10#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1e0#64) (n := 0x208 - 0x1e0) (k := 0x29f0 - 0x208)
        (b' := fsp + 0x208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x208#64) (n := 24) (k := 0x29f0 - 0x220)
        (b' := fsp + 0x220#64) rfl (by bv_omega) (by decide),
      (r2_tail_split_220 fsp : memRegion (fsp + 0x220#64) (0x29f0 - 0x220) = _)]
  unfold r2_localGaps; ac_rfl

theorem r2_locals_none_eq (fsp : BitVec 64) :
    runLocals fsp [] =
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
      memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp := by
  rw [runLocals_empty_eq]
  have heq : memRegion fsp runLocalBytes =
      runLocals fsp [(0x1d0, 16, memRegion (fsp + 0x1d0#64) 16)] := by
    dsimp only [runLocals, runLocalsFrom, runLocalBytes]
    have hf0 : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    have hf1e0 : fsp + BitVec.ofNat 64 (0x1d0 + 16) = fsp + 0x1e0#64 := by bv_omega
    rw [hf0, hf1e0,
        ProofLib.memRegion_split' (b := fsp) (n := 0x1d0) (k := 0x29f0 - 0x1d0)
          (b' := fsp + 0x1d0#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 16) (k := 0x29f0 - 0x1e0)
          (b' := fsp + 0x1e0#64) rfl (by bv_omega) (by decide)]
  rw [heq, r2_locals_some_eq]

theorem r2_locals_join_eq (fsp : BitVec 64) (outP : SepProp) :
    runLocals fsp [(0x208, 24, outP)] =
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ outP ∗
      memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp := by
  dsimp only [runLocals, runLocalsFrom]
  have hf0 : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
  have hf220 : fsp + BitVec.ofNat 64 (0x208 + 24) = fsp + 0x220#64 := by bv_omega
  rw [hf0, hf220,
      ProofLib.memRegion_split' (b := fsp) (n := 16) (k := 0x208 - 16)
        (b' := fsp + 0x10#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x10#64) (n := 0x1d0 - 0x10) (k := 0x208 - 0x1d0)
        (b' := fsp + 0x1d0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 16) (k := 0x208 - 0x1e0)
        (b' := fsp + 0x1e0#64) rfl (by bv_omega) (by decide),
      r2_tail_split_220 fsp]
  unfold r2_localGaps; ac_rfl

theorem r2_memRegion32_words4 (a : BitVec 64) :
    memRegion a 32 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
        (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8)
        (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w0 =>
      Entails.sepExists_right w0 (Entails.sepExists_right w1
        (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))

theorem r2_peerSlot_rejoin (a w0 w1 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ memRegion (a + 16#64) 16 ⊢ memRegion a 32 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
        (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

theorem r2_res_write_none (A : RustAlloc) (res w0 : BitVec 64)
    (hw0 : w0 = 0xffffffffffffffff#64) :
    (res ↦₆₄ w0) ∗ memRegion (res + 8#64) (runResSize - 8) ⊢
      runResAt A cliWrOk res (some none) := by
  subst hw0; exact Entails.refl _

theorem r2_res_open (res : BitVec 64) :
    memRegion res runResSize ⊢
      ∃∗ r0 : BitVec 64, (res ↦₆₄ r0) ∗ memRegion (res + 8#64) (runResSize - 8) := by
  rw [ProofLib.memRegion_split' (b := res) (n := 8) (k := runResSize - 8)
        (b' := res + 8#64) (by decide) rfl (by decide),
      ProofLib.memRegion_eight res, sepExists_sepConj_left]
  exact Entails.refl _

theorem r2_now_open (fsp : BitVec 64) :
    memRegion fsp 16 ⊢
      ∃∗ n0 : BitVec 64, ∃∗ n1 : BitVec 32,
        (fsp ↦₆₄ n0) ∗ ((fsp + 8#64) ↦₃₂ n1) ∗ memRegion (fsp + 12#64) 4 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 8)
        (b' := fsp + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_eight fsp,
      ProofLib.memRegion_split' (b := fsp + 8#64) (n := 4) (k := 4)
        (b' := fsp + 12#64) rfl (by bv_omega) (by decide),
      r2_memRegion4_eq_exists_u32 (fsp + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim fun n1 => Entails.sepExists_elim fun n0 =>
    Entails.sepExists_right n0 (Entails.sepExists_right n1 (Entails.refl _))

theorem r2_now_to_mem16 (fsp : BitVec 64) :
    nowCellAt fsp unixEpoch ⊢ memRegion fsp 16 := by
  unfold nowCellAt unixEpoch
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 8)
        (b' := fsp + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 8#64) (n := 4) (k := 4)
        (b' := fsp + 12#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left
      (IsBlock.entails (IsBlock.pointsTo32 (fsp + 8#64) 0#32)
        (IsBlock.memRegion (fsp + 8#64) 4) fun _ _ => trivial))

theorem r2_tag8_open (a : BitVec 64) :
    memRegion a 8 ⊢ ∃∗ b0 : BitVec 8, (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 1) (k := 7) (b' := a + 1#64) rfl rfl (by decide),
      Path.Helpers.memRegion_1_eq_pointsTo8, sepExists_sepConj_left]
  exact Entails.refl _

theorem r2_tag8_close (a : BitVec 64) (b : BitVec 8) :
    SpqrV1.ChainProofs.bytesAt false a [b] ∗ memRegion (a + 1#64) 7 ⊢ memRegion a 8 := by
  dsimp only [SpqrV1.ChainProofs.bytesAt]
  rw [ProofLib.memRegion_split' (b := a) (n := 1) (k := 7) (b' := a + 1#64) rfl rfl (by decide)]
  exact sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion a [b])

theorem r2_pointsTo8_to_bytesAt (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = SpqrV1.ChainProofs.bytesAt false a [b] :=
  (ProofLib.pointsToBytes_singleton a b).symm

theorem r2_ans_of_trace_eq {P : Prop} {s1 s2 : State}
    (_htr : s2.trace = s1.trace) (h : P) : P := h

theorem r2_allocFailedIn_of_trace_eq {s0 s1 sf : State}
    (h : s1.trace = s0.trace) (ha : allocFailedIn s1 sf) : allocFailedIn s0 sf := by
  unfold allocFailedIn at ha ⊢; rw [← h]; exact ha

theorem r2_allocFailedIn_congr_right {s0 s1 sf : State}
    (h : sf.trace = s1.trace) (ha : allocFailedIn s0 s1) : allocFailedIn s0 sf := by
  unfold allocFailedIn at ha ⊢; rw [h]; exact ha

def r2_hold (P : SepProp) : SepProp := P
theorem r2_hold_eq (P : SepProp) : r2_hold P = P := rfl
attribute [local irreducible] r2_hold

macro "r2p_step_run" : tactic =>
  `(tactic| ((try dsimp only [runProgPlaced, lsProg_579]); (try rw [runPcPlaced_eq]); wp_steps))

macro "r2p_pc_done" : tactic =>
  `(tactic| ((try dsimp only [runPcPlaced]); (try simp only [arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]); (try rfl)))

macro "r2p_eq" : tactic =>
  `(tactic| first | rfl | (simp only [arm64_norm]; try rfl))

set_option maxHeartbeats 800000 in
theorem r2p_free_peer_reject [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {peerG : AddrGhost} {g' : StoresGhost} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 2984)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced r2p_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  let restPeer : SepProp :=
    runSaved s0 ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  let peerRest : SepProp :=
    runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  refine sepWPp_weaken_pre
    (P' := runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
      restPeer)
    (by dsimp only [restPeer]; exact Entails.of_eq (by ac_rfl)) ?_
  rw [r2_addrNameHeap_eq_ownedBytes A peerG]
  have hpc : s.pc = runPcPlaced 2984 := hin.pc; change s.pc = (blkPl_579).base + 2984#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = fsp := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  by_cases hcap : peerG.name.cap = 0#64
  · rw [hcap]
    refine sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (ownedBytes_zero_entails_emp A _ _ _)))))) ?_
    rw [emp_sepConj]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 11388) hin.inv
    rw [← hsp0]
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    intro hinv1
    rw [hsp0]
    have hin1 : InRunPlaced r2p_CodeOk s0 _ 11388 :=
      r2p_inRun_mk hin (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
        (by r2p_eq) (by r2p_eq) hinv1 (by r2p_eq)
    have hatRej : AtRejectPlaced r2p_CodeOk g g' .postDispatch s0 _ :=
      { base := hin1
        x19 := by (try simp only [arm64_norm]); exact hx19
        preRegs := fun h => by cases h
        trace := by (try simp only [arm64_norm]); exact htr
        hist := r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq)
        ans := hans }
    refine sepWPp_weaken_pre ?_ (hrej _ g' .postDispatch hatRej)
    dsimp only [rejectMem, restPeer]
    have hp32 := r2_peerSlot_rejoin (fsp + 0x320#64) 0#64 peerG.name.ptr
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp32)
    rw [r2_locals_none_eq fsp]
    refine Entails.trans (Entails.of_eq ?_)
      (Entails.trans (sepConj_mono_left (Q := peerRest) hp32) (Entails.of_eq ?_))
    · dsimp only [peerRest, fsp]; ac_rfl
    · dsimp only [peerRest, fsp]; ac_rfl
  · refine sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (ownedBytes_dealloc A hcap)))))) ?_
    have hpull :
        runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗ A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
            memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          restPeer =
        ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          (((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
              memRegion peerG.name.ptr peerG.name.cap.toNat ∗
              runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ restPeer)) := by ac_rfl
    rw [hpull]
    apply SepWPp.pure_left; rintro ⟨hpos, _, hlt⟩
    have hlt63 : peerG.name.cap.toNat < 2 ^ 63 := by omega
    have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hin.inv
    rw [← hsp0]
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    intro hinv1
    rw [hsp0]
    refine sepWPp_weaken_pre
      (P' := A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
        memRegion peerG.name.ptr peerG.name.cap.toNat ∗
        A.pool ∗ stackAt fsp (resStack - runFrame) ∗
        (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          (((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16) ∗
          memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
          memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap))
      (by dsimp only [restPeer, fsp]; exact Entails.of_eq (by ac_rfl)) ?_
    refine r2p_call_dealloc (nextOff := 11388) hh hextNeed hsub64 hin hinv1
      (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
      (by r2p_eq) (by r2p_eq) (by r2p_eq) (by r2p_pc_done)
      (by r2p_eq) (by r2p_eq) (by r2p_eq) hpos hlt63
      (by (try simp only [arm64_norm]); exact htr)
      (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq))
      fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
    have hatRej : AtRejectPlaced r2p_CodeOk g g' .postDispatch s0 sf :=
      { base := hin_f
        x19 := by rw [(r2p_cs_regs hcsm).1]; (try simp only [arm64_norm]); exact hx19
        preRegs := fun h => by cases h
        trace := htr_f
        hist := hhist_f
        ans := r2_ans_of_trace_eq (htr_eq.trans (by r2p_eq)) hans }
    refine sepWPp_weaken_pre ?_ (hrej sf g' .postDispatch hatRej)
    dsimp only [rejectMem]
    have hp32 := r2_peerSlot_rejoin (fsp + 0x320#64) peerG.name.cap peerG.name.ptr
    dsimp only [fsp] at hp32
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp32)
    rw [r2_locals_none_eq fsp]
    refine Entails.trans (Entails.of_eq ?_)
      (Entails.trans (sepConj_mono_left (Q := peerRest) hp32) (Entails.of_eq ?_))
    · dsimp only [peerRest, fsp]; ac_rfl
    · dsimp only [peerRest, fsp]; ac_rfl

set_option maxHeartbeats 800000 in
theorem r2p_free_peer_join [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {peerG : AddrGhost} {g' : StoresGhost} {out : Bytes}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 3960)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, out)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced r2p_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  let restJoin : SepProp :=
    runSaved s0 ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  let joinRest : SepProp :=
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  refine sepWPp_weaken_pre
    (P' := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
      restJoin)
    (by dsimp only [restJoin]; exact Entails.of_eq (by ac_rfl)) ?_
  rw [r2_addrNameHeap_eq_ownedBytes A peerG]
  have hpc : s.pc = runPcPlaced 3960 := hin.pc; change s.pc = (blkPl_579).base + 3960#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = fsp := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  by_cases hcap : peerG.name.cap = 0#64
  · rw [hcap]
    refine sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (ownedBytes_zero_entails_emp A _ _ _)))))) ?_
    rw [emp_sepConj]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 3980) hin.inv
    rw [← hsp0]
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    intro hinv1
    rw [hsp0]
    have hin1 : InRunPlaced r2p_CodeOk s0 _ 3980 :=
      r2p_inRun_mk hin (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
        (by r2p_eq) (by r2p_eq) hinv1 (by r2p_eq)
    have hatJoin : AtJoinPlaced r2p_CodeOk g g' out s0 _ :=
      { base := hin1
        x19 := by (try simp only [arm64_norm]); exact hx19
        x20 := by (try simp only [arm64_norm]); exact hx20
        trace := by (try simp only [arm64_norm]); exact htr
        hist := r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq)
        ans := hans
        wrOk := hwr }
    refine sepWPp_weaken_pre ?_ (hjoin _ g' out hatJoin)
    dsimp only [joinMem, restJoin]
    have hp32 := r2_peerSlot_rejoin (fsp + 0x320#64) 0#64 peerG.name.ptr
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp32)
    rw [r2_locals_join_eq fsp (vecU8 A (fsp + 0x208#64) out)]
    refine Entails.trans (Entails.of_eq ?_)
      (Entails.trans (sepConj_mono_left (Q := joinRest) hp32) (Entails.of_eq ?_))
    · dsimp only [joinRest, fsp]; ac_rfl
    · dsimp only [joinRest, fsp]; ac_rfl
  · refine sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (ownedBytes_dealloc A hcap)))))) ?_
    have hpull :
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗ A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
            memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          restJoin =
        ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          (((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
              memRegion peerG.name.ptr peerG.name.cap.toNat ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ restJoin)) := by ac_rfl
    rw [hpull]
    apply SepWPp.pure_left; rintro ⟨hpos, _, hlt⟩
    have hlt63 : peerG.name.cap.toNat < 2 ^ 63 := by omega
    have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hin.inv
    rw [← hsp0]
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    intro hinv1
    rw [hsp0]
    refine sepWPp_weaken_pre
      (P' := A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
        memRegion peerG.name.ptr peerG.name.cap.toNat ∗
        A.pool ∗ stackAt fsp (resStack - runFrame) ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          (((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16) ∗
          memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
          vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
          memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap))
      (by dsimp only [restJoin, fsp]; exact Entails.of_eq (by ac_rfl)) ?_
    refine r2p_call_dealloc (nextOff := 3980) hh hextNeed hsub64 hin hinv1
      (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
      (by r2p_eq) (by r2p_eq) (by r2p_eq) (by r2p_pc_done)
      (by r2p_eq) (by r2p_eq) (by r2p_eq) hpos hlt63
      (by (try simp only [arm64_norm]); exact htr)
      (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq))
      fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
    have hcs := r2p_cs_regs hcsm
    have hatJoin : AtJoinPlaced r2p_CodeOk g g' out s0 sf :=
      { base := hin_f
        x19 := by rw [hcs.1]; (try simp only [arm64_norm]); exact hx19
        x20 := by rw [hcs.2.1]; (try simp only [arm64_norm]); exact hx20
        trace := htr_f
        hist := hhist_f
        ans := r2_ans_of_trace_eq (htr_eq.trans (by r2p_eq)) hans
        wrOk := hwr }
    refine sepWPp_weaken_pre ?_ (hjoin sf g' out hatJoin)
    dsimp only [joinMem]
    have hp32 := r2_peerSlot_rejoin (fsp + 0x320#64) peerG.name.cap peerG.name.ptr
    dsimp only [fsp] at hp32
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp32)
    rw [r2_locals_join_eq fsp (vecU8 A (fsp + 0x208#64) out)]
    refine Entails.trans (Entails.of_eq ?_)
      (Entails.trans (sepConj_mono_left (Q := joinRest) hp32) (Entails.of_eq ?_))
    · dsimp only [joinRest, fsp]; ac_rfl
    · dsimp only [joinRest, fsp]; ac_rfl

set_option maxHeartbeats 800000 in
theorem r2p_free_me_peer_join [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {peerG meG : AddrGhost} {g' : StoresGhost} {out : Bytes}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 3940)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, out)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced r2p_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  let tailMeJoin : SepProp :=
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  change SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (addrNameHeap A meG ∗ tailMeJoin) Q Qp (runOom s0)
  rw [r2_addrNameHeap_eq_ownedBytes A meG]
  have hpc : s.pc = runPcPlaced 3940 := hin.pc; change s.pc = (blkPl_579).base + 3940#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = fsp := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  by_cases hcap : meG.name.cap = 0#64
  · rw [hcap]
    refine sepWPp_weaken_pre (sepConj_mono_left (ownedBytes_zero_entails_emp A _ _ _)) ?_
    rw [emp_sepConj]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 3960) hin.inv
    have hx21_0 : s.readReg64 (.gpr 21#5) = 0#64 := hx21.trans hcap
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    intro hinv1
    have hin1 : InRunPlaced r2p_CodeOk s0 _ 3960 :=
      r2p_inRun_mk hin (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
        (by r2p_eq) (by r2p_eq) hinv1 (by r2p_eq)
    exact r2p_free_peer_join (peerG := peerG) hh hextNeed hsub64 hin1
      (by (try simp only [arm64_norm]); exact hx19)
      (by (try simp only [arm64_norm]); exact hx20)
      (by (try simp only [arm64_norm]); exact htr)
      (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq))
      hans hwr hjoin
  · refine sepWPp_weaken_pre (sepConj_mono_left (ownedBytes_dealloc A hcap)) ?_
    rw [sepConj_assoc, sepConj_assoc]
    apply SepWPp.pure_left; rintro ⟨hpos, _, hlt⟩
    have hlt63 : meG.name.cap.toNat < 2 ^ 63 := by omega
    have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hx21_b : (s.readReg64 (.gpr 21#5) == 0#64) = false := hx21.symm ▸ hbeq
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hin.inv
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    intro hinv1
    have hreord :
        A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          (memRegion meG.name.ptr meG.name.cap.toNat ∗ tailMeJoin) =
        A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat ∗
          A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A peerG ∗ runSaved s0 ∗
            ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x330#64) 16 ∗
            memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap) := by
      dsimp only [tailMeJoin]; ac_rfl
    rw [hreord]
    refine r2p_call_dealloc (nextOff := 3960) hh hextNeed hsub64 hin hinv1
      (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
      (by r2p_eq) (by r2p_eq) (by r2p_eq) (by r2p_pc_done)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by r2p_eq) hpos hlt63
      (by (try simp only [arm64_norm]); exact htr)
      (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq))
      fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
    have hcs := r2p_cs_regs hcsm
    have hback :
        A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A peerG ∗ runSaved s0 ∗
            ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x330#64) 16 ∗
            memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap) ⊢
        tailMeJoin := by
      dsimp only [tailMeJoin]; exact Entails.of_eq (by ac_rfl)
    exact sepWPp_weaken_pre hback
      (r2p_free_peer_join (peerG := peerG) hh hextNeed hsub64 hin_f
        (by rw [hcs.1]; (try simp only [arm64_norm]); exact hx19)
        (by rw [hcs.2.1]; (try simp only [arm64_norm]); exact hx20)
        htr_f hhist_f
        (r2_ans_of_trace_eq (htr_eq.trans (by r2p_eq)) hans)
        hwr hjoin)

theorem r2_sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x : α, P x) Q Qp oom := by
  intro R hm hL; rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hm⟩ := hm; exact h x R hm hL

macro "r2p_cond" : tactic => `(tactic| first
  | (simp only [arm64_norm, conditionHolds_mi_subsPState64, conditionHolds_pl_subsPState64,
        conditionHolds_mi_addsPState64, conditionHolds_pl_addsPState64,
        conditionHolds_mi_subsPState32, conditionHolds_pl_subsPState32,
        conditionHolds_mi_addsPState32, conditionHolds_pl_addsPState32])
  | (simp only [arm64_norm, conditionHolds_mi_subsPState64, conditionHolds_pl_subsPState64,
        conditionHolds_mi_addsPState64, conditionHolds_pl_addsPState64,
        conditionHolds_mi_subsPState32, conditionHolds_pl_subsPState32,
        conditionHolds_mi_addsPState32, conditionHolds_pl_addsPState32]
     decide))

set_option maxHeartbeats 800000 in
theorem r2p_err_arm [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {peerG meG : AddrGhost} {g' : StoresGhost} {err : ApiError AddrVal Unit}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hdropNeed : 32 + extHookStack ≤ resStack - runFrame)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1308)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hneStore : err ≠ .store ())
    (hans : g.a = some none)
    (hrej : RejectKPlaced r2p_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (encResAt A (fsp + 0x4d0#64) (.error err) ∗
        addrNameHeap A meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  let tailErr : SepProp :=
    addrNameHeap A meG ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  let tailErrPost : SepProp :=
    memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  let tailErrPostNoPool : SepProp :=
    memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap
  refine sepWPp_weaken_pre
    (sepConj_mono_left (RunProofs.encResAt_err_owned A (fsp + 0x4d0#64) err hneStore)) ?_
  have hpull_k :
      (((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
          (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A ((fsp + 0x4d0#64) + 8#64) k) ∗
          memRegion ((fsp + 0x4d0#64) + 56#64) 192) ∗ tailErr =
      (∃∗ k : RunDrop.SpeOwned,
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
          RunDrop.speOwnedAt A ((fsp + 0x4d0#64) + 8#64) k ∗
          memRegion ((fsp + 0x4d0#64) + 56#64) 192 ∗ tailErr) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  rw [hpull_k]
  apply r2_sepWPp_exists_left; intro k
  have hpc : s.pc = runPcPlaced 1308 := hin.pc; change s.pc = (blkPl_579).base + 1308#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = fsp := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  have herr_val : errTag = 0xffffffffffffffff#64 := rfl
  have he_eq2 : ConditionHolds .EQ (addsPState64 0xffffffffffffffff#64 2#64) = false := by r2p_cond
  have he_ne2 : ConditionHolds .NE (addsPState64 0xffffffffffffffff#64 2#64) = true := by r2p_cond
  have he_eq1 : ConditionHolds .EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by r2p_cond
  have he_ne1 : ConditionHolds .NE (addsPState64 0xffffffffffffffff#64 1#64) = false := by r2p_cond
  have hmi_e : ConditionHolds .MI (subsPState64 0xffffffffffffffff#64 0#64) = true := by r2p_cond
  have hpl_e : ConditionHolds .PL (subsPState64 0xffffffffffffffff#64 0#64) = false := by r2p_cond
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := (blkPl_553).base) hin.inv
  rw [herr_val, ← r2_hold_eq (RunDrop.speOwnedAt A ((fsp + 0x4d0#64) + 8#64) k ∗ _)]
  change s.readReg64 (.gpr 22#5) = fsp + 0x4d0#64 at hx22
  rw [← hsp0] at hx22 ⊢
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx22 ⊢)
  r2p_step_run
  apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
  intro hinv1
  clear hpc
  rw [hsp0]
  rw [r2_hold_eq]
  have hdrop_call := hdrop (resStack - runFrame) hdropNeed hsub64
  refine r2p_call (s0 := s0) (RunDrop.DropSpeOwnedGhost.mk ((fsp + 0x4d0#64) + 8#64) k)
    hdrop_call hinv1 (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    (by simp only [arm64_norm]; exact hsp_al)
    (ret_pc := runPcPlaced 2956) (by r2p_pc_done)
    (F := ((fsp + 0x4d0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion ((fsp + 0x4d0#64) + 56#64) 192 ∗
      addrNameHeap A meG ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
      memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap)
    ?_
    (hnext := fun s2 hsteps2 hinv2 hpcm2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [RunDrop.dropSpeOwnedSpec, tailErr]
    rw [sepConj_assoc]
    refine Entails.pure_right
      (by (try simp only [arm64_norm]); (try dsimp only [fsp]); try bv_omega) ?_
    (try simp only [arm64_norm])
    rw [hsp0]; dsimp only [fsp, runFsp]; (try simp only [arm64_norm])
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [RunDrop.dropSpeOwnedSpec]
    rw [sepConj_assoc]
    apply SepWPp.pure_left; intro htr2
    have hfs2 := r2p_files_of_trace_eq hh hsteps2 htr2
    have htr_s2 : s0.trace <+: s2.trace := htr2 ▸ (by simpa only [arm64_norm] using htr)
    have hhist_s2 : RunHistOk g.i s0 s2 :=
      r2p_histOk_of_trace_files (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq)) htr2 hfs2
    have hans_s2 : g.a = some none := r2_ans_of_trace_eq htr2 hans
    have hcs := r2p_cs_regs hcs2
    have hin2 : InRunPlaced r2p_CodeOk s0 s2 2956 :=
      r2p_inRun_mk hin hpcm2 hrun2 (hsp2.trans (by r2p_eq))
        (hcs.2.2.2.2.2.2.2.2.2.2.1.trans (by r2p_eq)) hinv2
        (hcs.2.2.2.2.2.2.2.2.2.2.2.trans (by r2p_eq))
    have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := by
      rw [hcs.1]; (try simp only [arm64_norm]); exact hx19
    have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := by
      rw [hcs.2.1]; (try simp only [arm64_norm]); exact hx20
    have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := by
      rw [hcs.2.2.1]; (try simp only [arm64_norm]); exact hx21
    have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr := by
      rw [hcs.2.2.2.2.2.2.2.2.2.1]; (try simp only [arm64_norm]); exact hx28
    have hsret := RunProofs.sret248_rejoin (fsp + 0x4d0#64) 0xffffffffffffffff#64
    refine sepWPp_weaken_pre
      (P' := memRegion g.res runResSize ∗ addrNameHeap A meG ∗ tailErrPost)
      (by
        dsimp only [tailErrPost]
        rw [← hsp2, (hin2.sp : s2.sp = fsp)]
        refine Entails.trans (Entails.of_eq ?_)
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsret)))))))))))))))
        ac_rfl) ?_
    refine sepWPp_weaken_pre (sepConj_mono_left (r2_res_open g.res)) ?_
    rw [sepExists_sepConj_left]
    apply r2_sepWPp_exists_left; intro r0
    rw [r2_addrNameHeap_eq_ownedBytes A meG]
    have hpc : s2.pc = runPcPlaced 2956 := hin2.pc; change s2.pc = (blkPl_579).base + 2956#64 at hpc
    have hrun2' : s2.status = .Running := hin2.run
    have hsp2_cur : s2.sp = fsp := hin2.sp
    have hsp_al2 : s2.spAligned = true := hin2.spAligned_cur
    by_cases hcap : meG.name.cap = 0#64
    · rw [hcap]
      refine sepWPp_weaken_pre
        (sepConj_mono_right (sepConj_mono_left (ownedBytes_zero_entails_emp A _ _ _))) ?_
      rw [emp_sepConj]
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 2984) hin2.inv
      have hx21_0 : s2.readReg64 (.gpr 21#5) = 0#64 := hx21_2.trans hcap
      r2p_step_run
      apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun2'])
      intro hinv3
      have hin3 : InRunPlaced r2p_CodeOk s0 _ 2984 :=
        r2p_inRun_mk hin2 (by r2p_pc_done) (by simp only [arm64_norm, hrun2'])
          (by r2p_eq) (by r2p_eq) hinv3 (by r2p_eq)
      refine sepWPp_weaken_pre
        (sepConj_mono_left (r2_res_write_none A g.res 0xffffffffffffffff#64 rfl)) ?_
      exact r2p_free_peer_reject (peerG := peerG) hh hextNeed hsub64 hin3
        (by (try simp only [arm64_norm]); exact hx19_2)
        (by (try simp only [arm64_norm]); exact htr_s2)
        (r2p_histOk_of_trace_files hhist_s2 (by r2p_eq) (by r2p_eq))
        hans_s2 hrej
    · refine sepWPp_weaken_pre
        (sepConj_mono_right (sepConj_mono_left (ownedBytes_dealloc A hcap))) ?_
      have hpull_me :
          ((g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
            (⌜LayoutOk meG.name.cap.toNat 1⌝ ∗ A.live meG.name.ptr meG.name.cap.toNat 1 ∗
              memRegion meG.name.ptr meG.name.cap.toNat) ∗ tailErrPost =
          ⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
            (((g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
              (A.live meG.name.ptr meG.name.cap.toNat 1 ∗
                memRegion meG.name.ptr meG.name.cap.toNat ∗ tailErrPost)) := by ac_rfl
      rw [hpull_me]
      apply SepWPp.pure_left; rintro ⟨hpos, _, hlt⟩
      have hlt63 : meG.name.cap.toNat < 2 ^ 63 := by omega
      have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      have hx21_b : (s2.readReg64 (.gpr 21#5) == 0#64) = false := hx21_2.symm ▸ hbeq
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hin2.inv
      r2p_step_run
      apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun2'])
      intro hinv3
      have hres_none := r2_res_write_none A g.res 0xffffffffffffffff#64 rfl
      refine sepWPp_weaken_pre (sepConj_mono_left hres_none) ?_
      have hreord_da :
          runResAt A cliWrOk g.res (some none) ∗
            (A.live meG.name.ptr meG.name.cap.toNat 1 ∗
              memRegion meG.name.ptr meG.name.cap.toNat ∗ tailErrPost) =
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
            memRegion meG.name.ptr meG.name.cap.toNat ∗
            A.pool ∗ stackAt fsp (resStack - runFrame) ∗
            (runResAt A cliWrOk g.res (some none) ∗ tailErrPostNoPool) := by
        dsimp only [tailErrPost, tailErrPostNoPool]; ac_rfl
      rw [hreord_da]
      refine r2p_call_dealloc (nextOff := 2984) hh hextNeed hsub64 hin2 hinv3
        (by r2p_pc_done) (by simp only [arm64_norm, hrun2'])
        (by r2p_eq) (by r2p_eq) (by r2p_eq) (by r2p_pc_done)
        (by (try simp only [arm64_norm]); try exact hx28_2)
        (by (try simp only [arm64_norm]); try exact hx21_2)
        (by r2p_eq) hpos hlt63
        (by (try simp only [arm64_norm]); exact htr_s2)
        (r2p_histOk_of_trace_files hhist_s2 (by r2p_eq) (by r2p_eq))
        fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
      have hcs_f := r2p_cs_regs hcsm
      have hback :
          A.pool ∗ stackAt fsp (resStack - runFrame) ∗
            (runResAt A cliWrOk g.res (some none) ∗ tailErrPostNoPool) ⊢
          runResAt A cliWrOk g.res (some none) ∗ tailErrPost := by
        dsimp only [tailErrPost, tailErrPostNoPool]; exact Entails.of_eq (by ac_rfl)
      exact sepWPp_weaken_pre hback
        (r2p_free_peer_reject (peerG := peerG) hh hextNeed hsub64 hin_f
          (by rw [hcs_f.1]; (try simp only [arm64_norm]); exact hx19_2)
          htr_f hhist_f
          (r2_ans_of_trace_eq htr_eq hans_s2)
          hrej)

set_option maxHeartbeats 800000 in
theorem r2p_step_chk_copy_sig [LibsignalPlacement] {H : LibsignalHooks}
    {ws dst0 : r2_SlotWords} {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hin : InRunPlaced r2p_CodeOk s0 s 1308)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hw0 : ws.w0 = ctSignalTag)
    (hnext : ∀ s' : State,
      s'.trace = s.trace →
      s'.fs = s.fs →
      InRunPlaced r2p_CodeOk s0 s' 1476 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s'
        (r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) dst0 ∗ F)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 1308 := hin.pc; change s.pc = (blkPl_579).base + 1308#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  have hw0_val : ws.w0 = 0x8000000000000000#64 := hw0
  have hs_eq2 : ConditionHolds .EQ (addsPState64 0x8000000000000000#64 2#64) = false := by r2p_cond
  have hs_ne2 : ConditionHolds .NE (addsPState64 0x8000000000000000#64 2#64) = true := by r2p_cond
  have hs_eq1 : ConditionHolds .EQ (addsPState64 0x8000000000000000#64 1#64) = false := by r2p_cond
  have hs_ne1 : ConditionHolds .NE (addsPState64 0x8000000000000000#64 1#64) = true := by r2p_cond
  have hmi_s : ConditionHolds .MI (subsPState64 0x8000000000000000#64 0#64) = true := by r2p_cond
  have hpl_s : ConditionHolds .PL (subsPState64 0x8000000000000000#64 0#64) = false := by r2p_cond
  have hgt_s : ConditionHolds .GT (subsPState64 0#64 1#64) = false := by r2p_cond
  have hle_s : ConditionHolds .LE (subsPState64 0#64 1#64) = true := by r2p_cond
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 1476) hin.inv
  unfold r2_words31
  rw [hw0_val, ← r2_hold_eq F]
  rw [← hin.sp] at hx22 hx26 hx27 ⊢
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx22 hx26 hx27 ⊢)
  r2p_step_run
  apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
  intro hinv1
  rw [hin.sp, r2_hold_eq F]
  have hin1 : InRunPlaced r2p_CodeOk s0 _ 1476 :=
    r2p_inRun_mk hin (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
      (by r2p_eq) (by r2p_eq) hinv1 (by r2p_eq)
  refine sepWPp_weaken_pre
    (P' := r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F)
    (by unfold r2_words31; rw [hw0_val]; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl))
    (hnext _ (by r2p_eq) (by r2p_eq) hin1
      (by r2p_eq) (by r2p_eq) (by r2p_eq) (by r2p_eq))

set_option maxHeartbeats 800000 in
theorem r2p_step_chk_copy_pk [LibsignalPlacement] {H : LibsignalHooks}
    {ws dst0 : r2_SlotWords} {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hin : InRunPlaced r2p_CodeOk s0 s 1308)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hw0 : ws.w0.toNat < 2 ^ 63)
    (hnext : ∀ s' : State,
      s'.trace = s.trace →
      s'.fs = s.fs →
      InRunPlaced r2p_CodeOk s0 s' 3792 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s'
        (r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) dst0 ∗ F)
      Q Qp (runOom s0) := by
  have hz2 : (ws.w0 + 2#64 == 0#64) = false := beq_eq_false_iff_ne.mpr (by bv_omega)
  have hnz2 : (ws.w0 + 2#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have hz1 : (ws.w0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr (by bv_omega)
  have hnz1 : (ws.w0 + 1#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have heq2 : ConditionHolds .EQ (addsPState64 ws.w0 2#64) = false := by
    rw [conditionHolds_eq_addsPState64]; exact hz2
  have hne2 : ConditionHolds .NE (addsPState64 ws.w0 2#64) = true := by
    rw [conditionHolds_ne_addsPState64]; exact hnz2
  have heq1 : ConditionHolds .EQ (addsPState64 ws.w0 1#64) = false := by
    rw [conditionHolds_eq_addsPState64]; exact hz1
  have hne1 : ConditionHolds .NE (addsPState64 ws.w0 1#64) = true := by
    rw [conditionHolds_ne_addsPState64]; exact hnz1
  have hmsb : ws.w0.msb = false := by bv_bits
  have hmsb0 : (ws.w0 - 0#64).msb = false := by rw [BitVec.sub_zero]; exact hmsb
  have hbit63 : ws.w0.getLsbD 63 = false := by bv_bits
  have hmi : ConditionHolds .MI (subsPState64 ws.w0 0#64) = false := by
    rw [conditionHolds_mi_subsPState64]; exact hmsb0
  have hpl : ConditionHolds .PL (subsPState64 ws.w0 0#64) = true := by
    rw [conditionHolds_pl_subsPState64, hmsb0]; rfl
  have hgt_p : ConditionHolds .GT (subsPState64 1#64 1#64) = false := by r2p_cond
  have hle_p : ConditionHolds .LE (subsPState64 1#64 1#64) = true := by r2p_cond
  have hpc : s.pc = runPcPlaced 1308 := hin.pc; change s.pc = (blkPl_579).base + 1308#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 3792) hin.inv
  unfold r2_words31
  rw [← r2_hold_eq F]
  rw [← hin.sp] at hx22 hx26 hx27 ⊢
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx22 hx26 hx27 ⊢)
  r2p_step_run
  apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
  intro hinv1
  rw [hin.sp, r2_hold_eq F]
  have hin1 : InRunPlaced r2p_CodeOk s0 _ 3792 :=
    r2p_inRun_mk hin (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
      (by r2p_eq) (by r2p_eq) hinv1 (by r2p_eq)
  refine sepWPp_weaken_pre
    (P' := r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F)
    (by unfold r2_words31; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl))
    (hnext _ (by r2p_eq) (by r2p_eq) hin1
      (by r2p_eq) (by r2p_eq) (by r2p_eq) (by r2p_eq))

theorem r2_csm_trans {s1 s2 s3 : State} (h1 : CalleeSavedPreserved s1 s2)
    (h2 : CalleeSavedPreserved s2 s3) : CalleeSavedPreserved s1 s3 := by
  unfold CalleeSavedPreserved at *; simp_all

set_option maxHeartbeats 800000 in
theorem r2p_sig_free_ct [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {i : Inputs} {ws : r2_SlotWords} {s0 s : State} {sub : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1532)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State,
      sf.trace = s.trace →
      InRunPlaced r2p_CodeOk s0 sf 1552 →
      CalleeSavedPreserved s sf →
      s0.trace <+: sf.trace →
      RunHistOk i s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
        DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗ F)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 1532 := hin.pc; change s.pc = (blkPl_579).base + 1532#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  unfold DropPreKeyMsgHelpers.sliceDeallocX
  by_cases hzero : ws.w5 = 0#64
  · simp only [hzero, beq_self_eq_true, ↓reduceIte, emp_sepConj]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 1552) hin.inv
    unfold r2_words31
    rw [hzero, ← r2_hold_eq (A.pool ∗ stackAt (runFsp s0) sub ∗ F), ← hin.sp]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    intro hinv1
    rw [hin.sp, r2_hold_eq]
    have hin1 : InRunPlaced r2p_CodeOk s0 _ 1552 :=
      r2p_inRun_mk hin (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
        (by r2p_eq) (by r2p_eq) hinv1 (by r2p_eq)
    refine sepWPp_weaken_pre
      (P' := r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F)
      (by unfold r2_words31; rw [hzero]; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl))
      (hnext _ (by r2p_eq) hin1
        (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm])
        (by (try simp only [arm64_norm]); exact htr)
        (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq)))
  · have hbeq : (ws.w5 == 0#64) = false := beq_eq_false_iff_ne.mpr hzero
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    have hpull :
        r2_words31 (runFsp s0 + 0x1750#64) ws ∗
          (⌜0 < ws.w5.toNat ∧ ws.w5.toNat < 2 ^ 63⌝ ∗ A.live ws.w4 ws.w5.toNat 1 ∗
            memRegion ws.w4 ws.w5.toNat) ∗
          A.pool ∗ stackAt (runFsp s0) sub ∗ F =
        ⌜0 < ws.w5.toNat ∧ ws.w5.toNat < 2 ^ 63⌝ ∗
          (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
            (A.live ws.w4 ws.w5.toNat 1 ∗ memRegion ws.w4 ws.w5.toNat ∗
              A.pool ∗ stackAt (runFsp s0) sub ∗ F)) := by ac_rfl
    rw [hpull]
    apply SepWPp.pure_left; rintro ⟨hpos, hlt⟩
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hin.inv
    unfold r2_words31
    rw [← r2_hold_eq (A.live ws.w4 ws.w5.toNat 1 ∗ _), ← hin.sp]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    intro hinv1
    rw [hin.sp, r2_hold_eq]
    refine sepWPp_weaken_pre
      (P' := A.live ws.w4 ws.w5.toNat 1 ∗ memRegion ws.w4 ws.w5.toNat ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F))
      (by unfold r2_words31; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl)) ?_
    refine r2p_call_dealloc (nextOff := 1552) hh hextNeed hsub64 hin hinv1
      (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
      (by r2p_eq) (by r2p_eq) (by r2p_eq) (by r2p_pc_done)
      (by r2p_eq) (by r2p_eq) (by r2p_eq)
      hpos hlt
      (by (try simp only [arm64_norm]); exact htr)
      (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq))
      fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
    have hcsm' : CalleeSavedPreserved s sf :=
      r2_csm_trans (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm]) hcsm
    have hback :
        A.pool ∗ stackAt (runFsp s0) sub ∗ (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F) ⊢
          r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F :=
      Entails.of_eq (by ac_rfl)
    exact sepWPp_weaken_pre hback (hnext sf htr_eq hin_f hcsm' htr_f hhist_f)

theorem r2_words4_216_rejoin (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      memRegion (a + 32#64) 216 ⊢
      memRegion a 248 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 240) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 232)
        (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 224)
        (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 216)
        (b' := a + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))

end CryptoVerification.SignalSession.Cli.RunCompose
