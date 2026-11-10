/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `signal_session::run` Arm `R3b`: PreKey Arm Step Lemmas

Relocatable (`[LibsignalPlacement]`) step lemmas on Block `579` (`runProgPlaced H`) for the
`PreKeySignalMessage::try_from` `Err` path, the two-part `Ok` stack shuffle (`R+0x994 → R+0xaa0`
and `R+0xaa0 → blkPl_520.base`), and the `decrypt_prekey` `Err` and `Ok` tails.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. Flat Word-Slot Collapse Helpers -/

theorem r3b_pt64_eq {a b v w : BitVec 64} (ha : a = b) (hv : v = w) :
    (a ↦₆₄ v) ⊢ (b ↦₆₄ w) := by
  subst ha; subst hv; exact Entails.refl _

theorem r3b_collapse5_flat {a a1 a2 a3 a4 : BitVec 64}
    {w0 w1 w2 w3 w4 : BitVec 64} {T R : SepProp}
    (e1 : a + 8#64 = a1) (e2 : a + 16#64 = a2) (e3 : a + 24#64 = a3) (e4 : a + 32#64 = a4)
    (hT : memRegion a 40 ∗ T ⊢ R) :
    (a ↦₆₄ w0) ∗ (a1 ↦₆₄ w1) ∗ (a2 ↦₆₄ w2) ∗ (a3 ↦₆₄ w3) ∗ (a4 ↦₆₄ w4) ∗ T ⊢ R := by
  subst e1; subst e2; subst e3; subst e4
  have h5 : (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ⊢ memRegion a 40 :=
    r3b_slot5_to_mem40 a ⟨w0, w1, w2, w3, w4⟩
  refine Entails.trans ?_ hT
  simpa only [sepConj_assoc] using sepConj_mono_left (Q := T) h5

theorem r3b_collapse30_flat {a : BitVec 64}
    {w00 w01 w02 w03 w04 w05 w06 w07 w08 w09
     w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
     w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64}
    {a01 a02 a03 a04 a05 a06 a07 a08 a09
     a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
     a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 : BitVec 64}
    {T R : SepProp}
    (e01 : a + 8#64 = a01) (e02 : a + 16#64 = a02) (e03 : a + 24#64 = a03)
    (e04 : a + 32#64 = a04) (e05 : a + 40#64 = a05) (e06 : a + 48#64 = a06)
    (e07 : a + 56#64 = a07) (e08 : a + 64#64 = a08) (e09 : a + 72#64 = a09)
    (e10 : a + 80#64 = a10) (e11 : a + 88#64 = a11) (e12 : a + 96#64 = a12)
    (e13 : a + 104#64 = a13) (e14 : a + 112#64 = a14) (e15 : a + 120#64 = a15)
    (e16 : a + 128#64 = a16) (e17 : a + 136#64 = a17) (e18 : a + 144#64 = a18)
    (e19 : a + 152#64 = a19) (e20 : a + 160#64 = a20) (e21 : a + 168#64 = a21)
    (e22 : a + 176#64 = a22) (e23 : a + 184#64 = a23) (e24 : a + 192#64 = a24)
    (e25 : a + 200#64 = a25) (e26 : a + 208#64 = a26) (e27 : a + 216#64 = a27)
    (e28 : a + 224#64 = a28) (e29 : a + 232#64 = a29)
    (hT : memRegion a 240 ∗ T ⊢ R) :
    (a ↦₆₄ w00) ∗ (a01 ↦₆₄ w01) ∗ (a02 ↦₆₄ w02) ∗ (a03 ↦₆₄ w03) ∗ (a04 ↦₆₄ w04) ∗
    (a05 ↦₆₄ w05) ∗ (a06 ↦₆₄ w06) ∗ (a07 ↦₆₄ w07) ∗ (a08 ↦₆₄ w08) ∗ (a09 ↦₆₄ w09) ∗
    (a10 ↦₆₄ w10) ∗ (a11 ↦₆₄ w11) ∗ (a12 ↦₆₄ w12) ∗ (a13 ↦₆₄ w13) ∗ (a14 ↦₆₄ w14) ∗
    (a15 ↦₆₄ w15) ∗ (a16 ↦₆₄ w16) ∗ (a17 ↦₆₄ w17) ∗ (a18 ↦₆₄ w18) ∗ (a19 ↦₆₄ w19) ∗
    (a20 ↦₆₄ w20) ∗ (a21 ↦₆₄ w21) ∗ (a22 ↦₆₄ w22) ∗ (a23 ↦₆₄ w23) ∗ (a24 ↦₆₄ w24) ∗
    (a25 ↦₆₄ w25) ∗ (a26 ↦₆₄ w26) ∗ (a27 ↦₆₄ w27) ∗ (a28 ↦₆₄ w28) ∗ (a29 ↦₆₄ w29) ∗
    T ⊢ R := by
  subst e01; subst e02; subst e03; subst e04; subst e05
  subst e06; subst e07; subst e08; subst e09; subst e10
  subst e11; subst e12; subst e13; subst e14; subst e15
  subst e16; subst e17; subst e18; subst e19; subst e20
  subst e21; subst e22; subst e23; subst e24; subst e25
  subst e26; subst e27; subst e28; subst e29
  have h30 := r3b_slot30_to_mem240 a
    ⟨⟨w00, w01, w02, w03, w04⟩, ⟨w05, w06, w07, w08, w09⟩, ⟨w10, w11, w12, w13, w14⟩,
     ⟨w15, w16, w17, w18, w19⟩, ⟨w20, w21, w22, w23, w24⟩, ⟨w25, w26, w27, w28, w29⟩⟩
  dsimp only [r3b_slot30, r3b_slot5] at h30
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h30
  refine Entails.trans ?_ hT
  simpa only [sepConj_assoc] using sepConj_mono_left (Q := T) h30
/-! ## 2. `PreKeySignalMessage::try_from` `Err` Path (`r3b_recvP_parse_err_placed`) -/

set_option maxHeartbeats 600000 in
/-- `PreKeySignalMessage::try_from` `Err` path (`R+0x994 → R+0xeb8 → R+0xfe0 → (blkPl_553).base → R+0xfec`). -/
theorem r3b_recvP_parse_err_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall}
    (meG peerG : AddrGhost) (cw4 hiMe : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0x994)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A meG ∗ addrNameHeap A peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ cw4)) ∗
        memRegion (runFsp s0 + 0x240#64) 0x20 ∗
        (((runFsp s0 + 0x260#64) ↦₆₄ meG.name.cap) ∗
          ((runFsp s0 + 0x268#64) ↦₆₄ meG.name.ptr) ∗
          ((runFsp s0 + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((runFsp s0 + 0x278#64) ↦₆₄ hiMe)) ∗
        memRegion (runFsp s0 + 0x280#64) (0x4d0 - 0x280) ∗
        pksmResAt A (runFsp s0 + 0x4d0#64) none ∗
        memRegion (runFsp s0 + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 0x994 := hs.pc
  change s.pc = (blkPl_579).base + 0x994#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  generalize hfsp : runFsp s0 = fsp at hsp hx26 ⊢
  have h280 : memRegion (fsp + 0x280#64) (0x4d0 - 0x280) =
      memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2a0#64) 40 ∗
        memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) := by
    rw [r3b_split_at fsp 0x280 0x20 0x4d0 (by omega) (by omega),
        r3b_split_at fsp 0x2a0 40 0x4d0 (by omega) (by omega)]
  rw [h280]
  have hpkm_err :
      pksmResAt A (fsp + 0x4d0#64) none ∗ memRegion (fsp + 0x2a0#64) 40 ∗ anyHeap ⊢
      ∃∗ k : RunDrop.SpeOwned, ∃∗ t : r3b_W5,
        RunDrop.speOwnedAt A (fsp + 0x4d8#64) k ∗
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
        r3b_slot5 (fsp + 0x2a0#64) t ∗
        memRegion (fsp + 0x508#64) 192 ∗ anyHeap := by
    have ha4d8 : fsp + 0x4d0#64 + 8#64 = fsp + 0x4d8#64 := by bv_omega
    have ha508 : fsp + 0x4d0#64 + 56#64 = fsp + 0x508#64 := by bv_omega
    refine Entails.trans
      (sepConj_mono (pksmResAt_err_owned A (fsp + 0x4d0#64))
        (sepConj_mono (r3b_mem40_to_slot5 (fsp + 0x2a0#64)) (Entails.refl anyHeap)))
      ?_
    rw [ha4d8, ha508]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro t
    apply Entails.sepExists_elim; intro k
    refine Entails.sepExists_right k (Entails.sepExists_right t ?_)
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (entails_anyHeap (anyHeap ∗ anyHeap))
          (Entails.refl (RunDrop.speOwnedAt A (fsp + 0x4d8#64) k ∗
            ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
            r3b_slot5 (fsp + 0x2a0#64) t ∗
            memRegion (fsp + 0x508#64) 192)))
        (by ac_rfl))
      (by ac_rfl)
  apply r3b_sepWPp_weaken_pre
    (r3b_perm
      (sepConj_mono_left
        (Q := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
          memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        hpkm_err)
      (by ac_rfl))
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro k
  apply r3b_sepWPp_exists_left; intro t
  rw [sepConj_assoc]
  refine r3b_with_speOwned_words6 (src := fsp + 0x4d8#64) (dst := fsp + 0x4d0#64) (k := k)
    (fun sw _ _ => ?_)
  apply r3b_sepWPp_weaken_pre
    (show (r3b_slot6 (fsp + 0x4d8#64) sw ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x4d0#64) k) ∗
        (((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
          r3b_slot5 (fsp + 0x2a0#64) t ∗
          memRegion (fsp + 0x508#64) 192 ∗ anyHeap) ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
          memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool)) ⊢
      (((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
        r3b_slot6 (fsp + 0x4d8#64) sw ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x4d0#64) k) ∗
        r3b_slot5 (fsp + 0x2a0#64) t ∗
        memRegion (fsp + 0x508#64) 192 ∗ anyHeap) ∗
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
        memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
          ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
          ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
        memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
        memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool) from Entails.of_eq (by ac_rfl))
  have herr_eq : ((errTag + 1#64) == 0#64) = true := rfl
  apply r3b_seq (mid := (blkPl_553).base) hs.inv
  dsimp only [r3b_slot6, r3b_slot5]
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx26 ⊢
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, hrun])
  intro hinv_c
  refine r3b_call_lscro
    (F := ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
      r3b_slot5 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩ ∗
      memRegion (fsp + 0x508#64) 192 ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
      memRegion fsp 0x220 ∗
      (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
        ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
        ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
      memRegion (fsp + 0x240#64) 0x20 ∗
      (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
        ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
      memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
      memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗ anyHeap)
    (s0 := s0) ⟨fsp + 0x4d0#64, k⟩
    (hdrop (resStack - runFrame) hstk32 hsub64) hinv_c
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, hrun])
    (by simpa only [State.spAligned, arm64_norm] using hsp_al)
    (retAddr := runPcPlaced 0xfec)
    (by simp only [runPcPlaced_eq, arm64_norm])
    ?_
    (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
  · dsimp only [RunDrop.dropSpeOwnedSpec]
    simp only [sepConj_assoc]
    apply Entails.pure_right
    · simp only [arm64_norm]; try rw [hsp]
    simp only [arm64_norm]
    try rw [hsp]
    have hwand :
        r3b_slot6 (fsp + 0x4d0#64) sw ∗
          (r3b_slot6 (fsp + 0x4d0#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x4d0#64) k) ⊢
        RunDrop.speOwnedAt A (fsp + 0x4d0#64) k := Entails.wand_elim _ _
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono hwand
          (Entails.refl (A.pool ∗ stackAt fsp (resStack - runFrame) ∗
            ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
            r3b_slot5 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩ ∗
            memRegion (fsp + 0x508#64) 192 ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
            memRegion fsp 0x220 ∗
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
            memRegion (fsp + 0x240#64) 0x20 ∗
            (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
              ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
            memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
            memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗ anyHeap)))
        (by ac_rfl))
      (by
        dsimp only [r3b_slot6, r3b_slot5]
        have o1 : fsp + 0x4d0#64 + 8#64 = fsp + 1240#64 := by bv_omega
        have o2 : fsp + 0x4d0#64 + 16#64 = fsp + 1248#64 := by bv_omega
        have o3 : fsp + 0x4d0#64 + 24#64 = fsp + 1256#64 := by bv_omega
        have o4 : fsp + 0x4d0#64 + 32#64 = fsp + 1264#64 := by bv_omega
        have o5 : fsp + 0x4d0#64 + 40#64 = fsp + 1272#64 := by bv_omega
        have t1 : fsp + 672#64 + 8#64 = fsp + 680#64 := by bv_omega
        have t2 : fsp + 672#64 + 16#64 = fsp + 688#64 := by bv_omega
        have t3 : fsp + 672#64 + 24#64 = fsp + 696#64 := by bv_omega
        have t4 : fsp + 672#64 + 32#64 = fsp + 704#64 := by bv_omega
        have z0 : fsp + 1232#64 = fsp + 0x4d0#64 := rfl
        rw [o1, o2, o3, o4, o5, t1, t2, t3, t4, z0]
        ac_rfl)
  · dsimp only [RunDrop.dropSpeOwnedSpec]
    simp only [sepConj_assoc]
    apply r3b_sepWPp_pure_left; intro htr_m
    have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [arm64_norm])
    have hfs_tot : sm.fs.files = s.fs.files := by
      have hs_steps : Steps (runProgPlaced H) _ sm := ‹_›
      exact (r3b_files_of_trace_eq (hh.fs (runProgPlaced H) 579) hs_steps htr_m).trans
        (by simp only [arm64_norm])
    have hs_m : InRunPlaced CodeOk s0 sm 0xfec :=
      r3b_inRun_step hs hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
        (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
        (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
    refine r3b_sepWPp_weaken_pre ?_
      (r3b_reject_from_fec_placed StoresGhost.opened meG peerG
        (BitVec.ofNat 64 peerG.name.bytes.length) cw4 hh hext_le hsub64 hs_m
        (hcsm.1.trans (by simp only [arm64_norm, hx19]))
        (hcsm.2.1.trans (by simp only [arm64_norm, hx20]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, hx21]))
        (hcsm.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx28]))
        (htr_tot ▸ htr)
        (r3b_hist_of_eq htr_tot hfs_tot hhist)
        hans hrej)
    have hloc_back :
        memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) 0x20 ∗
          r3b_slot5 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩ ∗
          memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
          memRegion (fsp + 0x4d0#64) 48 ∗
          ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
          memRegion (fsp + 0x508#64) 192 ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ⊢
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
      have hpkm_back :
          memRegion (fsp + 0x4d0#64) 48 ∗ ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
            memRegion (fsp + 0x508#64) 192 ⊢
          memRegion (fsp + 0x4d0#64) 248 := by
        rw [ProofLib.memRegion_split' (b := fsp + 0x4d0#64) (n := 48) (k := 200)
              (b' := fsp + 1280#64) rfl (by bv_omega) (by decide),
            ProofLib.memRegion_split' (b := fsp + 1280#64) (n := 8) (k := 192)
              (b' := fsp + 0x508#64) rfl (by bv_omega) (by decide)]
        exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))
      have hm1 := sepConj_mono (Entails.refl (memRegion (fsp + 0x240#64) 0x20))
        (sepConj_mono (r3b_words4_entails_mem32 (fsp + 0x260#64) meG.name.cap meG.name.ptr
              (BitVec.ofNat 64 meG.name.bytes.length) hiMe)
          (sepConj_mono (Entails.refl (memRegion (fsp + 0x280#64) 0x20))
            (sepConj_mono (r3b_slot5_to_mem40 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩)
              (sepConj_mono (Entails.refl (memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8)))
                (sepConj_mono hpkm_back
                  (Entails.refl (memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8))))))))
      have heq_all : memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) =
          memRegion (fsp + 0x240#64) 0x20 ∗
            (memRegion (fsp + 0x260#64) 32 ∗
              (memRegion (fsp + 0x280#64) 0x20 ∗
                (memRegion (fsp + 672#64) 40 ∗
                  (memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
                    (memRegion (fsp + 0x4d0#64) 248 ∗
                      memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8)))))) := by
        rw [r3b_split_at fsp 0x240 0x20 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x260 32 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x280 0x20 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x2a0 40 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x2c8 (0x4d0 - 0x2c8) runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x4d0 248 runLocalBytes (by decide) (by decide)]
      rw [heq_all]
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1
      exact r3b_perm hm1 (by ac_rfl)
    subst hfsp
    rw [← hspm, hs_m.sp]
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono hloc_back
          (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
            memRegion (runFsp s0) 0x220 ∗
            (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((runFsp s0 + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((runFsp s0 + 0x238#64) ↦₆₄ cw4)) ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)))
        (by ac_rfl))
      (by ac_rfl)

/-! ## 3. `PreKeySignalMessage::try_from` `Ok` Shuffle (`r3b_recvP_shuf1_placed`, `r3b_recvP_shuf2_placed`) -/

set_option maxHeartbeats 800000 in
/-- First half of `PreKeySignalMessage::try_from` `Ok` shuffle (`R+0x994 → R+0xaa0`). -/
theorem r3b_recvP_shuf1_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {H : LibsignalHooks}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (pqCap : BitVec 64) (w : r3b_W30) (t : r3b_W5) (z m : r3b_W30) (F : SepProp)
    (hs : InRunPlaced CodeOk s0 s 0x994)
    (hcap : pqCap.toNat < 2 ^ 63)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hk : ∀ s' : State,
      InRunPlaced CodeOk s0 s' 0xaa0 →
      s'.readReg64 (.gpr 8#5) = w.b0.w0 →
      s'.readReg64 (.gpr 9#5) = pqCap →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      s'.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      s'.trace = s.trace →
      s'.fs = s.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s'
        (((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
          r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗
          memRegion (runFsp s0 + 0x2a0#64) 40 ∗
          r3b_slot30 (runFsp s0 + 0x3e0#64) (r3b_shufMid w z) ∗
          memRegion (runFsp s0 + 0x1750#64) 240 ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
        r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗
        r3b_slot5 (runFsp s0 + 0x2a0#64) t ∗
        r3b_slot30 (runFsp s0 + 0x3e0#64) z ∗
        r3b_slot30 (runFsp s0 + 0x1750#64) m ∗ F)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 0x994 := hs.pc
  change s.pc = (blkPl_579).base + 0x994#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hcmn : ((pqCap + 1#64) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by intro h0; bv_omega)
  generalize hfsp : runFsp s0 = fsp at hsp hx26 hx27 ⊢
  apply r3b_seq (mid := runPcPlaced 0xaa0) hs.inv
  rw [runPcPlaced_eq]
  dsimp only [r3b_slot30, r3b_slot5]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hx26 hx27 ⊢
  wp_steps
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  intro hinv'
  subst hfsp
  let fsp := runFsp s0
  have hs' : InRunPlaced CodeOk s0 _ 0xaa0 :=
    r3b_inRun_step hs (by simp only [runPcPlaced_eq, arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv' (by simp only [calleeSavedVRegs, arm64_norm])
  refine r3b_sepWPp_weaken_pre ?_
    (hk _ hs'
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]))
  try rw [hsp]
  have hc5 : ∀ (T : SepProp),
      ((fsp + 672#64) ↦₆₄ w.b0.w1) ∗ ((fsp + 680#64) ↦₆₄ w.b0.w2) ∗
      ((fsp + 688#64) ↦₆₄ w.b0.w3) ∗ ((fsp + 696#64) ↦₆₄ w.b0.w4) ∗
      ((fsp + 704#64) ↦₆₄ w.b1.w0) ∗ T ⊢ memRegion (fsp + 0x2a0#64) 40 ∗ T :=
    fun T => r3b_collapse5_flat (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (Entails.refl _)
  have hc30 : ∀ (T : SepProp),
      ((fsp + 5968#64) ↦₆₄ w.b0.w1) ∗ ((fsp + 5976#64) ↦₆₄ w.b0.w2) ∗
      ((fsp + 5984#64) ↦₆₄ w.b0.w3) ∗ ((fsp + 5992#64) ↦₆₄ w.b0.w4) ∗
      ((fsp + 6000#64) ↦₆₄ w.b1.w0) ∗ ((fsp + 6008#64) ↦₆₄ w.b1.w1) ∗
      ((fsp + 6016#64) ↦₆₄ w.b1.w2) ∗ ((fsp + 6024#64) ↦₆₄ w.b1.w3) ∗
      ((fsp + 6032#64) ↦₆₄ w.b1.w4) ∗ ((fsp + 6040#64) ↦₆₄ w.b2.w0) ∗
      ((fsp + 6048#64) ↦₆₄ w.b2.w1) ∗ ((fsp + 6056#64) ↦₆₄ w.b2.w2) ∗
      ((fsp + 6064#64) ↦₆₄ w.b2.w3) ∗ ((fsp + 6072#64) ↦₆₄ w.b2.w4) ∗
      ((fsp + 6080#64) ↦₆₄ w.b3.w0) ∗ ((fsp + 6088#64) ↦₆₄ w.b3.w1) ∗
      ((fsp + 6096#64) ↦₆₄ w.b3.w2) ∗ ((fsp + 6104#64) ↦₆₄ w.b3.w3) ∗
      ((fsp + 6112#64) ↦₆₄ w.b3.w4) ∗ ((fsp + 6120#64) ↦₆₄ w.b4.w0) ∗
      ((fsp + 6128#64) ↦₆₄ w.b4.w1) ∗ ((fsp + 6136#64) ↦₆₄ w.b4.w2) ∗
      ((fsp + 6144#64) ↦₆₄ w.b4.w3) ∗ ((fsp + 6152#64) ↦₆₄ w.b4.w4) ∗
      ((fsp + 6160#64) ↦₆₄ w.b5.w0) ∗ ((fsp + 6168#64) ↦₆₄ w.b5.w1) ∗
      ((fsp + 6176#64) ↦₆₄ w.b5.w2) ∗ ((fsp + 6184#64) ↦₆₄ w.b5.w3) ∗
      ((fsp + 6192#64) ↦₆₄ w.b5.w4) ∗ ((fsp + 6200#64) ↦₆₄ m.b5.w4) ∗ T ⊢
      memRegion (fsp + 0x1750#64) 240 ∗ T :=
    fun T => r3b_collapse30_flat
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (Entails.refl _)
  dsimp only [fsp, r3b_slot30, r3b_slot5, r3b_shufMid] at hc5 hc30 ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hc5 hc30 ⊢
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (Entails.trans (hc5 _) (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (hc30 _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxHeartbeats 800000 in
/-- Second half of `PreKeySignalMessage::try_from` `Ok` shuffle (`R+0xaa0 → lsmpl.base 520`,
returning to `R+0xb78`). -/
theorem r3b_recvP_shuf2_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {H : LibsignalHooks}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (stores pqCap : BitVec 64) (t0 : r3b_W5) (w z : r3b_W30) (F : SepProp)
    (hs : InRunPlaced CodeOk s0 s 0xaa0)
    (hx8 : s.readReg64 (.gpr 8#5) = w.b0.w0)
    (hx9 : s.readReg64 (.gpr 9#5) = pqCap)
    (hx19 : s.readReg64 (.gpr 19#5) = stores)
    (hk : ∀ sc : State,
      CodeOk sc.mem →
      sc.pc = lsmpl.base 520 →
      sc.status = .Running →
      sc.sp = runFsp s0 →
      sc.spAligned = true →
      sc.readReg64 Reg.lr = runPcPlaced 0xb78 →
      sc.readReg64 .x0 = runFsp s0 + 0x4d0#64 →
      sc.readReg64 .x1 = runFsp s0 + 0x220#64 →
      sc.readReg64 .x2 = runFsp s0 + 0x260#64 →
      sc.readReg64 .x3 = stores + 0xf0#64 →
      sc.readReg64 .x4 = lsρ cliSessionVtSym →
      sc.readReg64 .x5 = stores →
      sc.readReg64 .x6 = lsρ cliIdentityVtSym →
      sc.readReg64 .x7 = stores + 0xc8#64 →
      sc.readReg64 .x8 = runFsp s0 + 0x320#64 →
      sc.readReg64 (.gpr 19#5) = stores →
      sc.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sc.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sc.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      sc.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      sc.readReg64 .fp = s.readReg64 .fp →
      calleeSavedVRegs sc = calleeSavedVRegs s →
      sc.trace = s.trace →
      sc.fs = s.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sc
        ((runFsp s0 ↦₆₄ lsρ cliPreKeyVtSym) ∗
          ((runFsp s0 + 8#64) ↦₆₄ (stores + 0x50#64)) ∗
          ((runFsp s0 + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
          ((runFsp s0 + 24#64) ↦₆₄ (stores + 0x78#64)) ∗
          ((runFsp s0 + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
          memRegion (runFsp s0 + 0x3e0#64) 240 ∗
          ((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
          r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r3b_slot5 (runFsp s0) t0 ∗
        r3b_slot30 (runFsp s0 + 0x3e0#64) (r3b_shufMid w z) ∗
        ((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
        r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗ F)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 0xaa0 := hs.pc
  change s.pc = (blkPl_579).base + 0xaa0#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  generalize hfsp : runFsp s0 = fsp at hsp ⊢
  apply r3b_seq (mid := lsmpl.base 520) hs.inv
  dsimp only [r3b_slot30, r3b_slot5, r3b_shufMid]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hrun])
  intro hinv_c
  subst hfsp
  let fsp := runFsp s0
  refine r3b_sepWPp_weaken_pre ?_
    (hk _ hinv_c
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm]; try rw [hsp])
      (by simpa only [State.spAligned, arm64_norm] using hsp_al)
      (by simp only [runPcPlaced_eq, arm64_norm])
      (by simp only [arm64_norm]; try rw [hsp])
      (by simp only [arm64_norm]; try rw [hsp])
      (by simp only [arm64_norm]; try rw [hsp])
      (by simp only [arm64_norm]; try rw [hx19])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; try rw [hx19])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; try rw [hx19])
      (by simp only [arm64_norm]; try rw [hsp])
      (by simp only [arm64_norm]; try rw [hx19])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [calleeSavedVRegs, arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]))
  try rw [hsp]
  dsimp only [fsp, r3b_slot30, r3b_slot5]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepConj_mono (r3b_pt64_eq rfl rfl)
    (sepConj_mono (r3b_pt64_eq rfl rfl)
      (sepConj_mono (r3b_pt64_eq rfl rfl)
        (sepConj_mono (r3b_pt64_eq rfl rfl)
          (sepConj_mono (r3b_pt64_eq rfl rfl)
            (r3b_collapse30_flat
              (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
              (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
              (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
              (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
              (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
              (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
              (Entails.refl _))))))

/-! ## 4. `decrypt_prekey` `Err` Tail (`r3b_recvP_dec_err_placed`) -/

set_option maxHeartbeats 800000 in
/-- `decrypt_prekey` `Err` tail from `R+0xd94` (`R+0xd94 → R+0xfc4 → (blkPl_553).base → R+0xfec → R+0x2c7c`). -/
theorem r3b_recvP_dec_err_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (err : ApiError AddrVal Unit) (peerG meG : AddrGhost)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0xd94)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        memRegion (runFsp s0 + 0x240#64) 0x20 ∗
        memRegion (runFsp s0 + 0x280#64) 0xa0 ∗
        decResAt A (runFsp s0 + 0x320#64) (.error err) ∗
        memRegion (runFsp s0 + 0x350#64) (runLocalBytes - 0x350) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 0xd94 := hs.pc
  change s.pc = (blkPl_579).base + 0xd94#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  generalize hfsp : runFsp s0 = fsp at hsp hx26 ⊢
  have h350 : memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) =
      memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
        memRegion (fsp + 0x4d0#64) 48 ∗
        memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) := by
    rw [r3b_split_at fsp 0x350 (0x4d0 - 0x350) runLocalBytes (by decide) (by decide),
        r3b_split_at fsp 0x4d0 48 runLocalBytes (by decide) (by decide)]
  have hprep :
      decResAt A (fsp + 0x320#64) (.error err) ∗ memRegion (fsp + 0x4d0#64) 48 ⊢
        ∃∗ k : RunDrop.SpeOwned, ∃∗ d0 : r3b_W6,
          RunDrop.speOwnedAt A (fsp + 0x320#64) k ∗
          r3b_slot6 (fsp + 0x4d0#64) d0 := by
    dsimp only [decResAt]
    refine Entails.trans (sepConj_mono_right (r3b_mem48_to_slot6 (fsp + 0x4d0#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro d0
    apply Entails.sepExists_elim; intro k
    exact Entails.sepExists_right k (Entails.sepExists_right d0 (Entails.refl _))
  rw [h350]
  apply r3b_sepWPp_weaken_pre
    (r3b_perm
      (sepConj_mono_left
        (Q := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          protocolAddressAt A peerG (fsp + 0x220#64) ∗
          protocolAddressAt A meG (fsp + 0x260#64) ∗
          runSaved s0 ∗
          memRegion fsp 0x220 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          memRegion (fsp + 0x280#64) 0xa0 ∗
          memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
          memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
        hprep)
      (by ac_rfl))
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro k
  apply r3b_sepWPp_exists_left; intro d0
  rw [sepConj_assoc]
  refine r3b_with_speOwned_words6 (src := fsp + 0x320#64) (dst := fsp + 0x4d0#64) (k := k)
    (fun sw hu3 hu2 => ?_)
  have hcmn3 : ((sw.w0 + 3#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hu3
  have hcmn2_eq : ((sw.w0 + 2#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hu2
  have hcmn2_ne : ((sw.w0 + 2#64) != 0#64) = true := bne_iff_ne.mpr hu2
  apply r3b_sepWPp_weaken_pre
    (show (r3b_slot6 (fsp + 0x320#64) sw ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x4d0#64) k) ∗
        (r3b_slot6 (fsp + 0x4d0#64) d0 ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            protocolAddressAt A peerG (fsp + 0x220#64) ∗
            protocolAddressAt A meG (fsp + 0x260#64) ∗
            runSaved s0 ∗
            memRegion fsp 0x220 ∗
            memRegion (fsp + 0x240#64) 0x20 ∗
            memRegion (fsp + 0x280#64) 0xa0 ∗
            memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
            memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap))) ⊢
      (r3b_slot6 (fsp + 0x320#64) sw ∗
        r3b_slot6 (fsp + 0x4d0#64) d0 ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x4d0#64) k)) ∗
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A peerG (fsp + 0x220#64) ∗
        protocolAddressAt A meG (fsp + 0x260#64) ∗
        runSaved s0 ∗
        memRegion fsp 0x220 ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        memRegion (fsp + 0x280#64) 0xa0 ∗
        memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
        memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) from Entails.of_eq (by ac_rfl))
  apply r3b_seq (mid := (blkPl_553).base) hs.inv
  dsimp only [r3b_slot6]
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx26 ⊢
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, hrun])
  intro hinv_c
  refine r3b_call_lscro
    (F := memRegion (fsp + 0x320#64) 48 ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      protocolAddressAt A peerG (fsp + 0x220#64) ∗
      protocolAddressAt A meG (fsp + 0x260#64) ∗
      runSaved s0 ∗
      memRegion fsp 0x220 ∗
      memRegion (fsp + 0x240#64) 0x20 ∗
      memRegion (fsp + 0x280#64) 0xa0 ∗
      memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
      memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗ anyHeap)
    (s0 := s0) ⟨fsp + 0x4d0#64, k⟩
    (hdrop (resStack - runFrame) hstk32 hsub64) hinv_c
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, hrun])
    (by simpa only [State.spAligned, arm64_norm] using hsp_al)
    (retAddr := runPcPlaced 0xfec)
    (by simp only [runPcPlaced_eq, arm64_norm])
    ?_
    (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
  · dsimp only [RunDrop.dropSpeOwnedSpec]
    simp only [sepConj_assoc]
    apply Entails.pure_right
    · simp only [arm64_norm]; try rw [hsp]
    simp only [arm64_norm]
    try rw [hsp]
    have hwand :
        r3b_slot6 (fsp + 0x4d0#64) sw ∗
          (r3b_slot6 (fsp + 0x4d0#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x4d0#64) k) ⊢
        RunDrop.speOwnedAt A (fsp + 0x4d0#64) k := Entails.wand_elim _ _
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono hwand
          (sepConj_mono (r3b_slot6_to_mem48 (fsp + 0x320#64) sw)
            (Entails.refl (A.pool ∗ stackAt fsp (resStack - runFrame) ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              protocolAddressAt A peerG (fsp + 0x220#64) ∗
              protocolAddressAt A meG (fsp + 0x260#64) ∗
              runSaved s0 ∗
              memRegion fsp 0x220 ∗
              memRegion (fsp + 0x240#64) 0x20 ∗
              memRegion (fsp + 0x280#64) 0xa0 ∗
              memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
              memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗ anyHeap))))
        (by ac_rfl))
      (by
        dsimp only [r3b_slot6]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        ac_rfl)
  · dsimp only [RunDrop.dropSpeOwnedSpec]
    simp only [sepConj_assoc]
    apply r3b_sepWPp_pure_left; intro htr_m
    have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [arm64_norm])
    have hfs_tot : sm.fs.files = s.fs.files := by
      have hs_steps : Steps (runProgPlaced H) _ sm := ‹_›
      exact (r3b_files_of_trace_eq (hh.fs (runProgPlaced H) 579) hs_steps htr_m).trans
        (by simp only [arm64_norm])
    have hs_m : InRunPlaced CodeOk s0 sm 0xfec :=
      r3b_inRun_step hs hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
        (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
        (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
    have hunp :
        protocolAddressAt A peerG (fsp + 0x220#64) ∗ protocolAddressAt A meG (fsp + 0x260#64) ⊢
          ∃∗ hiP : BitVec 64,
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((fsp + 0x238#64) ↦₆₄ hiP)) ∗
            memRegion (fsp + 0x260#64) 32 ∗
            addrNameHeap A meG ∗ addrNameHeap A peerG := by
      refine Entails.trans
        (sepConj_mono
          (r3b_addr_unpack A peerG (fsp + 0x220#64) (fsp + 0x228#64) (fsp + 0x230#64) (fsp + 0x238#64)
            (by bv_omega) (by bv_omega) (by bv_omega))
          (r3b_addr_unpack A meG (fsp + 0x260#64) (fsp + 0x268#64) (fsp + 0x270#64) (fsp + 0x278#64)
            (by bv_omega) (by bv_omega) (by bv_omega))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro hiM
      apply Entails.sepExists_elim; intro hiP
      simp only [sepConj_assoc]
      apply Entails.pure_left; intro _
      apply r3b_pure5; intro _
      have hm4 := r3b_words4_entails_mem32 (fsp + 0x260#64) meG.name.cap meG.name.ptr
        (BitVec.ofNat 64 meG.name.bytes.length) hiM
      have o1 : fsp + 0x260#64 + 8#64 = fsp + 0x268#64 := by bv_omega
      have o2 : fsp + 0x260#64 + 16#64 = fsp + 0x270#64 := by bv_omega
      have o3 : fsp + 0x260#64 + 24#64 = fsp + 0x278#64 := by bv_omega
      rw [o1, o2, o3] at hm4
      refine Entails.sepExists_right hiP ?_
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono hm4
            (Entails.refl ((((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((fsp + 0x238#64) ↦₆₄ hiP)) ∗
              addrNameHeap A meG ∗ addrNameHeap A peerG)))
          (by ac_rfl))
        (by ac_rfl)
    simp only [arm64_norm, hsp]
    apply r3b_sepWPp_weaken_pre
      (r3b_perm
        (sepConj_mono_left
          (Q := memRegion (fsp + 0x4d0#64) 48 ∗ A.pool ∗ stackAt fsp (resStack - runFrame) ∗
            memRegion (fsp + 0x320#64) 48 ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            runSaved s0 ∗
            memRegion fsp 0x220 ∗
            memRegion (fsp + 0x240#64) 0x20 ∗
            memRegion (fsp + 0x280#64) 0xa0 ∗
            memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
            memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗ anyHeap)
          hunp)
        (by ac_rfl))
    simp only [sepExists_sepConj_left]
    apply r3b_sepWPp_exists_left; intro hiP
    have hloc_back :
        memRegion (fsp + 0x240#64) 0x20 ∗
          memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x280#64) 0xa0 ∗
          memRegion (fsp + 0x320#64) 48 ∗
          memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
          memRegion (fsp + 0x4d0#64) 48 ∗
          memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) =
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
      rw [r3b_split_at fsp 0x240 0x20 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x260 32 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x280 0xa0 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x320 48 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x350 (0x4d0 - 0x350) runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x4d0 48 runLocalBytes (by decide) (by decide)]
    refine r3b_sepWPp_weaken_pre ?_
      (r3b_reject_from_fec_placed g' meG peerG
        (BitVec.ofNat 64 peerG.name.bytes.length) hiP hh hext_le hsub64 hs_m
        (hcsm.1.trans (by simp only [arm64_norm, hx19]))
        (hcsm.2.1.trans (by simp only [arm64_norm, hx20]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, hx21]))
        (hcsm.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx28]))
        (htr_tot ▸ htr)
        (r3b_hist_of_eq htr_tot hfs_tot hhist)
        hans
        hrej)
    subst hfsp
    rw [← hloc_back]
    exact Entails.of_eq (by ac_rfl)

/-! ## 5. `decrypt_prekey` `Ok` Tail Helpers (`r3b_recvP_from_de0_placed`, `r3b_recvP_from_dcc_placed`) -/

set_option maxHeartbeats 800000 in
/-- Continuation from `R+0xde0` (`R+0xde0 → R+0xf8c` `AtJoinPlaced`, freeing `peerG.name` if `cap ≠ 0`). -/
theorem r3b_recvP_from_de0_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG : AddrGhost)
    {s0 sd : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hsd : InRunPlaced CodeOk s0 sd 0xde0)
    (hx19d : sd.readReg64 (.gpr 19#5) = g.stores)
    (hx20d : sd.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: sd.trace)
    (hhist : RunHistOk g.i s0 sd)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) sd
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x208 ∗
        vecU8 A (runFsp s0 + 0x208#64) pt ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (runFsp s0 + 0x230#64) 16) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  let fsp := runFsp s0
  have hjoin_loc :
      memRegion fsp 0x208 ∗
        vecU8 A (fsp + 0x208#64) pt ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ⊢
      runLocals fsp [(0x208, 24, vecU8 A (fsp + 0x208#64) pt)] := by
    have hp32 :
        ((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16 ⊢
        memRegion (fsp + 0x220#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x220#64) (n := 8) (k := 24)
            (b' := fsp + 0x228#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x228#64) (n := 8) (k := 16)
            (b' := fsp + 0x230#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
    have h220 :
        memRegion (fsp + 0x220#64) (runLocalBytes - 0x220) =
          memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) :=
      r3b_split_at fsp 0x220 32 runLocalBytes (by decide) (by decide)
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero]
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    rw [hz, show BitVec.ofNat 64 (0x208 + 24) = 0x220#64 from rfl, h220]
    exact Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hp32)))
  by_cases hcapP : peerG.name.cap = 0#64
  · have hpcd : sd.pc = runPcPlaced 0xde0 := hsd.pc
    change sd.pc = (blkPl_579).base + 0xde0#64 at hpcd
    have hrund : sd.status = .Running := hsd.run
    have hsp_ald : sd.spAligned = true := hsd.spAligned_cur
    apply r3b_seq (mid := runPcPlaced 0xf8c) hsd.inv
    rw [runPcPlaced_eq]
    rw [hcapP, ← hsd.sp]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrund])
    intro hinv'
    have hsj : InRunPlaced CodeOk s0 (r3b_stOf hinv') 0xf8c :=
      r3b_inRun_step hsd (by simp only [runPcPlaced_eq, arm64_norm])
        (by simp only [arm64_norm, hrund]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv' (by simp only [calleeSavedVRegs, arm64_norm])
    have htrj : (r3b_stOf hinv').trace = sd.trace := by simp only [arm64_norm]
    have hfsj : (r3b_stOf hinv').fs = sd.fs := by simp only [arm64_norm]
    have hat : AtJoinPlaced CodeOk g g' pt s0 (r3b_stOf hinv') :=
      { base := hsj
        x19 := by simp only [arm64_norm, hx19d]
        x20 := by simp only [arm64_norm, hx20d]
        trace := htrj ▸ htr
        hist := r3b_hist_of_eq htrj (congrArg FsState.files hfsj) hhist
        ans := hans
        wrOk := hwr }
    refine r3b_sepWPp_weaken_pre ?_ (hjoin (r3b_stOf hinv') g' pt hat)
    rw [hsd.sp, ← hcapP]
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (r3b_nameHeap_zero A peerG hcapP)
          (sepConj_mono hjoin_loc
            (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap))))
        (by rw [emp_sepConj]; dsimp only [joinMem, fsp]; ac_rfl))
      (by dsimp only [fsp]; ac_rfl)
  · have hbeqP : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcapP
    have hpcd : sd.pc = runPcPlaced 0xde0 := hsd.pc
    change sd.pc = (blkPl_579).base + 0xde0#64 at hpcd
    have hrund : sd.status = .Running := hsd.run
    have hspd : sd.sp = fsp := hsd.sp
    have hsp_ald : sd.spAligned = true := hsd.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A peerG hcapP))))))
    rw [show (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        runSaved s0 ∗ memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) =
      ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat ∗
          runSaved s0 ∗ memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) by ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlayP
    apply r3b_seq (mid := lsρ lsRustDeallocSym) hsd.inv
    rw [← hspd]
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrund])
    intro hinv_c
    have hstk_split := r3b_stackAt_split_ge sd.sp hext_le hsub64
    refine r3b_call_lscro
      (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
          (resStack - runFrame - extHookStack) ∗
        anyHeap)
      (s0 := s0) (peerG.name.ptr, peerG.name.cap.toNat, 1)
      (r3b_dealloc_ok hh) hinv_c
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrund])
      (by simpa only [State.spAligned, arm64_norm] using hsp_ald)
      (retAddr := runPcPlaced 0xf8c)
      (by simp only [runPcPlaced_eq, arm64_norm])
      ?_
      (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply Entails.pure_right
      · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], hlayP⟩
      rw [hspd] at hstk_split ⊢
      rw [hstk_split]
      simp only [arm64_norm, hspd]
      exact Entails.of_eq (by dsimp only [fsp]; simp only [arm64_norm]; ac_rfl)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply r3b_sepWPp_pure_left; intro hfs_m
      apply r3b_sepWPp_pure_left; intro htr_m
      have hs_m : InRunPlaced CodeOk s0 sm 0xf8c :=
        r3b_inRun_step hsd hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
      have htr_tot : sm.trace = sd.trace :=
        htr_m.trans (by simp only [arm64_norm])
      have hfs_tot : sm.fs = sd.fs :=
        hfs_m.trans (by simp only [arm64_norm])
      have hat : AtJoinPlaced CodeOk g g' pt s0 sm :=
        { base := hs_m
          x19 := hcsm.1.trans (by simp only [arm64_norm, hx19d])
          x20 := hcsm.2.1.trans (by simp only [arm64_norm, hx20d])
          trace := htr_tot ▸ htr
          hist := r3b_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist
          ans := hans
          wrOk := hwr }
      refine r3b_sepWPp_weaken_pre ?_ (hjoin sm g' pt hat)
      rw [hspd] at hstk_split
      dsimp only [joinMem, fsp] at hjoin_loc hstk_split ⊢
      rw [hstk_split]
      simp only [arm64_norm, hspd]
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono hjoin_loc
            (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗
              memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
                (resStack - runFrame - extHookStack) ∗
              stackAt (runFsp s0) extHookStack ∗ A.pool ∗ anyHeap)))
          (by simp only [arm64_norm]; ac_rfl))
        (by simp only [arm64_norm]; ac_rfl)

end CryptoVerification.SignalSession.Cli.RunCompose
