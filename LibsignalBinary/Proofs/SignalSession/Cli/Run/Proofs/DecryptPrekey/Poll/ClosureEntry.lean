/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtables
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Poll Entry Unpacking and Stage P1/P3/P4 Frame Helpers

Unpacks `dpPollSpecState.inImage.pre` into pure invariants (`DpPollEntryPure` /
`DpPollEntryPureExt`) and spatial preconditions (`dpPollEntrySpatial` / `dpPollEntrySpatialExt`),
together with 3280-byte stack-splitting helpers and the `Ext`-generalized untrusted branch
`closure_untrusted_x_ext_ok`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- Canonical spatial precondition unpacked from `dpPollSpecState.inImage` at `K₀_state`, with
`dpCxAt y.cx` already weakened to `memRegion y.cx 32`. -/
def dpPollEntrySpatial {B : RunBudgets} {S : RunSem} (img : Obj.Image) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 : State) (R : SepProp) : SepProp :=
  memRegion y.out 48 ∗
  dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
  memRegion y.cx 32 ∗
  storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
  protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
  protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
  coinsInstalled img y.g.coinsP y.g.coins ∗
  TokenInit img ∗
  logOff img ∗
  E2E.HooksE.A0.pool ∗
  preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
  stackAt s0.sp stk' ∗
  R

/-- Pure invariants unpacked from `dpPollSpecState.inImage` at `K₀_state`. -/
structure DpPollEntryPure {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 : State) : Prop where
  inv : ImgCallInv img s0
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val
  decPkOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg

/-- Unpack `((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).pre`
into `DpPollEntryPure` and `dpPollEntrySpatial`. -/
theorem dpPollPre_unpack
    {img : Obj.Image} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).pre y s0 ∗ R) :
    DpPollEntryPure (X := X) (W := W) (Scope := Scope) img stk' y s0 ∧
      (s0.mem ⊨ dpPollEntrySpatial img stk' y s0 R) := by
  have h1 : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = y.out ∧ s0.readReg64 .x1 = y.fut ∧ s0.readReg64 .x2 = y.cx ∧
        (dpSlotArgs img y.g).length = 13 ∧ stk' ≤ s0.sp.toNat⌝ ∗
      (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
        dpCxAt y.cx ∗
        (⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
            S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg⌝ ∗
          (⌜y.g.coins.length < 2 ^ 63⌝ ∗
            (storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
              protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
              protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
              coinsInstalled img y.g.coinsP y.g.coins ∗
              TokenInit img ∗
              logOff img ∗
              E2E.HooksE.A0.pool ∗
              preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗
              R))))) := by
    simpa only [Spec.inImage, dpPollSpecState, dpSlotPollKState, slotFrame, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨hinv, h2⟩
  rw [satisfies_pure_sepConj] at h2
  rcases h2 with ⟨⟨hx0, hx1, hx2, _, hstk_sp⟩, h3⟩
  have h3' : s0.mem ⊨
      ⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
          S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg⌝ ∗
        (⌜y.g.coins.length < 2 ^ 63⌝ ∗
          (dpCxAt y.cx ∗
            (memRegion y.out 48 ∗
              dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
              storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
              protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
              protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
              coinsInstalled img y.g.coinsP y.g.coins ∗
              TokenInit img ∗
              logOff img ∗
              E2E.HooksE.A0.pool ∗
              preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗
              R))) := by
    convert h3 using 1
    ac_rfl
  rw [satisfies_pure_sepConj] at h3'
  rcases h3' with ⟨⟨hfiles, hfOk, hdOk⟩, h4⟩
  rw [satisfies_pure_sepConj] at h4
  rcases h4 with ⟨hcoins_lt, h5⟩
  obtain ⟨hfPeer, hdecOk⟩ := hSemOk y.g.F y.g.peer.val y.g.me.val y.g.msg hfOk hdOk
  have h5_cx := Satisfies.mono (sepConj_mono_left (dpCxAt_entails_memRegion32 y.cx)) h5
  refine ⟨⟨hinv, hx0, hx1, hx2, hstk_sp, hfiles, hcoins_lt, hfPeer, hdecOk⟩, ?_⟩
  dsimp only [dpPollEntrySpatial]
  convert h5_cx using 1
  ac_rfl

/-- Allocator-polymorphic spatial precondition unpacked from `dpPollSpecState.inImage` at
`dpSlotPollKState A img B S`, with `dpCxAt y.cx` already weakened to `memRegion y.cx 32`. -/
def dpPollEntrySpatialExt (A : RustAlloc) {B : RunBudgets} {S : RunSem} (img : Obj.Image)
    (stk' : Nat) (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 : State) (R : SepProp) : SepProp :=
  memRegion y.out 48 ∗
  dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
  memRegion y.cx 32 ∗
  storesAt A y.g.stores StoresGhost.opened ∗
  protocolAddressAt A y.g.peer y.g.peerA ∗
  protocolAddressAt A y.g.me y.g.meA ∗
  coinsInstalled img y.g.coinsP y.g.coins ∗
  TokenInit img ∗
  logOff img ∗
  A.pool ∗
  preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
  stackAt s0.sp stk' ∗
  R

/-- Parameter- and allocator-polymorphic pure invariants unpacked from `dpPollSpecState.inImage` at
`dpSlotPollKState A img B S`. -/
structure DpPollEntryPureExt (P : PEParams) (A : RustAlloc)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 : State) : Prop where
  inv : ImgCallInv img s0
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val
  decPkOk : DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg

/-- Unpack `((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).pre`
into `DpPollEntryPureExt P A` and `dpPollEntrySpatialExt A`. -/
theorem dpPollPre_unpack_ext
    {img : Obj.Image} {P : PEParams} {A : RustAlloc} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ P Scope F peer me pm)
    (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).pre y s0 ∗ R) :
    DpPollEntryPureExt P A (Scope := Scope) img stk' y s0 ∧
      (s0.mem ⊨ dpPollEntrySpatialExt A img stk' y s0 R) := by
  have h1 : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = y.out ∧ s0.readReg64 .x1 = y.fut ∧ s0.readReg64 .x2 = y.cx ∧
        (dpSlotArgs img y.g).length = 13 ∧ stk' ≤ s0.sp.toNat⌝ ∗
      (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
        dpCxAt y.cx ∗
        (⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
            S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg⌝ ∗
          (⌜y.g.coins.length < 2 ^ 63⌝ ∗
            (storesAt A y.g.stores StoresGhost.opened ∗
              protocolAddressAt A y.g.peer y.g.peerA ∗
              protocolAddressAt A y.g.me y.g.meA ∗
              coinsInstalled img y.g.coinsP y.g.coins ∗
              TokenInit img ∗
              logOff img ∗
              A.pool ∗
              preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗
              R))))) := by
    simpa only [Spec.inImage, dpPollSpecState, dpSlotPollKState, slotFrame, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨hinv, h2⟩
  rw [satisfies_pure_sepConj] at h2
  rcases h2 with ⟨⟨hx0, hx1, hx2, _, hstk_sp⟩, h3⟩
  have h3' : s0.mem ⊨
      ⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
          S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg⌝ ∗
        (⌜y.g.coins.length < 2 ^ 63⌝ ∗
          (dpCxAt y.cx ∗
            (memRegion y.out 48 ∗
              dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
              storesAt A y.g.stores StoresGhost.opened ∗
              protocolAddressAt A y.g.peer y.g.peerA ∗
              protocolAddressAt A y.g.me y.g.meA ∗
              coinsInstalled img y.g.coinsP y.g.coins ∗
              TokenInit img ∗
              logOff img ∗
              A.pool ∗
              preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗
              R))) := by
    convert h3 using 1
    ac_rfl
  rw [satisfies_pure_sepConj] at h3'
  rcases h3' with ⟨⟨hfiles, hfOk, hdOk⟩, h4⟩
  rw [satisfies_pure_sepConj] at h4
  rcases h4 with ⟨hcoins_lt, h5⟩
  obtain ⟨hfPeer, hdecOk⟩ := hSemOk y.g.F y.g.peer.val y.g.me.val y.g.msg hfOk hdOk
  have h5_cx := Satisfies.mono (sepConj_mono_left (dpCxAt_entails_memRegion32 y.cx)) h5
  refine ⟨⟨hinv, hx0, hx1, hx2, hstk_sp, hfiles, hcoins_lt, hfPeer, hdecOk⟩, ?_⟩
  dsimp only [dpPollEntrySpatialExt]
  convert h5_cx using 1
  ac_rfl

/-- Untouched stack sub-regions of `memRegion sp 3280` for `StageP1OkExtStmt`. -/
def closStackUnusedP1OkAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x8#64) 144 ∗
  memRegion (sp + 0x234#64) 428 ∗
  memRegion (sp + 0x550#64) 1824

/-- Split `memRegion (sp0 - 0xcd0#64) 3280` into the exact stack slots consumed by
`StageP1OkExtStmt` plus `closStackUnusedP1OkAt`. -/
theorem clos_stack_3280_split_for_p1_ok (sp0 : BitVec 64) :
    let sp := sp0 - 0xcd0#64
    memRegion sp 3280 =
      (∃∗ u_98 : BitVec 64, ∃∗ u_a0 : BitVec 64,
       ∃∗ u_a8 : BitVec 64, ∃∗ u_b0 : BitVec 64, ∃∗ u_b8 : BitVec 64,
       ∃∗ u_c0 : BitVec 64, ∃∗ u_c8 : BitVec 64, ∃∗ u_d0 : BitVec 64,
       ∃∗ v_sp0 : BitVec 64,
        (sp ↦₆₄ v_sp0) ∗
        ((sp + 0x98#64) ↦₆₄ u_98) ∗
        ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
        ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
        ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
        ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
        ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
        ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
        ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
        memRegion (sp + 0xd8#64) 348 ∗
        memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp0 - 0x60#64) 12 ∗
        closStackUnusedP1OkAt sp) := by
  dsimp only
  let sp := sp0 - 0xcd0#64
  change memRegion sp 3280 = _
  rw [memRegion_split sp 8 3272 (by decide),
      memRegion_split (sp + 8#64) 144 3128 (by decide),
      memRegion_split (sp + 8#64 + 144#64) 64 3064 (by decide),
      memRegion_split (sp + 8#64 + 144#64 + 64#64) 348 2716 (by decide),
      memRegion_split (sp + 8#64 + 144#64 + 64#64 + 348#64) 428 2288 (by decide),
      memRegion_split (sp + 8#64 + 144#64 + 64#64 + 348#64 + 428#64) 368 1920 (by decide),
      memRegion_split (sp + 8#64 + 144#64 + 64#64 + 348#64 + 428#64 + 368#64) 1824 96 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h_c70 : sp + 0xc70#64 = sp0 - 0x60#64 := by dsimp only [sp]; bv_omega
  have h1 : memRegion sp 8 = (∃∗ v_sp0 : BitVec 64, sp ↦₆₄ v_sp0) := by
    rw [ProofLib.memRegion_cells sp 1 (by decide)]
    simp only [cells, sepConj_emp]
  have h8 : memRegion (sp + 0x98#64) 64 =
      (∃∗ u_98 : BitVec 64, ∃∗ u_a0 : BitVec 64,
       ∃∗ u_a8 : BitVec 64, ∃∗ u_b0 : BitVec 64, ∃∗ u_b8 : BitVec 64,
       ∃∗ u_c0 : BitVec 64, ∃∗ u_c8 : BitVec 64, ∃∗ u_d0 : BitVec 64,
        ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
        ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
        ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
        ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0)) := by
    rw [ProofLib.memRegion_cells (sp + 0x98#64) 8 (by decide)]
    simp only [cells_succ, cells_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_right]
  rw [h_c70, h1, h8,
      ProofLib.memRegion_cells (sp0 - 0x60#64) 12 (by decide)]
  unfold closStackUnusedP1OkAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun u_98 => ?_)
  refine congrArg sepExists (funext fun u_a0 => ?_)
  refine congrArg sepExists (funext fun u_a8 => ?_)
  refine congrArg sepExists (funext fun u_b0 => ?_)
  refine congrArg sepExists (funext fun u_b8 => ?_)
  refine congrArg sepExists (funext fun u_c0 => ?_)
  refine congrArg sepExists (funext fun u_c8 => ?_)
  refine congrArg sepExists (funext fun u_d0 => ?_)
  refine congrArg sepExists (funext fun v_sp0 => ?_)
  dsimp only [sp]
  ac_rfl

/-- From `dpPollNeed B ≤ stk'` and `stk' ≤ s0.sp.toNat`, `(s0.sp - 0xcd0#64).toNat ≥ rootStack`
and `(s0.sp - 0xcd0#64).toNat ≥ dpClosSubStack B`. -/
theorem subStack_le_sp_of_dpPollNeed {B : RunBudgets} {stk' : Nat} {s0 : State}
    (hneed : dpPollNeed B ≤ stk') (hstk_sp : stk' ≤ s0.sp.toNat) :
    dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat ∧
      rootStack ≤ (s0.sp - 0xcd0#64).toNat := by
  have heq := dpPollNeed_eq_frame_add_subStack B
  have hroot := rootStack_le_subStack B
  have hsp_ge : 3280 ≤ s0.sp.toNat := by omega
  have hsub_toNat : (s0.sp - 0xcd0#64).toNat = s0.sp.toNat - 3280 := by
    have hlt := s0.sp.isLt
    bv_omega
  rw [hsub_toNat]
  omega

/-- Any `coroOpkIdAtP4 coroPtr opkId?` weakens to `memRegion (coroPtr + 0x298#64) 8` for exit
coroutine folding into `dpFutDoneAt`. -/
private theorem coroOpkIdAtP4_entails_memRegion8_entry (coroPtr : BitVec 64) (opkId? : Option (BitVec 32)) :
    coroOpkIdAtP4 coroPtr opkId? ⊢ memRegion (coroPtr + 0x298#64) 8 := by
  have hpair : ∀ lo hi : BitVec 32,
      ((coroPtr + 0x298#64) ↦₃₂ lo) ∗ ((coroPtr + 0x29c#64) ↦₃₂ hi) ⊢
        memRegion (coroPtr + 0x298#64) 8 := by
    intro lo hi
    rw [← coro298_split_eq coroPtr lo hi]
    exact ProofLib.pointsTo64_entails_memRegion _ _
  cases opkId? with
  | none =>
    dsimp only [coroOpkIdAtP4]
    exact Entails.sepExists_elim fun hi => hpair 0#32 hi
  | some opkId =>
    exact hpair 1#32 opkId

theorem coinsInstalled_to_coinsAt (img : Obj.Image) (p : BitVec 64) (coins : List (BitVec 8))
    (hlen : coins.length < 2 ^ 63) :
    coinsInstalled img p coins ⊢ Coins.coinsAt img.base p coins :=
  CryptoVerification.SignalSession.Cli.Slots.coinsInstalled_entails_coinsAt img p coins hlen

/-! ## `Ext`-Generalized Stage P1 Kit Obligations & Untrusted Branch (`closure_untrusted_x_ext_ok`) -/

/-- `SessionOnlyKitOkSE` obligation on `cliExternsWith ext` for `cliPollSessKit` at `Slots.scopeKit`. -/
def PollSessKitOkExtStmt : Prop :=
  ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (B : RunBudgets),
    CliExternsOk P A ext →
    Obj.Loads libsignalSessionImage img →
    RunHooksExt img A (cliExternsWith ext) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit A img) →
    ∀ (F0 : FsFiles) (peer : AddrGhost),
      MessageDecrypt.SessionOnlyKitOkSE
        (cliPollSessKit A img.base F0 Slots.scopeKit peer (cliKitStk B))
        Slots.scopeKit E2E.Record.encodeRecord (cliExternsWith ext)

/-- `IdentityStoreKitOkIE` obligation on `cliExternsWith ext` for `cliPollIdKit`. -/
def PollIdKitOkExtStmt : Prop :=
  ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (B : RunBudgets),
    CliExternsOk P A ext →
    Obj.Loads libsignalSessionImage img →
    RunHooksExt img A (cliExternsWith ext) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile) →
    ∀ (F0 : FsFiles) (peer : AddrGhost),
      StoreKit.Identity.IdentityStoreKitOkIE img
        (cliPollIdKit A img.base F0 peer (cliKitStk B))
        (cliExternsWith ext)

/-- `FsAt` on `tripleRatchetProgAtExt img.base ext` for Stage P1 (`cliPollSessKit` + `cliPollIdKit`)
from `TraceFsSound`. -/
theorem cliPollStageP1_fsAt_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hfs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (B : RunBudgets) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (fun F => (cliPollSessKit A img.base F0 Scope peer (cliKitStk B)).envOk F ∧
                (cliPollIdKit A img.base F0 peer (cliKitStk B)).envOk F)
      ((cliPollSessKit A img.base F0 Scope peer (cliKitStk B)).Quiet ∧
       (cliPollIdKit A img.base F0 peer (cliKitStk B)).Quiet)
      (tripleRatchetProgAtExt img.base ext) s :=
  .inr ⟨⟨cliPollSess_quiet img.base F0 Scope peer (cliKitStk B),
         cliPollId_quiet F0 peer (cliKitStk B)⟩, hfs, ⟨hf, hf⟩⟩

set_option maxHeartbeats 800000 in
/-- Untrusted-identity branch (`trusted =.ok false`) of `subroutine_ok_of_sepWPp_steps` for
`cliDpPollName` on `tripleRatchetProgAtExt img.base (cliExternsWith ext)` using
`StageP1UntrustedXExtStmt`. -/
theorem closure_untrusted_x_ext_ok
    (hUntrusted : StageP1UntrustedXExtStmt)
    (hSessKit : PollSessKitOkExtStmt)
    (hIdKit : PollIdKitOkExtStmt)
    {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit A img))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr cliDpPollName)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hinv0 : ImgCallInv img s0)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A y.g.stores StoresGhost.opened ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗
      TokenInit img ∗
      logOff img ∗
      A.pool ∗
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := tripleRatchetProgAtExt img.base (cliExternsWith ext)
    let K := dpSlotPollKState A img B S
    ∃ P0 Fr : SepProp, (s0.mem ⊨ P0 ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P0
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).onPanic y s0 sf ∗ R)) := by
  dsimp only
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
  let pkKit := cliPollPkKit A img.base y.g.F pid σ
  let spkKit := cliPollSpkKit A img.base y.g.F sid σ
  let kpkKit := cliPollKpkKit A img.base y.g.F kid sid kbk σ
  let sp := s0.sp - 0xcd0#64
  have hm_vt :=
    satisfies_stageP1VtablesAt
      (cliPollSess_vtablesOk (A := A) himg y.g.F Slots.scopeKit y.g.peer σ)
      (cliPollId_vtablesOk (A := A) himg y.g.F y.g.peer σ)
      hinv0.1 hm_base
  have hent_stores := storesAt_entails_cliPollStoresKitsAt (A := A) img.base σ
    y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hfPeer)
    (cliIdOwnInv_opened hdecOk)
    (cliIdInv_opened_peer hfPeer)
    (cliPkInv_opened hdecOk pid)
    (cliSpkInv_opened hdecOk sid)
    (cliKpkInvFull_opened hdecOk kid sid kbk)
  have hm_stores : s0.mem ⊨ stageP1VtablesAt img kit ikit ∗
      (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAt A img.base y.g.F Slots.scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A y.g.peer y.g.peerA ∗
        protocolAddressAt A y.g.me y.g.meA ∗
        coinsInstalled img y.g.coinsP y.g.coins ∗
        TokenInit img ∗
        logOff img ∗
        A.pool ∗
        preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R) :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hent_stores))))) hm_vt
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1UntrustedCallStack_le_subStack (A := A)
    img.base y.g.F Slots.scopeKit y.g.peer B
  have hp1_64 : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1 img y.g y.fut,
      preKeyMsgAt_eq_idKey_sep A y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_untrusted s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  dsimp only [cliPollStoresKitsAt, stageP1VtablesAt] at hm_flat
  rw [sessVt_eq_cliPollSessKit A img y.g.F Slots.scopeKit y.g.peer σ,
      idVt_eq_cliPollIdKit A img y.g.F y.g.peer σ,
      oneTimeVt_eq_cliPollPkKit A img y.g.F pid σ,
      signedVt_eq_cliPollSpkKit A img y.g.F sid σ,
      kyberVt_eq_cliPollKpkKit A img y.g.F kid sid kbk σ] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗ cells (y.fut + 0xe0#64) 4 ∗
    memRegion (y.fut + 0x100#64) 336 ∗ cells (y.fut + 0x250#64) 6 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗ ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
    ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗ (sp ↦₆₄ v_sp0) ∗
    ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x370#64) 36 ∗
    memRegion (sp + 0x3e0#64) 368 ∗ cells (sp + 0xa90#64) 6 ∗
    cells (s0.sp - 0x60#64) 12 ∗ memRegion y.out 48 ∗
    ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
    ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
    ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
    ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
    ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
    ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
    ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
    ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
    logOff img ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt A y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    A.pool ∗ stackAt sp (stageP1UntrustedCallStack kit ikit)
  let Fr_inner : SepProp :=
    cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗
    ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ coroUnusedP1At y.fut ∗
    closStackUnusedUntrustedAt sp ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt A y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalled img y.g.coinsP y.g.coins ∗ TokenInit img
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := hUntrusted
    y.g.peer y.g.msg.identityKey hh.alloc hh.allocHooks
    (hSessKit P A ext B hOk himg hh hRead hDeser y.g.F y.g.peer)
    (hIdKit P A ext B hOk himg hh hRead y.g.F y.g.peer)
    hp1_64
    (by
      have hext : extHookStack = 16384 := rfl
      have hdeser : 32768 ≤ E2E.Record.recDeserializeStack := by decide
      dsimp [kit, σ, loadCallStack, cliPollSessKit, cliSessionStoreSpec, cliKitStk,
            SessKit.loadPollNeed]
      omega)
    rfl rfl
    (fun _ (h : kit.loadRel StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : ikit.trustRel StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    (cliBase_aligned himg) hinv0
    (cliPollStageP1_fsAt_ext hh.fs y.g.F Slots.scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  refine SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨⟨opt, hload, _, htr_evs, hent_f⟩, hspf, hcs, hvregs, _hFf, _⟩
    refine ⟨?_, hspf, calleeSavedPreserved_of_closure hcs hvregs⟩
    intro hsteps hmf
    have htr_eq : sf.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKit, cliPollIdKit, cliSessionStoreSpec,
        cliIdStoreSpecFull, cliIdentityStoreSpec] using htr_evs
    have hloadRec : Slots.loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSess_loadRel hinjK hsub hfPeer hload
    have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none := by
      rw [hS]
      exact decPkDef_of_trust_err X P Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadRec (Or.inr htrusted)
    have hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) s0.trace sf.trace :=
      slotOutTr_of_err StoresGhost.opened s0.trace sf.trace nofun nofun hans
    have hmf1 := Satisfies.mono (sepConj_mono_left hent_f) hmf
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hmf1
    rcases hmf1 with ⟨v_a8, v_b8, v_d0, hmf2⟩
    have hcoro := coro_of_p1_untrusted_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins b_4f2
    have hstk3280 := clos_stack_3280_of_p1_untrusted s0.sp s0
      0#64 v_a8 (y.fut + 0x390#64) v_b8 y.cx y.out v_d0
    have hres := apiDecResultAt_untrusted_entails_decResAt A y.out y.g.peer.val
    have hstores_back := cliPollStoresKitsAt_entails_storesAt (A := A)
      img.base (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    let Leftover : SepProp :=
      stageP1VtablesAt img kit ikit ∗ coinsInstalled img y.g.coinsP y.g.coins ∗ TokenInit img
    have hmf_reord : sf.mem ⊨
        (apiDecResultAt A y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          cliPollStoresKitsAt A img.base y.g.F Slots.scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
          protocolAddressAt A y.g.peer y.g.peerA ∗
          protocolAddressAt A y.g.me y.g.meA ∗
          (((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRemIdKeyAt A y.g.msgG y.g.msgA y.g.msg) ∗
          logOff img ∗ A.pool ∗ Leftover ∗
          (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            memRegion (y.fut + 0xe0#64) 368 ∗ cells (y.fut + 0x250#64) 6 ∗
            ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
              (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
            ((y.fut + 0x390#64) ↦₈ 1#8) ∗ cells (y.fut + 0x398#64) 2 ∗
            cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗
            ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ coroUnusedP1At y.fut) ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
                (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit)) ∗
            ((sp ↦₆₄ 0#64) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗ memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              closStackUnusedUntrustedAt sp))) ∗ R := by
      have htrust_id : ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val
          y.g.msg.identityKey .receiving (.ok false) = StoresGhost.opened.identity := rfl
      rw [htrust_id] at hmf2
      dsimp only [Fr_inner] at hmf2
      refine Satisfies.mono ?_ hmf2
      dsimp only [Leftover, stageP1VtablesAt, cliPollStoresKitsAt]
      sep_frame
    rw [← preKeyMsgAt_eq_idKey_sep A y.g.msgG y.g.msgA y.g.msg,
        ← stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
        show sp + 0xcd0#64 = s0.sp from sp_frame_sub_add s0.sp] at hmf_reord
    have hmf_folded : sf.mem ⊨
        (decResAt A y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          storesAt A y.g.stores StoresGhost.opened ∗
          protocolAddressAt A y.g.peer y.g.peerA ∗
          protocolAddressAt A y.g.me y.g.meA ∗
          preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
          logOff img ∗ A.pool ∗ Leftover ∗
          dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            stackAt sp (dpClosSubStack B) ∗ memRegion sp 3280)) ∗ R :=
      Satisfies.mono (sepConj_mono_left
        (sepConj_mono hres
          (sepConj_mono hstores_back
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono hcoro
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk3280)))))))))))))
        hmf_reord
    dsimp only [sp] at hmf_folded
    rw [← stackAt_poll_entry_split s0.sp B stk' hneed hstk63] at hmf_folded
    have hpost := dpPollPost_of_decResAt_ext B S stk' y s0 sf StoresGhost.opened
      (.error (.untrustedIdentity y.g.peer.val)) Leftover hh.fs hsteps htr_eq hout
    exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · intro sf P_f hoom _hsteps hmf
    rw [← sepConj_assoc] at hmf
    exact dpPollOnPanic_of_closOom stk' y hoom hmf

end CryptoVerification.SignalSession.Cli.RunProofs.Poll

