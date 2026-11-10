/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCut
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2b
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhDefs
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHChain
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptDecode
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCallees
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Mac.Compute
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop

/-!
# CLI `initialize_bob_session` at SPQR V1

Verifies `initialize_bob_session` (`0x21c80`, 608 B; frame `fsp = sp0 - 768`) on the SPQR V1
accepting path (`Model.acceptKeys P inp = some drKey`):
- `initBob_to_spqr_full_v1`: entry to `bl spqr::initial_state` (`+248`), preserving the full stack
  frame (`bobFrameAtSpqr`) and saved registers (`initBobSavedRegs`) alongside `bobSpqrCutCells`;
- `initBob_session_build_v1`: `spqr::initial_state` return (`+252`) to `+564`, checking the `Ok`
  tag (`0`), serializing keys, invoking `with_sender_chain`, and packing the 344-byte V1
  `SessionState` (`bobSession344Bv8V1`) with dynamic SPQR `Vec<u8>` header `(cap, ptr, len)` at `+0x78`;
- `initBob_epilogue_v1` and `initializeBobSession_ok_v1`: epilogue (`+564 → RET`) and end-to-end
  composition at caller stack budget `stageP2bStack + 0x700`.
-/

@[expose] public section

namespace CryptoVerification.E2E.V1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure (stageP2bStack)
open CryptoVerification.SpqrV1.Top.InitialState
  (initialStateStack initialStateStackExt initialStateValue paramsAt InitialStateOkX InitialStateOkXExt)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x21c80

@[local arm64_norm ↓, local wp_norm ↓]
private theorem _root_.CryptoVerification.Cli.E2E.V1.calleeSavedVRegs_setPC_pre_bob (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem _root_.CryptoVerification.Cli.E2E.V1.calleeSavedVRegs_setMem_setPC_pre_bob (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem _root_.CryptoVerification.Cli.E2E.V1.calleeSavedVRegs_writeVReg128_0_bob (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl

/-- Fetches of `initialize_bob_session` (`0x21c80`) from `+k0`, `len` bytes. -/
macro "bob_v1_fetches " b:term:max H:term:max hfn:ident k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.initializeBobSession $b $H $hfn 0x21c80 $k0 $len)

/-! ## Definitions -/

/-- The `Params` Bob passes to `spqr::initial_state`: `B2A`, `V1`, `V1`, `auth_key = pqr_key`,
`ChainParams::default` (25000, 2000). -/
def _root_.CryptoVerification.Cli.E2E.V1.bobSpqrParams (pqrKey : SignalPqxdh.Bytes) : CryptoVerification.LibsignalSpqrV1.Params :=
  { direction := .b2a, version := .v1, minVersion := .v1, authKey := bytesToBv8 pqrKey }

/-- Heap buffer part of a `Vec<u8>` with capacity `cap` at `ptr` holding `bs` (`vecU8At` without
its 24-byte header). -/
def _root_.CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem _root_.CryptoVerification.Cli.E2E.V1.vecU8At_eq_header_bobBuf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A cap ptr bs := rfl

/-- First 144 bytes of Bob's `SessionState` with dynamic SPQR `Vec<u8>` length `spqrLen` at `+0x88`. -/
def _root_.CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen : BitVec 64) : List (BitVec 8) :=
  unpack64 33#64 ++ unpack64 localIkBoxPtr ++ unpack64 33#64 ++
  unpack64 33#64 ++ unpack64 remoteIkBoxPtr ++ unpack64 33#64 ++
  unpack64 32#64 ++ unpack64 rootKeyBoxPtr ++ unpack64 32#64 ++
  unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++
  unpack64 33#64 ++ unpack64 baseKeyBoxPtr ++ unpack64 33#64 ++
  unpack64 spqrCap ++ unpack64 spqrBufPtr ++ unpack64 spqrLen

@[local simp]
theorem _root_.CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1_length (p1 p2 p3 p4 c5 p5 l5 : BitVec 64) :
    (CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 p1 p2 p3 p4 c5 p5 l5).length = 144 := by
  simp [CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1]

theorem _root_.CryptoVerification.Cli.E2E.V1.bobHead144Bv8_eq_V1 (p1 p2 p3 p4 c5 p5 : BitVec 64) :
    bobHead144Bv8 p1 p2 p3 p4 c5 p5 = CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 p1 p2 p3 p4 c5 p5 0#64 := rfl

theorem _root_.CryptoVerification.Cli.E2E.V1.bobHead144V1_eq_pointsToBytes (ptr : BitVec 64)
    (p1 p2 p3 p4 c5 p5 l5 : BitVec 64) :
    (ptr ↦₆₄ 33#64) ∗
    ((ptr + 0x08#64) ↦₆₄ p1) ∗
    ((ptr + 0x10#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x18#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x20#64) ↦₆₄ p2) ∗
    ((ptr + 0x28#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x30#64) ↦₆₄ 32#64) ∗
    ((ptr + 0x38#64) ↦₆₄ p3) ∗
    ((ptr + 0x40#64) ↦₆₄ 32#64) ∗
    ((ptr + 0x48#64) ↦₆₄ 0#64) ∗
    ((ptr + 0x50#64) ↦₆₄ 8#64) ∗
    ((ptr + 0x58#64) ↦₆₄ 0#64) ∗
    ((ptr + 0x60#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x68#64) ↦₆₄ p4) ∗
    ((ptr + 0x70#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x78#64) ↦₆₄ c5) ∗
    ((ptr + 0x80#64) ↦₆₄ p5) ∗
    ((ptr + 0x88#64) ↦₆₄ l5) =
      (ptr ↦ₛ CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 p1 p2 p3 p4 c5 p5 l5) := by
  unfold CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes]

/-- The 344-byte `SessionState` Bob builds, with the V1 pq vec header `(spqrCap, spqrBufPtr,
spqrLen)` at `+0x78`. -/
def _root_.CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) : List (BitVec 8) :=
  CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    spqrLen ++
  senderChainBytes100 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ++ unpack32 pad_f4 ++
  bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2

@[local simp]
theorem _root_.CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1_length (p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2).length =
      344 := by
  simp [CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1]

theorem _root_.CryptoVerification.Cli.E2E.V1.bobSession344Bv8_eq_V1 (p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    bobSession344Bv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 =
      CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 p1 p2 p3 p4 c5 p5 0#64 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 := rfl

theorem _root_.CryptoVerification.Cli.E2E.V1.bobSession344V1_pack (ptr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (ptr ↦ₛ CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap
      spqrBufPtr spqrLen) ∗
    senderChainFieldsAt ptr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ∗
    ((ptr + 0xf4#64) ↦ₛ (unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2)) =
      (ptr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap
        spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) := by
  unfold CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1
  rw [senderChainFieldsAt_eq_pointsToBytes]
  simp only [List.append_assoc, pointsToBytes_append, CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1_length,
    senderChainBytes100_length, BitVec.add_assoc, BitVec.reduceAdd]

/-- The twelve callee-saved words `initialize_bob_session`'s prologue stores at `sp0 - 96`
(`stp x29, x30, [sp, #-0x60]!` … `stp x20, x19, [sp, #0x50]`). -/
def _root_.CryptoVerification.Cli.E2E.V1.initBobSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((sp0 - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗ ((sp0 - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

theorem _root_.CryptoVerification.Cli.E2E.V1.initBobSavedRegs_entails_memRegion96 (sp0 : BitVec 64) (s0 : State) :
    CryptoVerification.Cli.E2E.V1.initBobSavedRegs sp0 s0 ⊢ memRegion (sp0 - 96#64) 96 := by
  rw [(ProofLib.memRegion_cells (sp0 - 96#64) 12 (by decide) :
    memRegion (sp0 - 96#64) 96 = cells (sp0 - 96#64) 12)]
  exact cells12_sub96_merge sp0 _ _ _ _ _ _ _ _ _ _ _ _

/-- The cells of `initialize_bob_session`'s frame at `spqr::initial_state`'s entry other than
`bobSpqrCutCells`, the saved registers and the stack below `sp0 - 768`. `sp0 - 768 .. sp0 - 672`
is the cut's leftover copy of the handshake keys (`sp + 0` is the callee's sret);
`sp0 - 452 .. sp0 - 384` is the rest of `pqxdhAccept`'s result after the `Params`. -/
def _root_.CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr (sp0 : BitVec 64) (rk pq ck : SignalPqxdh.Bytes) : SepProp :=
  ((sp0 - 768#64) ↦ₛ bytesToBv8 rk) ∗ ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ∗
  ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ∗ ((sp0 - 672#64) ↦₃₂ 0#32) ∗
  memRegion (sp0 - 668#64) 12 ∗ ((sp0 - 592#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 588#64) 12 ∗
  memRegion (sp0 - 544#64) 56 ∗
  ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
  ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288

/-! ## Stack and parameter bridges -/

private theorem _root_.CryptoVerification.Cli.E2E.V1.bv_add_sub_lit_bob (x a b : BitVec 64) : (x + a) - b = x + (a - b) := by bv_omega

private theorem _root_.CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega, memRegion_split' (n := d) (k := n) (by omega) rfl (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

private theorem _root_.CryptoVerification.Cli.E2E.V1.split64_hi_lo (p : BitVec 64) (lo hi : BitVec 32) (w : BitVec 64)
    (hw : unpack64 w = unpack32 lo ++ unpack32 hi) :
    (p ↦₆₄ w) = (p ↦₃₂ lo) ∗ ((p + 4#64) ↦₃₂ hi) := by
  rw [pointsTo64_eq_pointsToBytes, hw, pointsToBytes_append, unpack32_length,
    ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]

/-- Rewrites `bobSpqrCutCells` into `paramsAt (sp0 - 488) (sp0 - 576) (bobSpqrParams pq)` plus the
32-byte `auth_key` slice at `sp0 - 576`. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.bobSpqrCutCells_eq_paramsAt (sp0 rkp : BitVec 64) (rk pq ck spkPk spkSk : SignalPqxdh.Bytes)
    (hpq : pq.length = 32) :
    bobSpqrCutCells sp0 rkp rk pq ck spkPk spkSk =
      paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
      ((sp0 - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq).authKey) ∗
      ((sp0 - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((sp0 - 624#64) ↦ₛ bytesToBv8 ck) ∗
      (rkp ↦ₛ bytesToBv8 spkPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkSk) := by
  have hlen : (bytesToBv8 pq).length = 32 := by simp [bytesToBv8, hpq]
  have h468 := CryptoVerification.Cli.E2E.V1.split64_hi_lo (sp0 - 468#64) 2000#32 1#32 0x1000007d0#64 (by decide)
  have h460 := CryptoVerification.Cli.E2E.V1.split64_hi_lo (sp0 - 460#64) 1#32 1#32 0x100000001#64 (by decide)
  simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h468 h460
  unfold bobSpqrCutCells paramsAt CryptoVerification.Cli.E2E.V1.bobSpqrParams
  rw [h468, h460]
  simp only [hlen, Initiator.bv_sub_add_lit', BitVec.reduceSub]
  have hdir : (CryptoVerification.LibsignalSpqrV1.Direction.b2a).toI32 = 1#32 := rfl
  have hver : (CryptoVerification.LibsignalSpqrV1.Version.v1).toI32 = 1#32 := rfl
  have hmj : (CryptoVerification.LibsignalSpqrV1.ChainParams.default).maxJump = 25000#32 := rfl
  have hmo : (CryptoVerification.LibsignalSpqrV1.ChainParams.default).maxOooKeys = 2000#32 := rfl
  simp only [hdir, hver, hmj, hmo]
  ac_rfl

/-- Splits `stackAt sp0 (stageP2bStack + 0x700)` into `768 + pqxdhEntryStack` and the `0x700`
extra bytes immediately below `initialStateStack` at `sp0 - 768`. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.bobV1_stack_extra (sp0 : BitVec 64) :
    stackAt sp0 (stageP2bStack + 0x700) =
      memRegion (sp0 - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
        stackAt sp0 (768 + Initiator.pqxdhEntryStack) := by
  have ha : sp0 - BitVec.ofNat 64 (stageP2bStack + 0x700) =
      sp0 - 768#64 - BitVec.ofNat 64 initialStateStack := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add,
      show stageP2bStack + 0x700 = 768 + initialStateStack by decide]
  rw [CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom sp0 stageP2bStack 0x700 (by decide), ha]

/-- Joins the `0x700` extra bytes with `stackAt (sp0 - 768) pqxdhEntryStack` to form
`stackAt (sp0 - 768) initialStateStack` at the `spqr::initial_state` call site. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.bobV1_stack_join (sp0 : BitVec 64) :
    memRegion (sp0 - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
      stackAt (sp0 - 768#64) Initiator.pqxdhEntryStack =
    stackAt (sp0 - 768#64) initialStateStack := by
  have h := CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom (sp0 - 768#64) Initiator.pqxdhEntryStack 0x700 (by decide)
  rw [show Initiator.pqxdhEntryStack + 0x700 = initialStateStack by decide] at h
  exact h.symm

theorem _root_.CryptoVerification.Cli.E2E.V1.bobV1_stack_ext_split (sp0 : BitVec 64) :
    stackAt sp0 (768 + Initiator.pqxdhEntryStackExt) =
      memRegion (sp0 - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 16384 ∗
        stackAt sp0 (768 + Initiator.pqxdhEntryStack) := by
  have ha : sp0 - BitVec.ofNat 64 (768 + Initiator.pqxdhEntryStackExt) =
      sp0 - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  have h := CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom sp0
    (768 + Initiator.pqxdhEntryStack) 16384 (by decide)
  rw [show (768 + Initiator.pqxdhEntryStack) + 16384 = 768 + Initiator.pqxdhEntryStackExt by decide,
    ha] at h
  exact h

theorem _root_.CryptoVerification.Cli.E2E.V1.bobV1_entry_ext_split (sp0 : BitVec 64) :
    stackAt (sp0 - 768#64) Initiator.pqxdhEntryStackExt =
      memRegion (sp0 - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 16384 ∗
        stackAt (sp0 - 768#64) Initiator.pqxdhEntryStack := by
  have h := CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom (sp0 - 768#64)
    Initiator.pqxdhEntryStack 16384 (by decide)
  rwa [show Initiator.pqxdhEntryStack + 16384 = Initiator.pqxdhEntryStackExt by decide] at h

theorem _root_.CryptoVerification.Cli.E2E.V1.bobV1_entry_ext_to_initialState (sp0 : BitVec 64) :
    stackAt (sp0 - 768#64) Initiator.pqxdhEntryStackExt =
      memRegion (sp0 - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 14592 ∗
        stackAt (sp0 - 768#64) initialStateStack := by
  have h := CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom (sp0 - 768#64)
    initialStateStack 14592 (by decide)
  rwa [show initialStateStack + 14592 = Initiator.pqxdhEntryStackExt by decide] at h

theorem _root_.CryptoVerification.Cli.E2E.V1.bobV1_entry_ext_to_initialStateExt (sp0 : BitVec 64) :
    stackAt (sp0 - 768#64) Initiator.pqxdhEntryStackExt =
      memRegion (sp0 - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 13360 ∗
        stackAt (sp0 - 768#64) initialStateStackExt := by
  have h := CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom (sp0 - 768#64)
    initialStateStackExt 13360 (by decide)
  rwa [show initialStateStackExt + 13360 = Initiator.pqxdhEntryStackExt by decide] at h

/-! ## Subroutine segments and end-to-end composition -/

private theorem fnAddr_spqrInitialState_rel_bob_ext_v1 {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr "spqr::initial_state" =
      (tripleRatchetProgAtExt b ext).fnAddr initializeBobSessionSym + 184920#64 := by
  dsimp only [tripleRatchetProgAtExt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      CryptoVerification.libsignalSessionCode_fnOff_0x21c80,
      CryptoVerification.libsignalSessionCode_fnOff_0x4eed8, BitVec.add_assoc]
  congr 1

private theorem fnAddr_spqrInitialState_rel_bob_trap_v1 {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    (trTrapProgAt b C abs).fnAddr "spqr::initial_state" =
      (trTrapProgAt b C abs).fnAddr initializeBobSessionSym + 184920#64 := by
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      CryptoVerification.libsignalSessionCode_fnOff_0x21c80,
      CryptoVerification.libsignalSessionCode_fnOff_0x4eed8, BitVec.add_assoc]
  congr 1

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.V1.initBob_to_spqr_full_v1_trap_of_accept {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hWF : StructuralPrims P) (hH : ResponderCore.PqxdhHookContracts P A img absHooks)
    (haccept_sub : subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpec P A img))
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (h_2 : img.FrozenLoaded s0) (h_1 : s0.symtab = img.symtab)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr "spqr::initial_state") s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + Initiator.pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        (P_f ⊢
          bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
            spkBPk inp.spkBSk ∗
          CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
          (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
          pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
          ((argPtr + 297#64) ↦₈ 0#8) ∗
          memRegion outPtr 344 ∗ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
          (logFilterAddr img ↦₆₄ 0#64) ∗
          stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗ Frame) ∧
        sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 8#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 19#5) = outPtr ∧
        sf.readReg64 (.gpr 20#5) = ratchetKeyPairPtr ∧
        sf.readReg64 (.gpr 21#5) = argPtr ∧
        sf.readReg64 (.gpr 23#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 27#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 30#5) =
          (trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym + 252#64 ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      (BobPanicOom s0) := by
  have hA := hH.alloc
  have hfn : libsignalSessionCode.fnOff initializeBobSessionSym = 0x21c80 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x21c80
  have haccept := subroutine_ok_rel_pqxdh_trap haccept_sub
    CryptoVerification.libsignalSessionCode_fnOff_0x23920 hfn (k := 7328) (by decide)
  dsimp only [pqxdhAcceptOptFieldsSpec, pqxdhAcceptErrStrong2At, Spec.inImage,
    rustPanicOnOom] at haccept
  simp only [State.spAligned] at hsp_align
  rw [fnAddr_spqrInitialState_rel_bob_trap_v1]
  unfold bobParamsFieldsAt
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.initializeBobSession img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x21c80 608
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (trTrapExterns C absHooks))).fnAddr initializeBobSessionSym :=
        by
    try dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc
    rw [hpc]
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at haccept ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr initializeBobSessionSym = entry
  examples_hide_fetches
  subst h_3 h_4 h_5
  rw (occs := .pos [1]) [stackAt_initBob_entry s0.sp]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.of_sepWP_frozen_inImage h_2 h_1 (mid := entry + 7328#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF1 hsym1
  refine SepWPp.call_inImage_frame' hF1 hsym1 haccept
    (ret_pc := entry + 56#64) (x := ⟨inp, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr,
      s0.sp - 488#64⟩)
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
      (by wp_norm_lhs)
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, *]; exact h_8)
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ R hm => by
      exact allowPanic_frame (fun h => CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_trace_eq (s0 :=
        s0) (by simp only [arm64_norm]) h) hm)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 hF2 hsym2 => ?_)
  dsimp only at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29 hcs1_vregs
  conv =>
    arg 4
    simp only [arm64_norm, sepConj_assoc]
  refine SepWPp.pure_left fun htr1 => ?_
  have ⟨hlen_rk, hlen_pq, hlen_ck⟩ := acceptKeys_some_lengths hWF hacc
  have ⟨_, _, hlen_spkSk, _, _, _, _, hlen_ikA, hlen_ekA, _⟩ := h_9
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ :=
    exists_unpack64_of_length_32 (bs :=
    bytesToBv8 drKey.rootKey) (by simp [bytesToBv8, hlen_rk])
  obtain ⟨pq0, pq1, pq2, pq3, _, hpq_cells⟩ :=
    exists_unpack64_of_length_32 (bs := bytesToBv8 drKey.pqrKey) (by simp [bytesToBv8, hlen_pq])
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ :=
    exists_unpack64_of_length_32 (bs :=
    bytesToBv8 drKey.chainKey) (by simp [bytesToBv8, hlen_ck])
  have h104_unpack := handshakeKeysResultOk104_unpack (s0.sp - 488#64) drKey
    hrk_cells hpq_cells hck_cells hlen_rk hlen_pq hlen_ck
  conv =>
    arg 4
    simp only [hacc]
  rw [h104_unpack, memRegion_280_some_split s0.sp,
      stackAt_entry_some_split (s0.sp - 768#64)]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.fold (realign_4_8_8_to_8_8_4 (s0.sp - 488#64) 0#32 rk0 rk1) (by sep_focus) ?_
  simp (config := { maxSteps := 1000000 }) only [
    sepExists_sepConj_left, Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_pull_exists
  wp_steps
  refine SepWP.fold (Entails.of_eq (by
    have h := (hpq_cells (s0.sp - 576#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hrk_cells (s0.sp - 656#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hck_cells (s0.sp - 624#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hpq_cells (s0.sp - 452#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hck_cells (s0.sp - 420#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hrk_cells (s0.sp - 768#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hpq_cells (s0.sp - 736#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hck_cells (s0.sp - 704#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_160_sub5024 s0.sp)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_entry_some_merge s0.sp)) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, by wp_norm_goal, by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
  exact Entails.of_eq (by
    dsimp only [bobSpqrCutCells, CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr, CryptoVerification.Cli.E2E.V1.initBobSavedRegs]
    rw [stackAt_entry_some_split (s0.sp - 768#64)]
    ac_rfl)

theorem _root_.CryptoVerification.Cli.E2E.V1.initBob_to_spqr_full_v1_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : ResponderCore.PqxdhHookContracts P A img absHooks)
    (hP : PrimitivesMatchCrypto P C)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (h_2 : img.FrozenLoaded s0) (h_1 : s0.symtab = img.symtab)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr "spqr::initial_state") s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + Initiator.pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        (P_f ⊢
          bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
            spkBPk inp.spkBSk ∗
          CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
          (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
          pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
          ((argPtr + 297#64) ↦₈ 0#8) ∗
          memRegion outPtr 344 ∗ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
          (logFilterAddr img ↦₆₄ 0#64) ∗
          stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗ Frame) ∧
        sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 8#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 19#5) = outPtr ∧
        sf.readReg64 (.gpr 20#5) = ratchetKeyPairPtr ∧
        sf.readReg64 (.gpr 21#5) = argPtr ∧
        sf.readReg64 (.gpr 23#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 27#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 30#5) =
          (trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym + 252#64 ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      (BobPanicOom s0) :=
  CryptoVerification.Cli.E2E.V1.initBob_to_spqr_full_v1_trap_of_accept hWF hH
    (pqxdhAccept_opt_fields_base_ok_trap himg hWF hH
      (pqxdhHkdfExtract_ok_trap hP himg) (pqxdhHkdfExpandMultiInfo_ok_trap hP)
      (pqxdhCalculateAgreement_ok_trap hP himg hH.alloc))
    s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    h_2 h_1 hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 _h_10 _h_11 hacc

/-- Steps `initialize_bob_session` from entry to `bl spqr::initial_state` (`+248`) with
`sameAccountByte = 0`, preserving `bobFrameAtSpqr`, `initBobSavedRegs`, and all live GPRs. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.initBob_to_spqr_full_v1 {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : ResponderCore.PqxdhHookContracts P A img absHooks)
    (hP : PrimitivesMatchCrypto P C)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (h_2 : img.FrozenLoaded s0) (h_1 : s0.symtab = img.symtab)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr "spqr::initial_state") s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + Initiator.pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        (P_f ⊢
          bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
            spkBPk inp.spkBSk ∗
          CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
          (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
          pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
          ((argPtr + 297#64) ↦₈ 0#8) ∗
          memRegion outPtr 344 ∗ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
          (logFilterAddr img ↦₆₄ 0#64) ∗
          stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗ Frame) ∧
        sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 8#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 19#5) = outPtr ∧
        sf.readReg64 (.gpr 20#5) = ratchetKeyPairPtr ∧
        sf.readReg64 (.gpr 21#5) = argPtr ∧
        sf.readReg64 (.gpr 23#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 27#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 30#5) =
          (tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym + 252#64 ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      (BobPanicOom s0) := by
  have hTraps := trapsOnly_trTrap_kit img.base C ctl absHooks
  rw [← hTraps.fnAddr] at hpc
  simp only [← hTraps.fnAddr]
  exact SepWPp_kit_of_trTrap (CryptoVerification.Cli.E2E.V1.initBob_to_spqr_full_v1_trap
    himg hWF hH hP s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
    outPtr drKey Frame h_2 h_1 hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 _h_10 _h_11 hacc)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.V1.initBob_to_spqr_full_v1_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : ResponderCore.PqxdhHookContractsExt P A img ext)
    (hext : Initiator.PqxdhHkdfExtractOk_ext P img ext)
    (hexp : Initiator.PqxdhHkdfExpandMultiInfoOk_ext P img ext)
    (hag : ResponderCore.PqxdhCalculateAgreementOkExt P A img ext)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (h_2 : img.FrozenLoaded s0) (h_1 : s0.symtab = img.symtab)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr "spqr::initial_state") s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + Initiator.pqxdhEntryStackExt) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        (P_f ⊢
          bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
            spkBPk inp.spkBSk ∗
          CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
          (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
          pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
          ((argPtr + 297#64) ↦₈ 0#8) ∗
          memRegion outPtr 344 ∗ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
          (logFilterAddr img ↦₆₄ 0#64) ∗
          stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStackExt ∗ A.pool ∗ Frame) ∧
        sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 8#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 19#5) = outPtr ∧
        sf.readReg64 (.gpr 20#5) = ratchetKeyPairPtr ∧
        sf.readReg64 (.gpr 21#5) = argPtr ∧
        sf.readReg64 (.gpr 23#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 27#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 30#5) =
          (tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym + 252#64 ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      (BobPanicOom s0) := by
  have hfn : libsignalSessionCode.fnOff initializeBobSessionSym = 0x21c80 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x21c80
  have haccept := subroutine_ok_rel_pqxdh_ext
    (pqxdhAccept_opt_fields_base_ok_ext himg hWF hH hext hexp hag)
    CryptoVerification.libsignalSessionCode_fnOff_0x23920 hfn (k := 7328) (by decide)
  dsimp only [pqxdhAcceptOptFieldsSpecExt, pqxdhAcceptErrStrong2At, Spec.inImage,
    rustPanicOnOom] at haccept
  simp only [State.spAligned] at hsp_align
  rw [fnAddr_spqrInitialState_rel_bob_ext_v1]
  unfold bobParamsFieldsAt
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.initializeBobSession img.base
    (Rust.withPanics ext) hfn 0x21c80 608
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr initializeBobSessionSym := by
    try dsimp only [tripleRatchetProgAtExt] at hpc
    rw [hpc]
  dsimp only [tripleRatchetProgAtExt] at haccept ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr initializeBobSessionSym = entry
  examples_hide_fetches
  subst h_3 h_4 h_5
  rw (occs := .pos [1]) [CryptoVerification.Cli.E2E.V1.bobV1_stack_ext_split s0.sp]
  rw (occs := .pos [1]) [stackAt_initBob_entry s0.sp]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.of_sepWP_frozen_inImage h_2 h_1 (mid := entry + 7328#64)
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (CryptoVerification.Cli.E2E.V1.bobV1_entry_ext_split s0.sp).symm)
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF1 hsym1
  refine SepWPp.call_inImage_frame' hF1 hsym1 haccept
    (ret_pc := entry + 56#64) (x := ⟨inp, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr,
      s0.sp - 488#64⟩)
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
      (by wp_norm_lhs)
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, *]; exact h_8)
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ R hm => by
      exact allowPanic_frame (fun h => CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_trace_eq (s0 :=
        s0) (by simp only [arm64_norm]) h) hm)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 hF2 hsym2 => ?_)
  dsimp only at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29 hcs1_vregs
  conv =>
    arg 4
    simp only [arm64_norm, sepConj_assoc]
  refine SepWPp.pure_left fun htr1 => ?_
  have ⟨hlen_rk, hlen_pq, hlen_ck⟩ := acceptKeys_some_lengths hWF hacc
  have ⟨_, _, hlen_spkSk, _, _, _, _, hlen_ikA, hlen_ekA, _⟩ := h_9
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ :=
    exists_unpack64_of_length_32 (bs :=
    bytesToBv8 drKey.rootKey) (by simp [bytesToBv8, hlen_rk])
  obtain ⟨pq0, pq1, pq2, pq3, _, hpq_cells⟩ :=
    exists_unpack64_of_length_32 (bs := bytesToBv8 drKey.pqrKey) (by simp [bytesToBv8, hlen_pq])
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ :=
    exists_unpack64_of_length_32 (bs :=
    bytesToBv8 drKey.chainKey) (by simp [bytesToBv8, hlen_ck])
  have h104_unpack := handshakeKeysResultOk104_unpack (s0.sp - 488#64) drKey
    hrk_cells hpq_cells hck_cells hlen_rk hlen_pq hlen_ck
  conv =>
    arg 4
    simp only [hacc]
  rw [h104_unpack, memRegion_280_some_split s0.sp,
      CryptoVerification.Cli.E2E.V1.bobV1_entry_ext_split s0.sp,
      stackAt_entry_some_split (s0.sp - 768#64)]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.fold (realign_4_8_8_to_8_8_4 (s0.sp - 488#64) 0#32 rk0 rk1) (by sep_focus) ?_
  simp (config := { maxSteps := 1000000 }) only [
    sepExists_sepConj_left, Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_pull_exists
  wp_steps
  refine SepWP.fold (Entails.of_eq (by
    have h := (hpq_cells (s0.sp - 576#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hrk_cells (s0.sp - 656#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hck_cells (s0.sp - 624#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hpq_cells (s0.sp - 452#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hck_cells (s0.sp - 420#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hrk_cells (s0.sp - 768#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hpq_cells (s0.sp - 736#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hck_cells (s0.sp - 704#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_160_sub5024 s0.sp)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_entry_some_merge s0.sp)) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, by wp_norm_goal, by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
  exact Entails.of_eq (by
    dsimp only [bobSpqrCutCells, CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr, CryptoVerification.Cli.E2E.V1.initBobSavedRegs]
    have hex : s0.sp - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt = s0.sp - 33536#64 := by
      rw [BitVec.sub_sub]; rfl
    rw [stackAt_entry_some_split (s0.sp - 768#64), hex]
    ac_rfl)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.V1.initBob_epilogue_v1_trap {img : Obj.Image} {C : Crypto}
    {absHooks : String → Option (State → State)}
    (s0 s : State) (Frame : SepProp)
    (hsp0_align : s0.sp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym + 564#64)
    (hsp : s.sp = s0.sp - 768#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (trTrapProgAt img.base C absHooks) (s0.readReg64 (.gpr 30#5)) s
      (CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ memRegion (s0.sp - 96#64) 96 ∗ Frame) ∧ sf.status = ExecStatus.Running ∧
        sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧ sf.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff initializeBobSessionSym = 0x21c80 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x21c80
  have hs0 : s0.sp = s.sp + 768#64 := by rw [hsp]; bv_omega
  have hal : s.sp &&& 15#64 == 0#64 := by rw [hsp]; revert hsp0_align; bv_bits
  have hfold := CryptoVerification.Cli.E2E.V1.initBobSavedRegs_entails_memRegion96 (s.sp + 768#64) s0
  dsimp only [CryptoVerification.Cli.E2E.V1.initBobSavedRegs] at hfold
  simp only [CryptoVerification.Cli.E2E.V1.bv_add_sub_lit_bob, BitVec.reduceSub] at hfold
  bob_v1_fetches img.base (Rust.withPanics (trTrapExterns C absHooks)) hfn 564 32
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt, CryptoVerification.Cli.E2E.V1.initBobSavedRegs] at hpc ⊢
  rw [hs0]
  clear hsp hsp0_align hs0
  simp only [CryptoVerification.Cli.E2E.V1.bv_add_sub_lit_bob, BitVec.reduceSub]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr initializeBobSessionSym = entry
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.fold hfold (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
     by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       by wp_norm_goal, by wp_norm_goal, by simp only [arm64_norm, *]⟩, by wp_norm_goal⟩

/-- Steps the `initialize_bob_session` epilogue (`+564 → RET`), restoring `x19..x30` and advancing
`sp` by `0x300`. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.initBob_epilogue_v1 {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (s0 s : State) (Frame : SepProp)
    (hsp0_align : s0.sp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym +
      564#64)
    (hsp : s.sp = s0.sp - 768#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAt img.base C ctl absHooks) (s0.readReg64 (.gpr 30#5)) s
      (CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ memRegion (s0.sp - 96#64) 96 ∗ Frame) ∧ sf.status = ExecStatus.Running ∧
        sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧ sf.trace = s.trace) := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl absHooks).fnAddr] at hpc
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.V1.initBob_epilogue_v1_trap s0 s Frame hsp0_align hrun hpc hsp hvregs)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.V1.initBob_epilogue_v1_ext {img : Obj.Image}
    {ext : String → Option (State → State)}
    (s0 s : State) (Frame : SepProp)
    (hsp0_align : s0.sp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym + 564#64)
    (hsp : s.sp = s0.sp - 768#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (.gpr 30#5)) s
      (CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ memRegion (s0.sp - 96#64) 96 ∗ Frame) ∧ sf.status = ExecStatus.Running ∧
        sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧ sf.trace = s.trace) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::ratchet::initialize_bob_session")
  have hs0 : s0.sp = s.sp + 768#64 := by rw [hsp]; bv_omega
  have hal : s.sp &&& 15#64 == 0#64 := by rw [hsp]; revert hsp0_align; bv_bits
  have hfold := CryptoVerification.Cli.E2E.V1.initBobSavedRegs_entails_memRegion96 (s.sp + 768#64) s0
  dsimp only [CryptoVerification.Cli.E2E.V1.initBobSavedRegs] at hfold
  simp only [CryptoVerification.Cli.E2E.V1.bv_add_sub_lit_bob, BitVec.reduceSub] at hfold
  bob_v1_fetches img.base (Rust.withPanics ext) hfn 564 32
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.E2E.V1.initBobSavedRegs] at hpc ⊢
  rw [hs0]
  clear hsp hsp0_align hs0
  simp only [CryptoVerification.Cli.E2E.V1.bv_add_sub_lit_bob, BitVec.reduceSub]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr initializeBobSessionSym = entry
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.fold hfold (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
     by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       by wp_norm_goal, by wp_norm_goal, by simp only [arm64_norm, *]⟩, by wp_norm_goal⟩

@[local arm64_norm, local wp_norm]
private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb1b_bv_sub_add_lit' (x a b : BitVec 64) :
    (x - a) + b = x - (a - b) := Initiator.bv_sub_add_lit' x a b

@[local simp, local arm64_norm, local wp_norm]
private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb1b_cond_ne_subs64_0_1 :
    ConditionHolds CondCode.NE (subsPState64 0#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb1b_sub488_split (sp : BitVec 64) :
    memRegion (sp - 488#64) 344 =
      cells (sp - 488#64) 19 ∗
      memRegion (sp - 336#64) 92 ∗
      (∃∗ pad_f4 : BitVec 32, (sp - 244#64) ↦₃₂ pad_f4) ∗
      memRegion (sp - 240#64) 96 := by
  rw [ProofLib.memRegion_split' (b := sp - 488#64) (n := 152) (k := 192)
      (b' := sp - 336#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 336#64) (n := 92) (k := 100)
      (b' := sp - 244#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 244#64) (n := 4) (k := 96)
      (b' := sp - 240#64) rfl (by bv_omega) (by decide),
    (ProofLib.memRegion_cells (sp - 488#64) 19 (by decide) :
      memRegion (sp - 488#64) 152 = cells (sp - 488#64) 19),
    ProofLib.memRegion_four (sp - 244#64)]

/-- Steps `initialize_bob_session` from `spqr::initial_state` return (`+252`) to the epilogue
(`+564`), checking the `Ok` tag (`0`) and assembling `bobSession344Bv8V1` at `outPtr` with the
SPQR `Vec<u8>` header `(spqrCap, spqrBufPtr, spqrLen)` at `+0x78`. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.initBob_session_build_v1_trap
    {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hA : AllocHooks A absHooks)
    (s0 s : State) (argPtr rkp outPtr : BitVec 64)
    (spqrCap spqrBufPtr spqrLen : BitVec 64)
    (ikBPk ikAPk ekAPk spkBPk spkBSk rk ck : SignalPqxdh.Bytes)
    (Frame : SepProp)
    (hikB_len : ikBPk.length = 32)
    (hikA_len : ikAPk.length = 32)
    (hekA_len : ekAPk.length = 32)
    (hspkPk_len : spkBPk.length = 32)
    (hspkSk_len : spkBSk.length = 32)
    (hrk_len : rk.length = 32)
    (hck_len : ck.length = 32)
    (hsp0_align : s0.sp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym +
      252#64)
    (hsp : s.sp = s0.sp - 768#64)
    (hx19 : s.readReg64 (.gpr 19#5) = outPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = rkp)
    (hx21 : s.readReg64 (.gpr 21#5) = argPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = s0.sp - 768#64)
    (hx27 : s.readReg64 (.gpr 27#5) = s0.sp - 488#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym + 564#64) s
      (((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
       ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
       ((s0.sp - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((s0.sp - 624#64) ↦ₛ bytesToBv8 ck) ∗
       ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
       memRegion (s0.sp - 488#64) 344 ∗
       (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 ikAPk) ∗
       ((argPtr + 160#64) ↦ₛ bytesToBv8 ekAPk) ∗
       (rkp ↦ₛ bytesToBv8 spkBPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkBSk) ∗
       memRegion outPtr 344 ∗
       stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            memRegion (s0.sp - 768#64) 32 ∗
            ((s0.sp - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((s0.sp - 624#64) ↦ₛ bytesToBv8 ck) ∗
            ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 488#64) 344 ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 ikAPk) ∗
            ((argPtr + 160#64) ↦ₛ bytesToBv8 ekAPk) ∗
            (rkp ↦ₛ bytesToBv8 spkBPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkBSk) ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikAPk)) ∗ A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 rk) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ekAPk)) ∗ A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 ck) ∗ A.live chainKeyBoxPtr 32 1 ∗
            stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧
          sf.pc = (trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym +
            564#64 ∧
          sf.sp = s0.sp - 768#64 ∧ sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      (BobPanicOom s0) := by
  have hsp_align : s.spAligned = true := by
    simp only [State.spAligned, hsp]
    revert hsp0_align; bv_bits
  have hfn : libsignalSessionCode.fnOff initializeBobSessionSym = 0x21c80 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x21c80
  have hserPub := subroutine_ok_rel_pqxdh_trap
    (ecPubKeySerialize_alloc_ok_trap (img := img) (C := C) hA)
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4 hfn (k := 116292) (by decide)
  have hshim := pqxdh_shim_ok_at_trap (b := img.base) (C := C)
    (absHooks := absHooks) (name := initializeBobSessionSym) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x21c80))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := pqxdh_alloc_ok_at_trap (b := img.base) (C := C) hA
    (name := initializeBobSessionSym) (k := num% (ls_off% "__rustc::__rust_alloc" - 0x21c80))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  have hpan_rawvec := pqxdh_panic_at_raw_vec_handle_error_trap (b := img.base) (C := C)
    (absHooks := absHooks) (name := initializeBobSessionSym) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x21c80))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hwithSender := subroutine_ok_rel_pqxdh_trap
    (withSenderChain_none_base_ok_trap (img := img) (C := C) hA)
    CryptoVerification.libsignalSessionCode_fnOff_0x117e8 hfn (k := 18446744073709484904)
    (by decide)
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := bytesToBv8 rk) (by simp [bytesToBv8, hrk_len])
  conv =>
    arg 4
    rw [hrk_cells (s0.sp - 656#64), stackAt_entry_some_split (s0.sp - 768#64)]
    simp (config := { maxSteps := 1000000 }) only [
      Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  bob_v1_fetches img.base (Rust.withPanics (trTrapExterns C absHooks)) hfn 252 356
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc hserPub hshim halloc hpan_rawvec hwithSender ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr initializeBobSessionSym = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 116292#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (argPtr, ikBPk)) hserPub
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [*, State.spAligned, arm64_norm])
    (ret_pc := entry + 400#64) (by wp_norm_lhs)
    (by
      conv =>
        lhs
        dsimp only [ecPubKeySerializeAllocSpec]
        simp only [arm64_norm, hsp, Initiator.bv_sub_add_lit', BitVec.reduceSub])
    hikB_len
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ R hm => by
      dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
      simpa only [sepConj_assoc] using
        allowPanic_frame (fun h => CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_trace_eq (s0 :=
        s0) (by simp only [*, arm64_norm]) h) hm)
    (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 => ?_)
  simp only [*, arm64_norm] at hspm1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
  rcases hcsm1 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
    hcs2_27, hcs2_28, hcs2_29, hcs2_vregs⟩
  simp only [*, arm64_norm]
    at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29 hcs2_vregs
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocSpec]
    simp only [arm64_norm, hsp, Initiator.bv_sub_add_lit', BitVec.reduceSub,
      sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun localIkBoxPtr => ?_
  refine SepWPp.pure_left fun ⟨htr2, hx0_1, hx1_1, hne_localIk⟩ => ?_
  apply SepWPp.of_sepWP (mid := entry + 116292#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (argPtr + 128#64, ikAPk)) hserPub
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [*, State.spAligned, arm64_norm])
    (ret_pc := entry + 416#64) (by wp_norm_lhs)
    (by
      conv =>
        lhs
        dsimp only [ecPubKeySerializeAllocSpec]
        simp only [arm64_norm, hspm1, Initiator.bv_sub_add_lit', BitVec.reduceSub])
    hikA_len
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ R hm => by
      dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
      simpa only [sepConj_assoc] using
        allowPanic_frame (fun h => CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_trace_eq (s0 :=
        s0) (by simp only [*, arm64_norm]) h) hm)
    (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 => ?_)
  simp only [*, arm64_norm] at hspm2
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
  rcases hcsm2 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25, hcs3_26,
    hcs3_27, hcs3_28, hcs3_29, hcs3_vregs⟩
  simp only [*, arm64_norm]
    at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28 hcs3_29 hcs3_vregs
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocSpec]
    simp only [arm64_norm, hspm1, Initiator.bv_sub_add_lit', BitVec.reduceSub,
      sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun remoteIkBoxPtr => ?_
  refine SepWPp.pure_left fun ⟨htr3, hx0_2, hx1_2, hne_remoteIk⟩ => ?_
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 440#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · conv =>
      arg 4
      simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x21c80))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpan_rawvec) fun R hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (Initiator.allocFailedIn_of_eq (by simp only [*, Rust.panicked, arm64_norm])) hm
  · have hm32_rk : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      ProofLib.memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    conv =>
      arg 4
      simp only [hoom1, ite_false, ‹sf.sp = sm2.sp›, hspm2, hm32_rk, cells, sepConj_emp,
        sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
        sepConj_assoc]
    refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 =>
      SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun r3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod_rk, htr4⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 116292#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.call_frame (x := (argPtr + 160#64, ekAPk)) hserPub
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := entry + 464#64) (by wp_norm_lhs)
      (by
        conv =>
          lhs
          dsimp only [ecPubKeySerializeAllocSpec]
          simp only [arm64_norm, ‹sf_1.sp = sf.sp›, ‹sf.sp = sm2.sp›, hspm2,
            Initiator.bv_sub_add_lit', BitVec.reduceSub])
      hekA_len
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ R hm => by
        dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
        simpa only [sepConj_assoc] using
          allowPanic_frame (fun h => CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_trace_eq (s0 :=
          s0) (by simp only [*, arm64_norm]) h) hm)
      (fun sm3 hpcm3 hrunm3 hspm3 hcsm3 => ?_)
    simp only [*, arm64_norm] at hspm3
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm3
    rcases hcsm3 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25, hcs4_26,
      hcs4_27, hcs4_28, hcs4_29, hcs4_vregs⟩
    simp only [*, arm64_norm]
      at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28 hcs4_29 hcs4_vregs
    conv =>
      arg 4
      dsimp only [ecPubKeySerializeAllocSpec]
      simp only [arm64_norm, ‹sf_1.sp = sf.sp›, ‹sf.sp = sm2.sp›, hspm2,
        Initiator.bv_sub_add_lit', BitVec.reduceSub,
        sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun baseKeyBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr5, hx0_3, hx1_3, hne_baseKey⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 18446744073709484904#64)
    conv =>
      arg 4
      rw [CryptoVerification.Cli.E2E.V1.wp6pb1b_sub488_split s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists
    rename_i pad_f4
    conv =>
      arg 4
      simp (config := { maxSteps := 1000000 }) only [
        cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
        Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_pull_exists
    conv =>
      arg 4
      rw [(ProofLib.memRegion_cells (s0.sp - 240#64) 12 (by decide) :
        memRegion (s0.sp - 240#64) 96 = cells (s0.sp - 240#64) 12)]
      simp (config := { maxSteps := 1000000 }) only [
        cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
        Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_pull_exists
    rename_i w_f8 c0 c1 c2 c3 c4 w_128 d0 d1 d2 w_148 w_150
    wp_steps
    refine SepWP.fold (Entails.of_eq (hrk_cells (sf_1.readReg64 (.gpr 0#5))).symm)
      (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (by
      have h := (hrk_cells (s0.sp - 656#64)).symm
      simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
      exact h)) (by sep_focus) ?_
    refine SepWP.fold (cells4_sub768_merge s0.sp _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (memRegion_160_sub5024 s0.sp)) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (by
      have h := CryptoVerification.Cli.E2E.V1.bobHead144V1_eq_pointsToBytes (s0.sp - 488#64) localIkBoxPtr remoteIkBoxPtr
        (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
      simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
      exact h)) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (by
      have h := post100_pack (s0.sp - 488#64) pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
      simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
      exact h)) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hφ_ws : spkBPk.length = 32 ∧ spkBSk.length = 32 ∧ ck.length = 32 ∧
        (CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
          spqrCap spqrBufPtr spqrLen).length = 144 ∧
        (unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2).length = 100 :=
      ⟨hspkPk_len, hspkSk_len, hck_len, CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1_length _ _ _ _ _ _ _,
        by simp [unpack32]⟩
    refine SepWPp.call_frame (x :=
      ⟨outPtr, s0.sp - 488#64, rkp, spkBPk, spkBSk, s0.sp - 624#64, ck, 0#32,
        CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
          spqrCap spqrBufPtr spqrLen,
        unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2⟩) hwithSender
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := entry + 564#64) (by wp_norm_lhs)
      (by
        conv =>
          lhs
          dsimp only [withSenderChainNoneSpec]
          simp only [arm64_norm, hspm3, hcs4_19, hcs3_19, hcs2_19, hx19,
            hcs4_20, hcs3_20, hcs2_20, hx20, Initiator.bv_sub_add_lit', BitVec.reduceSub])
      hφ_ws
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ R hm => by
        dsimp only [withSenderChainNoneSpec, rustPanicOnOom] at hm
        simpa only [sepConj_assoc] using
          allowPanic_frame (fun h => CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_trace_eq (s0 :=
          s0) (by simp only [*, arm64_norm]) h) hm)
      (fun sm4 hpcm4 hrunm4 hspm4 hcsm4 => ?_)
    simp only [*, arm64_norm] at hspm4
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm4
    rcases hcsm4 with ⟨hcs5_19, hcs5_20, hcs5_21, hcs5_22, hcs5_23, hcs5_24, hcs5_25, hcs5_26,
      hcs5_27, hcs5_28, hcs5_29, hcs5_vregs⟩
    simp only [*, arm64_norm]
      at hcs5_19 hcs5_20 hcs5_21 hcs5_22 hcs5_23 hcs5_24 hcs5_25 hcs5_26 hcs5_27 hcs5_28 hcs5_29 hcs5_vregs
    conv =>
      arg 4
      dsimp only [withSenderChainNoneSpec]
      simp only [arm64_norm, hspm3, Initiator.bv_sub_add_lit', BitVec.reduceSub,
        sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun ratchetPubBoxPtr =>
      SepWPp.exists_elim fun ratchetPrivBoxPtr =>
      SepWPp.exists_elim fun chainKeyBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr6, hne_rPub, hne_rPriv, hne_ck⟩ => ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.fold (Entails.of_eq (CryptoVerification.Cli.E2E.V1.bobSession344V1_pack outPtr
      localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
      spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2))
      (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (by
      have h := CryptoVerification.Cli.E2E.V1.bobSession344V1_pack (s0.sp - 488#64)
        localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
        spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
      simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
      exact h)) (by sep_focus) ?_
    have h344_weaken :
        ((s0.sp - 488#64) ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr
          (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
          ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ⊢
        memRegion (s0.sp - 488#64) 344 := by
      have h := pointsToBytes_entails_memRegion (s0.sp - 488#64)
        (CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5))
          baseKeyBoxPtr spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr
          chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2)
      rwa [CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1_length] at h
    refine SepWP.fold h344_weaken (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_entry_some_merge s0.sp)) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨localIkBoxPtr, remoteIkBoxPtr, sf_1.readReg64 (.gpr 0#5), baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hne_localIk, hne_remoteIk, hoom1, hne_baseKey,
      hne_rPub, hne_rPriv, hne_ck,
      Entails.of_eq (by ac_rfl),
      by wp_norm_goal, by wp_norm_goal, by simp only [*, arm64_norm],
      by simp only [*, arm64_norm], by simp only [*, arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.E2E.V1.initBob_session_build_v1
    {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hA : AllocHooks A absHooks)
    (s0 s : State) (argPtr rkp outPtr : BitVec 64)
    (spqrCap spqrBufPtr spqrLen : BitVec 64)
    (ikBPk ikAPk ekAPk spkBPk spkBSk rk ck : SignalPqxdh.Bytes)
    (Frame : SepProp)
    (hikB_len : ikBPk.length = 32)
    (hikA_len : ikAPk.length = 32)
    (hekA_len : ekAPk.length = 32)
    (hspkPk_len : spkBPk.length = 32)
    (hspkSk_len : spkBSk.length = 32)
    (hrk_len : rk.length = 32)
    (hck_len : ck.length = 32)
    (hsp0_align : s0.sp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym +
      252#64)
    (hsp : s.sp = s0.sp - 768#64)
    (hx19 : s.readReg64 (.gpr 19#5) = outPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = rkp)
    (hx21 : s.readReg64 (.gpr 21#5) = argPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = s0.sp - 768#64)
    (hx27 : s.readReg64 (.gpr 27#5) = s0.sp - 488#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym + 564#64) s
      (((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
       ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
       ((s0.sp - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((s0.sp - 624#64) ↦ₛ bytesToBv8 ck) ∗
       ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
       memRegion (s0.sp - 488#64) 344 ∗
       (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 ikAPk) ∗
       ((argPtr + 160#64) ↦ₛ bytesToBv8 ekAPk) ∗
       (rkp ↦ₛ bytesToBv8 spkBPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkBSk) ∗
       memRegion outPtr 344 ∗
       stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            memRegion (s0.sp - 768#64) 32 ∗
            ((s0.sp - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((s0.sp - 624#64) ↦ₛ bytesToBv8 ck) ∗
            ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 488#64) 344 ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 ikAPk) ∗
            ((argPtr + 160#64) ↦ₛ bytesToBv8 ekAPk) ∗
            (rkp ↦ₛ bytesToBv8 spkBPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkBSk) ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikAPk)) ∗ A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 rk) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ekAPk)) ∗ A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 ck) ∗ A.live chainKeyBoxPtr 32 1 ∗
            stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧
          sf.pc = (tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym +
            564#64 ∧
          sf.sp = s0.sp - 768#64 ∧ sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      (BobPanicOom s0) := by
  have hTraps := trapsOnly_trTrap_kit img.base C ctl absHooks
  rw [← hTraps.fnAddr] at hpc
  simp only [← hTraps.fnAddr]
  exact SepWPp_kit_of_trTrap (CryptoVerification.Cli.E2E.V1.initBob_session_build_v1_trap
    hA s0 s argPtr rkp outPtr spqrCap spqrBufPtr spqrLen
    ikBPk ikAPk ekAPk spkBPk spkBSk rk ck Frame
    hikB_len hikA_len hekA_len hspkPk_len hspkSk_len hrk_len hck_len
    hsp0_align hrun hpc hsp hx19 hx20 hx21 hx23 hx27 htr hvregs)

theorem _root_.CryptoVerification.Cli.E2E.V1.initBob_session_build_v1_ext
    {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hM : Initiator.SessionMemHooks A ext)
    (s0 s : State) (argPtr rkp outPtr : BitVec 64)
    (spqrCap spqrBufPtr spqrLen : BitVec 64)
    (ikBPk ikAPk ekAPk spkBPk spkBSk rk ck : SignalPqxdh.Bytes)
    (Frame : SepProp)
    (hikB_len : ikBPk.length = 32)
    (hikA_len : ikAPk.length = 32)
    (hekA_len : ekAPk.length = 32)
    (hspkPk_len : spkBPk.length = 32)
    (hspkSk_len : spkBSk.length = 32)
    (hrk_len : rk.length = 32)
    (hck_len : ck.length = 32)
    (hsp0_align : s0.sp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym + 252#64)
    (hsp : s.sp = s0.sp - 768#64)
    (hx19 : s.readReg64 (.gpr 19#5) = outPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = rkp)
    (hx21 : s.readReg64 (.gpr 21#5) = argPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = s0.sp - 768#64)
    (hx27 : s.readReg64 (.gpr 27#5) = s0.sp - 488#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym + 564#64) s
      (((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
       ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
       ((s0.sp - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((s0.sp - 624#64) ↦ₛ bytesToBv8 ck) ∗
       ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
       memRegion (s0.sp - 488#64) 344 ∗
       (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 ikAPk) ∗
       ((argPtr + 160#64) ↦ₛ bytesToBv8 ekAPk) ∗
       (rkp ↦ₛ bytesToBv8 spkBPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkBSk) ∗
       memRegion outPtr 344 ∗
       stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            memRegion (s0.sp - 768#64) 32 ∗
            ((s0.sp - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((s0.sp - 624#64) ↦ₛ bytesToBv8 ck) ∗
            ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 488#64) 344 ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 ikAPk) ∗
            ((argPtr + 160#64) ↦ₛ bytesToBv8 ekAPk) ∗
            (rkp ↦ₛ bytesToBv8 spkBPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkBSk) ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikAPk)) ∗ A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 rk) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ekAPk)) ∗ A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 ck) ∗ A.live chainKeyBoxPtr 32 1 ∗
            stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧
          sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym + 564#64 ∧
          sf.sp = s0.sp - 768#64 ∧ sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      (BobPanicOom s0) := by
  have hsp_align : s.spAligned = true := by
    simp only [State.spAligned, hsp]
    revert hsp0_align; bv_bits
  have hfn : libsignalSessionCode.fnOff initializeBobSessionSym = 0x21c80 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x21c80
  have hserPub := subroutine_ok_rel_pqxdh_ext
    (ecPubKeySerialize_alloc_ok_ext (img := img) hM.shim hM.alloc)
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4 hfn (k := 116292) (by decide)
  have hshim := shim_ok_at_session_ext img.base hM.shim initializeBobSessionSym
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x21c80))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := pqxdh_alloc_ok_at_ext (b := img.base) (ext := ext) hM.alloc
    (name := initializeBobSessionSym) (k := num% (ls_off% "__rustc::__rust_alloc" - 0x21c80))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  have hpan_rawvec := pqxdh_panic_at_raw_vec_handle_error_ext (b := img.base) (ext := ext)
    (name := initializeBobSessionSym) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x21c80))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hwithSender := subroutine_ok_rel_pqxdh_ext
    (withSenderChain_none_base_ok_ext (img := img) hM)
    CryptoVerification.libsignalSessionCode_fnOff_0x117e8 hfn (k := 18446744073709484904)
    (by decide)
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := bytesToBv8 rk) (by simp [bytesToBv8, hrk_len])
  conv =>
    arg 4
    rw [hrk_cells (s0.sp - 656#64), stackAt_entry_some_split (s0.sp - 768#64)]
    simp (config := { maxSteps := 1000000 }) only [
      Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  bob_v1_fetches img.base (Rust.withPanics ext) hfn 252 356
  dsimp only [tripleRatchetProgAtExt] at hpc hserPub hshim halloc hpan_rawvec hwithSender ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr initializeBobSessionSym = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 116292#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (argPtr, ikBPk)) hserPub
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [*, State.spAligned, arm64_norm])
    (ret_pc := entry + 400#64) (by wp_norm_lhs)
    (by
      conv =>
        lhs
        dsimp only [ecPubKeySerializeAllocSpec]
        simp only [arm64_norm, hsp, Initiator.bv_sub_add_lit', BitVec.reduceSub])
    hikB_len
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ R hm => by
      dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
      simpa only [sepConj_assoc] using
        allowPanic_frame (fun h => CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_trace_eq (s0 :=
        s0) (by simp only [*, arm64_norm]) h) hm)
    (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 => ?_)
  simp only [*, arm64_norm] at hspm1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
  rcases hcsm1 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
    hcs2_27, hcs2_28, hcs2_29, hcs2_vregs⟩
  simp only [*, arm64_norm]
    at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29 hcs2_vregs
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocSpec]
    simp only [arm64_norm, hsp, Initiator.bv_sub_add_lit', BitVec.reduceSub,
      sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun localIkBoxPtr => ?_
  refine SepWPp.pure_left fun ⟨htr2, hx0_1, hx1_1, hne_localIk⟩ => ?_
  apply SepWPp.of_sepWP (mid := entry + 116292#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (argPtr + 128#64, ikAPk)) hserPub
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [*, State.spAligned, arm64_norm])
    (ret_pc := entry + 416#64) (by wp_norm_lhs)
    (by
      conv =>
        lhs
        dsimp only [ecPubKeySerializeAllocSpec]
        simp only [arm64_norm, hspm1, Initiator.bv_sub_add_lit', BitVec.reduceSub])
    hikA_len
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ R hm => by
      dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
      simpa only [sepConj_assoc] using
        allowPanic_frame (fun h => CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_trace_eq (s0 :=
        s0) (by simp only [*, arm64_norm]) h) hm)
    (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 => ?_)
  simp only [*, arm64_norm] at hspm2
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
  rcases hcsm2 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25, hcs3_26,
    hcs3_27, hcs3_28, hcs3_29, hcs3_vregs⟩
  simp only [*, arm64_norm]
    at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28 hcs3_29 hcs3_vregs
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocSpec]
    simp only [arm64_norm, hspm1, Initiator.bv_sub_add_lit', BitVec.reduceSub,
      sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun remoteIkBoxPtr => ?_
  refine SepWPp.pure_left fun ⟨htr3, hx0_2, hx1_2, hne_remoteIk⟩ => ?_
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 440#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · conv =>
      arg 4
      simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x21c80))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpan_rawvec) fun R hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (Initiator.allocFailedIn_of_eq (by simp only [*, Rust.panicked, arm64_norm])) hm
  · have hm32_rk : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      ProofLib.memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    conv =>
      arg 4
      simp only [hoom1, ite_false, ‹sf.sp = sm2.sp›, hspm2, hm32_rk, cells, sepConj_emp,
        sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
        sepConj_assoc]
    refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 =>
      SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun r3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod_rk, htr4⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 116292#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.call_frame (x := (argPtr + 160#64, ekAPk)) hserPub
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := entry + 464#64) (by wp_norm_lhs)
      (by
        conv =>
          lhs
          dsimp only [ecPubKeySerializeAllocSpec]
          simp only [arm64_norm, ‹sf_1.sp = sf.sp›, ‹sf.sp = sm2.sp›, hspm2,
            Initiator.bv_sub_add_lit', BitVec.reduceSub])
      hekA_len
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ R hm => by
        dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
        simpa only [sepConj_assoc] using
          allowPanic_frame (fun h => CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_trace_eq (s0 :=
          s0) (by simp only [*, arm64_norm]) h) hm)
      (fun sm3 hpcm3 hrunm3 hspm3 hcsm3 => ?_)
    simp only [*, arm64_norm] at hspm3
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm3
    rcases hcsm3 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25, hcs4_26,
      hcs4_27, hcs4_28, hcs4_29, hcs4_vregs⟩
    simp only [*, arm64_norm]
      at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28 hcs4_29 hcs4_vregs
    conv =>
      arg 4
      dsimp only [ecPubKeySerializeAllocSpec]
      simp only [arm64_norm, ‹sf_1.sp = sf.sp›, ‹sf.sp = sm2.sp›, hspm2,
        Initiator.bv_sub_add_lit', BitVec.reduceSub,
        sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun baseKeyBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr5, hx0_3, hx1_3, hne_baseKey⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 18446744073709484904#64)
    conv =>
      arg 4
      rw [CryptoVerification.Cli.E2E.V1.wp6pb1b_sub488_split s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists
    rename_i pad_f4
    conv =>
      arg 4
      simp (config := { maxSteps := 1000000 }) only [
        cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
        Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_pull_exists
    conv =>
      arg 4
      rw [(ProofLib.memRegion_cells (s0.sp - 240#64) 12 (by decide) :
        memRegion (s0.sp - 240#64) 96 = cells (s0.sp - 240#64) 12)]
      simp (config := { maxSteps := 1000000 }) only [
        cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
        Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_pull_exists
    rename_i w_f8 c0 c1 c2 c3 c4 w_128 d0 d1 d2 w_148 w_150
    wp_steps
    refine SepWP.fold (Entails.of_eq (hrk_cells (sf_1.readReg64 (.gpr 0#5))).symm)
      (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (by
      have h := (hrk_cells (s0.sp - 656#64)).symm
      simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
      exact h)) (by sep_focus) ?_
    refine SepWP.fold (cells4_sub768_merge s0.sp _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (memRegion_160_sub5024 s0.sp)) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (by
      have h := CryptoVerification.Cli.E2E.V1.bobHead144V1_eq_pointsToBytes (s0.sp - 488#64) localIkBoxPtr remoteIkBoxPtr
        (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
      simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
      exact h)) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (by
      have h := post100_pack (s0.sp - 488#64) pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
      simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
      exact h)) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hφ_ws : spkBPk.length = 32 ∧ spkBSk.length = 32 ∧ ck.length = 32 ∧
        (CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
          spqrCap spqrBufPtr spqrLen).length = 144 ∧
        (unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2).length = 100 :=
      ⟨hspkPk_len, hspkSk_len, hck_len, CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1_length _ _ _ _ _ _ _,
        by simp [unpack32]⟩
    refine SepWPp.call_frame (x :=
      ⟨outPtr, s0.sp - 488#64, rkp, spkBPk, spkBSk, s0.sp - 624#64, ck, 0#32,
        CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
          spqrCap spqrBufPtr spqrLen,
        unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2⟩) hwithSender
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := entry + 564#64) (by wp_norm_lhs)
      (by
        conv =>
          lhs
          dsimp only [withSenderChainNoneSpec]
          simp only [arm64_norm, hspm3, hcs4_19, hcs3_19, hcs2_19, hx19,
            hcs4_20, hcs3_20, hcs2_20, hx20, Initiator.bv_sub_add_lit', BitVec.reduceSub])
      hφ_ws
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ R hm => by
        dsimp only [withSenderChainNoneSpec, rustPanicOnOom] at hm
        simpa only [sepConj_assoc] using
          allowPanic_frame (fun h => CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_trace_eq (s0 :=
          s0) (by simp only [*, arm64_norm]) h) hm)
      (fun sm4 hpcm4 hrunm4 hspm4 hcsm4 => ?_)
    simp only [*, arm64_norm] at hspm4
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm4
    rcases hcsm4 with ⟨hcs5_19, hcs5_20, hcs5_21, hcs5_22, hcs5_23, hcs5_24, hcs5_25, hcs5_26,
      hcs5_27, hcs5_28, hcs5_29, hcs5_vregs⟩
    simp only [*, arm64_norm]
      at hcs5_19 hcs5_20 hcs5_21 hcs5_22 hcs5_23 hcs5_24 hcs5_25 hcs5_26 hcs5_27 hcs5_28 hcs5_29 hcs5_vregs
    conv =>
      arg 4
      dsimp only [withSenderChainNoneSpec]
      simp only [arm64_norm, hspm3, Initiator.bv_sub_add_lit', BitVec.reduceSub,
        sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun ratchetPubBoxPtr =>
      SepWPp.exists_elim fun ratchetPrivBoxPtr =>
      SepWPp.exists_elim fun chainKeyBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr6, hne_rPub, hne_rPriv, hne_ck⟩ => ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.fold (Entails.of_eq (CryptoVerification.Cli.E2E.V1.bobSession344V1_pack outPtr
      localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
      spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2))
      (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (by
      have h := CryptoVerification.Cli.E2E.V1.bobSession344V1_pack (s0.sp - 488#64)
        localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
        spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
      simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
      exact h)) (by sep_focus) ?_
    have h344_weaken :
        ((s0.sp - 488#64) ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr
          (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
          ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ⊢
        memRegion (s0.sp - 488#64) 344 := by
      have h := pointsToBytes_entails_memRegion (s0.sp - 488#64)
        (CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5))
          baseKeyBoxPtr spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr
          chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2)
      rwa [CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1_length] at h
    refine SepWP.fold h344_weaken (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_entry_some_merge s0.sp)) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨localIkBoxPtr, remoteIkBoxPtr, sf_1.readReg64 (.gpr 0#5), baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hne_localIk, hne_remoteIk, hoom1, hne_baseKey,
      hne_rPub, hne_rPriv, hne_ck,
      Entails.of_eq (by ac_rfl),
      by wp_norm_goal, by wp_norm_goal, by simp only [*, arm64_norm],
      by simp only [*, arm64_norm], by simp only [*, arm64_norm]⟩

private def _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameRest (sp0 : BitVec 64) (pq ck : SignalPqxdh.Bytes) : SepProp :=
  ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ∗
  ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ∗ ((sp0 - 672#64) ↦₃₂ 0#32) ∗
  memRegion (sp0 - 668#64) 12 ∗ ((sp0 - 592#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 588#64) 12 ∗
  memRegion (sp0 - 544#64) 56 ∗
  ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
  ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameAtSpqr_entails (sp0 : BitVec 64) (rk pq ck : SignalPqxdh.Bytes)
    (hrk : rk.length = 32) :
    CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr sp0 rk pq ck ⊢
      memRegion (sp0 - 768#64) 32 ∗ CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameRest sp0 pq ck := by
  unfold CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameRest
  have hlen : (bytesToBv8 rk).length = 32 := by simp [bytesToBv8, hrk]
  have hm : ((sp0 - 768#64) ↦ₛ bytesToBv8 rk) ⊢ memRegion (sp0 - 768#64) 32 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (sp0 - 768#64) (bytesToBv8 rk)
  exact sepConj_mono_left hm

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_sub488_merge (sp0 : BitVec 64) (pq ck : SignalPqxdh.Bytes)
    (hpq : pq.length = 32) (hck : ck.length = 32) :
    paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
    ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
    ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288 ⊢
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 := by
  have hpq_len : (bytesToBv8 pq).length = 32 := by simp [bytesToBv8, hpq]
  have hck_len : (bytesToBv8 ck).length = 32 := by simp [bytesToBv8, hck]
  have h104 :
      paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
      ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
      ((sp0 - 388#64) ↦₃₂ 0#32) ⊢ memRegion (sp0 - 488#64) 104 := by
    unfold paramsAt CryptoVerification.Cli.E2E.V1.bobSpqrParams
    simp only [hpq_len, Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    rw [ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 8) (k := 96)
        (b' := sp0 - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 480#64) (n := 8) (k := 88)
        (b' := sp0 - 472#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 472#64) (n := 4) (k := 84)
        (b' := sp0 - 468#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 468#64) (n := 4) (k := 80)
        (b' := sp0 - 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 464#64) (n := 4) (k := 76)
        (b' := sp0 - 460#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 460#64) (n := 4) (k := 72)
        (b' := sp0 - 456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 456#64) (n := 4) (k := 68)
        (b' := sp0 - 452#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 452#64) (n := 32) (k := 36)
        (b' := sp0 - 420#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 420#64) (n := 32) (k := 4)
        (b' := sp0 - 388#64) rfl (by bv_omega) (by decide)]
    have hm_pq : ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ⊢ memRegion (sp0 - 452#64) 32 := by
      rw [← hpq_len]; exact pointsToBytes_entails_memRegion (sp0 - 452#64) (bytesToBv8 pq)
    have hm_ck : ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ⊢ memRegion (sp0 - 420#64) 32 := by
      rw [← hck_len]; exact pointsToBytes_entails_memRegion (sp0 - 420#64) (bytesToBv8 ck)
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono (pointsTo32_entails_memRegion _ _)
              (sepConj_mono (pointsTo32_entails_memRegion _ _)
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono hm_pq
                    (sepConj_mono hm_ck
                      (pointsTo32_entails_memRegion _ _)))))))))
  have hsplit :
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 =
      memRegion (sp0 - 488#64) 104 ∗ memRegion (sp0 - 384#64) 288 := by
    rw [(ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 344) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 104) (k := 288)
        (b' := sp0 - 384#64) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  have hrearr :
      paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
      ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
      ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288 =
      (paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
       ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
       ((sp0 - 388#64) ↦₃₂ 0#32)) ∗ memRegion (sp0 - 384#64) 288 := by ac_rfl
  rw [hrearr]
  exact sepConj_mono_left h104

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_sub768_merge_280 (sp0 : BitVec 64) (rk pq ck : SignalPqxdh.Bytes)
    (hrk : rk.length = 32) (hpq : pq.length = 32) (hck : ck.length = 32) :
    memRegion (sp0 - 768#64) 32 ∗
    ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ∗
    ((sp0 - 672#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 668#64) 12 ∗
    ((sp0 - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((sp0 - 624#64) ↦ₛ bytesToBv8 ck) ∗
    ((sp0 - 592#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 588#64) 12 ∗
    ((sp0 - 576#64) ↦ₛ bytesToBv8 pq) ∗ memRegion (sp0 - 544#64) 56 ⊢
      memRegion (sp0 - 768#64) 280 := by
  have hrk_len : (bytesToBv8 rk).length = 32 := by simp [bytesToBv8, hrk]
  have hpq_len : (bytesToBv8 pq).length = 32 := by simp [bytesToBv8, hpq]
  have hck_len : (bytesToBv8 ck).length = 32 := by simp [bytesToBv8, hck]
  rw [ProofLib.memRegion_split' (b := sp0 - 768#64) (n := 32) (k := 248)
      (b' := sp0 - 736#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 736#64) (n := 32) (k := 216)
      (b' := sp0 - 704#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 704#64) (n := 32) (k := 184)
      (b' := sp0 - 672#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 672#64) (n := 4) (k := 180)
      (b' := sp0 - 668#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 668#64) (n := 12) (k := 168)
      (b' := sp0 - 656#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 656#64) (n := 32) (k := 136)
      (b' := sp0 - 624#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 624#64) (n := 32) (k := 104)
      (b' := sp0 - 592#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 592#64) (n := 4) (k := 100)
      (b' := sp0 - 588#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 588#64) (n := 12) (k := 88)
      (b' := sp0 - 576#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 576#64) (n := 32) (k := 56)
      (b' := sp0 - 544#64) rfl (by bv_omega) (by decide)]
  have hm_pq736 : ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ⊢ memRegion (sp0 - 736#64) 32 := by
    rw [← hpq_len]; exact pointsToBytes_entails_memRegion (sp0 - 736#64) (bytesToBv8 pq)
  have hm_ck704 : ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ⊢ memRegion (sp0 - 704#64) 32 := by
    rw [← hck_len]; exact pointsToBytes_entails_memRegion (sp0 - 704#64) (bytesToBv8 ck)
  have hm_rk656 : ((sp0 - 656#64) ↦ₛ bytesToBv8 rk) ⊢ memRegion (sp0 - 656#64) 32 := by
    rw [← hrk_len]; exact pointsToBytes_entails_memRegion (sp0 - 656#64) (bytesToBv8 rk)
  have hm_ck624 : ((sp0 - 624#64) ↦ₛ bytesToBv8 ck) ⊢ memRegion (sp0 - 624#64) 32 := by
    rw [← hck_len]; exact pointsToBytes_entails_memRegion (sp0 - 624#64) (bytesToBv8 ck)
  have hm_pq576 : ((sp0 - 576#64) ↦ₛ bytesToBv8 pq) ⊢ memRegion (sp0 - 576#64) 32 := by
    rw [← hpq_len]; exact pointsToBytes_entails_memRegion (sp0 - 576#64) (bytesToBv8 pq)
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono hm_pq736
      (sepConj_mono hm_ck704
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono hm_rk656
              (sepConj_mono hm_ck624
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono (Entails.refl _)
                    (sepConj_mono hm_pq576
                      (Entails.refl _))))))))))

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_stack_final_eq (sp0 : BitVec 64) :
    memRegion (sp0 - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
    stackAt (sp0 - 768#64) Initiator.pqxdhEntryStack ∗
    memRegion (sp0 - 768#64) 280 ∗
    memRegion (sp0 - 488#64) 344 ∗
    memRegion (sp0 - 144#64) 48 ∗
    memRegion (sp0 - 96#64) 96 =
      stackAt sp0 (stageP2bStack + 0x700) := by
  have hsplit :
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 =
      memRegion (sp0 - 488#64) 104 ∗ memRegion (sp0 - 384#64) 288 := by
    rw [(ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 344) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 104) (k := 288)
        (b' := sp0 - 384#64) rfl (by bv_omega) (by decide)]
  rw [CryptoVerification.Cli.E2E.V1.bobV1_stack_extra sp0, stackAt_initBob_entry sp0,
    ← (ProofLib.memRegion_cells (sp0 - 96#64) 12 (by decide) :
      memRegion (sp0 - 96#64) 96 = cells (sp0 - 96#64) 12),
    ← sepConj_assoc (memRegion (sp0 - 488#64) 344), hsplit]
  ac_rfl

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_bind_loaded {prog : Program} {img : Obj.Image} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (h1 : SepWPp prog mid s P Qm Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Qm sm Pm → SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  unfold SepWPp at h1 ⊢
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | hpan⟩
  · rcases h2 sm Pm hpcm hrunm (hF.of_keepsFrozen hsteps.keepsFrozen)
      (hsteps.symtab_eq.trans hsym) hQ R hmm (hsteps.codeLoaded hL) with ⟨sf, hsteps', hout⟩
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_seq {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Qm Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm → SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  unfold SepWPp at h1 ⊢
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | hpan⟩
  · rcases h2 sm Pm hpcm hrunm hQ R hmm (hsteps.codeLoaded hL) with ⟨sf, hsteps', hout⟩
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩

theorem _root_.CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_ext_trap_of_accept {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {C : Crypto}
    {absHooks ext : String → Option (State → State)}
    (hWF : StructuralPrims P) (hH : ResponderCore.PqxdhHookContracts P A img absHooks)
    (haccept_sub : subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpec P A img))
    (hTraps : ProofLib.Variant.TrapsOnly (trTrapProgAt img.base C absHooks)
      (tripleRatchetProgAtExt img.base ext))
    (hinit : InitialStateOkX img A F ext)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (h_2 : img.FrozenLoaded s0) (h_1 : s0.symtab = img.symtab)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
    (hsp_align : s0.spAligned = true)
    (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr
              (BitVec.ofNat 64 (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)).length)
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr
              (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)) ∗
            bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
              inp ikBPk spkBPk 0#8 ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
            A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
            A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
            (logFilterAddr img ↦₆₄ 0#64) ∗
            stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (BobPanicOom s0) := by
  have hfn_ib :
      (trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym =
      (tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym :=
    hTraps.fnAddr _
  have hfn_is :
      (trTrapProgAt img.base C absHooks).fnAddr "spqr::initial_state" =
      (tripleRatchetProgAtExt img.base ext).fnAddr "spqr::initial_state" :=
    hTraps.fnAddr _
  have ⟨hlen_rk, hlen_pq, hlen_ck⟩ := acceptKeys_some_lengths hWF hacc
  have ⟨_, _, hlen_spkSk, _, _, _, _, hlen_ikA, hlen_ekA, _⟩ := h_9
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned] using hsp_align
  let Frame1 : SepProp :=
    memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame
  have hpb3 := SepWPp.of_trapsOnly hTraps
    (CryptoVerification.Cli.E2E.V1.initBob_to_spqr_full_v1_trap_of_accept hWF hH haccept_sub s0 inp ikBPk spkBPk
      argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame1
      h_2 h_1 hrun (by rw [hfn_ib]; exact hpc) hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 _h_10 _h_11 hacc)
  rw [hfn_is] at hpb3
  refine CryptoVerification.Cli.E2E.V1.wp6pb4b_bind_loaded h_2 h_1
    (SepWPp.weaken_pre
      (Entails.of_eq (by
        dsimp only [Frame1]
        rw [CryptoVerification.Cli.E2E.V1.bobV1_stack_extra s0.sp]
        ac_rfl))
      hpb3) ?_
  intro s1 P1 hpc1 hrun1 hF1 hsym1
    ⟨hent1, _, hsp1, hx0_1, hx8_1, hx19_1, hx20_1, hx21_1, hx23_1, hx27_1, hx30_1, htr1, hvregs1⟩
  rw [hfn_ib] at hx30_1
  let FrameCall : SepProp :=
    ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
    ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
    (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
    ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
    CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameRest s0.sp drKey.pqrKey drKey.chainKey ∗
    (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
    pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
    ((argPtr + 297#64) ↦₈ 0#8) ∗
    memRegion outPtr 344 ∗ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗ Frame
  have hent1_call : P1 ⊢
      (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
       ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
       memRegion (s0.sp - 768#64) 32 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       A.pool ∗ stackAt s1.sp initialStateStack) ∗ FrameCall := by
    refine Entails.trans hent1 ?_
    dsimp only [Frame1, FrameCall, logFilterAddr]
    rw [CryptoVerification.Cli.E2E.V1.bobSpqrCutCells_eq_paramsAt s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey
      drKey.chainKey spkBPk inp.spkBSk hlen_pq, hsp1]
    have hrearr :
        (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
         ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
         ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
         ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
         (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
         ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk)) ∗
        CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
        (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
        pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
        ((argPtr + 297#64) ↦₈ 0#8) ∗
        memRegion outPtr 344 ∗ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗
        (memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame) =
        CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
        (memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
         stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack) ∗
        (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
         ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
         ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗
         ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
         ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
         (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
         ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
         pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
         ((argPtr + 297#64) ↦₈ 0#8) ∗
         memRegion outPtr 344 ∗ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗ Frame) := by ac_rfl
    rw [hrearr, CryptoVerification.Cli.E2E.V1.bobV1_stack_join s0.sp]
    exact Entails.trans
      (sepConj_mono_left
        (CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameAtSpqr_entails s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey hlen_rk))
      (Entails.of_eq (by ac_rfl))
  refine SepWPp.weaken_pre hent1_call ?_
  let gx : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost :=
    ⟨s0.sp - 488#64, s0.sp - 768#64, s0.sp - 576#64, CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey⟩
  have hsp1_align : s1.spAligned = true := by
    simp only [State.spAligned, hsp1]
    revert hsp0_align; bv_bits
  refine SepWPp.call hinit (x := gx) (F := FrameCall)
    hpc1 hrun1 hsp1_align hx30_1
    (fun R hm => ?_)
    (fun sf code R' _ hex => ?_)
    (fun sf _ R hm => ?_)
    (fun s2 hpc2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecX,
      Spec.inImage, CryptoVerification.SpqrV1.Top.InitialState.initialStateSpec,
      CryptoVerification.Cli.E2E.V1.bobSpqrParams, gx]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    refine ⟨⟨hF1, hsym1⟩, ⟨hx0_1, hx8_1, hpqr_ne, ?_⟩, hm⟩
    simp [bytesToBv8, hlen_pq]
  · dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecX,
      Spec.inImage, CryptoVerification.SpqrV1.Top.InitialState.initialStateSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact hex.1
  · dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecX,
      Spec.inImage, CryptoVerification.SpqrV1.Top.InitialState.initialStateSpec,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateOnPanic] at hm
    exact ProofLib.allowPanic_frame
      (φ := allocFailedIn s1 sf ∧ s1.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, hsub⟩ => by
        unfold allocFailedIn at haf ⊢
        rw [htr1] at haf hsub
        exact ⟨haf, hsub⟩) hm
  · dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecX,
      Spec.inImage, CryptoVerification.SpqrV1.Top.InitialState.initialStateSpec,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateResultAt,
      RustHeap.vecU8, gx]
    rw [hsp1, sepConj_assoc]
    refine SepWPp.pure_left fun htr2 => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by
      simp only [CryptoVerification.Cli.E2E.V1.vecU8At_eq_header_bobBuf, vecHeader,
        sepExists_sepConj_left, sepExists_sepConj_right,
        Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      rfl)) ?_
    refine SepWPp.exists_elim fun spqrCap => SepWPp.exists_elim fun spqrBufPtr => ?_
    obtain ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, _, _, _, hx27_2, _, _, hvregs2⟩ := hcs2
    let v := initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)
    let spqrLen := BitVec.ofNat 64 v.length
    let Frame2 : SepProp :=
      CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
      ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
      ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
      ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
      memRegion (s0.sp - 588#64) 12 ∗
      ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
      memRegion (s0.sp - 544#64) 56 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
      ((argPtr + 297#64) ↦₈ 0#8) ∗
      CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame
    have hent2 :
        paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
        ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
        ((s0.sp - 768#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
        ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗
        ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
        CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool ∗ stackAt (s0.sp - 768#64) initialStateStack ∗ FrameCall ⊢
        ((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
        ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
        ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
        ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
        ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
        memRegion (s0.sp - 488#64) 344 ∗
        (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
        ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
        (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
        ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
        memRegion outPtr 344 ∗
        stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗ Frame2 := by
      dsimp only [FrameCall, Frame2, CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameRest]
      rw [← CryptoVerification.Cli.E2E.V1.bobV1_stack_join s0.sp, pqxdhAcceptFieldsAt_split argPtr pqskPtr ctSlicePtr ctBufPtr inp]
      have hrearr :
          paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
          ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
          ((s0.sp - 768#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
          ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗
          ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
          CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
          ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          A.pool ∗
          (memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
           stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack) ∗
          (((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
           ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
           ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
           (((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
            ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗ ((s0.sp - 672#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 668#64) 12 ∗ ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 588#64) 12 ∗ memRegion (s0.sp - 544#64) 56 ∗
            ((s0.sp - 452#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
            ((s0.sp - 420#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
            ((s0.sp - 388#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 384#64) 288) ∗
           (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
           (((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
            ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
            pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp) ∗
           ((argPtr + 297#64) ↦₈ 0#8) ∗
           memRegion outPtr 344 ∗ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗ Frame) =
          (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
           ((s0.sp - 452#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 420#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 388#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 384#64) 288) ∗
          (((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
           ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
           ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
           ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
           (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
           ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
           (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
           ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
           memRegion outPtr 344 ∗
           stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗
           CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
           ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
           memRegion (s0.sp - 588#64) 12 ∗
           ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
           memRegion (s0.sp - 544#64) 56 ∗
           pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
           ((argPtr + 297#64) ↦₈ 0#8) ∗
           CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
           ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame) := by
        ac_rfl
      rw [hrearr]
      exact Entails.trans
        (sepConj_mono_left (CryptoVerification.Cli.E2E.V1.wp6pb4b_sub488_merge s0.sp drKey.pqrKey drKey.chainKey hlen_pq hlen_ck))
        (Entails.of_eq (by ac_rfl))
    have hpb1 := SepWPp.of_trapsOnly hTraps
      (CryptoVerification.Cli.E2E.V1.initBob_session_build_v1_trap hH.alloc s0 s2 argPtr ratchetKeyPairPtr outPtr
        spqrCap spqrBufPtr spqrLen
        ikBPk inp.hdr.ikAPk inp.hdr.ekAPk spkBPk inp.spkBSk drKey.rootKey drKey.chainKey Frame2
        _h_10 hlen_ikA hlen_ekA _h_11 hlen_spkSk hlen_rk hlen_ck
        hsp0_align hrun2 (by rw [hfn_ib]; exact hpc2) (hsp2.trans hsp1)
        (hx19_2.trans hx19_1) (hx20_2.trans hx20_1) (hx21_2.trans hx21_1)
        (hx23_2.trans hx23_1) (hx27_2.trans hx27_1) (htr2.trans htr1) (hvregs2.trans hvregs1))
    rw [hfn_ib] at hpb1
    refine CryptoVerification.Cli.E2E.V1.wp6pb4b_seq
      (SepWPp.weaken_pre hent2 hpb1) ?_
    intro s3 P3 hpc3 hrun3
      ⟨localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
       ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr,
       pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
       hlik, hrik, hrk_box, hbk, hrp, hrpriv, hck_box,
       hent3, _, _, hsp3, htr3, hvregs3⟩
    let sessBytes := CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
      spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
    let FrameEpi : SepProp :=
      (outPtr ↦ₛ sessBytes) ∗
      CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
      bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
      (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
      (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
      A.live remoteIkBoxPtr 33 1 ∗
      (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
      (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
      A.live baseKeyBoxPtr 33 1 ∗
      (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
      A.live ratchetPubBoxPtr 33 1 ∗
      (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
      (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
      (logFilterAddr img ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
      stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗
      memRegion (s0.sp - 768#64) 280 ∗
      memRegion (s0.sp - 488#64) 344 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      A.pool ∗ Frame
    have hent3_epi : P3 ⊢ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗ FrameEpi := by
      refine Entails.trans hent3 ?_
      dsimp only [Frame2, FrameEpi, sessBytes, bobParamsFieldsAt, CryptoVerification.Cli.E2E.V1.bobSpqrParams, logFilterAddr]
      rw [pqxdhAcceptFieldsAt_split argPtr pqskPtr ctSlicePtr ctBufPtr inp]
      have hrearr :
          (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
            spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
            pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
          memRegion (s0.sp - 768#64) 32 ∗
          ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
          ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
          ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
          memRegion (s0.sp - 488#64) 344 ∗
          (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
          ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
          (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
          ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
          (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
          (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
          A.live remoteIkBoxPtr 33 1 ∗
          (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
          (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
          A.live baseKeyBoxPtr 33 1 ∗
          (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
          A.live ratchetPubBoxPtr 33 1 ∗
          (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
          (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
          stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗
          (CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
           ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
           memRegion (s0.sp - 588#64) 12 ∗
           ((s0.sp - 576#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           memRegion (s0.sp - 544#64) 56 ∗
           memRegion (s0.sp - 144#64) 48 ∗
           pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
           ((argPtr + 297#64) ↦₈ 0#8) ∗
           CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
           ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame) =
          (memRegion (s0.sp - 768#64) 32 ∗
           ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
           ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
           ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 592#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 588#64) 12 ∗
           ((s0.sp - 576#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           memRegion (s0.sp - 544#64) 56) ∗
          (CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
           (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
             spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
             pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
           CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
           ((argPtr ↦ₛ bytesToBv8 ikBPk) ∗
            (((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
             ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
             pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp) ∗
            ((argPtr + 297#64) ↦₈ 0#8) ∗
            (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
            ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk)) ∗
           (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
           (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
           A.live remoteIkBoxPtr 33 1 ∗
           (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
           (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
           A.live baseKeyBoxPtr 33 1 ∗
           (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
           A.live ratchetPubBoxPtr 33 1 ∗
           (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
           (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
           ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
           stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗
           memRegion (s0.sp - 488#64) 344 ∗
           memRegion (s0.sp - 144#64) 48 ∗
           A.pool ∗ Frame) := by ac_rfl
      rw [hrearr]
      exact Entails.trans
        (sepConj_mono_left
          (CryptoVerification.Cli.E2E.V1.wp6pb4b_sub768_merge_280 s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey
            hlen_rk hlen_pq hlen_ck))
        (Entails.of_eq (by ac_rfl))
    have hpb2 := SepWP.of_trapsOnly hTraps
      (CryptoVerification.Cli.E2E.V1.initBob_epilogue_v1_trap s0 s3 FrameEpi hsp0_align hrun3
        (by rw [hfn_ib]; exact hpc3) hsp3 hvregs3)
    refine SepWPp.of_sepWP_ret
      (SepWP.weaken_pre hent3_epi
        (SepWP.mono
          hpb2
          (fun sf Pf _ _ ⟨hPf, hrun_f, hpc_f, hsp_f, hcs_f, htr_f⟩ => ?_)))
    refine ⟨localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hlik, hrik, hrk_box, hbk, hrp, hrpriv, hck_box,
      Entails.trans hPf (Entails.of_eq (by
        dsimp only [FrameEpi, sessBytes, spqrLen, v]
        rw [← CryptoVerification.Cli.E2E.V1.wp6pb4b_stack_final_eq s0.sp]
        ac_rfl)),
      hrun_f, hpc_f, hsp_f, hcs_f, htr_f.trans htr3⟩

theorem _root_.CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_ext_trap {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {C : Crypto}
    {absHooks ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : ResponderCore.PqxdhHookContracts P A img absHooks)
    (hP : PrimitivesMatchCrypto P C)
    (hTraps : ProofLib.Variant.TrapsOnly (trTrapProgAt img.base C absHooks)
      (tripleRatchetProgAtExt img.base ext))
    (hinit : InitialStateOkX img A F ext)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (h_2 : img.FrozenLoaded s0) (h_1 : s0.symtab = img.symtab)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
    (hsp_align : s0.spAligned = true)
    (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr
              (BitVec.ofNat 64 (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)).length)
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr
              (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)) ∗
            bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
              inp ikBPk spkBPk 0#8 ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
            A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
            A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
            (logFilterAddr img ↦₆₄ 0#64) ∗
            stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (BobPanicOom s0) :=
  CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_ext_trap_of_accept hWF hH
    (pqxdhAccept_opt_fields_base_ok_trap himg hWF hH
      (pqxdhHkdfExtract_ok_trap hP himg) (pqxdhHkdfExpandMultiInfo_ok_trap hP)
      (pqxdhCalculateAgreement_ok_trap hP himg hH.alloc))
    hTraps hinit
    s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    h_2 h_1 hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 _h_10 _h_11 hacc

theorem _root_.CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_trap {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {C : Crypto}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : ResponderCore.PqxdhHookContracts P A img absHooks)
    (hP : PrimitivesMatchCrypto P C)
    (hinit : InitialStateOkX img A F (trTrapExterns C absHooks))
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (h_2 : img.FrozenLoaded s0) (h_1 : s0.symtab = img.symtab)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym)
    (hsp_align : s0.spAligned = true)
    (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (trTrapProgAt img.base C absHooks)
      (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr
              (BitVec.ofNat 64 (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)).length)
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr
              (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)) ∗
            bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
              inp ikBPk spkBPk 0#8 ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
            A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
            A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
            (logFilterAddr img ↦₆₄ 0#64) ∗
            stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (BobPanicOom s0) :=
  CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_ext_trap himg hWF hH hP
    (ProofLib.Variant.TrapsOnly.refl _) hinit
    s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    h_2 h_1 hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 _h_10 _h_11 hacc

/-- End-to-end specification of `initialize_bob_session` at SPQR V1 when
`Model.acceptKeys P inp = some drKey` (`sameAccountByte = 0`), producing `bobSession344Bv8V1` at
`outPtr` with SPQR state `initialStateValue F (bobSpqrParams drKey.pqrKey)` and heap buffer
`bobSpqrVecBuf` at stack budget `stageP2bStack + 0x700`. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1 {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : ResponderCore.PqxdhHookContracts P A img absHooks)
    (hP : PrimitivesMatchCrypto P C)
    (hinit : InitialStateOkX img A F (tripleRatchetExterns C ctl absHooks))
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (h_2 : img.FrozenLoaded s0) (h_1 : s0.symtab = img.symtab)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym)
    (hsp_align : s0.spAligned = true)
    (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (tripleRatchetProgAt img.base C ctl absHooks)
      (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr
              (BitVec.ofNat 64 (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)).length)
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr
              (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)) ∗
            bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
              inp ikBPk spkBPk 0#8 ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
            A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
            A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
            (logFilterAddr img ↦₆₄ 0#64) ∗
            stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (BobPanicOom s0) :=
  CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_ext_trap himg hWF hH hP (trapsOnly_trTrap_kit img.base C ctl absHooks) hinit
    s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    h_2 h_1 hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 _h_10 _h_11 hacc

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_stack_final_ext_eq (sp0 : BitVec 64) :
    memRegion (sp0 - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 16384 ∗
    stackAt (sp0 - 768#64) Initiator.pqxdhEntryStack ∗
    memRegion (sp0 - 768#64) 280 ∗
    memRegion (sp0 - 488#64) 344 ∗
    memRegion (sp0 - 144#64) 48 ∗
    memRegion (sp0 - 96#64) 96 =
      stackAt sp0 (768 + Initiator.pqxdhEntryStackExt) := by
  have hsplit :
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 =
      memRegion (sp0 - 488#64) 104 ∗ memRegion (sp0 - 384#64) 288 := by
    rw [(ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 344) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 104) (k := 288)
        (b' := sp0 - 384#64) rfl (by bv_omega) (by decide)]
  rw [CryptoVerification.Cli.E2E.V1.bobV1_stack_ext_split sp0, stackAt_initBob_entry sp0,
    ← (ProofLib.memRegion_cells (sp0 - 96#64) 12 (by decide) :
      memRegion (sp0 - 96#64) 96 = cells (sp0 - 96#64) 12),
    ← sepConj_assoc (memRegion (sp0 - 488#64) 344), hsplit]
  ac_rfl

theorem _root_.CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_ext
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : ResponderCore.PqxdhHookContractsExt P A img ext)
    (hext : Initiator.PqxdhHkdfExtractOk_ext P img ext)
    (hexp : Initiator.PqxdhHkdfExpandMultiInfoOk_ext P img ext)
    (hag : ResponderCore.PqxdhCalculateAgreementOkExt P A img ext)
    (hinit : InitialStateOkXExt img A F ext)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (h_2 : img.FrozenLoaded s0) (h_1 : s0.symtab = img.symtab)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
    (hsp_align : s0.spAligned = true)
    (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + Initiator.pqxdhEntryStackExt) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr
              (BitVec.ofNat 64 (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)).length)
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr
              (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)) ∗
            bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
              inp ikBPk spkBPk 0#8 ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
            A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
            A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
            (logFilterAddr img ↦₆₄ 0#64) ∗
            stackAt s0.sp (768 + Initiator.pqxdhEntryStackExt) ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (BobPanicOom s0) := by
  have ⟨hlen_rk, hlen_pq, hlen_ck⟩ := acceptKeys_some_lengths hWF hacc
  have ⟨_, _, hlen_spkSk, _, _, _, _, hlen_ikA, hlen_ekA, _⟩ := h_9
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned] using hsp_align
  have hpb3 :=
    CryptoVerification.Cli.E2E.V1.initBob_to_spqr_full_v1_ext himg hWF hH hext hexp hag
      s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
      h_2 h_1 hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 _h_10 _h_11 hacc
  refine CryptoVerification.Cli.E2E.V1.wp6pb4b_bind_loaded h_2 h_1 hpb3 ?_
  intro s1 P1 hpc1 hrun1 hF1 hsym1
    ⟨hent1, _, hsp1, hx0_1, hx8_1, hx19_1, hx20_1, hx21_1, hx23_1, hx27_1, hx30_1, htr1, hvregs1⟩
  let FrameCall : SepProp :=
    ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
    ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
    (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
    ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
    CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameRest s0.sp drKey.pqrKey drKey.chainKey ∗
    (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
    pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
    ((argPtr + 297#64) ↦₈ 0#8) ∗
    memRegion outPtr 344 ∗ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
    memRegion (s0.sp - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 13360 ∗ Frame
  have hent1_call : P1 ⊢
      (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
       ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
       memRegion (s0.sp - 768#64) 32 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       A.pool ∗ stackAt s1.sp initialStateStackExt) ∗ FrameCall := by
    refine Entails.trans hent1 ?_
    dsimp only [FrameCall, logFilterAddr]
    rw [CryptoVerification.Cli.E2E.V1.bobSpqrCutCells_eq_paramsAt s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey
      drKey.chainKey spkBPk inp.spkBSk hlen_pq,
      CryptoVerification.Cli.E2E.V1.bobV1_entry_ext_to_initialStateExt s0.sp, hsp1]
    have hrearr :
        (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
         ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
         ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
         ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
         (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
         ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk)) ∗
        CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
        (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
        pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
        ((argPtr + 297#64) ↦₈ 0#8) ∗
        memRegion outPtr 344 ∗ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        (memRegion (s0.sp - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 13360 ∗
         stackAt (s0.sp - 768#64) initialStateStackExt) ∗
        A.pool ∗ Frame =
        CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
        (stackAt (s0.sp - 768#64) initialStateStackExt ∗
         paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
         ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
         ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗
         ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
         ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
         (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
         ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
         pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
         ((argPtr + 297#64) ↦₈ 0#8) ∗
         memRegion outPtr 344 ∗ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
         memRegion (s0.sp - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 13360 ∗ Frame) := by ac_rfl
    rw [hrearr]
    exact Entails.trans
      (sepConj_mono_left
        (CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameAtSpqr_entails s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey hlen_rk))
      (Entails.of_eq (by ac_rfl))
  refine SepWPp.weaken_pre hent1_call ?_
  let gx : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost :=
    ⟨s0.sp - 488#64, s0.sp - 768#64, s0.sp - 576#64, CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey⟩
  have hsp1_align : s1.spAligned = true := by
    simp only [State.spAligned, hsp1]
    revert hsp0_align; bv_bits
  refine SepWPp.call hinit (x := gx) (F := FrameCall)
    hpc1 hrun1 hsp1_align hx30_1
    (fun R hm => ?_)
    (fun sf code R' _ hex => ?_)
    (fun sf _ R hm => ?_)
    (fun s2 hpc2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecXExt,
      Spec.inImage, CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecExt,
      CryptoVerification.Cli.E2E.V1.bobSpqrParams, gx]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    refine ⟨⟨hF1, hsym1⟩, ⟨hx0_1, hx8_1, hpqr_ne, ?_⟩, hm⟩
    simp [bytesToBv8, hlen_pq]
  · dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecXExt,
      Spec.inImage, CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecExt] at hex
    rw [satisfies_pure_sepConj] at hex
    exact hex.1
  · dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecXExt,
      Spec.inImage, CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecExt,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateOnPanic] at hm
    exact ProofLib.allowPanic_frame
      (φ := allocFailedIn s1 sf ∧ s1.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, hsub⟩ => by
        unfold allocFailedIn at haf ⊢
        rw [htr1] at haf hsub
        exact ⟨haf, hsub⟩) hm
  · dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecXExt,
      Spec.inImage, CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecExt,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateResultAt,
      RustHeap.vecU8, gx]
    rw [hsp1, sepConj_assoc]
    refine SepWPp.pure_left fun htr2 => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by
      simp only [CryptoVerification.Cli.E2E.V1.vecU8At_eq_header_bobBuf, vecHeader,
        sepExists_sepConj_left, sepExists_sepConj_right,
        Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      rfl)) ?_
    refine SepWPp.exists_elim fun spqrCap => SepWPp.exists_elim fun spqrBufPtr => ?_
    obtain ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, _, _, _, hx27_2, _, _, hvregs2⟩ := hcs2
    let v := initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)
    let spqrLen := BitVec.ofNat 64 v.length
    let Frame2 : SepProp :=
      CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
      ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
      ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
      ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
      memRegion (s0.sp - 588#64) 12 ∗
      ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
      memRegion (s0.sp - 544#64) 56 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
      ((argPtr + 297#64) ↦₈ 0#8) ∗
      CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 16384 ∗ Frame
    have hstk_rejoin :
        stackAt (s0.sp - 768#64) initialStateStackExt ∗
          memRegion (s0.sp - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 13360 =
        memRegion (s0.sp - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 16384 ∗
          stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack := by
      rw [sepConj_comm, ← CryptoVerification.Cli.E2E.V1.bobV1_entry_ext_to_initialStateExt s0.sp,
        CryptoVerification.Cli.E2E.V1.bobV1_entry_ext_split s0.sp]
    have hent2 :
        paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
        ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
        ((s0.sp - 768#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
        ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗
        ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
        CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool ∗ stackAt (s0.sp - 768#64) initialStateStackExt ∗ FrameCall ⊢
        ((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
        ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
        ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
        ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
        ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
        memRegion (s0.sp - 488#64) 344 ∗
        (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
        ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
        (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
        ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
        memRegion outPtr 344 ∗
        stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗ Frame2 := by
      dsimp only [FrameCall, Frame2, CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameRest]
      rw [pqxdhAcceptFieldsAt_split argPtr pqskPtr ctSlicePtr ctBufPtr inp]
      have hrearr1 :
          paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
          ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
          ((s0.sp - 768#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
          ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗
          ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
          CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
          ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          A.pool ∗ stackAt (s0.sp - 768#64) initialStateStackExt ∗
          (((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
           ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
           ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
           (((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
            ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗ ((s0.sp - 672#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 668#64) 12 ∗ ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 588#64) 12 ∗ memRegion (s0.sp - 544#64) 56 ∗
            ((s0.sp - 452#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
            ((s0.sp - 420#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
            ((s0.sp - 388#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 384#64) 288) ∗
           (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
           (((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
            ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
            pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp) ∗
           ((argPtr + 297#64) ↦₈ 0#8) ∗
           memRegion outPtr 344 ∗ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 13360 ∗ Frame) =
          (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
           ((s0.sp - 452#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 420#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 388#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 384#64) 288) ∗
          (stackAt (s0.sp - 768#64) initialStateStackExt ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 13360) ∗
          (((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
           ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
           ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
           ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
           (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
           ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
           (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
           ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
           memRegion outPtr 344 ∗ A.pool ∗
           CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
           ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
           memRegion (s0.sp - 588#64) 12 ∗
           ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
           memRegion (s0.sp - 544#64) 56 ∗
           pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
           ((argPtr + 297#64) ↦₈ 0#8) ∗
           CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
           ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
           Frame) := by ac_rfl
      rw [hrearr1, hstk_rejoin]
      exact Entails.trans
        (sepConj_mono_left (CryptoVerification.Cli.E2E.V1.wp6pb4b_sub488_merge s0.sp drKey.pqrKey drKey.chainKey hlen_pq hlen_ck))
        (Entails.of_eq (by ac_rfl))
    have hM : Initiator.SessionMemHooks A ext := ⟨hH.shim, hH.alloc, hH.memcpy⟩
    have hpb1 :=
      CryptoVerification.Cli.E2E.V1.initBob_session_build_v1_ext (img := img) hM s0 s2 argPtr ratchetKeyPairPtr outPtr
        spqrCap spqrBufPtr spqrLen
        ikBPk inp.hdr.ikAPk inp.hdr.ekAPk spkBPk inp.spkBSk drKey.rootKey drKey.chainKey Frame2
        _h_10 hlen_ikA hlen_ekA _h_11 hlen_spkSk hlen_rk hlen_ck
        hsp0_align hrun2 hpc2 (hsp2.trans hsp1)
        (hx19_2.trans hx19_1) (hx20_2.trans hx20_1) (hx21_2.trans hx21_1)
        (hx23_2.trans hx23_1) (hx27_2.trans hx27_1) (htr2.trans htr1) (hvregs2.trans hvregs1)
    refine CryptoVerification.Cli.E2E.V1.wp6pb4b_seq
      (SepWPp.weaken_pre hent2 hpb1) ?_
    intro s3 P3 hpc3 hrun3
      ⟨localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
       ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr,
       pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
       hlik, hrik, hrk_box, hbk, hrp, hrpriv, hck_box,
       hent3, _, _, hsp3, htr3, hvregs3⟩
    let sessBytes := CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
      spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
    let FrameEpi : SepProp :=
      (outPtr ↦ₛ sessBytes) ∗
      CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
      bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
      (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
      (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
      A.live remoteIkBoxPtr 33 1 ∗
      (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
      (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
      A.live baseKeyBoxPtr 33 1 ∗
      (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
      A.live ratchetPubBoxPtr 33 1 ∗
      (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
      (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
      (logFilterAddr img ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 16384 ∗
      stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗
      memRegion (s0.sp - 768#64) 280 ∗
      memRegion (s0.sp - 488#64) 344 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      A.pool ∗ Frame
    have hent3_epi : P3 ⊢ CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗ FrameEpi := by
      refine Entails.trans hent3 ?_
      dsimp only [Frame2, FrameEpi, sessBytes, bobParamsFieldsAt, CryptoVerification.Cli.E2E.V1.bobSpqrParams, logFilterAddr]
      rw [pqxdhAcceptFieldsAt_split argPtr pqskPtr ctSlicePtr ctBufPtr inp]
      have hrearr :
          (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
            spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
            pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
          memRegion (s0.sp - 768#64) 32 ∗
          ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
          ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
          ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
          memRegion (s0.sp - 488#64) 344 ∗
          (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
          ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
          (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
          ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
          (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
          (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
          A.live remoteIkBoxPtr 33 1 ∗
          (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
          (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
          A.live baseKeyBoxPtr 33 1 ∗
          (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
          A.live ratchetPubBoxPtr 33 1 ∗
          (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
          (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
          stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗
          (CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
           ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
           memRegion (s0.sp - 588#64) 12 ∗
           ((s0.sp - 576#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           memRegion (s0.sp - 544#64) 56 ∗
           memRegion (s0.sp - 144#64) 48 ∗
           pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
           ((argPtr + 297#64) ↦₈ 0#8) ∗
           CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
           ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 16384 ∗ Frame) =
          (memRegion (s0.sp - 768#64) 32 ∗
           ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
           ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
           ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 592#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 588#64) 12 ∗
           ((s0.sp - 576#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           memRegion (s0.sp - 544#64) 56) ∗
          (CryptoVerification.Cli.E2E.V1.initBobSavedRegs s0.sp s0 ∗
           (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
             spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
             pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
           CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
           ((argPtr ↦ₛ bytesToBv8 ikBPk) ∗
            (((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
             ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
             pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp) ∗
            ((argPtr + 297#64) ↦₈ 0#8) ∗
            (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
            ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk)) ∗
           (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
           (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
           A.live remoteIkBoxPtr 33 1 ∗
           (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
           (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
           A.live baseKeyBoxPtr 33 1 ∗
           (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
           A.live ratchetPubBoxPtr 33 1 ∗
           (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
           (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
           ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 16384 ∗
           stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗
           memRegion (s0.sp - 488#64) 344 ∗
           memRegion (s0.sp - 144#64) 48 ∗
           A.pool ∗ Frame) := by ac_rfl
      rw [hrearr]
      exact Entails.trans
        (sepConj_mono_left
          (CryptoVerification.Cli.E2E.V1.wp6pb4b_sub768_merge_280 s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey
            hlen_rk hlen_pq hlen_ck))
        (Entails.of_eq (by ac_rfl))
    have hpb2 :=
      CryptoVerification.Cli.E2E.V1.initBob_epilogue_v1_ext (img := img) s0 s3 FrameEpi hsp0_align hrun3 hpc3 hsp3 hvregs3
    refine SepWPp.of_sepWP_ret
      (SepWP.weaken_pre hent3_epi
        (SepWP.mono
          hpb2
          (fun sf Pf _ _ ⟨hPf, hrun_f, hpc_f, hsp_f, hcs_f, htr_f⟩ => ?_)))
    refine ⟨localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hlik, hrik, hrk_box, hbk, hrp, hrpriv, hck_box,
      Entails.trans hPf (Entails.of_eq (by
        dsimp only [FrameEpi, sessBytes, spqrLen, v]
        rw [← CryptoVerification.Cli.E2E.V1.wp6pb4b_stack_final_ext_eq s0.sp]
        ac_rfl)),
      hrun_f, hpc_f, hsp_f, hcs_f, htr_f.trans htr3⟩

theorem _root_.CryptoVerification.Cli.E2E.V1.initialStateOkX_to_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (h : InitialStateOkX img A F ext) :
    InitialStateOkXExt img A F ext := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecX,
        CryptoVerification.SpqrV1.Top.InitialState.initialStateSpec, Spec.inImage] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecX,
        CryptoVerification.SpqrV1.Top.InitialState.initialStateSpec, Spec.inImage] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro x R s0 hpre
  have hsplit : stackAt s0.sp initialStateStackExt =
      memRegion (s0.sp - BitVec.ofNat 64 initialStateStackExt) 1232 ∗
        stackAt s0.sp initialStateStack := by
    have hs := CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom s0.sp
      initialStateStack 1232 (by decide)
    rwa [show initialStateStack + 1232 = initialStateStackExt by decide] at hs
  let F_stk : SepProp := memRegion (s0.sp - BitVec.ofNat 64 initialStateStackExt) 1232
  dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecXExt,
    CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecExt, Spec.inImage] at hpre
  rw [hsplit] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpure, hmem⟩
  refine ⟨x, F_stk ∗ R, ?_, fun sf hpost => ?_, fun sf hpan => ?_⟩
  · dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecX,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateSpec, Spec.inImage, F_stk]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecX,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateSpec,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecXExt,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecExt, Spec.inImage, F_stk] at hpost ⊢
    rw [hsplit]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩
  · dsimp only [CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecX,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateSpec,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecXExt,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecExt,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateOnPanic, Spec.inImage, F_stk] at hpan ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpan ⊢
    rcases hpan with ⟨hp, hmem_pan⟩
    exact ⟨hp, Satisfies.mono (Entails.trans
      (Entails.of_eq (show anyHeap ∗ (memRegion _ _ ∗ R) =
        (anyHeap ∗ memRegion _ _) ∗ R by ac_rfl))
      (sepConj_mono_left (ProofLib.entails_anyHeap _))) hmem_pan⟩

end CryptoVerification.E2E.V1
