/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
public import ProofLib.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Stage1Wire
import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
import VCVio.Prelude.Core

/-!
# Symbolic Encrypt Terms, Ghost Updates, and Faithfulness Steppers

Defines the symbolic `messageEncrypt` terms (`encWire`, `encMac`, `encMsg`, `encSt`), the fresh-wire
ghost updaters (`sendGhost`, `sendPendingGhost`), and `MatchedPrefix` / `ExplainsMoves` snoc lemmas
for `session_send_wire` moves.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.SendWire

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (TRState trMsgKeys trHonestWireMsg kdfCk)

/-- The serialized 36-byte `(aliceAddr || bobAddr)` pair produced by the PQXDH E2E harness:
`ALICE_NAME = "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b"` (ACI tag `0x00`, 16 UUID bytes, device `0x01`)
followed by `BOB_NAME = "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6"` (ACI tag `0x00`, 16 UUID bytes,
device `0x01`). -/
def pqHarnessAddrBytes : HwBytes :=
  [0x00#8, 0x8a#8, 0x6f#8, 0x1c#8, 0x2e#8, 0x3b#8, 0x4d#8, 0x4e#8, 0x5f#8,
   0x9a#8, 0x0b#8, 0x1c#8, 0x2d#8, 0x3e#8, 0x4f#8, 0x5a#8, 0x6b#8, 0x01#8,
   0x00#8, 0x5d#8, 0x3e#8, 0x2f#8, 0x10#8, 0x7a#8, 0x8b#8, 0x4c#8, 0x9d#8,
   0x8e#8, 0x0f#8, 0xa1#8, 0xb2#8, 0xc3#8, 0xd4#8, 0xe5#8, 0xf6#8, 0x01#8]

/-- Symbolic `TrWireMsg` constructed by `messageEncrypt` at trace timestamp `ts` with `coinsLen`. -/
def encWire (st : TRState) (coinsLen ts : Nat) : DY.Bytes :=
  let m := randTerm ts 32
  let coinsTerm := randTerm (ts + 1) coinsLen
  let (_, key, pqMsg) := Spqr.spqrSend st.spqr coinsTerm
  let (_, seed) := TripleRatchet.kdfCk st.cks
  let keys := trMsgKeys key seed
  trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn
    (DY.SymEnc.symEnc keys.cipherKey keys.iv m) pqMsg

/-- Symbolic 8-byte MAC appended by `messageEncrypt` at trace timestamp `ts` with `coinsLen`. -/
def encMac (st : TRState) (coinsLen ts : Nat) : DY.Bytes :=
  let coinsTerm := randTerm (ts + 1) coinsLen
  let (_, key, _) := Spqr.spqrSend st.spqr coinsTerm
  let (_, seed) := TripleRatchet.kdfCk st.cks
  let keys := trMsgKeys key seed
  TripleRatchet.computeMac keys.macKey st.myIk st.peerIk (encWire st coinsLen ts)

/-- Full inner `SignalMessage` term (`encWire || encMac`) sent by `messageEncrypt`. -/
def encMsg (st : TRState) (coinsLen ts : Nat) : DY.Bytes :=
  DY.Concat.concat (encWire st coinsLen ts) (encMac st coinsLen ts)

/-- Post-state `TRState` stored by `messageEncrypt` at trace timestamp `ts` with `coinsLen`. -/
def encSt (st : TRState) (coinsLen ts : Nat) : TRState :=
  { st with
    cks := (TripleRatchet.kdfCk st.cks).1
    ns := st.ns + 1
    spqr := (Spqr.spqrSend st.spqr (randTerm (ts + 1) coinsLen)).1 }

unseal DY.Bytes in
private instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_randTerm_ne_zero (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (i n : Nat) (hn : n ≠ 0) :
    gamma interpretation S g (randTerm i n) = g.σ i n := by
  unfold gamma gamma' randTerm
  show ((({ timestamp := i, size := n } : DY.Random.Random DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = g.σ i n
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]
  simp [concretizeRandom, hn, node]

/-- Recognizes a `TrWireMsg` term whose symmetric encryption plaintext is `randTerm ts 32`. -/
def isFreshSendWire (ts : Nat) (w : DY.Bytes) : Bool :=
  match w.view? DY.TrWire.TrWireMsg.SubF with
  | some x =>
    match x.ciphertext.view? DY.SymEnc.Enc.SubF with
    | some e =>
      match e.msg.view? DY.Random.Random with
      | some r => r.timestamp == ts && r.size == 32
      | none => false
    | none => false
  | none => false

def updateFreshAt (σ : Nat → Nat → HwBytes) (ts n : Nat) (m : HwBytes) : Nat → Nat → HwBytes :=
  fun i k => if i = ts ∧ k = n then m else σ i k

def clearSendAddr (g : Ghost) (ts : Nat) : Ghost :=
  { g with addr := fun w => if isFreshSendWire ts w then [] else g.addr w }

def setSendAddr (g : Ghost) (ts : Nat) (addr : HwBytes) : Ghost :=
  { g with addr := fun w => if isFreshSendWire ts w then addr else g.addr w }

/-- Whisper `session_send_wire` ghost update: binds `(ts, 32)` to `pt`, `(ts + 1, coins.length)` to
`coins`, and sets `addr := []` on the fresh `encWire`. -/
def sendGhost (g : Ghost) (ts : Nat) (pt coins : HwBytes) : Ghost :=
  let g₁ := { g with σ := updateFreshAt g.σ ts 32 pt }
  clearSendAddr { g₁ with σ := updateFreshAt g₁.σ (ts + 1) coins.length coins } ts

/-- Pending-prekey `session_send_wire` ghost update: binds `(ts, 32)` to `pt`,
`(ts + 1, coins.length)` to `coins`, and sets `addr := pqHarnessAddrBytes` on the fresh `encWire`. -/
def sendPendingGhost (g : Ghost) (ts : Nat) (pt coins : HwBytes) : Ghost :=
  setSendAddr
    { g with σ := updateFreshAt (updateFreshAt g.σ ts 32 pt) (ts + 1) coins.length coins }
    ts pqHarnessAddrBytes

theorem isFreshSendWire_encWire (st : TRState) (coinsLen ts : Nat) :
    isFreshSendWire ts (encWire st coinsLen ts) = true := by
  unfold isFreshSendWire encWire trHonestWireMsg randTerm
  simp [DY.TrWire.CanTrWireMsg.trWireMsg, DY.SymEnc.symEnc, DY.SymEnc.CanSymEnc.symEnc,
    BytesView.view_pack]

theorem sendGhost_addr_encWire (g : Ghost) (st : TRState) (coinsLen ts : Nat) (pt coins : HwBytes) :
    (sendGhost g ts pt coins).addr (encWire st coinsLen ts) = [] := by
  simp [sendGhost, clearSendAddr, isFreshSendWire_encWire]

theorem sendPendingGhost_addr_encWire (g : Ghost) (st : TRState) (coinsLen ts : Nat)
    (pt coins : HwBytes) :
    (sendPendingGhost g ts pt coins).addr (encWire st coinsLen ts) = pqHarnessAddrBytes := by
  simp [sendPendingGhost, setSendAddr, isFreshSendWire_encWire]

theorem gamma_sendGhost_pt (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ts : Nat) (pt coins : HwBytes) :
    gamma interpretation S (sendGhost g ts pt coins) (randTerm ts 32) = pt := by
  rw [gamma_randTerm_ne_zero _ _ _ ts 32 (by decide)]
  simp [sendGhost, clearSendAddr, updateFreshAt]

theorem gamma_sendGhost_coins (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ts : Nat) (pt coins : HwBytes) (h : coins.length ≠ 0) :
    gamma interpretation S (sendGhost g ts pt coins) (randTerm (ts + 1) coins.length) = coins := by
  rw [gamma_randTerm_ne_zero _ _ _ (ts + 1) coins.length h]
  simp [sendGhost, clearSendAddr, updateFreshAt]

theorem gamma_sendPendingGhost_pt (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ts : Nat) (pt coins : HwBytes) :
    gamma interpretation S (sendPendingGhost g ts pt coins) (randTerm ts 32) = pt := by
  rw [gamma_randTerm_ne_zero _ _ _ ts 32 (by decide)]
  simp [sendPendingGhost, setSendAddr, updateFreshAt]

theorem gamma_sendPendingGhost_coins (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ts : Nat) (pt coins : HwBytes) (h : coins.length ≠ 0) :
    gamma interpretation S (sendPendingGhost g ts pt coins) (randTerm (ts + 1) coins.length) = coins := by
  rw [gamma_randTerm_ne_zero _ _ _ (ts + 1) coins.length h]
  simp [sendPendingGhost, setSendAddr, updateFreshAt]

/-- Extends `MatchedPrefix` by an encrypt-family move `m` with `m.party? = some p`,
`m.prekeyPath? = none`, no `.recv` entries in `m.vis`, and `callStarts evs = [.pt pt]`. -/
theorem matchedPrefix_snoc_send {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move} {m : Move}
    {p : Participant} {pt : HwBytes} {τ evs : List MachineEvent}
    (hmp : MatchedPrefix interpretation r₀ S who g ms τ)
    (hrun : ModelRun r₀ (ms ++ [m]))
    (hparty : m.party? = some p)
    (hwho : who[(callStarts τ).length]? = some p)
    (hpath_none : m.prekeyPath? = none)
    (hcs : callStarts evs = [.pt pt])
    (hnorecv : ∀ v ∈ m.vis (runTraceMoves r₀ ms), v.kind ≠ .recv)
    (hevs : List.Forall₂ (EventMatchesEntry interpretation r₀ S g) evs
      (m.vis (runTraceMoves r₀ ms))) :
    MatchedPrefix interpretation r₀ S who g (ms ++ [m]) (τ ++ evs) := by
  have hcc : callCount (runVis r₀ ms) = (callStarts τ).length :=
    Stage1Wire.callCount_of_forall₂_eventMatchesEntry hmp.2.2.2.2.2
  have hrole : RoleFaithful r₀ who (ms ++ [m]) := by
    refine Stage1Wire.roleFaithful_snoc hmp.2.2.1 fun q hq => ?_
    rw [hparty, Option.some.injEq] at hq
    subst hq
    rw [hcc]
    exact hwho
  have hpath₁ : PathFaithful interpretation r₀ S g (ms ++ [m]) τ :=
    Stage1Wire.pathFaithful_snoc_of_prekeyPath_none hmp.2.2.2.1 hpath_none
  have hpath : PathFaithful interpretation r₀ S g (ms ++ [m]) (τ ++ evs) :=
    Stage1Wire.pathFaithful_append_pt hcs hpath₁
  have hread : ReadFaithful interpretation r₀ S g (ms ++ [m]) (τ ++ evs) :=
    Stage1Wire.readFaithful_append_no_recv hmp.2.2.2.2.2.length_eq
      (by simpa [runMoves] using hnorecv)
      hmp.2.2.2.2.1
  exact TR.matchedPrefix_snoc hmp hrun hrole hpath hread hevs

/-- Extends `ExplainsMoves` by a single encrypt-family move `m` that neither rejects nor logs
`AliceDone`. -/
theorem explains_snoc_send {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {m : Move}
    {p : Participant} {pt : HwBytes} {τ evs : List MachineEvent}
    (hmp : MatchedPrefix interpretation r₀ S who g ms τ)
    (hok : OutcomeFaithful r₀ ok ms)
    (hrun : ModelRun r₀ (ms ++ [m]))
    (hparty : m.party? = some p)
    (hwho : who[(callStarts τ).length]? = some p)
    (hpath_none : m.prekeyPath? = none)
    (hnot_rej : ∀ ds, m ≠ .reject ds)
    (hno_alice : (eventIdx isAliceDone (runTraceMoves r₀ ms) (m.next (runTraceMoves r₀ ms))).isSome = false)
    (hcs : callStarts evs = [.pt pt])
    (hnorecv : ∀ v ∈ m.vis (runTraceMoves r₀ ms), v.kind ≠ .recv)
    (hevs : List.Forall₂ (EventMatchesEntry interpretation r₀ S g) evs
      (m.vis (runTraceMoves r₀ ms))) :
    ExplainsMoves interpretation r₀ S who ok g (ms ++ [m]) (τ ++ evs) := by
  refine ⟨matchedPrefix_snoc_send hmp hrun hparty hwho hpath_none hcs hnorecv hevs, ?_⟩
  exact Stage1Wire.outcomeFaithful_snoc hok
    (fun ds h => absurd h (hnot_rej ds))
    (fun h => by rw [hno_alice] at h; cases h)

end Symbolic.Swarm.CREF.SendWire
