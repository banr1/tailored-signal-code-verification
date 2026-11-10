/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFrame

/-!
# Read-Only `.rodata` String Splitting and `r1b_ErrCtx.after_call` Helpers for Arm `R1b`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

theorem r1b_layout1 (n : Nat) (h1 : 0 < n := by decide) (h2 : n + 1 ≤ 2 ^ 63 := by decide) :
    LayoutOk n 1 :=
  ⟨h1, ⟨0, rfl⟩, h2⟩

theorem r1b_ErrCtx.after_call {img : Obj.Image} {ext : String → Option (State → State)}
    {g : RunCall} {d : Init1Data} {s0 s st_bl sf : State} {off off' : Nat}
    (hc : r1b_ErrCtx img ext g d s0 s off)
    (hx19 : st_bl.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hx20 : st_bl.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5))
    (hx21 : st_bl.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5))
    (htr0 : st_bl.trace = s.trace)
    (hfs0 : st_bl.fs.files = s.fs.files)
    (hin : InRun img ext s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hfs : sf.fs.files = st_bl.fs.files)
    (htr : sf.trace = st_bl.trace) :
    r1b_ErrCtx img ext g d s0 sf off' :=
  hc.of_step hin (hcs.1.trans hx19) (hcs.2.1.trans hx20) (hcs.2.2.1.trans hx21)
    (htr.trans htr0) (hfs.trans hfs0)

theorem r1b_ro8_u64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    ∃ w : BitVec 64, ∀ a : BitVec 64, (a ↦ᵣ bs) = (a ↦₆₄ᵣ w) := by
  match bs, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    exact ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0,
      fun a => pointsToBytesRO8_eq_pointsTo64RO a b0 b1 b2 b3 b4 b5 b6 b7⟩

private abbrev r1b_unreadableBytes : List (BitVec 8) :=
  [0x66#8, 0x69#8, 0x6c#8, 0x65#8, 0x20#8, 0x63#8, 0x6f#8, 0x75#8,
   0x6c#8, 0x64#8, 0x20#8, 0x6e#8, 0x6f#8, 0x74#8, 0x20#8, 0x62#8,
   0x65#8, 0x20#8, 0x72#8, 0x65#8, 0x61#8, 0x64#8]

private theorem r1b_utf8_unreadable : utf8 "file could not be read" = r1b_unreadableBytes := by
  rfl_kernel

private abbrev r1b_malformedBytes : List (BitVec 8) :=
  [0x6d#8, 0x61#8, 0x6c#8, 0x66#8, 0x6f#8, 0x72#8, 0x6d#8, 0x65#8,
   0x64#8, 0x20#8, 0x66#8, 0x69#8, 0x6c#8, 0x65#8]

private theorem r1b_utf8_malformed : utf8 "malformed file" = r1b_malformedBytes := by
  rfl_kernel

theorem r1b_ro_split22 (a : BitVec 64) :
    ∃ w0 w1 w2 : BitVec 64, ∃ rem : SepProp,
      (a ↦ᵣ utf8 "file could not be read") =
        (a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 14#64) ↦₆₄ᵣ w2) ∗ rem := by
  rw [r1b_utf8_unreadable]
  obtain ⟨w0, hw0⟩ := r1b_ro8_u64 (r1b_unreadableBytes.take 8) (by decide)
  obtain ⟨w1, hw1⟩ := r1b_ro8_u64 ((r1b_unreadableBytes.drop 8).take 8) (by decide)
  obtain ⟨w2, hw2⟩ := r1b_ro8_u64 (r1b_unreadableBytes.drop 14) (by decide)
  have hsplit1 : (a ↦ᵣ r1b_unreadableBytes) =
      (a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 16#64) ↦ᵣ r1b_unreadableBytes.drop 16) := by
    have heq : r1b_unreadableBytes =
        r1b_unreadableBytes.take 8 ++
          ((r1b_unreadableBytes.drop 8).take 8 ++ r1b_unreadableBytes.drop 16) := by
      decide
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_append]
    have hl0 : (r1b_unreadableBytes.take 8).length = 8 := by decide
    have hl1 : ((r1b_unreadableBytes.drop 8).take 8).length = 8 := by decide
    rw [hl0, hl1, hw0, hw1]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hsplit2 : (a ↦ᵣ r1b_unreadableBytes) =
      (a ↦ᵣ r1b_unreadableBytes.take 14) ∗ ((a + 14#64) ↦₆₄ᵣ w2) := by
    have heq : r1b_unreadableBytes = r1b_unreadableBytes.take 14 ++ r1b_unreadableBytes.drop 14 := by
      decide
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append]
    have hl2 : (r1b_unreadableBytes.take 14).length = 14 := by decide
    rw [hl2, hw2]
  refine ⟨w0, w1, w2,
    ((a + 16#64) ↦ᵣ r1b_unreadableBytes.drop 16) ∗ (a ↦ᵣ r1b_unreadableBytes.take 14), ?_⟩
  calc (a ↦ᵣ r1b_unreadableBytes)
      = (a ↦ᵣ r1b_unreadableBytes) ∗ (a ↦ᵣ r1b_unreadableBytes) :=
        (pointsToBytesRO_dup a r1b_unreadableBytes).symm
    _ = ((a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 16#64) ↦ᵣ r1b_unreadableBytes.drop 16)) ∗
          ((a ↦ᵣ r1b_unreadableBytes.take 14) ∗ ((a + 14#64) ↦₆₄ᵣ w2)) :=
        congrArg₂ sepConj hsplit1 hsplit2
    _ = (a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 14#64) ↦₆₄ᵣ w2) ∗
          (((a + 16#64) ↦ᵣ r1b_unreadableBytes.drop 16) ∗ (a ↦ᵣ r1b_unreadableBytes.take 14)) := by
        ac_rfl

theorem r1b_ro_split14 (a : BitVec 64) :
    ∃ w0 w1 : BitVec 64, ∃ rem : SepProp,
      (a ↦ᵣ utf8 "malformed file") =
        (a ↦₆₄ᵣ w0) ∗ ((a + 6#64) ↦₆₄ᵣ w1) ∗ rem := by
  rw [r1b_utf8_malformed]
  obtain ⟨w0, hw0⟩ := r1b_ro8_u64 (r1b_malformedBytes.take 8) (by decide)
  obtain ⟨w1, hw1⟩ := r1b_ro8_u64 (r1b_malformedBytes.drop 6) (by decide)
  have hsplit1 : (a ↦ᵣ r1b_malformedBytes) =
      (a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦ᵣ r1b_malformedBytes.drop 8) := by
    have heq : r1b_malformedBytes = r1b_malformedBytes.take 8 ++ r1b_malformedBytes.drop 8 := by
      decide
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append]
    have hl0 : (r1b_malformedBytes.take 8).length = 8 := by decide
    rw [hl0, hw0]
  have hsplit2 : (a ↦ᵣ r1b_malformedBytes) =
      (a ↦ᵣ r1b_malformedBytes.take 6) ∗ ((a + 6#64) ↦₆₄ᵣ w1) := by
    have heq : r1b_malformedBytes = r1b_malformedBytes.take 6 ++ r1b_malformedBytes.drop 6 := by
      decide
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append]
    have hl1 : (r1b_malformedBytes.take 6).length = 6 := by decide
    rw [hl1, hw1]
  refine ⟨w0, w1,
    ((a + 8#64) ↦ᵣ r1b_malformedBytes.drop 8) ∗ (a ↦ᵣ r1b_malformedBytes.take 6), ?_⟩
  calc (a ↦ᵣ r1b_malformedBytes)
      = (a ↦ᵣ r1b_malformedBytes) ∗ (a ↦ᵣ r1b_malformedBytes) :=
        (pointsToBytesRO_dup a r1b_malformedBytes).symm
    _ = ((a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦ᵣ r1b_malformedBytes.drop 8)) ∗
          ((a ↦ᵣ r1b_malformedBytes.take 6) ∗ ((a + 6#64) ↦₆₄ᵣ w1)) :=
        congrArg₂ sepConj hsplit1 hsplit2
    _ = (a ↦₆₄ᵣ w0) ∗ ((a + 6#64) ↦₆₄ᵣ w1) ∗
          (((a + 8#64) ↦ᵣ r1b_malformedBytes.drop 8) ∗ (a ↦ᵣ r1b_malformedBytes.take 6)) := by
        ac_rfl

end CryptoVerification.SignalSession.Cli.RunCompose
