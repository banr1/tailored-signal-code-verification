/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DecDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Inlined `SessionStructure::decode` Seam

Relocatable (`[LibsignalPlacement]`) seam statement for the inlined `SessionStructure::decode`
segment (`(blkPl_518).base + 0x1ee8 → (blkPl_518).base + 0x2620`) on `lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.CliHandshake.RespClosurePlaced
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (prostSSGQAt ssgqOf)

/-- Relocatable inlined `SessionStructure::decode` seam
(`(blkPl_518).base + 0x1ee8 → (blkPl_518).base + 0x2620`) on `lsProg_518 ext`. -/
def OverPrevDecodeCliPlacedStmtGen [LibsignalPlacement] (trackVRegs : Bool) : Prop :=
  ∀ (ext : String → Option (State → State)),
    ∀ (s0 s : State) (prevCap prevPtr : BitVec 64) (enc : List (BitVec 8))
      (sess : Session (List (BitVec 8))),
      enc = CryptoVerification.E2E.Record.encSession sess →
      DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩ →
      sess.state.sessionVersion = 4#32 →
      sess.pendingPreKey = none →
      sess.pendingKyberPreKey = none →
      (lsProg_518 ext).CodeLoaded s.mem →
      s.pc = (blkPl_518).base + 0x1ee8#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      overDecStackX ≤ s.sp.toNat →
      s.trace = s0.trace →
      s.readReg64 .x21 = s.sp + 0x930#64 →
      s.readReg64 .x24 = 1#64 →
      s.readReg64 .x25 = 0xffffffffffffffff#64 →
      s.readReg64 .x27 = prevPtr →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
        (overPrevElemAt A0 prevCap prevPtr enc ∗
         overDecScratchPre s.sp ∗
         A0.pool ∗
         stackAt s.sp overDecStackX)
        (fun sf P_f =>
          (P_f ⊢
            prostSSGQAt A0 (s.sp + 0x930#64) (ssgqOf sess) ∗
            overPrevElemAt A0 prevCap prevPtr enc ∗
            overDecScratchPost s.sp ∗
            A0.pool ∗
            stackAt s.sp overDecStackX ∗
            anyHeap) ∧
          sf.sp = s.sp ∧
          sf.trace = s0.trace ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x21 = s.sp + 0x930#64 ∧
          sf.readReg64 .x24 = 1#64 ∧
          sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧
          sf.readReg64 .x27 = prevPtr ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          optVRegsEq trackVRegs sf s ∧
          (lsProg_518 ext).CodeLoaded sf.mem)
        (PanicOomProp s0)

abbrev OverPrevDecodeCliPlacedStmt [LibsignalPlacement] : Prop :=
  OverPrevDecodeCliPlacedStmtGen true

abbrev OverPrevDecodeCliGPRPlacedStmt [LibsignalPlacement] : Prop :=
  OverPrevDecodeCliPlacedStmtGen false

theorem overPrevDecodeCliGPR_placed_of_vregs [LibsignalPlacement]
    (h : OverPrevDecodeCliPlacedStmt) : OverPrevDecodeCliGPRPlacedStmt := by
  intro ext s0 s prevCap prevPtr enc sess henc hQ hver4 hpp hkpk
    hCL hpc hrun hsp_align hsp_le htr hx21 hx24 hx25 hx27 hx29
  have hwp := h ext s0 s prevCap prevPtr enc sess henc hQ hver4 hpp hkpk
    hCL hpc hrun hsp_align hsp_le htr hx21 hx24 hx25 hx27 hx29
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', P_f, hmf, hP, hsp', htr', hx19', hx20', hx21', hx24', hx25',
    hx27', hx29', _, hCLf⟩ | hpan⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc', hrun', P_f, hmf, hP, hsp', htr', hx19', hx20', hx21', hx24',
      hx25', hx27', hx29', trivial, hCLf⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
