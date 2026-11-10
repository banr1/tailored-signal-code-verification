/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Defs

/-!
# Inlined `SessionStructure::decode` Seam Definitions

Stack budget (`overDecStackX`), `previous_sessions` element buffer layout (`overPrevElemAt`),
closure stack scratch predicates (`overDecScratchPre`, `overDecScratchPost`), and seam statements
(`OverPrevDecodeCliStmtGenExt`) for the inlined `SessionStructure::decode` block
(`+0x1ee8 → +0x2620`) in the CLI PQXDH responder closure.
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
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (prostSSGQAt ssgqOf)

/-- Callee stack budget (64 KiB) below closure `sp` during inlined `SessionStructure::decode`. -/
abbrev overDecStackX : Nat := 65536

/-- Buffer half of `prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc]`:
for `prevCap ≠ 0#64`, `prevVecAt A r prevCap prevPtr [enc]` equals
`HdrP r prevCap prevPtr 1#64 ∗ overPrevElemAt A prevCap prevPtr enc`. -/
def overPrevElemAt (A : RustAlloc) (prevCap prevPtr : BitVec 64) (enc : List (BitVec 8)) : SepProp :=
  ⌜1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
    (A.live prevPtr (prevCap.toNat * 24) 8 ∗ vecU8 A prevPtr enc ∗
      memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24))

theorem prevVecAt_one_eq_elemAt (A : RustAlloc) (r prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (hcap : prevCap ≠ 0#64) :
    prevVecAt A r prevCap prevPtr [enc] =
      HdrP r prevCap prevPtr 1#64 ∗ overPrevElemAt A prevCap prevPtr enc :=
  prevVecAt_one_eq A r prevCap prevPtr enc hcap

/-- Stack scratch region touched by inlined `SessionStructure::decode` (`+0x1ee8 → +0x2620`):
- `sp + 0x920` (16B): `prost` `&[u8]` slice cursor `{ptr, end}`;
- `sp + 0x930` (344B): destination `SessionStructure` (`x21`);
- `sp + 0xa88` (8B): `merge_varint` cursor pointer scratch;
- `sp + 0xa90` (344B): nested field `merge` scratch (`x28`);
- `sp + 0xbe8` (136B): `DecodeError` return / `be8` cursor pointer scratch. -/
def overDecScratchPre (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x920#64) 16 ∗
  memRegion (sp + 0x930#64) 344 ∗
  memRegion (sp + 0xa88#64) 8 ∗
  memRegion (sp + 0xa90#64) 344 ∗
  memRegion (sp + 0xbe8#64) 136

/-- Stack scratch region returned intact after `+0x1ee8 → +0x2620` (all slots except `sp + 0x930`,
which now holds `prostSSGQAt A0 (sp + 0x930#64) (ssgqOf sess)`). -/
def overDecScratchPost (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x920#64) 16 ∗
  memRegion (sp + 0xa88#64) 8 ∗
  memRegion (sp + 0xa90#64) 344 ∗
  memRegion (sp + 0xbe8#64) 136

/-- Inlined `SessionStructure::decode` seam (`+0x1ee8 → +0x2620`) for arbitrary `A : RustAlloc`:
given `AllocContractsX img A ext` and a canonical v4 archived session `sess` with no pending
pre-keys, decodes `enc = Record.encSession sess` into `prostSSGQAt A (s.sp + 0x930#64) (ssgqOf sess)`
while preserving `overPrevElemAt` and `overDecScratchPost` (up to `anyHeap`, or OOM `PanicOomProp s0`). -/
def OverPrevDecodeCliStmtGenExt (A : RustAlloc) (trackVRegs : Bool) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext →
    ∀ (s0 s : State) (prevCap prevPtr : BitVec 64) (enc : List (BitVec 8))
      (sess : Session (List (BitVec 8))),
      enc = CryptoVerification.E2E.Record.encSession sess →
      DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩ →
      sess.state.sessionVersion = 4#32 →
      sess.pendingPreKey = none →
      sess.pendingKyberPreKey = none →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1ee8#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      overDecStackX ≤ s.sp.toNat →
      s.trace = s0.trace →
      s.readReg64 .x21 = s.sp + 0x930#64 →
      s.readReg64 .x24 = 1#64 →
      s.readReg64 .x25 = 0xffffffffffffffff#64 →
      s.readReg64 .x27 = prevPtr →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x2620#64) s
        (overPrevElemAt A prevCap prevPtr enc ∗
         overDecScratchPre s.sp ∗
         A.pool ∗
         stackAt s.sp overDecStackX)
        (fun sf P_f =>
          (P_f ⊢
            prostSSGQAt A (s.sp + 0x930#64) (ssgqOf sess) ∗
            overPrevElemAt A prevCap prevPtr enc ∗
            overDecScratchPost s.sp ∗
            A.pool ∗
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
          img.FrozenLoaded sf ∧
          sf.symtab = img.symtab)
        (PanicOomProp s0)

abbrev OverPrevDecodeCliStmtExt (A : RustAlloc) : Prop := OverPrevDecodeCliStmtGenExt A true
abbrev OverPrevDecodeCliGPRStmtExt (A : RustAlloc) : Prop := OverPrevDecodeCliStmtGenExt A false

abbrev OverPrevDecodeCliStmtGen (trackVRegs : Bool) : Prop := OverPrevDecodeCliStmtGenExt A0 trackVRegs

abbrev OverPrevDecodeCliStmt : Prop := OverPrevDecodeCliStmtGen true

abbrev OverPrevDecodeCliGPRStmt : Prop := OverPrevDecodeCliStmtGen false

theorem overPrevDecodeCliGPR_of_vregs_ext {A : RustAlloc}
    (h : OverPrevDecodeCliStmtExt A) : OverPrevDecodeCliGPRStmtExt A := by
  intro img ext himg hAX s0 s prevCap prevPtr enc sess henc hQ hver4 hpp hkpk
    hF hsym hpc hrun hsp_align hsp_le htr hx21 hx24 hx25 hx27 hx29
  have hwp := h img ext himg hAX s0 s prevCap prevPtr enc sess henc hQ hver4 hpp hkpk
    hF hsym hpc hrun hsp_align hsp_le htr hx21 hx24 hx25 hx27 hx29
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', P_f, hmf, hP, hsp', htr', hx19', hx20', hx21', hx24', hx25',
    hx27', hx29', _, hFf, hsymf⟩ | hpan⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc', hrun', P_f, hmf, hP, hsp', htr', hx19', hx20', hx21', hx24',
      hx25', hx27', hx29', trivial, hFf, hsymf⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

theorem overPrevDecodeCliGPR_of_vregs (h : OverPrevDecodeCliStmt) : OverPrevDecodeCliGPRStmt :=
  overPrevDecodeCliGPR_of_vregs_ext h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
