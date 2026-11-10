/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Compose
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Composition of Inlined `SessionStructure::decode` Loop

Relocatable (`[LibsignalPlacement]`) composition of Entry, Loop Head, Key dispatch, and the four
field-arm groups into `OverPrevDecodePlacedStmt` on Block `518` (`lsProg_518 ext`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Std Arm64 ProofLib ProofLib.ObjectLoad SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Compose `OverDecKeyPlacedStmt` and `OverDecArmPlacedStmtTR P` into `OverDecFieldPlacedStmt P`. -/
theorem overDecField_placed_of_key_arm [LibsignalPlacement] {P : GenFieldQ → Prop}
    (hK : OverDecKeyPlacedStmt) (hA : OverDecArmPlacedStmtTR P)
    (hPA : ∀ fl, P fl → OverDecAnyField fl) :
    OverDecFieldPlacedStmt P := by
  intro ext s0 s g v fl rest hP hok hfr hsuf hlen hregs
  refine overDec_sepWPp_seq (hK ext s0 s g v fl rest (hPA fl hP) hok hsuf hlen hregs) ?_
  rintro sm Pm - - ⟨hregs', hx0, hx22, hent⟩
  exact overDec_sepWPp_weaken_pre hent
    (hA ext s0 sm g v fl rest hP hok hfr hsuf hlen hregs' hx0 hx22)

/-- Combine the four field-arm groups into `OverDecArmPlacedStmtTR OverDecAnyField`. -/
theorem overDecArm_placed_any [LibsignalPlacement]
    (hV : OverDecArmPlacedStmtTR OverDecVarintField)
    (hB : OverDecArmPlacedStmtTR OverDecBytesField)
    (hS : OverDecArmPlacedStmtTR OverDecSenderField)
    (hR : OverDecArmPlacedStmtTR OverDecRecvField) :
    OverDecArmPlacedStmtTR OverDecAnyField := by
  intro ext s0 s g v fl rest hP
  rcases hP with h | h | h | h
  · exact hV ext s0 s g v fl rest h
  · exact hB ext s0 s g v fl rest h
  · exact hS ext s0 s g v fl rest h
  · exact hR ext s0 s g v fl rest h

/-- Field-loop induction (`+0x216c → +0x2620`) under `[LibsignalPlacement]`. -/
theorem overDec_placed_loop [LibsignalPlacement]
    (hField : OverDecFieldPlacedStmt OverDecAnyField)
    (hCons : OverDecHeadConsPlacedStmt) (hNil : OverDecHeadNilPlacedStmt)
    (ext : String → Option (State → State))
    (s0 : State) (g : OverDecG) (hlen : g.enc.length < 2 ^ 62) :
    ∀ (fs : List GenFieldQ) (v : SSGQ) (s : State), fs ≠ [] →
      (∀ fl ∈ fs, OverDecAnyField fl ∧ fl.Ok) → OverDecFreshChain fs v →
      fs.flatMap GenFieldQ.enc <:+ g.enc →
      OverDecRegsPlaced ext s0 g 0x216c#64 s →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
        (overDecHeap g (fs.flatMap GenFieldQ.enc) v)
        (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2620#64 sf ∧
          (P_f ⊢ overDecHeap g [] (fs.foldl SSGQ.apply v)))
        (PanicOomProp s0) := by
  intro fs
  induction fs with
  | nil => intro v s hne; exact absurd rfl hne
  | cons fl fs ih =>
    intro v s _ hmem hfr hsuf hregs
    have hfl := hmem fl (List.mem_cons_self ..)
    obtain ⟨hfr1, hfr2⟩ := overDecFreshChain_cons_inv hfr
    rw [overDec_flatMap_cons] at hsuf ⊢
    refine overDec_sepWPp_seq
      (hField ext s0 s g v fl _ hfl.1 hfl.2 hfr1 hsuf hlen hregs) ?_
    rintro sm Pm - - ⟨hregsm, hentm⟩
    refine overDec_sepWPp_weaken_pre hentm ?_
    have hsuf' : fs.flatMap GenFieldQ.enc <:+ g.enc :=
      List.IsSuffix.trans (List.suffix_append _ _) hsuf
    rcases fs with _ | ⟨fl', fs'⟩
    · exact hNil ext s0 sm g (v.apply fl) hlen hregsm
    · have hne : (fl' :: fs').flatMap GenFieldQ.enc ≠ [] := by
        rw [overDec_flatMap_cons]
        intro h
        exact overDec_enc_ne_nil fl' (List.append_eq_nil_iff.mp h).1
      refine overDec_sepWPp_seq (hCons ext s0 sm g (v.apply fl) _ hne hsuf' hlen hregsm) ?_
      rintro sn Pn - - ⟨hregsn, hentn⟩
      exact overDec_sepWPp_weaken_pre hentn
        (ih (v.apply fl) sn (List.cons_ne_nil _ _)
          (fun f hf => hmem f (List.mem_cons_of_mem _ hf)) hfr2 hsuf' hregsn)

/-- The decode from the field body (`+0x216c`, after Entry) to the frozen post at `+0x2620`
under `[LibsignalPlacement]`. -/
theorem overDec_placed_after_entry [LibsignalPlacement]
    (hField : OverDecFieldPlacedStmt OverDecAnyField)
    (hCons : OverDecHeadConsPlacedStmt) (hNil : OverDecHeadNilPlacedStmt)
    (ext : String → Option (State → State))
    (s0 sm : State) (g : OverDecG) (sess : Session (List (BitVec 8)))
    (hencfs : g.enc = (genFieldsQ sess).flatMap GenFieldQ.enc)
    (hlen : g.enc.length < 2 ^ 62) (hfsne : genFieldsQ sess ≠ [])
    (hmem : ∀ fl ∈ genFieldsQ sess, OverDecAnyField fl ∧ fl.Ok)
    (hfresh : OverDecFreshChain (genFieldsQ sess) SSGQ.empty)
    (hfold : (genFieldsQ sess).foldl SSGQ.apply SSGQ.empty = ssgqOf sess)
    (hregsm : OverDecRegsPlaced ext s0 g 0x216c#64 sm) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) sm
      (overDecHeap g g.enc SSGQ.empty)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2620#64 sf ∧
        (P_f ⊢ overDecHeap g [] (ssgqOf sess)))
      (PanicOomProp s0) := by
  have hsuf : (genFieldsQ sess).flatMap GenFieldQ.enc <:+ g.enc := by
    rw [← hencfs]
  have hloop := overDec_placed_loop hField hCons hNil ext s0 g hlen (genFieldsQ sess)
    SSGQ.empty sm hfsne hmem hfresh hsuf hregsm
  rw [← hencfs, hfold] at hloop
  exact hloop

/-- Compose Entry, the field loop over `genFieldsQ sess`, and loop exit into `OverPrevDecodePlacedStmt`. -/
theorem overPrevDecode_placed_of_steps [LibsignalPlacement]
    (hEntry : OverDecEntryPlacedStmt)
    (hField : OverDecFieldPlacedStmt OverDecAnyField)
    (hCons : OverDecHeadConsPlacedStmt) (hNil : OverDecHeadNilPlacedStmt) :
    OverPrevDecodePlacedStmt := by
  intro ext s0 s prevCap prevPtr encCap encPtr enc sess hok hcl hpc hrun
    hal htr hx21 hx24 hx25 hx27 hx29
  obtain ⟨henc, hscope, hver, hpp, hpk⟩ := hok
  have hencfs : enc = (genFieldsQ sess).flatMap GenFieldQ.enc :=
    henc.trans (overDec_encSession_eq sess hscope)
  have hfsne := overDec_genFieldsQ_ne_nil sess hver
  have hne : enc ≠ [] := hencfs ▸ overDec_flatMap_ne_nil _ hfsne
  have hlen : enc.length < 2 ^ 62 := henc ▸ overDec_encSession_length_lt sess hscope
  have hEntry' := hEntry ext s0 s
    ⟨s.sp, s.readReg64 .x19, s.readReg64 .x20, s.readReg64 .x26, prevCap, prevPtr, encCap,
      encPtr, enc, s⟩ hne hlen hcl hpc hrun rfl hal htr rfl rfl rfl hx21 hx24 hx25 hx27 hx29 rfl
  refine overDec_sepWPp_seq hEntry' ?_
  rintro sm Pm - - ⟨hregsm, hentm⟩
  refine overDec_sepWPp_weaken_pre hentm ?_
  refine overDec_sepWPp_mono_post ?_ (overDec_placed_after_entry hField hCons hNil ext s0
    sm _ sess hencfs hlen hfsne (overDec_mem_genFieldsQ sess hscope hpp hpk)
    (overDec_freshChain_genFieldsQ sess hscope) (overDec_fold_genFieldsQ sess hscope) hregsm)
  rintro sf P_f - - ⟨⟨-, -, hsp, -, htrf, hclf, h19, h20, h26, h21, h24, h25, h27, -, h29, hvregsf⟩,
    hentf⟩
  exact ⟨Entails.trans hentf (overDec_exit _ (ssgqOf sess) (by exact hne)), hsp, htrf, hclf,
    h19, h20, h21, h24, h25, h26, h27, h29, hvregsf⟩

/-- Assemble `OverPrevDecodePlacedStmt` from Entry, Key, the four Arm groups, and Loop Head. -/
theorem overPrevDecode_placed_of_key_arms [LibsignalPlacement]
    (hEntry : OverDecEntryPlacedStmt)
    (hCons : OverDecHeadConsPlacedStmt) (hNil : OverDecHeadNilPlacedStmt)
    (hKey : OverDecKeyPlacedStmt)
    (hVarint : OverDecArmPlacedStmtTR OverDecVarintField)
    (hBytes : OverDecArmPlacedStmtTR OverDecBytesField)
    (hSender : OverDecArmPlacedStmtTR OverDecSenderField)
    (hRecv : OverDecArmPlacedStmtTR OverDecRecvField) :
    OverPrevDecodePlacedStmt :=
  overPrevDecode_placed_of_steps hEntry
    (overDecField_placed_of_key_arm hKey
      (overDecArm_placed_any hVarint hBytes hSender hRecv) (fun _ h => h))
    hCons hNil

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
