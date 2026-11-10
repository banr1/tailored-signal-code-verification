/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Witness
public import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux

/-!
# Reusable Collision-Excuses Dischargers

Provides finite-list prefix/suffix step combinators and computable `Bool` checkers (`by decide`)
for discharging `¬ CollisionAfterExplainedPrefix` in the CLI non-vacuity handshake and session
reachability proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision

open DY
open scoped DY.Libsignal.Composed
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.TripleRatchet (trMsgKeys TRSignalMsg computeMac hkdfBlock2 hmac parseTrSignalMsg)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
   gamma gamma' assumedInjective prefixTerms plaintextTerms
   TrialCtx whisperTrials bobTrials trialTerms honestSaltsOf storedRatchetKeys ReselectsTo
   MemoCollisionOn UnknownSeedMacGuess TruncatedMacSeedCollision MacTagForgeryOrCollision
   RecvCollisionOn ReselectCollisionOn
   PreKeyFields PreKeyRep parsePreKeyWire recvRepresentationsOn preKeyRepresentationsOn
   BobSessionStartCollidesOrImplicitRejectsOn KyberMismatch
   KnownBaseKeyOn Explains runTrace bobDoneBaseKeys)
open DY.Libsignal.Composed.Refinement.Cli
  (ReadCollisionCli ModelAcceptsTermAfterAttackerSends RepresentationsCollideOrAcceptedCollide
   SignalMsgAcceptedOnlyViaCollision PreKeyStartCollidesOrRejects
   NextEventCollides CollisionAfterExplainedPrefix)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myInterp mkRecords mkRecords_wf not_kyberMismatch_myInterp)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux
  (noRecvEvent bobDoneBaseKeys_eq_nil_of_no_recv not_knownBaseKeyOn_of_no_recv)

/-! ## Finite-List Step Decomposition of `¬ CollisionAfterExplainedPrefix` -/

/-- Suffix-indexed invariant asserting that no split `rest = δ ++ (.run ev :: evs₂)` extends `evs₁`
to a prefix `evs₁ ++ δ` whose next run event `ev` triggers `NextEventCollides` under an `Explains`
witness. -/
def NoCollisionFrom (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (evs₁ rest : List CliEvent) : Prop :=
  ∀ (δ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent)
    (g : Ghost) (ss : List Step) (vis : List VisEntry),
    rest = δ ++ (.run ev :: evs₂) →
    Explains interp r S g ss vis (evs₁ ++ δ) →
    ¬ NextEventCollides interp r S g ss vis (evs₁ ++ δ) ev

theorem not_collisionAfterExplainedPrefix_iff {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {evs : List CliEvent} :
    ¬ CollisionAfterExplainedPrefix interp r S evs ↔
      NoCollisionFrom interp r S [] evs := by
  constructor
  · intro h δ ev evs₂ g ss vis heq hExp hNext
    rw [List.nil_append] at hExp hNext
    exact h ⟨δ, ev, evs₂, g, ss, vis, heq, hExp, hNext⟩
  · rintro h ⟨evs₁, ev, evs₂, g, ss, vis, heq, hExp, hNext⟩
    exact h evs₁ ev evs₂ g ss vis heq (by simpa using hExp) (by simpa using hNext)

theorem not_collisionAfterExplainedPrefix_of_from {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {evs : List CliEvent}
    (h : NoCollisionFrom interp r S [] evs) :
    ¬ CollisionAfterExplainedPrefix interp r S evs :=
  not_collisionAfterExplainedPrefix_iff.mpr h

theorem not_collision_nil {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {evs₁ : List CliEvent} :
    NoCollisionFrom interp r S evs₁ [] := by
  intro δ _ _ _ _ _ heq
  cases δ <;> cases heq

theorem not_collision_step_env {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {evs₁ : List CliEvent} {e : EnvEvent} {rest : List CliEvent}
    (h_tail : NoCollisionFrom interp r S (evs₁ ++ [.env e]) rest) :
    NoCollisionFrom interp r S evs₁ (.env e :: rest) := by
  intro δ ev evs₂ g ss vis heq hExp
  cases δ with
  | nil => cases heq
  | cons d δ' =>
    simp only [List.cons_append, List.cons.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    have hassoc : evs₁ ++ (.env e :: δ') = (evs₁ ++ [.env e]) ++ δ' := by simp [List.append_assoc]
    rw [hassoc] at hExp ⊢
    exact h_tail δ' ev evs₂ g ss vis rfl hExp

theorem not_collision_step_run {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {evs₁ : List CliEvent} {ev : RunEvent} {rest : List CliEvent}
    (h_here : ∀ g ss vis, Explains interp r S g ss vis evs₁ →
      ¬ NextEventCollides interp r S g ss vis evs₁ ev)
    (h_tail : NoCollisionFrom interp r S (evs₁ ++ [.run ev]) rest) :
    NoCollisionFrom interp r S evs₁ (.run ev :: rest) := by
  intro δ ev' evs₂ g ss vis heq hExp
  cases δ with
  | nil =>
    simp only [List.nil_append, List.cons.injEq, CliEvent.run.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rw [List.append_nil] at hExp ⊢
    exact h_here g ss vis hExp
  | cons d δ' =>
    simp only [List.cons_append, List.cons.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    have hassoc : evs₁ ++ (.run ev :: δ') = (evs₁ ++ [.run ev]) ++ δ' := by simp [List.append_assoc]
    rw [hassoc] at hExp ⊢
    exact h_tail δ' ev' evs₂ g ss vis rfl hExp

/-- CLI events that never trigger `NextEventCollides`: environment events, `init` calls, rejected
`recv` calls, and empty `recv` calls. -/
def isIrrelevantCliEvent : CliEvent → Bool
  | .env _ => true
  | .run ev =>
    match ev.cmd with
    | .init _ _ => true
    | .recv _ =>
      match ev.exit with
      | some (0, _) => ev.input.isEmpty
      | _ => true
    | .send _ => false

theorem nextEventCollides_AutoFalse {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent}
    (hirr : isIrrelevantCliEvent (.run ev) = true := by rfl) :
    ¬ NextEventCollides interp r S g ss vis evs₁ ev := by
  dsimp only [isIrrelevantCliEvent] at hirr
  unfold NextEventCollides
  cases hcmd : ev.cmd with
  | init _ _ => simp
  | send _ => simp [hcmd] at hirr
  | recv _ =>
    rw [hcmd] at hirr
    dsimp only at hirr ⊢
    rintro ⟨⟨out, hexit⟩, hbody⟩
    rw [hexit] at hirr
    cases hin : ev.input with
    | nil => rw [hin] at hbody; exact hbody
    | cons _ _ => rw [hin] at hirr; cases hirr

theorem not_collision_step_irrelevant {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {evs₁ : List CliEvent} {e : CliEvent} {rest : List CliEvent}
    (hirr : isIrrelevantCliEvent e = true := by rfl)
    (h_tail : NoCollisionFrom interp r S (evs₁ ++ [e]) rest) :
    NoCollisionFrom interp r S evs₁ (e :: rest) := by
  cases e with
  | env _ => exact not_collision_step_env h_tail
  | run _ => exact not_collision_step_run (fun _ _ _ _ => nextEventCollides_AutoFalse hirr) h_tail

theorem not_collision_steps_irrelevant {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {evs₁ blk rest : List CliEvent}
    (hirr : blk.all isIrrelevantCliEvent = true := by rfl)
    (h_tail : NoCollisionFrom interp r S (evs₁ ++ blk) rest) :
    NoCollisionFrom interp r S evs₁ (blk ++ rest) := by
  induction blk generalizing evs₁ with
  | nil => simpa using h_tail
  | cons e blk' ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hirr
    rw [List.cons_append]
    apply not_collision_step_irrelevant hirr.1
    apply ih hirr.2
    simpa [List.append_assoc] using h_tail

/-! ## Computable `noMemoCollisionBool` and Soundness -/

/-- Decidable pairwise non-collision check between a new-term memo entry `x₁` and a prefix-or-new
memo entry `x₂`, conservatively dropping `¬ known` so soundness holds for every `known` predicate. -/
def noMemoEntryPairCollides (pts : List DY.Bytes)
    (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) : Bool :=
  !(x₁.2.2 == x₂.2.2) ||
  (x₁.2.1 == x₂.2.1) ||
  (!(assumedInjective x₁.1) && !(assumedInjective x₂.1)) ||
  (pts.contains x₁.1 && (pts.contains x₂.1 || !(assumedInjective x₂.1))) ||
  (pts.contains x₂.1 && (pts.contains x₁.1 || !(assumedInjective x₁.1)))

/-- Computable `Bool` over-approximation refuting `MemoCollisionOn` for all `known` predicates. -/
def noMemoCollisionBool (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) (vis : List VisEntry)
    (newTerms newPts : List DY.Bytes) : Bool :=
  let memo := fun t => (gamma' interp S g t).memo
  let newMemos := newTerms.flatMap memo
  let allMemos := (prefixTerms r tr vis).flatMap memo ++ newMemos
  let pts := plaintextTerms vis ++ newPts
  newMemos.all fun x₁ => allMemos.all fun x₂ => noMemoEntryPairCollides pts x₁ x₂

theorem noMemoCollision_of_bool {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {vis : List VisEntry}
    {newTerms newPts : List DY.Bytes}
    (hb : noMemoCollisionBool interp r S g tr vis newTerms newPts = true)
    (known : DY.Bytes → Prop) :
    ¬ MemoCollisionOn interp r S g known tr vis newTerms newPts := by
  rintro ⟨x₁, hx₁, x₂, hx₂, hsh, hinj, hpt₁, hpt₂, hbytes⟩
  have hall₁ := List.all_eq_true.mp hb x₁ hx₁
  have hall₂ := List.all_eq_true.mp hall₁ x₂ hx₂
  unfold noMemoEntryPairCollides at hall₂
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq,
    beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_true_eq] at hall₂
  rcases hall₂ with (((hne | heq) | ⟨hn1, hn2⟩) | ⟨hm1, hm2 | hn2⟩) | ⟨hm2, hm1 | hn1⟩
  · exact hne hbytes
  · exact hsh heq
  · rcases hinj with h1 | h2 <;> simp_all
  · exact (hpt₁ hm1).1 hm2
  · have h2 := (hpt₁ hm1).2.1
    simp [h2] at hn2
  · exact (hpt₂ hm2).1 hm1
  · have h1 := (hpt₂ hm2).2.1
    simp [h1] at hn1

/-! ## Computable `noMacForgeryBool` and Soundness -/

/-- Syntactically extracts `seed` from `computeMac (trMsgKeys salt seed).macKey peerIk myIk w`. -/
def extractMacSeed? (mac : DY.Bytes) : Option DY.Bytes := do
  let t ← mac.view? DY.Trunc.Trunc8.SubF
  let hOuter ← t.input.view? DY.KdfExtract.KdfExtract.SubF
  let hMk ← hOuter.salt.view? DY.KdfExtract.KdfExtract.SubF
  let hPrk ← hMk.salt.view? DY.KdfExtract.KdfExtract.SubF
  pure hPrk.ikm

theorem extractMacSeed?_computeMac (salt seed peerIk myIk w : DY.Bytes) :
    extractMacSeed? (computeMac (trMsgKeys salt seed).macKey peerIk myIk w) = some seed := by
  simp [extractMacSeed?, computeMac, trMsgKeys, hkdfBlock2, hmac,
    DY.KdfExtract.kdfExtract, DY.Trunc.trunc8, DY.BytesView.view_pack]

/-- Computable check refuting `UnknownSeedMacGuess` for all `known` predicates: every own-salt trial
matching `γ msg.mac` has some `salt ∈ honest` producing identical `(cipherKey, macKey, iv)` bytes. -/
def noUnknownSeedMacGuessBool (interp : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (honest : List DY.Bytes) (msg : TRSignalMsg) (ctxs : List TrialCtx) : Bool :=
  let γ := gamma interp S g
  ctxs.all fun ctx =>
    match ctx.seed? with
    | none => true
    | some seed =>
      ctx.ownSalts.all fun k =>
        let mk := trMsgKeys k seed
        !(γ (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire) == γ msg.mac) ||
          honest.any fun salt =>
            let hmk := trMsgKeys salt seed
            (γ hmk.cipherKey == γ mk.cipherKey) &&
              (γ hmk.macKey == γ mk.macKey) &&
              (γ hmk.iv == γ mk.iv)

theorem not_unknownSeedMacGuess_of_bool {interp : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {honest : List DY.Bytes} {msg : TRSignalMsg} {ctxs : List TrialCtx}
    (hb : noUnknownSeedMacGuessBool interp S g honest msg ctxs = true)
    (known : DY.Bytes → Prop) :
    ¬ UnknownSeedMacGuess interp S g known honest msg ctxs := by
  rintro ⟨ctx, hctx, seed, hseed, k, hk, hmacEq, _, hnoHonest⟩
  have h1 := List.all_eq_true.mp hb ctx hctx
  rw [hseed] at h1
  have h2 := List.all_eq_true.mp h1 k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at h2
  rcases h2 with hne | ⟨salt, hsalt, ⟨hc, hm⟩, hi⟩
  · exact hne hmacEq
  · exact hnoHonest salt hsalt (Prod.ext hc (Prod.ext hm hi))

/-- Computable check refuting `TruncatedMacSeedCollision`: whenever a trial `(ctx, seed, k)` matches
`γ msg.mac`, every trial `(ctx₀, seed₀)` with `γ seed ≠ γ seed₀` neither matches `γ msg.mac` on
`ctx₀.ownSalts ++ honest` nor equals `extractMacSeed? msg.mac`. -/
def noTruncatedMacSeedCollisionBool (interp : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (honest : List DY.Bytes) (msg : TRSignalMsg) (ctxs : List TrialCtx) : Bool :=
  let γ := gamma interp S g
  let macSeed? := extractMacSeed? msg.mac
  ctxs.all fun ctx =>
    match ctx.seed? with
    | none => true
    | some seed =>
      ctx.ownSalts.all fun k =>
        let mk := trMsgKeys k seed
        !(γ (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire) == γ msg.mac) ||
          ctxs.all fun ctx₀ =>
            match ctx₀.seed? with
            | none => true
            | some seed₀ =>
              (γ seed == γ seed₀) ||
                (((ctx₀.ownSalts ++ honest).all fun salt₀ =>
                    !(γ (computeMac (trMsgKeys salt₀ seed₀).macKey ctx₀.peerIk ctx₀.myIk msg.wire) ==
                        γ msg.mac)) &&
                  match macSeed? with
                  | none => true
                  | some sMac => !(sMac == seed₀))

theorem not_truncatedMacSeedCollision_of_bool {interp : ExternInterpretation}
    {S : OpaqueSymbolSemantics} {g : Ghost} {honest : List DY.Bytes} {msg : TRSignalMsg}
    {ctxs : List TrialCtx}
    (hb : noTruncatedMacSeedCollisionBool interp S g honest msg ctxs = true) :
    ¬ TruncatedMacSeedCollision interp S g honest msg ctxs := by
  rintro ⟨ctx, hctx, seed, hseed, k, hk, hmacEq, ctx₀, hctx₀, seed₀, hseed₀, hseedNe, hdisj⟩
  have h1 := List.all_eq_true.mp hb ctx hctx
  dsimp only at h1
  rw [hseed] at h1
  have h2 := List.all_eq_true.mp h1 k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h2
  rcases h2 with hne | hall₀
  · exact hne hmacEq
  · have h3 := List.all_eq_true.mp hall₀ ctx₀ hctx₀
    rw [hseed₀] at h3
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h3
    rcases h3 with hseedEq | ⟨hnoSalt₀, hnoSyntactic⟩
    · exact hseedNe hseedEq
    · rcases hdisj with ⟨salt₀, hsalt₀, hmac₀⟩ | ⟨peerIk₀, myIk₀, salt₀, w, hmacTerm, _⟩
      · have hs := List.all_eq_true.mp hnoSalt₀ salt₀ hsalt₀
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hs
        exact hs hmac₀
      · have hex : extractMacSeed? msg.mac = some seed₀ := by
          rw [hmacTerm, extractMacSeed?_computeMac]
        rw [hex] at hnoSyntactic
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hnoSyntactic
        exact hnoSyntactic rfl

/-- Combined computable check refuting `MacTagForgeryOrCollision` for every `known` predicate. -/
def noMacForgeryBool (interp : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (honest : List DY.Bytes) (msg : TRSignalMsg) (ctxs : List TrialCtx) : Bool :=
  noUnknownSeedMacGuessBool interp S g honest msg ctxs &&
    noTruncatedMacSeedCollisionBool interp S g honest msg ctxs

theorem not_macTagForgeryOrCollision_of_bool {interp : ExternInterpretation}
    {S : OpaqueSymbolSemantics} {g : Ghost} {honest : List DY.Bytes} {msg : TRSignalMsg}
    {ctxs : List TrialCtx}
    (hb : noMacForgeryBool interp S g honest msg ctxs = true)
    (known : DY.Bytes → Prop) :
    ¬ MacTagForgeryOrCollision interp S g known honest msg ctxs := by
  simp only [noMacForgeryBool, Bool.and_eq_true] at hb
  rintro (hGuess | hColl)
  · exact not_unknownSeedMacGuess_of_bool hb.1 known hGuess
  · exact not_truncatedMacSeedCollision_of_bool hb.2 hColl

/-! ## Receiver and Session-Start Dischargers -/

/-- Computable `Bool` check for the memo + MAC body of `BobSessionStartCollidesOrImplicitRejectsOn`. -/
def noBobStartCollisionBool (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) (vis : List VisEntry)
    (salts : List DY.Bytes) (p : PreKeyFields) (x : PreKeyRep) : Bool :=
  match parseTrSignalMsg x.msg with
  | none => noMemoCollisionBool interp r S g tr vis [x.ek, x.ct, x.msg] []
  | some msg =>
    let ctxs := bobTrials r tr p x msg
    noMemoCollisionBool interp r S g tr vis
        ([x.ek, x.ct, x.msg] ++ ctxs.flatMap (trialTerms salts msg)) [] &&
      noMacForgeryBool interp S g salts msg ctxs

theorem not_bobSessionStartCollidesOrImplicitRejectsOn_check {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace}
    {vis : List VisEntry} {salts : List DY.Bytes} {p : PreKeyFields} {x : PreKeyRep}
    (hb : noBobStartCollisionBool interp r S g tr vis salts p x = true) :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn interp r S g tr vis salts p x := by
  unfold BobSessionStartCollidesOrImplicitRejectsOn noBobStartCollisionBool at *
  intro hrest
  split at hrest
  · rename_i hparse
    rw [hparse] at hb
    exact noMemoCollision_of_bool hb _ hrest
  · rename_i msg hparse
    rw [hparse] at hb
    simp only [Bool.and_eq_true] at hb
    rcases hrest with hmemo | hmac
    · exact noMemoCollision_of_bool hb.1 _ hmemo
    · exact not_macTagForgeryOrCollision_of_bool hb.2 _ hmac

/-- Computable `Bool` check refuting `RecvCollisionOn interp r S g tr vis salts t`. -/
def noRecvCollisionBool (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) (vis : List VisEntry)
    (salts : List DY.Bytes) (t : DY.Bytes) : Bool :=
  match parseTrSignalMsg t with
  | none => noMemoCollisionBool interp r S g tr vis [t] []
  | some msg =>
    let ctxs := whisperTrials interp r S g tr msg
    noMemoCollisionBool interp r S g tr vis
        (t :: ctxs.flatMap (trialTerms salts msg)) [] &&
      noMacForgeryBool interp S g salts msg ctxs

theorem not_recvCollisionOn_check {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {vis : List VisEntry}
    {salts : List DY.Bytes} {t : DY.Bytes}
    (hb : noRecvCollisionBool interp r S g tr vis salts t = true) :
    ¬ RecvCollisionOn interp r S g tr vis salts t := by
  unfold RecvCollisionOn noRecvCollisionBool at *
  split
  · rename_i hparse
    rw [hparse] at hb
    exact noMemoCollision_of_bool hb _
  · rename_i msg hparse
    rw [hparse] at hb
    simp only [Bool.and_eq_true] at hb
    rintro (hmemo | hmac)
    · exact noMemoCollision_of_bool hb.1 _ hmemo
    · exact not_macTagForgeryOrCollision_of_bool hb.2 _ hmac

/-- Computable `Bool` check refuting `ReselectCollisionOn interp r S g tr vis salts t`: every stored
ratchet key `rk ∈ storedRatchetKeys r tr msg` either equals `msg.ratchetKey` syntactically or has
distinct concretized bytes `γ rk ≠ γ msg.ratchetKey`. -/
def noReselectCollisionBool (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) (t : DY.Bytes) : Bool :=
  let γ := gamma interp S g
  match parseTrSignalMsg t with
  | none => true
  | some msg =>
    (storedRatchetKeys r tr msg).all fun rk =>
      (rk == msg.ratchetKey) || !(γ rk == γ msg.ratchetKey)

theorem not_reselectCollisionOn_check {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {vis : List VisEntry}
    {salts : List DY.Bytes} {t : DY.Bytes}
    (hb : noReselectCollisionBool interp r S g tr t = true) :
    ¬ ReselectCollisionOn interp r S g tr vis salts t := by
  rintro ⟨msg, hparse, rk, hrk, hgamEq, hrkNe, _⟩
  unfold noReselectCollisionBool at hb
  rw [hparse] at hb
  have hall := List.all_eq_true.mp hb rk hrk
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hall
  rcases hall with heq | hgamNe
  · exact hrkNe heq
  · exact hgamNe hgamEq

/-- Discharges `¬ PreKeyStartCollidesOrRejects` universally across all outer `(g, ss)` using a
single clean prefix explanation `(g', ss', vis')` and representation `x`. -/
theorem not_preKeyStartCollidesOrRejects_of_clean {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {evs₁ : List CliEvent} {b : HwBytes} {p : PreKeyFields}
    {g' : Ghost} {ss' : List Step} {vis' : List VisEntry} {x : PreKeyRep}
    (hNoKyber : ¬ KyberMismatch interp r p)
    (hExp : Explains interp r S g' ss' vis' evs₁)
    (hNoRead : ¬ ReadCollisionCli interp r S g' ss' evs₁)
    (hx : x ∈ preKeyRepresentationsOn interp r S g' (runTrace r ss') b)
    (hNoBob : ¬ BobSessionStartCollidesOrImplicitRejectsOn interp r S g'
      (runTrace r ss') vis' (honestSaltsOf r ss') p x) :
    ¬ PreKeyStartCollidesOrRejects interp r S g ss evs₁ b p := by
  rintro ⟨_, hkyb | hall⟩
  · exact hNoKyber hkyb
  · exact hNoBob (hall g' ss' vis' hExp hNoRead x hx)

theorem not_preKeyStartCollidesOrRejects_myInterp {withOpk : Bool}
    {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {evs₁ : List CliEvent} {b : HwBytes} {p : PreKeyFields}
    {g' : Ghost} {ss' : List Step} {vis' : List VisEntry} {x : PreKeyRep}
    (hExp : Explains myInterp (mkRecords withOpk) S g' ss' vis' evs₁)
    (hNoRead : ¬ ReadCollisionCli myInterp (mkRecords withOpk) S g' ss' evs₁)
    (hx : x ∈ preKeyRepresentationsOn myInterp (mkRecords withOpk) S g' (runTrace (mkRecords withOpk) ss') b)
    (hNoBob : ¬ BobSessionStartCollidesOrImplicitRejectsOn myInterp (mkRecords withOpk) S g'
      (runTrace (mkRecords withOpk) ss') vis' (honestSaltsOf (mkRecords withOpk) ss') p x) :
    ¬ PreKeyStartCollidesOrRejects myInterp (mkRecords withOpk) S g ss evs₁ b p :=
  not_preKeyStartCollidesOrRejects_of_clean (not_kyberMismatch_myInterp withOpk p)
    hExp hNoRead hx hNoBob

/-- Discharges `¬ SignalMsgAcceptedOnlyViaCollision` universally across all outer `(g, ss)` using a
single clean prefix explanation `(g', ss', vis')` and accepted representation `t`. -/
theorem not_signalMsgAcceptedOnlyViaCollision_of_clean {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {evs₁ : List CliEvent} {ev : RunEvent} {b : HwBytes}
    {g' : Ghost} {ss' : List Step} {vis' : List VisEntry} {t : DY.Bytes}
    (hExp : Explains interp r S g' ss' vis' evs₁)
    (hNoRead : ¬ ReadCollisionCli interp r S g' ss' evs₁)
    (ht : t ∈ recvRepresentationsOn interp S g' (runTrace r ss') b)
    (hAcc : ModelAcceptsTermAfterAttackerSends interp r S g' ss' evs₁ ev t)
    (hNoRecv : ¬ RecvCollisionOn interp r S g' (runTrace r ss') vis' (honestSaltsOf r ss') t)
    (hNoResel : ¬ ReselectCollisionOn interp r S g' (runTrace r ss') vis' (honestSaltsOf r ss') t) :
    ¬ SignalMsgAcceptedOnlyViaCollision interp r S g ss evs₁ ev b := by
  rintro ⟨_, hall⟩
  rcases hall g' ss' vis' hExp hNoRead with hallColl | ⟨_, hallAcc⟩
  · rcases hallColl t ht with hrc | hrs
    · exact hNoRecv hrc
    · exact hNoResel hrs
  · exact hNoRecv (hallAcc t ht hAcc)

theorem not_nextEventCollides_accepted_recv {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent} {peer : CryptoVerification.SignalSession.Address} {tag : BitVec 8} {body : HwBytes}
    (hcmd : ev.cmd = .recv peer := by rfl)
    (hin : ev.input = tag :: body := by rfl)
    (hWhisper : tag = wireWhisperTag →
      ¬ SignalMsgAcceptedOnlyViaCollision interp r S g ss evs₁ ev body)
    (hPreKey : ∀ p, parsePreKeyWire (tag :: body) = some p →
      (KnownBaseKeyOn interp S g (runTrace r ss) p →
        ¬ SignalMsgAcceptedOnlyViaCollision interp r S g ss evs₁ ev p.message) ∧
      (¬ KnownBaseKeyOn interp S g (runTrace r ss) p →
        ¬ PreKeyStartCollidesOrRejects interp r S g ss evs₁ (tag :: body) p)) :
    ¬ NextEventCollides interp r S g ss vis evs₁ ev := by
  unfold NextEventCollides
  rw [hcmd, hin]
  rintro ⟨_, ⟨htag, hsm⟩ | ⟨p, hp, ⟨hkb, _, _, hsm⟩ | ⟨hnkb, hpk⟩⟩⟩
  · exact hWhisper htag hsm
  · exact (hPreKey p hp).1 hkb hsm
  · exact (hPreKey p hp).2 hnkb hpk

theorem not_nextEventCollides_accepted_whisper {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent} {peer : CryptoVerification.SignalSession.Address} {body : HwBytes}
    {g' : Ghost} {ss' : List Step} {vis' : List VisEntry} {t : DY.Bytes}
    (hcmd : ev.cmd = .recv peer)
    (hin : ev.input = wireWhisperTag :: body)
    (hExp : Explains interp r S g' ss' vis' evs₁)
    (hNoRead : ¬ ReadCollisionCli interp r S g' ss' evs₁)
    (ht : t ∈ recvRepresentationsOn interp S g' (runTrace r ss') body)
    (hAcc : ModelAcceptsTermAfterAttackerSends interp r S g' ss' evs₁ ev t)
    (hNoRecv : ¬ RecvCollisionOn interp r S g' (runTrace r ss') vis' (honestSaltsOf r ss') t)
    (hNoResel : ¬ ReselectCollisionOn interp r S g' (runTrace r ss') vis' (honestSaltsOf r ss') t) :
    ¬ NextEventCollides interp r S g ss vis evs₁ ev := by
  apply not_nextEventCollides_accepted_recv hcmd hin
  · intro _
    exact not_signalMsgAcceptedOnlyViaCollision_of_clean hExp hNoRead ht hAcc hNoRecv hNoResel
  · intro p hp
    have htag : wireWhisperTag ≠ wirePrekeyTag := by decide
    simp [parsePreKeyWire, htag] at hp

theorem not_nextEventCollides_accepted_whisper_check {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent} {peer : CryptoVerification.SignalSession.Address} {body : HwBytes}
    {g' : Ghost} {ss' : List Step} {vis' : List VisEntry} {t : DY.Bytes}
    (hcmd : ev.cmd = .recv peer := by rfl)
    (hin : ev.input = wireWhisperTag :: body := by rfl)
    (hExp : Explains interp r S g' ss' vis' evs₁)
    (hNoRead : ¬ ReadCollisionCli interp r S g' ss' evs₁)
    (ht : t ∈ recvRepresentationsOn interp S g' (runTrace r ss') body)
    (hAcc : ModelAcceptsTermAfterAttackerSends interp r S g' ss' evs₁ ev t)
    (hNoRecv : noRecvCollisionBool interp r S g' (runTrace r ss') vis'
      (honestSaltsOf r ss') t = true := by decide)
    (hNoResel : noReselectCollisionBool interp r S g' (runTrace r ss') t = true := by decide) :
    ¬ NextEventCollides interp r S g ss vis evs₁ ev :=
  not_nextEventCollides_accepted_whisper hcmd hin hExp hNoRead ht hAcc
    (not_recvCollisionOn_check hNoRecv) (not_reselectCollisionOn_check hNoResel)

theorem not_nextEventCollides_accepted_prekey {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent} {peer : CryptoVerification.SignalSession.Address} {body : HwBytes} {p : PreKeyFields}
    (hcmd : ev.cmd = .recv peer)
    (hin : ev.input = wirePrekeyTag :: body)
    (hp : parsePreKeyWire (wirePrekeyTag :: body) = some p)
    (hNotKnown : ¬ KnownBaseKeyOn interp S g (runTrace r ss) p)
    (hNoPk : ¬ PreKeyStartCollidesOrRejects interp r S g ss evs₁ (wirePrekeyTag :: body) p) :
    ¬ NextEventCollides interp r S g ss vis evs₁ ev := by
  apply not_nextEventCollides_accepted_recv hcmd hin
  · intro htag
    have hne : wirePrekeyTag ≠ wireWhisperTag := by decide
    exact absurd htag hne
  · intro p' hp'
    rw [hp] at hp'
    injection hp' with heq
    subst heq
    exact ⟨fun hkb => absurd hkb hNotKnown, fun _ => hNoPk⟩

theorem not_nextEventCollides_accepted_prekey_both {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent} {peer : CryptoVerification.SignalSession.Address} {body : HwBytes} {p : PreKeyFields}
    (hcmd : ev.cmd = .recv peer)
    (hin : ev.input = wirePrekeyTag :: body)
    (hp : parsePreKeyWire (wirePrekeyTag :: body) = some p)
    (hNoSm : ¬ SignalMsgAcceptedOnlyViaCollision interp r S g ss evs₁ ev p.message)
    (hNoPk : ¬ PreKeyStartCollidesOrRejects interp r S g ss evs₁ (wirePrekeyTag :: body) p) :
    ¬ NextEventCollides interp r S g ss vis evs₁ ev := by
  apply not_nextEventCollides_accepted_recv hcmd hin
  · intro htag
    have hne : wirePrekeyTag ≠ wireWhisperTag := by decide
    exact absurd htag hne
  · intro p' hp'
    rw [hp] at hp'
    injection hp' with heq
    subst heq
    exact ⟨fun _ => hNoSm, fun _ => hNoPk⟩

/-! ## Pre-Key `recv` Wrappers -/

/-- Discharges `¬ NextEventCollides` at Bob's initial pre-key `recv` under `myInterp` and
`mkRecords withOpk` when `evs₁` contains no `.recv` run events. -/
theorem not_nextEventCollides_accepted_prekey_no_recv {withOpk : Bool}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent} {peer : CryptoVerification.SignalSession.Address} {body : HwBytes} {p : PreKeyFields}
    {g' : Ghost} {ss' : List Step} {vis' : List VisEntry} {x : PreKeyRep}
    (hcmd : ev.cmd = .recv peer := by rfl)
    (hin : ev.input = wirePrekeyTag :: body := by rfl)
    (hOuterExp : Explains myInterp (mkRecords withOpk) S g ss vis evs₁)
    (hNoRecvEv : evs₁.all noRecvEvent = true := by decide)
    (hp : parsePreKeyWire (wirePrekeyTag :: body) = some p := by decide)
    (hCleanExp : Explains myInterp (mkRecords withOpk) S g' ss' vis' evs₁)
    (hNoRead : ¬ ReadCollisionCli myInterp (mkRecords withOpk) S g' ss' evs₁)
    (hx : x ∈ preKeyRepresentationsOn myInterp (mkRecords withOpk) S g'
      (runTrace (mkRecords withOpk) ss') (wirePrekeyTag :: body))
    (hNoBob : ¬ BobSessionStartCollidesOrImplicitRejectsOn myInterp (mkRecords withOpk) S g'
      (runTrace (mkRecords withOpk) ss') vis' (honestSaltsOf (mkRecords withOpk) ss') p x) :
    ¬ NextEventCollides myInterp (mkRecords withOpk) S g ss vis evs₁ ev :=
  not_nextEventCollides_accepted_prekey hcmd hin hp
    (not_knownBaseKeyOn_of_no_recv (mkRecords_wf withOpk) hOuterExp hNoRecvEv)
    (not_preKeyStartCollidesOrRejects_myInterp hCleanExp hNoRead hx hNoBob)

/-- Discharges `¬ NextEventCollides` at a subsequent pre-key-wrapped `recv` under `myInterp` and
`mkRecords withOpk`, refuting both the `KnownBaseKeyOn` and `¬ KnownBaseKeyOn` branches from a
single clean prefix explanation `(g', ss', vis')`. -/
theorem not_nextEventCollides_accepted_prekey_subsequent {withOpk : Bool}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent} {peer : CryptoVerification.SignalSession.Address} {body : HwBytes} {p : PreKeyFields}
    {g' : Ghost} {ss' : List Step} {vis' : List VisEntry} {t : DY.Bytes} {x : PreKeyRep}
    (hcmd : ev.cmd = .recv peer := by rfl)
    (hin : ev.input = wirePrekeyTag :: body := by rfl)
    (hp : parsePreKeyWire (wirePrekeyTag :: body) = some p := by decide)
    (hCleanExp : Explains myInterp (mkRecords withOpk) S g' ss' vis' evs₁)
    (hNoRead : ¬ ReadCollisionCli myInterp (mkRecords withOpk) S g' ss' evs₁)
    (ht : t ∈ recvRepresentationsOn myInterp S g' (runTrace (mkRecords withOpk) ss') p.message)
    (hAcc : ModelAcceptsTermAfterAttackerSends myInterp (mkRecords withOpk) S g' ss' evs₁ ev t)
    (hNoRecv : noRecvCollisionBool myInterp (mkRecords withOpk) S g'
      (runTrace (mkRecords withOpk) ss') vis'
      (honestSaltsOf (mkRecords withOpk) ss') t = true := by decide)
    (hNoResel : noReselectCollisionBool myInterp (mkRecords withOpk) S g'
      (runTrace (mkRecords withOpk) ss') t = true := by decide)
    (hx : x ∈ preKeyRepresentationsOn myInterp (mkRecords withOpk) S g'
      (runTrace (mkRecords withOpk) ss') (wirePrekeyTag :: body))
    (_hKnownEk : ((bobDoneBaseKeys (runTrace (mkRecords withOpk) ss')).any fun ek =>
        gamma myInterp S g' ek == gamma myInterp S g' x.ek) = true := by decide)
    (hNoBob : noBobStartCollisionBool myInterp (mkRecords withOpk) S g'
      (runTrace (mkRecords withOpk) ss') vis'
      (honestSaltsOf (mkRecords withOpk) ss') p x = true := by decide) :
    ¬ NextEventCollides myInterp (mkRecords withOpk) S g ss vis evs₁ ev :=
  not_nextEventCollides_accepted_prekey_both hcmd hin hp
    (not_signalMsgAcceptedOnlyViaCollision_of_clean hCleanExp hNoRead ht hAcc
      (not_recvCollisionOn_check hNoRecv) (not_reselectCollisionOn_check hNoResel))
    (not_preKeyStartCollidesOrRejects_myInterp hCleanExp hNoRead hx
      (not_bobSessionStartCollidesOrImplicitRejectsOn_check hNoBob))

end Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
