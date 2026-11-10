/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFrame
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkReg
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.RoFrame
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Stage 1 (`registration-id` and `signed-pre-key`) Helpers of Arm `R1b` (`R+0x074c → R+0x1260`)
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

theorem r1b_errCommon_fold (A : RustAlloc) (g : RunCall) (d : Init1Data)
    (s0 : State) (resStack : Nat) :
    r1b_errCore A g d s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap =
      r1b_errCommon A g d s0 resStack := rfl

theorem r1b_fnBase_eq {img : Obj.Image} {ext : String → Option (State → State)} {fnBase : BitVec 64}
    (heq : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase) :
    fnBase = img.base + bv% (ls_off% "libsignal_cli::run") := by
  rw [← heq, Program.fnAddr_rebase, r1b_run_fnOff]

theorem r1b_live_bytes_to_ownedBytes (A : RustAlloc) {buf : BitVec 64} {bs : List (BitVec 8)}
    (hbuf : buf ≠ 0#64) (hpos : 0 < bs.length) (hlen : bs.length < 2 ^ 63) :
    A.live buf bs.length 1 ∗ (buf ↦ₛ bs) ⊢
      ownedBytes A (BitVec.ofNat 64 bs.length) buf (BitVec.ofNat 64 bs.length) bs := by
  rw [r1b_ownedBytes_borrow]
  have hcap_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; simp only [hcap_nat, BitVec.toNat_ofNat] at this; omega
  refine Entails.pure_right ⟨rfl, by omega, by omega, hbuf⟩ ?_
  dsimp only [r1b_ownedRest]
  simp only [show (0 : BitVec 64) = 0#64 from rfl, hne0, ↓reduceIte, hcap_nat, Nat.sub_self,
    memRegion_zero, sepConj_emp]
  exact Entails.of_eq (by ac_rfl)

theorem r1b_sepWPp_pure_left {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hk : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom := SepWPp.pure_elim hk

theorem r1b_sepWPp_borrow_core (A : RustAlloc) {prog : Program} {ret : BitVec 64} {s : State}
    {cap ptr len : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hk : (len = BitVec.ofNat 64 bs.length ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) →
      SepWPp prog ret s ((ptr ↦ₛ bs) ∗ r1b_ownedRest A cap ptr bs.length ∗ F) Q Qp oom) :
    SepWPp prog ret s (ownedBytes A cap ptr len bs ∗ F) Q Qp oom := by
  rw [r1b_ownedBytes_borrow A cap ptr len bs]
  simp only [sepConj_assoc]
  exact SepWPp.pure_elim hk

macro "r1b_prove_spe_str" : tactic =>
  `(tactic| (refine r1b_SpePayload_str _ ?_; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits))

macro "r1b_ac" : tactic =>
  `(tactic| first | rfl | simp only [emp_sepConj] | ac_rfl | ((try dsimp +zetaDelta only); first | rfl | simp only [emp_sepConj] | ac_rfl))

private meta def r1bStripLets2 : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLets2 n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLets2 n e
  | _, e => e

private meta def r1bSplitSep2 : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLets2 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSep2 fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSep2 fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPure2 (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLets2 64 x; let a := r1bStripLets2 64 a
  if x.getAppFn.constName? != a.getAppFn.constName? then return false
  let n := x.getAppNumArgs
  if n != a.getAppNumArgs then return false
  let st ← Lean.saveState
  let mut ok := true
  for i in [0:n] do
    if ok then ok ← Lean.Meta.isDefEq (x.getArg! i) (a.getArg! i)
  st.restore
  return ok

elab:10 "r1b_call_frame" "<|" h:term:10 : term <= expectedType => do
    let exp ← Lean.instantiateMVars expectedType
    if exp.isMVar then Lean.Elab.Term.tryPostpone
    let expS := r1bStripLets2 64 exp
    let hExpr ← Lean.Elab.Term.elabTerm h none
    let hTy0 := r1bStripLets2 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
    for idx in [0, 1, 2, 4, 5, 6] do
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
    let p ← Lean.instantiateMVars (expS.getArg! 3)
    let p' ← Lean.instantiateMVars ((r1bStripLets2 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
    let sepTy := Lean.mkConst ``SepProp []
    let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
    let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
    let sar := sepSample.getAppNumArgs
    let mkSep (x y : Lean.Expr) : Lean.Expr :=
      sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
    let ps := (r1bSplitSep2 64 sepSample p).toList
    let p's := (r1bSplitSep2 64 sepSample p').toList
    let mut mvarFOpt : Option Lean.Expr := none
    let mut a1s : List Lean.Expr := []
    for a in p's do
      let ai ← Lean.instantiateMVars a
      if mvarFOpt.isNone && ai.isMVar then mvarFOpt := some ai
      else a1s := a1s.concat ai
    let mut rem := ps
    for a in a1s do
      let mut removed := false
      let mut next : List Lean.Expr := []
      for x in rem do
        if !removed && (← r1bIsDefEqPure2 x a) then removed := true
        else next := next.concat x
      rem := next
    let remProd := match rem.reverse with
      | [] => empExpr
      | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
    if let some mf := mvarFOpt then
      discard <| Lean.Meta.isDefEq mf remProd
    let eqTy ← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')
    let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac)) (some eqTy)
    let ent ← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof]
    Lean.Meta.mkAppM ``MainHops.sepWPp_weaken_pre #[ent, hExpr]

gen_decodes CryptoVerification.libsignalSessionCode_tree r1bDecRegSpk
  [(ls_off% "libsignal_cli::run" + 0x074c) → (ls_off% "libsignal_cli::run" + 0x07a4),
   (ls_off% "libsignal_cli::run" + 0x0c14) → (ls_off% "libsignal_cli::run" + 0x0cdc),
   (ls_off% "libsignal_cli::run" + 0x0cec) → (ls_off% "libsignal_cli::run" + 0x0d24),
   (ls_off% "libsignal_cli::run" + 0x0df0) → (ls_off% "libsignal_cli::run" + 0x0e54),
   (ls_off% "libsignal_cli::run" + 0x11b4) → (ls_off% "libsignal_cli::run" + 0x1260),
   (ls_off% "libsignal_cli::run" + 0x1384) → (ls_off% "libsignal_cli::run" + 0x13e0)]

/-! ## Error Exits (`0x13bc`, `0x1384`, `0x11b4`, `0x0df0`, `0x0cec`, `0x0c14`) -/

set_option maxHeartbeats 400000 in
private theorem r1b_err_13bc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr spkCap spkPtr regCap regPtr : BitVec 64}
    {eBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x13bc)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1)
    (hx10 : s.readReg64 (.gpr 10#5) = eCap)
    (hx27 : s.readReg64 (.gpr 27#5) = ePtr)
    (hx2 : s.readReg64 .x2 = ((BitVec.ofNat 64 eBs.length).truncate 32).zeroExtend 64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗ ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4f0#64) 16 ∗
        ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  have hst := hc.st
  have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hfp := hst.fp; have hinv := hst.inv; have hvregs := hst.vregs; have hsp0 := hst.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hsp0
  have hsplit16 := r1b_region16_to_cells (fsp + 0x4f0#64)
  have h4f8 : (fsp + 0x4f0#64) + 8#64 = fsp + 0x4f8#64 := by bv_omega
  rw [h4f8] at hsplit16
  have he8 : ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) =
      ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
        ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) := by
    have hz := r1b_u64_split32 (fsp + 0x4e8#64) (BitVec.ofNat 64 eBs.length)
    have ha : (fsp + 0x4e8#64) + 4#64 = fsp + 0x4ec#64 := by bv_omega
    rwa [ha] at hz
  rw [he8, hsplit16]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x13bc 0x24
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2b28#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm hinv_m => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2b28 := hc.of_step
    { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hrun], sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hfp, inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hvregs, spAligned := hsp0 }
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
  refine MainHops.sepWPp_weaken_pre ?_
    (herrCommon ▸ r1b_cleanup_2b28 (spkCap := spkCap) (spkPtr := spkPtr)
      (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr)
      (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs) hh hdrop hbnd hc_m hpanic hrej)
  have h4d0 :
      ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗
        ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        (((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
          ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32)) ∗
        ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) ⊢
        memRegion (fsp + 0x4d0#64) 48 := by
    rw [← he8]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      r1b_cells6_to_region48 (fsp + 0x4d0#64) (speWord 1) eCap ePtr (BitVec.ofNat 64 eBs.length) w4 w5
  have hpay : ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ⊢
      r1b_SpePayload A (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5))
        (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
        (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
        (sm.readReg64 (.gpr 2#5)) := by
    simp only [hsm, arm64_norm, hx12, hx10, hx27, hx2]; r1b_prove_spe_str
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono hpay h4d0) (by r1b_ac)

set_option maxHeartbeats 400000 in
private theorem r1b_err_1384_tail {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 sm : State} {resStack : Nat}
    {buf d2 pCap v188 regCap regPtr : BitVec 64} {regBs : List (BitVec 8)}
    {errCommon : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack) (hc_m : r1b_ErrCtx img ext g d s0 sm 0x2b78)
    (herrCommon : r1b_errCommon A g d s0 resStack = errCommon)
    (hbuf : buf ≠ 0#64)
    (hpay : ∀ eBs, ownedBytes A 22#64 buf 22#64 eBs ⊢
      r1b_SpePayload A (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5)) (sm.readReg64 (.gpr 23#5))
        (sm.readReg64 (.gpr 27#5)) (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5)) (sm.readReg64 (.gpr 2#5)))
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) sm
      (((fsp + 0x170#64) ↦₆₄ 22#64) ∗ ((fsp + 0x188#64) ↦₆₄ v188) ∗
        A.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗ errCommon ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf22_owned A buf d2 hbuf) (by r1b_ac) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun eBs => r1b_sepWPp_pure_left fun _ => ?_
  refine MainHops.sepWPp_weaken_pre ?_
    (herrCommon ▸ r1b_cleanup_2b78 (regCap := regCap) (regPtr := regPtr)
      (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs) hh hdrop hbnd hc_m hpanic hrej)
  (try dsimp +zetaDelta only)
  generalize runFsp s0 = fsp0
  have h4d0 : ((fsp0 + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp0 + 0x4d8#64) 40 ⊢ memRegion (fsp0 + 0x4d0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1b_cell64_cons (a := fsp0 + 0x4d0#64) pCap (n := 40) (by decide)
  have h168 : memRegion (fsp0 + 0x168#64) 8 ∗ ((fsp0 + 0x170#64) ↦₆₄ 22#64) ∗ memRegion (fsp0 + 0x178#64) 8 ⊢
      memRegion (fsp0 + 0x168#64) 24 := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))) ?_
    rw [r1b_join_region fsp0 0x170 8 8, r1b_join_region fsp0 0x168 8 16]; exact Entails.refl _
  have h188 : ((fsp0 + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp0 + 0x190#64) 8 ⊢ memRegion (fsp0 + 0x188#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1b_cell64_cons (a := fsp0 + 0x188#64) v188 (n := 8) (by decide)
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono (hpay eBs) (sepConj_mono h4d0 (sepConj_mono h168 h188))) (by r1b_ac)

private theorem r1b_err_1384 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {buf d2 pCap v188 regCap regPtr : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack) (hc : r1b_ErrCtx img ext g d s0 s 0x1384) (hbuf : buf ≠ 0#64)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1) (_hx9 : s.readReg64 (.gpr 9#5) = buf)
    (hx2 : s.readReg64 .x2 = 22#64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (A.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 8 ∗ ((fsp + 0x170#64) ↦₆₄ 22#64) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x1384 0x38
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2b78#64) hst.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm hinv_m => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2b78 := hc.of_step
    { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hst.run], sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hst.fp, inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs, spAligned := hst.spAligned }
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
  have hpay : ∀ eBs, ownedBytes A 22#64 buf 22#64 eBs ⊢
      r1b_SpePayload A (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5)) (sm.readReg64 (.gpr 23#5))
        (sm.readReg64 (.gpr 27#5)) (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5)) (sm.readReg64 (.gpr 2#5)) := fun eBs => by
    simp only [hsm, arm64_norm, hx12, hx2]; r1b_prove_spe_str
  exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by (try dsimp +zetaDelta only); generalize runFsp s0 = fsp0; r1b_ac))
    (r1b_err_1384_tail hh hdrop hbnd hc_m herrCommon hbuf hpay hpanic hrej)

set_option maxHeartbeats 400000 in
private theorem r1b_err_11c4 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 sf2 : State} {resStack : Nat}
    {buf pCap pPtr regCap regPtr : BitVec 64} {pBs regBs : List (BitVec 8)}
    {errCore : SepProp} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooksExt img A ext)
    (hdrop : RunDrop.DropSpeOwnedOk img A ext) (hbnd : r1b_StackBounds B resStack)
    (herrCore : r1b_errCore A g d s0 = errCore)
    (hc2 : r1b_ErrCtx img ext g d s0 sf2 0x11c4)
    (hx0_buf : sf2.readReg64 .x0 = buf) (hbuf : buf ≠ 0#64)
    (hx23_2 : sf2.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) sf2
      (A.live buf 22 1 ∗ memRegion buf 22 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        errCore ∗ anyHeap ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗ memRegion (fsp + 0x120#64) 16 ∗
        memRegion (fsp + 0x150#64) 16 ∗ memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  have hin2 := hc2.st
  have hbuf_f : (buf == 0#64) = false := beq_false_of_ne hbuf
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hin2.sp hin2.spAligned
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x11c4 0x74
  have hpc2_in := hin2.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2_in ⊢
  generalize_entry heq_fnBase : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  have hrun2_in := hin2.run
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x11d0#64) hin2.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm_a hsm_a hinv_a => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hin2 : InRun img ext s0 sm_a 0x11d0 :=
    { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm_a, arm64_norm]
      run := by simp [hsm_a, arm64_norm, hin2.run], sp := by simpa [hsm_a, arm64_norm] using hin2.sp
      fp := by simpa [hsm_a, arm64_norm] using hin2.fp, inv := hinv_a
      vregs := by simpa [calleeSavedVRegs, hsm_a, arm64_norm] using hin2.vregs, spAligned := hin2.spAligned }
  have hc2 : r1b_ErrCtx img ext g d s0 sm_a 0x11d0 := hc2.of_step hin2
    (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm])
    (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm])
  have hx0_buf : sm_a.readReg64 .x0 = buf := by simpa [hsm_a, arm64_norm] using hx0_buf
  have hx23_2 : sm_a.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by simpa [hsm_a, arm64_norm] using hx23_2
  have hx27_2 : sm_a.readReg64 (.gpr 27#5) = pPtr := by simpa [hsm_a, arm64_norm] using hx27_2
  have hx8_ro : sm_a.readReg64 (.gpr 8#5) = img.base + BitVec.ofNat 64
      (num% (ls_xref% (ls_off% "libsignal_cli::run" + 0x11c8) (ls_off% "libsignal_cli::run" + (0x11c8 + 4)))) := by
    have hba := RunSkeleton.base_aligned himg
    simp only [hsm_a, arm64_norm, r1b_fnBase_eq heq_fnBase]
  refine r1b_sepWPp_with_ro hin2.inv (r1b_ro_unreadable_11c8 himg) ?_
  obtain ⟨ro0, ro1, ro2, roRem, hroEq⟩ := r1b_ro_split22 (sm_a.readReg64 (.gpr 8#5))
  conv at hroEq => lhs; rw [hx8_ro]
  clear hsm_a hx8_ro
  rw [hroEq, r1b_buf22_split1 buf, ProofLib.memRegion_eight (fsp + 0x170#64), ProofLib.memRegion_eight (fsp + 0x188#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun v170 => SepWPp.exists_elim fun v188 => ?_
  have hpc2 := hin2.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢; rw [heq_fnBase] at hpc2
  have hrun2 := hin2.run; have hsp2 : sm_a.sp = fsp := hin2.sp
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x11e8#64) hin2.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  refine r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left ?_
  refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf22_realign buf _ _) (by r1b_ac) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun d2 => ?_
  dsimp only [runPc, mProg, tripleRatchetProgAtExt]
  by_cases hpCap : pCap = 0#64
  · subst hpCap
    have hpc3 : sm3.pc = fnBase + 0x11e8#64 := by simp [hsm3, arm64_norm]
    have hrun3 : sm3.status = .Running := by simp [hsm3, arm64_norm, hin2.run]
    have hsp3 : sm3.sp = fsp := by simpa [hsm3, arm64_norm] using hin2.sp
    have hr0 : sm3.readReg64 .x0 = buf := by simpa [hsm3, arm64_norm] using hx0_buf
    have hr23 : sm3.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by simpa [hsm3, arm64_norm] using hx23_2
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x1384#64) hinv3
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm4 hsm4 hinv4 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc4 : r1b_ErrCtx img ext g d s0 sm4 0x1384 := hc2.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm4, arm64_norm]
        run := by simp [hsm4, arm64_norm, hin2.run], sp := by simpa [hsm4, arm64_norm] using hin2.sp
        fp := by simpa [hsm4, arm64_norm] using hin2.fp, inv := hinv4
        vregs := by simpa [calleeSavedVRegs, hsm4, arm64_norm] using hin2.vregs, spAligned := hin2.spAligned }
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
    refine r1b_sepWPp_frame (by r1b_ac) (r1b_ownedBytes_zero A pPtr (BitVec.ofNat 64 pBs.length) pBs) (by r1b_ac) ?_
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_err_1384 (d2 := ro2) (pCap := 0#64) (v188 := d0)
        (regCap := regCap) (regPtr := regPtr) (regBs := regBs) hh hdrop hbnd hc4 hbuf
        (by simp [hsm4, arm64_norm, speWord])
        (by simp [hsm4, arm64_norm])
        (by simp [hsm4, arm64_norm]) hpanic hrej)
    subst herrCore; dsimp only [r1b_errCommon]; (try dsimp +zetaDelta only)
    generalize runFsp s0 = fsp0; exact Entails.of_eq (by r1b_ac)
  · have hpCap_f : (pCap == 0#64) = false := beq_false_of_ne hpCap
    have hpc3 : sm3.pc = fnBase + 0x11e8#64 := by simp [hsm3, arm64_norm]
    have hrun3 : sm3.status = .Running := by simp [hsm3, arm64_norm, hin2.run]
    have hsp3 : sm3.sp = fsp := by simpa [hsm3, arm64_norm] using hin2.sp
    have hr0 : sm3.readReg64 .x0 = buf := by simpa [hsm3, arm64_norm] using hx0_buf
    apply MainHops.sepWPp_seq_inImage
      (mid := fnBase + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run")) hinv3
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm4 hsm4 hinv4 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hx0_sm4 : sm4.readReg64 .x0 = pPtr := by
      simp [hsm4, arm64_norm]
    refine r1b_call_frame <| r1b_call_dealloc_ownedBytes (bs := pBs) hh hbnd hinv4
      (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm, hin2.run]) (by simpa [hsm4, arm64_norm] using hin2.sp)
      (by simpa [hsm4, arm64_norm] using hin2.fp) (by simpa [calleeSavedVRegs, hsm4, arm64_norm] using hin2.vregs)
      hin2.spAligned (retOff := 0x121c)
      (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm4, arm64_norm])
      hx0_sm4
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      hpCap hpanic fun sf4 hin4 hcs4 hfs4 htr4 => ?_
    have hc4 : r1b_ErrCtx img ext g d s0 sf4 0x121c := hc2.after_call
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) hin4 hcs4 (congrArg FsState.files hfs4) htr4
    have hx23_4 : sf4.readReg64 (.gpr 23#5) = 22#64 := hcs4.2.2.2.2.1.trans (by simp [hsm4, arm64_norm])
    have hx26_4 : sf4.readReg64 (.gpr 26#5) = speWord 1 :=
      hcs4.2.2.2.2.2.2.2.1.trans (by simp [hsm4, arm64_norm, speWord])
    have hx27_4 : sf4.readReg64 (.gpr 27#5) = buf :=
      hcs4.2.2.2.2.2.2.2.2.1.trans (by simp [hsm4, arm64_norm])
    have hpc4 := hin4.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc4 ⊢; rw [heq_fnBase] at hpc4
    have hrun4 := hin4.run; have hsp4 : sf4.sp = fsp := hin4.sp
    have hv188 : sm3.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by simpa [hsm3, arm64_norm] using hx23_2
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x1384#64) hin4.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm5 hsm5 hinv5 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc5 : r1b_ErrCtx img ext g d s0 sm5 0x1384 := hc4.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm5, arm64_norm]
        run := by simp [hsm5, arm64_norm, hin4.run], sp := by simpa [hsm5, arm64_norm] using hin4.sp
        fp := by simpa [hsm5, arm64_norm] using hin4.fp, inv := hinv5
        vregs := by simpa [calleeSavedVRegs, hsm5, arm64_norm] using hin4.vregs, spAligned := hin2.spAligned }
      (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
      (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_err_1384 (d2 := ro2) (pCap := pCap) (v188 := 0xffffffffffffffff#64)
        (regCap := regCap) (regPtr := regPtr) (regBs := regBs) hh hdrop hbnd hc5 hbuf
        (by simp [hsm5, arm64_norm, speWord])
        (by simp [hsm5, arm64_norm])
        (by simp [hsm5, arm64_norm]) hpanic hrej)
    subst herrCore; dsimp only [r1b_errCommon]; (try dsimp +zetaDelta only)
    generalize runFsp s0 = fsp0; exact Entails.of_eq (by r1b_ac)

theorem r1b_err_11b4 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {pCap pPtr regCap regPtr : BitVec 64} {pBs regBs : List (BitVec 8)} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooksExt img A ext)
    (hdrop : RunDrop.DropSpeOwnedOk img A ext) (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x11b4)
    (hx23 : s.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64) (hx27 : s.readReg64 (.gpr 27#5) = pPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗ r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗ memRegion (fsp + 0x120#64) 16 ∗
        memRegion (fsp + 0x150#64) 16 ∗ memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp; dsimp only [r1b_errCommon]; generalize herrCore : r1b_errCore A g d s0 = errCore
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x11b4 0x18
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli::run")) hst.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  refine r1b_call_frame <| r1b_call_shim hh hbnd hinv1
    (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm, hst.run]) (by simpa [hsm1, arm64_norm] using hst.sp)
    (by simpa [hsm1, arm64_norm] using hst.fp) (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
    hst.spAligned (retOff := 0x11b8)
    (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
    hpanic fun sf1 hin1 hcs1 hfs1 htr1 => ?_
  have hc1 : r1b_ErrCtx img ext g d s0 sf1 0x11b8 := hc.after_call
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) hin1 hcs1 (congrArg FsState.files hfs1) htr1
  have hx23_1 : sf1.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
    hcs1.2.2.2.2.1.trans (by simpa [hsm1, arm64_norm] using hx23)
  have hx27_1 : sf1.readReg64 (.gpr 27#5) = pPtr :=
    hcs1.2.2.2.2.2.2.2.2.1.trans (by simpa [hsm1, arm64_norm] using hx27)
  have hpc1 := hin1.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢; rw [heq_fnBase] at hpc1
  have hrun1 := hin1.run
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli::run")) hin1.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  refine r1b_call_frame <| r1b_call_alloc (size := 22) (align := 1) hh hbnd hinv2
    (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
    (by simp [hsm2, arm64_norm, hin1.run]) (by simpa [hsm2, arm64_norm] using hin1.sp)
    (by simpa [hsm2, arm64_norm] using hin1.fp) (by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs)
    hst.spAligned (retOff := 0x11c4)
    (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
    (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by decide) (r1b_layout1 22) hpanic
    (fun sf2 hin2 _ hx0_0 _ htr_null => ?_) (fun sf2 buf hin2 hcs2 hx0_buf hbuf hfs2 htr2 => ?_)
  · have hpc2 := hin2.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢; rw [heq_fnBase] at hpc2
    have hrun2 := hin2.run
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2d68#64) hin2.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
    exact r1b_oom_2d68
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm]
        run := by simp [hsm3, arm64_norm, hin2.run], sp := by simpa [hsm3, arm64_norm] using hin2.sp
        fp := by simpa [hsm3, arm64_norm] using hin2.fp, inv := hinv3
        vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs, spAligned := hst.spAligned }
      hpanic (r1b_allocFailedIn_mono
        (r1b_allocFailed_of_null (by simpa [hsm2, arm64_norm] using hc1.trace) htr_null) (by simp [hsm3, arm64_norm]))
  · have hc2 : r1b_ErrCtx img ext g d s0 sf2 0x11c4 := hc1.after_call
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) hin2 hcs2 (congrArg FsState.files hfs2) htr2
    have hx23_2 : sf2.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
      hcs2.2.2.2.2.1.trans (by simpa [hsm2, arm64_norm] using hx23_1)
    have hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr :=
      hcs2.2.2.2.2.2.2.2.2.1.trans (by simpa [hsm2, arm64_norm] using hx27_1)
    exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
      (r1b_err_11c4 himg hh hdrop hbnd herrCore hc2 hx0_buf hbuf hx23_2 hx27_2 hpanic hrej)

theorem r1b_err_0df0 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regCap regPtr : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x0df0)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x0df0 0x64
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli::run"))
    hst.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_shim hh hbnd hinv1
      (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run]) (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x0df4)
      (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      hpanic fun sf1 hin1 hcs1 hfs1 htr1 => ?_
  have hc1 : r1b_ErrCtx img ext g d s0 sf1 0x0df4 := hc.after_call
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    hin1 hcs1 (congrArg FsState.files hfs1) htr1
  have hpc1 := hin1.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢; rw [heq_fnBase] at hpc1
  have hrun1 := hin1.run
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli::run")) hin1.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_alloc (size := 14) (align := 1) hh hbnd hinv2
      (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm, hin1.run]) (by simpa [hsm2, arm64_norm] using hin1.sp)
      (by simpa [hsm2, arm64_norm] using hin1.fp)
      (by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs)
      hst.spAligned (retOff := 0x0e00)
      (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by decide) (r1b_layout1 14) hpanic
      (fun sf2 hin2 _ hx0_0 _ htr_null => ?_)
      (fun sf2 buf hin2 hcs2 hx0_buf hbuf hfs2 htr2 => ?_)
  · have hpc2 := hin2.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢; rw [heq_fnBase] at hpc2
    have hrun2 := hin2.run
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2d44#64) hin2.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
    exact r1b_oom_2d44
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm]
        run := by simp [hsm3, arm64_norm, hin2.run], sp := by simpa [hsm3, arm64_norm] using hin2.sp
        fp := by simpa [hsm3, arm64_norm] using hin2.fp, inv := hinv3
        vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs, spAligned := hst.spAligned }
      hpanic (r1b_allocFailedIn_mono
        (r1b_allocFailed_of_null (by simpa [hsm2, arm64_norm] using hc1.trace) htr_null)
        (by simp [hsm3, arm64_norm]))
  · have hc2 : r1b_ErrCtx img ext g d s0 sf2 0x0e00 := hc1.after_call
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      hin2 hcs2 (congrArg FsState.files hfs2) htr2
    have hbuf_f : (buf == 0#64) = false := beq_false_of_ne hbuf
    have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hin2.sp hst.spAligned
    have hpc2_in := hin2.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2_in ⊢; rw [heq_fnBase] at hpc2_in
    have hrun2_in := hin2.run
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x0e0c#64) hin2.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm_a hsm_a hinv_a => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hin2 : InRun img ext s0 sm_a 0x0e0c :=
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm_a, arm64_norm]
        run := by simp [hsm_a, arm64_norm, hin2.run], sp := by simpa [hsm_a, arm64_norm] using hin2.sp
        fp := by simpa [hsm_a, arm64_norm] using hin2.fp, inv := hinv_a
        vregs := by simpa [calleeSavedVRegs, hsm_a, arm64_norm] using hin2.vregs, spAligned := hst.spAligned }
    have hc2 : r1b_ErrCtx img ext g d s0 sm_a 0x0e0c := hc2.of_step hin2
      (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm])
      (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm])
    have hx0_buf : sm_a.readReg64 .x0 = buf := by simpa [hsm_a, arm64_norm] using hx0_buf
    have hx8_ro : sm_a.readReg64 (.gpr 8#5) =
        img.base + BitVec.ofNat 64 (num% (ls_xref% (ls_off% "libsignal_cli::run" + 0x0e04)
          (ls_off% "libsignal_cli::run" + (0x0e04 + 4)))) := by
      have hba := RunSkeleton.base_aligned himg; simp only [hsm_a, arm64_norm, r1b_fnBase_eq heq_fnBase]
    refine r1b_sepWPp_with_ro hin2.inv (r1b_ro_malformed_e04 himg) ?_
    obtain ⟨ro0, ro1, roRem, hroEq⟩ := r1b_ro_split14 (sm_a.readReg64 (.gpr 8#5))
    conv at hroEq => lhs; rw [hx8_ro]
    clear hsm_a hx8_ro
    rw [hroEq, r1b_buf14_split1 buf]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun d0 => ?_
    have hpc2 := hin2.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢; rw [heq_fnBase] at hpc2
    have hrun2 := hin2.run; have hsp2 : sm_a.sp = fsp := hin2.sp
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x0e34#64) hin2.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    refine r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left ?_
    refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf14_realign buf _) (by r1b_ac) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun d1 => ?_
    dsimp only [runPc, mProg, tripleRatchetProgAtExt]
    have hpc : sm3.pc = fnBase + 0x0e34#64 := by simp [hsm3, arm64_norm]
    have hrun : sm3.status = .Running := by simp [hsm3, arm64_norm, hin2.run]
    have hr0 : sm3.readReg64 .x0 = buf := by simpa [hsm3, arm64_norm] using hx0_buf
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2b78#64) hinv3
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm4 hsm4 hinv4 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc4 : r1b_ErrCtx img ext g d s0 sm4 0x2b78 := hc2.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm4, arm64_norm]
        run := by simp [hsm4, arm64_norm, hin2.run], sp := by simpa [hsm4, hsm3, arm64_norm] using hin2.sp
        fp := by simpa [hsm4, hsm3, arm64_norm] using hin2.fp, inv := hinv4
        vregs := by simpa [calleeSavedVRegs, hsm4, hsm3, arm64_norm] using hin2.vregs, spAligned := hst.spAligned }
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
    refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf14_owned A buf _ hbuf) (by r1b_ac) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun eBs => r1b_sepWPp_pure_left fun _ => ?_
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_cleanup_2b78 (regCap := regCap) (regPtr := regPtr)
        (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs) hh hdrop hbnd hc4 hpanic hrej)
    have hpay : ownedBytes A 14#64 buf 14#64 eBs ⊢
        r1b_SpePayload A (sm4.readReg64 (.gpr 12#5)) (sm4.readReg64 (.gpr 10#5))
          (sm4.readReg64 (.gpr 23#5)) (sm4.readReg64 (.gpr 27#5))
          (sm4.readReg64 (.gpr 16#5)) (sm4.readReg64 (.gpr 14#5))
          (sm4.readReg64 (.gpr 15#5)) (sm4.readReg64 (.gpr 28#5))
          (sm4.readReg64 (.gpr 2#5)) := by
      simp only [hsm4, arm64_norm]; r1b_prove_spe_str
    subst herrCore; dsimp only [r1b_errCommon]; (try dsimp +zetaDelta only)
    generalize runFsp s0 = fsp0
    exact r1b_entails_frame (by r1b_ac) hpay (by r1b_ac)

private theorem r1b_err_0cec {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {buf d2 pCap : BitVec 64} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack) (hc : r1b_ErrCtx img ext g d s0 s 0x0cec) (hbuf : buf ≠ 0#64)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1) (_hx25 : s.readReg64 (.gpr 25#5) = 22#64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (A.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ 22#64) ∗ ((fsp + 0x1a0#64) ↦₆₄ buf) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x0cec 0x38
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2bf0#64) hst.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm hinv_m => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2bf0 := hc.of_step
    { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hst.run], sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hst.fp, inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs, spAligned := hst.spAligned }
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
  refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf22_owned A buf d2 hbuf) (by r1b_ac) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun eBs => r1b_sepWPp_pure_left fun _ => ?_
  refine MainHops.sepWPp_weaken_pre ?_ (herrCommon ▸ r1b_cleanup_2bf0 hh hdrop hbnd hc_m hpanic hrej)
  have hpay : ownedBytes A 22#64 buf 22#64 eBs ⊢
      r1b_SpePayload A (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 9#5))
        (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
        (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
        (sm.readReg64 (.gpr 22#5)) := by
    simp only [hsm, arm64_norm, hx12]; r1b_prove_spe_str
  have h4d0 : ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ⊢
      memRegion (fsp + 0x4d0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cell64_cons (a := fsp + 0x4d0#64) pCap (n := 40) (by decide)
  have h188 : memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ 22#64) ∗
      ((fsp + 0x1a0#64) ↦₆₄ buf) ∗ memRegion (fsp + 0x1a8#64) 16 ⊢
      memRegion (fsp + 0x188#64) 48 := by
    rw [← sepConj_assoc ((fsp + 0x198#64) ↦₆₄ 22#64)]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cells2_to_region16 (fsp + 0x198#64) 22#64 buf))) ?_
    rw [r1b_join_region fsp 0x198 16 16, r1b_join_region fsp 0x188 16 32]; exact Entails.refl _
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono hpay (sepConj_mono h4d0 h188)) (by r1b_ac)

set_option maxHeartbeats 400000 in
private theorem r1b_err_0c24 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 sf2 : State} {resStack : Nat}
    {buf pCap pPtr : BitVec 64} {pBs : List (BitVec 8)}
    {errCore : SepProp} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (herrCore : r1b_errCore A g d s0 = errCore)
    (hc2 : r1b_ErrCtx img ext g d s0 sf2 0x0c24)
    (hx0_buf : sf2.readReg64 .x0 = buf) (hbuf : buf ≠ 0#64)
    (hx23_2 : sf2.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) sf2
      (A.live buf 22 1 ∗ memRegion buf 22 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        errCore ∗ anyHeap ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        memRegion (fsp + 0x198#64) 16 ∗ memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  have hin2 := hc2.st
  have hbuf_f : (buf == 0#64) = false := beq_false_of_ne hbuf
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hin2.sp hin2.spAligned
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x0c24 0x50
  have hpc2_in := hin2.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2_in ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  have hrun2_in := hin2.run
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x0c30#64) hin2.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm_a hsm_a hinv_a => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hin2 : InRun img ext s0 sm_a 0x0c30 :=
    { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm_a, arm64_norm]
      run := by simp [hsm_a, arm64_norm, hin2.run], sp := by simpa [hsm_a, arm64_norm] using hin2.sp
      fp := by simpa [hsm_a, arm64_norm] using hin2.fp, inv := hinv_a
      vregs := by simpa [calleeSavedVRegs, hsm_a, arm64_norm] using hin2.vregs, spAligned := hin2.spAligned }
  have hc2 : r1b_ErrCtx img ext g d s0 sm_a 0x0c30 := hc2.of_step hin2
    (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm])
    (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm])
  have hx0_buf : sm_a.readReg64 .x0 = buf := by simpa [hsm_a, arm64_norm] using hx0_buf
  have hx23_2 : sm_a.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by simpa [hsm_a, arm64_norm] using hx23_2
  have hx27_2 : sm_a.readReg64 (.gpr 27#5) = pPtr := by simpa [hsm_a, arm64_norm] using hx27_2
  have hx8_ro : sm_a.readReg64 (.gpr 8#5) =
      img.base + BitVec.ofNat 64 (num% (ls_xref% (ls_off% "libsignal_cli::run" + 0x0c28)
        (ls_off% "libsignal_cli::run" + (0x0c28 + 4)))) := by
    have hba := RunSkeleton.base_aligned himg; simp only [hsm_a, arm64_norm, r1b_fnBase_eq heq_fnBase]
  refine r1b_sepWPp_with_ro hin2.inv (r1b_ro_unreadable_c28 himg) ?_
  obtain ⟨ro0, ro1, ro2, roRem, hroEq⟩ := r1b_ro_split22 (sm_a.readReg64 (.gpr 8#5))
  conv at hroEq => lhs; rw [hx8_ro]
  clear hsm_a hx8_ro
  have h198 := r1b_region16_to_cells (fsp + 0x198#64)
  have ha1a0 : (fsp + 0x198#64) + 8#64 = fsp + 0x1a0#64 := by bv_omega
  rw [ha1a0] at h198
  rw [hroEq, r1b_buf22_split1 buf, h198]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun v198 => SepWPp.exists_elim fun v1a0 => ?_
  have hpc2 := hin2.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢; rw [heq_fnBase] at hpc2
  have hrun2 := hin2.run; have hsp2 : sm_a.sp = fsp := hin2.sp
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x0c44#64) hin2.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  refine r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left <|
    r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left ?_
  refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf22_realign buf _ _) (by r1b_ac) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun d2 => ?_
  dsimp only [runPc, mProg, tripleRatchetProgAtExt]
  by_cases hpCap : pCap = 0#64
  · subst hpCap
    have hpc : sm3.pc = fnBase + 0x0c44#64 := by simp [hsm3, arm64_norm]
    have hrun : sm3.status = .Running := by simp [hsm3, arm64_norm, hin2.run]
    have hsp : sm3.sp = fsp := by simpa [hsm3, arm64_norm] using hin2.sp
    have hr0 : sm3.readReg64 .x0 = buf := by simpa [hsm3, arm64_norm] using hx0_buf
    have hr23 : sm3.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by simpa [hsm3, arm64_norm] using hx23_2
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x0cec#64) hinv3
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm4 hsm4 hinv4 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc4 : r1b_ErrCtx img ext g d s0 sm4 0x0cec := hc2.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm4, arm64_norm]
        run := by simp [hsm4, arm64_norm, hin2.run], sp := by simpa [hsm4, arm64_norm] using hin2.sp
        fp := by simpa [hsm4, arm64_norm] using hin2.fp, inv := hinv4
        vregs := by simpa [calleeSavedVRegs, hsm4, arm64_norm] using hin2.vregs, spAligned := hin2.spAligned }
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
    refine r1b_sepWPp_frame (by r1b_ac)
      (r1b_ownedBytes_zero A pPtr (BitVec.ofNat 64 pBs.length) pBs)
      (by r1b_ac) ?_
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_err_0cec (d2 := ro2) (pCap := 0#64) hh hdrop hbnd hc4 hbuf
        (by simp [hsm4, arm64_norm, speWord]) (by simp [hsm4, arm64_norm]) hpanic hrej)
    subst herrCore; dsimp only [r1b_errCommon]; (try dsimp +zetaDelta only)
    generalize runFsp s0 = fsp0; exact Entails.of_eq (by r1b_ac)
  · have hpCap_f : (pCap == 0#64) = false := beq_false_of_ne hpCap
    have hpc : sm3.pc = fnBase + 0x0c44#64 := by simp [hsm3, arm64_norm]
    have hrun : sm3.status = .Running := by simp [hsm3, arm64_norm, hin2.run]
    have hsp : sm3.sp = fsp := by simpa [hsm3, arm64_norm] using hin2.sp
    have hr0 : sm3.readReg64 .x0 = buf := by simpa [hsm3, arm64_norm] using hx0_buf
    apply MainHops.sepWPp_seq_inImage
      (mid := fnBase + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run")) hinv3
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm4 hsm4 hinv4 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hx0_sm4 : sm4.readReg64 .x0 = pPtr := by
      simp [hsm4, arm64_norm]
    refine r1b_call_frame <|
      r1b_call_dealloc_ownedBytes (bs := pBs) hh hbnd hinv4
        (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm4, arm64_norm])
        (by simp [hsm4, arm64_norm, hin2.run]) (by simpa [hsm4, arm64_norm] using hin2.sp)
        (by simpa [hsm4, arm64_norm] using hin2.fp)
        (by simpa [calleeSavedVRegs, hsm4, arm64_norm] using hin2.vregs)
        hin2.spAligned (retOff := 0x0c68)
        (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm4, arm64_norm])
        hx0_sm4
        (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) hpCap hpanic
        fun sf4 hin4 hcs4 hfs4 htr4 => ?_
    have hc4 : r1b_ErrCtx img ext g d s0 sf4 0x0c68 := hc2.after_call
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      hin4 hcs4 (congrArg FsState.files hfs4) htr4
    have hx23_4 : sf4.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
      hcs4.2.2.2.2.1.trans (by simpa [hsm4, arm64_norm] using hx23_2)
    have hx25_4 : sf4.readReg64 (.gpr 25#5) = 22#64 :=
      hcs4.2.2.2.2.2.2.1.trans (by simp [hsm4, arm64_norm])
    have hx27_4 : sf4.readReg64 (.gpr 27#5) = speWord 1 :=
      hcs4.2.2.2.2.2.2.2.2.1.trans (by simp [hsm4, arm64_norm, speWord])
    have hpc4 := hin4.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc4 ⊢; rw [heq_fnBase] at hpc4
    have hrun4 := hin4.run
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x0cec#64) hin4.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm5 hsm5 hinv5 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc5 : r1b_ErrCtx img ext g d s0 sm5 0x0cec := hc4.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm5, arm64_norm]
        run := by simp [hsm5, arm64_norm, hin4.run], sp := by simpa [hsm5, arm64_norm] using hin4.sp
        fp := by simpa [hsm5, arm64_norm] using hin4.fp, inv := hinv5
        vregs := by simpa [calleeSavedVRegs, hsm5, arm64_norm] using hin4.vregs, spAligned := hin2.spAligned }
      (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
      (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_err_0cec (d2 := ro2) (pCap := pCap) hh hdrop hbnd hc5 hbuf
        (by simp [hsm5, arm64_norm, speWord])
        (by simpa [hsm5, arm64_norm] using hx25_4) hpanic hrej)
    subst herrCore; dsimp only [r1b_errCommon]; (try dsimp +zetaDelta only)
    generalize runFsp s0 = fsp0; exact Entails.of_eq (by r1b_ac)

theorem r1b_err_0c14 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {pCap pPtr : BitVec 64} {pBs : List (BitVec 8)} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack) (hc : r1b_ErrCtx img ext g d s0 s 0x0c14)
    (hx23 : s.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 (.gpr 27#5) = pPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        memRegion (fsp + 0x198#64) 16 ∗ memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x0c14 0x18
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli::run"))
    hst.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_shim hh hbnd hinv1
      (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run]) (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x0c18)
      (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      hpanic fun sf1 hin1 hcs1 htr_fs1 htr1 => ?_
  have hc1 : r1b_ErrCtx img ext g d s0 sf1 0x0c18 := hc.after_call
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    hin1 hcs1 (congrArg FsState.files htr_fs1) htr1
  have hx23_1 : sf1.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
    hcs1.2.2.2.2.1.trans (by simpa [hsm1, arm64_norm] using hx23)
  have hx27_1 : sf1.readReg64 (.gpr 27#5) = pPtr :=
    hcs1.2.2.2.2.2.2.2.2.1.trans (by simpa [hsm1, arm64_norm] using hx27)
  have hpc1 := hin1.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢; rw [heq_fnBase] at hpc1
  have hrun1 := hin1.run
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli::run")) hin1.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_alloc (size := 22) (align := 1) hh hbnd hinv2
      (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm, hin1.run]) (by simpa [hsm2, arm64_norm] using hin1.sp)
      (by simpa [hsm2, arm64_norm] using hin1.fp)
      (by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs)
      hst.spAligned (retOff := 0x0c24)
      (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by decide) (r1b_layout1 22) hpanic
      (fun sf2 hin2 _ hx0_0 _ htr_null => ?_)
      (fun sf2 buf hin2 hcs2 hx0_buf hbuf hfs2 htr2 => ?_)
  · have hpc2 := hin2.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢; rw [heq_fnBase] at hpc2
    have hrun2 := hin2.run
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2d68#64) hin2.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
    exact r1b_oom_2d68
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm]
        run := by simp [hsm3, arm64_norm, hin2.run], sp := by simpa [hsm3, arm64_norm] using hin2.sp
        fp := by simpa [hsm3, arm64_norm] using hin2.fp, inv := hinv3
        vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs, spAligned := hst.spAligned }
      hpanic (r1b_allocFailedIn_mono
        (r1b_allocFailed_of_null (by simpa [hsm2, arm64_norm] using hc1.trace) htr_null)
        (by simp [hsm3, arm64_norm]))
  · have hc2 : r1b_ErrCtx img ext g d s0 sf2 0x0c24 := hc1.after_call
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      hin2 hcs2 (congrArg FsState.files hfs2) htr2
    have hx23_2 : sf2.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
      hcs2.2.2.2.2.1.trans (by simpa [hsm2, arm64_norm] using hx23_1)
    have hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr :=
      hcs2.2.2.2.2.2.2.2.2.1.trans (by simpa [hsm2, arm64_norm] using hx27_1)
    exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
      (r1b_err_0c24 himg hh hdrop hbnd herrCore hc2 hx0_buf hbuf hx23_2 hx27_2 hpanic hrej)

/-! ## `split_signed` Sub-Step (`0x1230 → 0x1260`) -/

set_option maxHeartbeats 800000 in
private theorem r1b_after_spk_dealloc_err {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 sf1 : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {eCap ePtr regCap regPtr spkCap spkPtr : BitVec 64} {eBs spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack) (hc1 : r1b_ErrCtx img ext g d s0 sf1 0x1248)
    (hspk_le : spkBs.length ≤ spkCap.toNat) (hspk_lt : spkCap.toNat < 2 ^ 63) (hspk_ne : spkPtr ≠ 0)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) sf1
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d0#64 + 8#64) ↦₆₄ eCap) ∗ ((fsp + 0x4d0#64 + 16#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4d0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4d0#64 + 32#64) 16 ∗
        ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        (spkPtr ↦ₛ spkBs) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        (r1b_ownedRest A spkCap spkPtr spkBs.length ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore A img g d s0 ∗ logOff img ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗ memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 ∗ ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
          ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
          ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24))
      Q Qp (runOom s0) := by
  intro fsp
  generalize hinvCore : r1b_invCore A img g d s0 = invCore
  have hin1 := hc1.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hin1.sp hin1.spAligned
  have hrejoin := r1b_ownedBytes_rejoin A spkCap spkPtr spkBs hspk_le hspk_lt hspk_ne
  have he8 : ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) =
      ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
        ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) := by
    have hz := r1b_u64_split32 (fsp + 0x4e8#64) (BitVec.ofNat 64 eBs.length)
    have ha : (fsp + 0x4e8#64) + 4#64 = fsp + 0x4ec#64 := by bv_omega
    rwa [ha] at hz
  refine r1b_sepWPp_frame (by r1b_ac) hrejoin (by r1b_ac) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [he8]; simp only [sepConj_assoc]; dsimp only [speWord]
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x1248 0x18
  have hpc1 := hin1.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  have hrun1 := hin1.run; have hsp1 : sf1.sp = fsp := hin1.sp
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x13bc#64) hin1.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hc2 : r1b_ErrCtx img ext g d s0 sm2 0x13bc := hc1.of_step
    { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm]
      run := by simp [hsm2, arm64_norm, hin1.run], sp := by simpa [hsm2, arm64_norm] using hin1.sp
      fp := by simpa [hsm2, arm64_norm] using hin1.fp, inv := hinv2
      vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs, spAligned := hin1.spAligned }
    (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
    (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
  have he8' : ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
      ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) ⊢
      ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) := by
    rw [← he8]; exact Entails.refl _
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  have hst_err :
      (invCore ∗ logOff img ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗ ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool) ⊢
        errCommon ∗ memRegion (fsp + 0x190#64) 8 ∗ memRegion (fsp + 0x1a8#64) 16 := by
    rw [← hinvCore, ← herrCommon]
    exact r1b_stage_to_err A img g d s0 resStack (ofLe32 r0 r1 r2 r3)
  have h188 : memRegion (fsp + 0x188#64) 8 ∗ memRegion (fsp + 0x190#64) 8 ⊢
      memRegion (fsp + 0x188#64) 16 := by
    rw [r1b_join_region fsp 0x188 8 8]; exact Entails.refl _
  have hex :
      (memRegion (fsp + 0x188#64) 8 ∗
        (invCore ∗ logOff img ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗ ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool)) ⊢
        errCommon ∗ memRegion (fsp + 0x188#64) 16 ∗ memRegion (fsp + 0x1a8#64) 16 :=
    Entails.trans (sepConj_mono_right hst_err)
      (r1b_entails_frame (by r1b_ac) h188 (by r1b_ac))
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_err_13bc (eCap := eCap) (ePtr := ePtr) (eBs := eBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3]) hh hdrop hbnd hc2
      (by simp [hsm2, arm64_norm, speWord]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) hpanic hrej)
  rw [herrCommon]
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono he8' hex) (by r1b_ac)

set_option maxHeartbeats 600000 in
theorem r1b_after_spk_dealloc {S : RunSem} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {regCap regPtr spkCap spkPtr : BitVec 64} {spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack) (hok : r1b_OkCtx S img ext g d s0 s 0x1230)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok [r0, r1, r2, r3])
    (hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hx23 : s.readReg64 (.gpr 23#5) = spkCap) (hx9 : s.readReg64 (.gpr 9#5) = spkPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 spkBs.length)
    (hx26 : s.readReg64 (.gpr 26#5) = d.dirPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hk : ∀ (sf : State) (spkId : BitVec 32) (spkKey spkSig : List (BitVec 8)),
      r1b_OkCtx S img ext g d s0 sf 0x1260 →
      splitSigned spkBs = some (spkId, spkKey, spkSig) →
      sf.readReg64 (.gpr 10#5) = spkPtr + 4#64 →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 .x2 = spkId.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = d.dirPtr →
      sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
      let fsp := runFsp s0
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗ memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore A img g d s0 ∗ logOff img ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗ memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 ∗ ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
          ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
          ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (memRegion (fsp + 0x4d0#64) 48 ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCore A img g d s0 ∗ logOff img ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗ memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        memRegion (fsp + 0x150#64) 16 ∗ ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        memRegion (fsp + 0x168#64) 8 ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
        ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hreg_rd
  generalize hinvCore : r1b_invCore A img g d s0 = invCore at *
  have hst := hok.st; have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  rw [ProofLib.memRegion_eight (fsp + 0x168#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v168 =>
    r1b_call_frame <| r1b_sepWPp_borrow_core A (cap := spkCap) (ptr := spkPtr)
      (len := BitVec.ofNat 64 spkBs.length) (bs := spkBs)
      fun ⟨_, hspk_le, hspk_lt, hspk_ne⟩ => ?_
  have hcmn_f : (spkCap + 1#64 == 0#64) = false := beq_false_of_ne (r1b_cmn1_false_of_lt63 hspk_lt)
  have hlen_nat : (BitVec.ofNat 64 spkBs.length).toNat = spkBs.length := by
    simp only [BitVec.toNat_ofNat]; omega
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x1230 0x30
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% ((2 ^ 64 + ls_off% "libsignal_cli::public::split_signed" -
      ls_off% "libsignal_cli::run") % 2 ^ 64)) hst.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_splitSigned (ret := fsp + 0x4d0#64) (fp := spkPtr) (file := spkBs) himg hh hbnd hinv1
      (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run]) (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x1248)
      (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp only [hsm1, arm64_norm, hx2]; exact hlen_nat)
      (by simpa [hsm1, arm64_norm] using hok.trace) hpanic
      (fun sf1 eCap ePtr eBs hin1 hcs1 hsp_none hfs1 htr1 => ?_)
      (fun sf1 spkId spkKey spkSig hin1 hcs1 hsp_ok hfs1 htr1 => ?_)
  · have hok1 : r1b_OkCtx S img ext g d s0 sf1 0x1248 := hok.after_call
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      hin1 hcs1 hfs1 htr1
    have hc1 : r1b_ErrCtx img ext g d s0 sf1 0x1248 :=
      hok1.to_err (r1b_none_spk_split hspk_rd hsp_none)
    refine MainHops.sepWPp_weaken_pre ?_
      (hinvCore ▸ r1b_after_spk_dealloc_err (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
        (eCap := eCap) (ePtr := ePtr) (regCap := regCap) (regPtr := regPtr)
        (spkCap := spkCap) (spkPtr := spkPtr) (eBs := eBs) (spkBs := spkBs)
        hh hdrop hbnd hc1 hspk_le hspk_lt hspk_ne hpanic hrej)
    exact Entails.of_eq (by r1b_ac)
  · have hok1 : r1b_OkCtx S img ext g d s0 sf1 0x1248 := hok.after_call
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      hin1 hcs1 hfs1 htr1
    have hx26_1 : sf1.readReg64 (.gpr 26#5) = d.dirPtr :=
      hcs1.2.2.2.2.2.2.2.1.trans (by simpa [hsm1, arm64_norm] using hx26)
    have hx28_1 : sf1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
      hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simpa [hsm1, arm64_norm] using hx28)
    have hrejoin := r1b_ownedBytes_rejoin A spkCap spkPtr spkBs hspk_le hspk_lt hspk_ne
    refine r1b_sepWPp_frame (by r1b_ac) hrejoin (by r1b_ac) ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; dsimp only [splitOkTag]
    have hpc1 := hin1.pc; dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢; rw [heq_fnBase] at hpc1
    have hrun1 := hin1.run; have hsp1 : sf1.sp = fsp := hin1.sp
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x1260#64) hin1.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hok2 : r1b_OkCtx S img ext g d s0 sm2 0x1260 := hok1.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm]
        run := by simp [hsm2, arm64_norm, hin1.run], sp := by simpa [hsm2, arm64_norm] using hin1.sp
        fp := by simpa [hsm2, arm64_norm] using hin1.fp, inv := hinv2
        vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs, spAligned := hst.spAligned }
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 0x4d8#64) ↦₆₄ (spkPtr + 4#64)) ∗
          ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 spkKey.length) ∗
          (((fsp + 0x4e8#64) ↦₃₂ spkId) ∗ memRegion (fsp + 0x4ec#64) 4) ⊢
          memRegion (fsp + 0x4d0#64) 32 := by
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (pointsTo32_entails_memRegion _ _))))) ?_
      rw [r1b_join_region fsp 0x4e8 4 4]
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right
        (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x4e0#64) (BitVec.ofNat 64 spkKey.length) (n := 8) (by decide)))) ?_
      refine Entails.trans (sepConj_mono_right
        (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x4d8#64) (spkPtr + 4#64) (n := 16) (by decide))) ?_
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cell64_cons (a := fsp + 0x4d0#64) 0xfffffffffffffffe#64 (n := 24) (by decide)
    refine MainHops.sepWPp_weaken_pre ?_
      (hk sm2 spkId spkKey spkSig hok2 hsp_ok
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simpa [hsm2, arm64_norm] using hx26_1) (by simpa [hsm2, arm64_norm] using hx28_1))
    exact r1b_entails_frame (by r1b_ac) h4d0 (by r1b_ac)

end CryptoVerification.SignalSession.Cli.RunCompose
