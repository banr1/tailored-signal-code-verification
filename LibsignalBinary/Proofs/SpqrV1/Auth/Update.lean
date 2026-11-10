/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPb
public meta import ProofLib.SepLogic.WP.ControlTactics -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# Verification of `<spqr::authenticator::Authenticator>::update` (`0x5debc`, 107 instructions)

Proves `<spqr::authenticator::Authenticator>::update` (`src/authenticator.rs:44–54`) meets
`(authUpdateSpec F A).inImage img`: concatenates `ikm` and `info` via `sliceConcat2Spec A`,
allocates a 64B `kdf_out` buffer, derives 64B via `hkdf_to_slice`, and updates `root_key`/`mac_key`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState toBEBytes)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Keys CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.ChainProofs CryptoVerification.CodeLayout DoReserveNorm

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x58ac4 → 0x58c6c]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

structure AuthUpdatePinnedGhost where
  selfA : BitVec 64
  g : AuthenticatorGhost
  auth : Authenticator
  ep : Epoch
  kRO : Bool
  kA : BitVec 64
  k : Bytes

structure AuthUpdateGhost where
  selfA : BitVec 64
  auth : Authenticator
  ep : Epoch
  kRO : Bool
  kA : BitVec 64
  k : Bytes

def authUpdatePinnedSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthUpdatePinnedGhost where
  pre x s :=
    ⌜s.readReg64 .x0 = x.selfA ∧ s.readReg64 .x1 = x.ep ∧
      s.readReg64 .x2 = x.kA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.k.length ∧
      x.auth.rootKey.length + x.k.length < 2 ^ 63⌝ ∗
      authenticatorPinAt A x.g x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗
      A.pool ∗ stackAt s.sp authUpdateStackX
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorAt A x.selfA (x.auth.update F x.ep x.k) ∗ bytesAt x.kRO x.kA x.k ∗
      A.pool ∗ stackAt s0.sp authUpdateStackX
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def authUpdateSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthUpdateGhost where
  pre x s :=
    ⌜s.readReg64 .x0 = x.selfA ∧ s.readReg64 .x1 = x.ep ∧
      s.readReg64 .x2 = x.kA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.k.length ∧
      x.auth.rootKey.length + x.k.length < 2 ^ 63⌝ ∗
      authenticatorAt A x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗
      A.pool ∗ stackAt s.sp authUpdateStackX
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorAt A x.selfA (x.auth.update F x.ep x.k) ∗ bytesAt x.kRO x.kA x.k ∗
      A.pool ∗ stackAt s0.sp authUpdateStackX
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def AuthUpdateOkX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
    ((authUpdateSpec F A).inImage img)

/-- Stack budget of `<spqr::authenticator::Authenticator>::update` (`0x5debc`) under `CliExternsOk`:
own frame `0xa0 = 160` B + `hkdfToSliceStackExt` (`17616` B) = `17776` B. -/
abbrev authUpdateStackExt : Nat := 160 + hkdfToSliceStackExt

def authUpdatePinnedSpecExt (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthUpdatePinnedGhost where
  pre x s := ⌜s.readReg64 .x0 = x.selfA ∧ s.readReg64 .x1 = x.ep ∧
    s.readReg64 .x2 = x.kA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.k.length ∧
    x.auth.rootKey.length + x.k.length < 2 ^ 63⌝ ∗
    authenticatorPinAt A x.g x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗
    A.pool ∗ stackAt s.sp authUpdateStackExt
  post x s0 sf := ⌜sf.trace = s0.trace⌝ ∗
    authenticatorAt A x.selfA (x.auth.update F x.ep x.k) ∗ bytesAt x.kRO x.kA x.k ∗
    A.pool ∗ stackAt s0.sp authUpdateStackExt
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def authUpdateSpecExt (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthUpdateGhost where
  pre x s := ⌜s.readReg64 .x0 = x.selfA ∧ s.readReg64 .x1 = x.ep ∧
    s.readReg64 .x2 = x.kA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.k.length ∧
    x.auth.rootKey.length + x.k.length < 2 ^ 63⌝ ∗
    authenticatorAt A x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗
    A.pool ∗ stackAt s.sp authUpdateStackExt
  post x s0 sf := ⌜sf.trace = s0.trace⌝ ∗
    authenticatorAt A x.selfA (x.auth.update F x.ep x.k) ∗ bytesAt x.kRO x.kA x.k ∗
    A.pool ∗ stackAt s0.sp authUpdateStackExt
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def AuthUpdateOkExt (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
    ((authUpdateSpecExt F A).inImage img)

namespace UpdateFacts

theorem authUpdate_fnOff : libsignalSessionCode.fnOff authUpdateName = 0x58ac4 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x58ac4

theorem shim_fnOff : libsignalSessionCode.fnOff shimName =
    num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")

theorem alloc_fnOff : libsignalSessionCode.fnOff allocName =
    num% (ls_off% "__rustc::__rust_alloc") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "__rustc::__rust_alloc")

theorem allocZeroed_fnOff : libsignalSessionCode.fnOff allocZeroedName =
    num% (ls_off% "__rustc::__rust_alloc_zeroed") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "__rustc::__rust_alloc_zeroed")

theorem handleError_fnOff : libsignalSessionCode.fnOff handleErrorName =
    num% (ls_off% "alloc::raw_vec::handle_error") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "alloc::raw_vec::handle_error")

/-- `.rodata` slice at `0x8376b` (`ls_xref% 0x5df04 0x5df08`, 45 bytes): `Authenticator.updateLabel`. -/
theorem rodata_updateLabel {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x58b0c 0x58b10)) ↦ᵣ Authenticator.updateLabel) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x58b0c 0x58b10)) (n := 45) (bs := Authenticator.updateLabel)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-- `.rodata` slice at `0x83798` (`ls_xref% 0x5df54 0x5df58`, 32 bytes): `List.replicate 32 0#8`. -/
theorem rodata_zeros32_update {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x58b5c 0x58b60)) ↦ᵣ List.replicate 32 0#8) ∗ P :=
  NextKeyInternalFacts.rodata_zeros32 himg hF hP

theorem rodata_updateLabel_placed [LibsignalPlacement]
    {m : Memory} (hF : NextKeyInternalFacts.LsCallInv lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ "spqr:.rodata..Lanon.138") ↦ᵣ Authenticator.updateLabel) ∗ P :=
  lsro_intro_chk hF.1 (by decide +kernel) hP

open Lean Elab Tactic Meta in
meta def wppCallMidCore (lemId : Ident) (hcall a hF : Term) : TacticM Unit := do
  let hcallCopyId ← freshIdent `hcall_copy
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    have $hcallCopyId := $hcall
    apply ($lemId $hcallCopyId (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wppCallMidCore: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR'
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm, *]
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcallCopyId)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; first
      | exact NextKeyInternalFacts.onPanic_entails_of_trace_eq (by wp_norm_lhs)
      | exact Entails.pure_left False.elim)
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    try clear $hcallCopyId
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  for _ in [:2] do
    let mvarId ← getMainGoal
    let ref ← IO.mkRef #[]
    mvarId.withContext do
      let ty ← instantiateMVars (← mvarId.getType)
      ty.forEach fun sub => do
        if sub.isConst then
          let nm := sub.constName!
          if nm != ``Arm64.Spec.mk && nm != ``Arm64.Spec.inImage &&
              nm != ``NextKeyInternalFacts.withLsCallInv then
            let subTy ← inferType sub
            if subTy.getForallBody.isAppOf ``Arm64.Spec then
              let arr ← ref.get
              if !arr.any (fun i => i.getId == nm) then
                ref.set (arr.push (mkIdent nm))
    let ids ← ref.get
    for id in ids do
      let _ ← tryTactic (evalTactic (← `(tactic| dsimp only [$id:ident])))
  let _ ← tryTactic (evalTactic (← `(tactic| dsimp only)))
  for hId in [hspId, hcsId] do
    let _ ← tryTactic (evalTactic (← `(tactic| dsimp only at $hId:ident)))
    let _ ← tryTactic (evalTactic (← `(tactic|
      simp (config := { decide := true }) only [
        ← disjointRegions_iff_disjoint64,
        ← disjointRegions_iff_disjoint128,
        Arm64.CalleeSavedPreserved,
        wp_norm, arm64_norm] at $hId:ident)))
  let mut worklist : List Ident := [hspId, hcsId]
  while !worklist.isEmpty do
    let currId :: rest := worklist | break
    worklist := rest
    let mvarId ← getMainGoal
    let lctx ← mvarId.withContext getLCtx
    if let some decl := lctx.findFromUserName? currId.getId then
      let ty ← mvarId.withContext (instantiateMVars decl.type)
      if ty.isAppOfArity ``And 2 then
        let h1 ← freshIdent `h
        if ← tryTactic (evalTactic (← `(tactic| rcases $currId:ident with ⟨$h1:ident, $currId:ident⟩))) then
          worklist := h1 :: currId :: worklist
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 4
      simp (config := { decide := true }) only [
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hspId:ident]))))

open Lean Elab Tactic in
elab "wpp_call_inImage_mid " hcall:term:max a:term:max hF:term:max : tactic =>
  wppCallMidCore (mkIdent ``MacHdrFacts.SepWPp.call_allowPanic_inImage_mid) hcall a hF

open Lean Elab Tactic in
elab "wpp_call_lsCallInv_mid " hcall:term:max a:term:max hF:term:max : tactic =>
  wppCallMidCore (mkIdent ``NextKeyInternalFacts.SepWPp.call_allowPanic_lsCallInv_mid) hcall a hF

end UpdateFacts

open UpdateFacts NextKeyInternalFacts AgreeStateSimp

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length updateLabel_length replicate_32_zero_length
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  libsignalSessionCode_fnOff_0x58ac4 libsignalSessionCode_fnOff_0x5eab8 libsignalSessionCode_fnOff_0x5de8c
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")

theorem hkdfToVecUnchecked_eq_hkdfToSliceUnchecked
    (F : ShaState → List (BitVec 8) → ShaState) (salt ikm info : Bytes) (okmLen : Nat) :
    hkdfToVecUnchecked F salt ikm info okmLen = hkdfToSliceUnchecked F salt ikm info okmLen := rfl

theorem SepWPp.seq_frame_lsCallInv {prog : Program} {pl : Obj.MultiPlacement}
    {mid_pc ret_pc : BitVec 64} {s : State} {P P_local Q_local F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (hframe : P = P_local ∗ F)
    (h1 : SepWP prog mid_pc s P_local
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ sm.trace = s.trace ∧ (Pm ⊢ Q_local)))
    (h2 : ∀ sm : State, sm.pc = mid_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → sm.trace = s.trace → LsCallInv pl sm.mem →
      SepWPp prog ret_pc sm (Q_local ∗ F) Q Qp) :
    SepWPp prog ret_pc s P Q Qp := by
  intro R hm hL
  rw [hframe, sepConj_assoc] at hm
  rcases h1.elim (R := F ∗ R) hm hL with
    ⟨sm, hsteps1, ⟨hpc, hrun, Pm, hPm, hsp, hcs, htr, hent⟩ | ⟨_, hoom⟩⟩
  · have hPm' : sm.mem ⊨ (Q_local ∗ F) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hPm
    obtain ⟨sf, hsteps2, hout2⟩ :=
      h2 sm hpc hrun hsp hcs htr (hF.of_steps hsteps1) R hPm' (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem vecBufAt_of_cap_ne_zero (A : RustAlloc) {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hcap : cap ≠ 0#64) (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    vecBufAt A cap ptr bs ⊢
      ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold vecBufAt
  have hcap_pos : 0 < cap.toNat := by
    by_contra h0; apply hcap; apply BitVec.eq_of_toNat_eq; simpa using h0
  have hlay : LayoutOk cap.toNat 1 := ⟨hcap_pos, ⟨0, rfl⟩, by omega⟩
  have hcap0 : cap ≠ 0 := hcap
  simp only [hcap0, ↓reduceIte]
  rw [show (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
      A.live ptr cap.toNat 1 ∗
        ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl]
  refine Entails.pure_right hlay ?_
  exact sepConj_mono_right (pointsToBytes_memRegion_entails ptr hle hlay)

def AllocZeroedWithStackOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr allocZeroedName)
    ((rustAllocZeroedSpecWithStack A extHookStack).inImage img)

theorem allocZeroedWithStackOkX_of_hook {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    AllocZeroedWithStackOkX img A ext := by
  have h0 := alloc_zeroed_ok_at_ext img.base A ext hZero allocZeroedName 0 (by simp only [Nat.add_zero])
  have hadd : (tripleRatchetProgAtExt img.base ext).fnAddr allocZeroedName + BitVec.ofNat 64 0 =
      (tripleRatchetProgAtExt img.base ext).fnAddr allocZeroedName := by bv_kernel
  rw [hadd] at h0
  exact subroutine_ok_inImage_of_subroutine_ok img (rustAllocZeroedWithStack_of_rustAllocZeroed h0)

private def authUpdatePinnedSpecAt (stk : Nat) (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) : Spec AuthUpdatePinnedGhost where
  pre x s := ⌜s.readReg64 .x0 = x.selfA ∧ s.readReg64 .x1 = x.ep ∧
    s.readReg64 .x2 = x.kA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.k.length ∧
    x.auth.rootKey.length + x.k.length < 2 ^ 63⌝ ∗
    authenticatorPinAt A x.g x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗ A.pool ∗ stackAt s.sp stk
  post x s0 sf := ⌜sf.trace = s0.trace⌝ ∗
    authenticatorAt A x.selfA (x.auth.update F x.ep x.k) ∗ bytesAt x.kRO x.kA x.k ∗
    A.pool ∗ stackAt s0.sp stk
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private def authHkdfSpecAt (stk : Nat) (hkdf : HkdfFn) : Spec HkdfToSliceGhost where
  pre x s := ⌜s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
    s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
    s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
    s.readReg64 .x6 = x.okmA ∧ s.readReg64 .x7 = BitVec.ofNat 64 x.okmLen ∧
    x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
    (¬x.saltRO ∨ x.salt.length ≤ 64) ∧ (¬x.ikmRO ∨ x.ikm.length < 64) ∧
    32 ≤ x.info.length ∧ x.info.length < 55 ∧
    (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96)⌝ ∗
    bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
    bytesAt x.infoRO x.infoA x.info ∗ memRegion x.okmA x.okmLen ∗ stackAt s.sp stk
  post x s0 sf := ⌜(hkdf x.salt x.ikm x.info x.okmLen).length = x.okmLen ∧ sf.trace = s0.trace⌝ ∗
    bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
    bytesAt x.infoRO x.infoA x.info ∗ (x.okmA ↦ₛ hkdf x.salt x.ikm x.info x.okmLen) ∗
    stackAt s0.sp stk

private def AuthHkdfOkAt (stk : Nat) (img : Obj.Image) (hkdf : HkdfFn)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
    ((authHkdfSpecAt stk hkdf).inImage img)

set_option maxHeartbeats 3200000 in
private theorem authUpdatePinned_ok_gen {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)} {totalStk hkdfStk extra : Nat}
    (hsplit_top : ∀ sp, stackAt sp totalStk =
      memRegion (sp - BitVec.ofNat 64 totalStk) extra ∗ stackAt sp authUpdateStackX)
    (hjoin_hkdf : ∀ sp, memRegion (sp - BitVec.ofNat 64 totalStk) extra ∗
      stackAt (sp - 160#64) extHookStack = stackAt (sp - 160#64) hkdfStk)
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : AuthHkdfOkAt hkdfStk img (hkdfToSliceUnchecked F) ext)
    (hA : AllocContractsX img A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
      ((authUpdatePinnedSpecAt totalStk F A).inImage img) := by
  unfold tripleRatchetProgAtExt at *
  refine subroutine_ok_inImage_rodata2_keep (rodata_updateLabel himg) (rodata_zeros32_update himg) ?_
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff authUpdateName = 0x58ac4 := authUpdate_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x58ac4 428
  have h_concat := sub_ok_at_rebase (name := authUpdateName) (callee := sliceConcatName)
    (k := num% (0x5eab8 - 0x58ac4)) (by rw [authUpdate_fnOff, sliceConcat_fnOff]) hconcat
  have h_hkdf := sub_ok_at_rebase (name := authUpdateName) (callee := hkdfToSliceName)
    (k := num% (0x5de8c - 0x58ac4)) (by rw [authUpdate_fnOff, hkdfToSlice_fnOff]) hhkdf
  have h_shim := sub_ok_at_rebase (name := authUpdateName) (callee := shimName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x58ac4))
    (by rw [authUpdate_fnOff, shim_fnOff])
    (hA.shim extHookStack (Nat.le_refl _) (by decide))
  have h_alloc := sub_ok_at_rebase (name := authUpdateName) (callee := allocName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - 0x58ac4))
    (by rw [authUpdate_fnOff, alloc_fnOff]) hA.alloc
  have h_allocZeroed := sub_ok_at_rebase (name := authUpdateName) (callee := allocZeroedName)
    (k := num% (ls_off% "__rustc::__rust_alloc_zeroed" - 0x58ac4))
    (by rw [authUpdate_fnOff, allocZeroed_fnOff]) hallocZeroed
  have h_dealloc := sub_ok_at_rebase (name := authUpdateName) (callee := deallocName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4))
    (by rw [authUpdate_fnOff, dealloc_fnOff]) hA.dealloc
  have h_panic := panic_at_handle_error_ext img.base ext authUpdateName
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x58ac4))
    (by rw [authUpdate_fnOff, handleError_fnOff])
  dsimp only [tripleRatchetProgAtExt] at h_panic
  have hadrp1 : ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      authUpdateName + 72#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x58b0c 0x58b10 - 0x58000) =
      img.base + bv% (ls_xref% 0x58b0c 0x58b10) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  have hadrp2 : ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      authUpdateName + 152#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x58b5c 0x58b60 - 0x58000) =
      img.base + bv% (ls_xref% 0x58b5c 0x58b60) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr authUpdateName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear himg hconcat hhkdf hA hallocZeroed hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      authUpdateName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rcases x with ⟨selfA, g, auth, ep, kRO, kA, k⟩
  dsimp only [authUpdatePinnedSpecAt] at hpre h_1 h_2 h_3 h_4 h_5 h_6 h ⊢
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  subst h_3 h_4 h_5
  refine SepWPp.rw_pre (by rw [hsplit_top s0.sp, stackAt_authUpdateX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x5eab8 - 0x58ac4)) hinv0 ?_
  refine SepWP.fold (authenticatorPinAt_expose_entails A g (s0.readReg64 (.gpr 0#5)) auth) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨⟨hrk_le, hrk_lt, hrk_ptr⟩, ⟨hmk_le, hmk_lt, hmk_ptr⟩⟩
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_inImage_mid h_concat
    (⟨s0.sp - 160#64, s0.sp - 112#64, false, g.rootKey.ptr, auth.rootKey,
      kRO, s0.readReg64 (.gpr 2#5), k⟩ : SliceConcat2Ghost)
    hinv1
  refine SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x5eab8 - 0x58ac4)) hF_sf ?_
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 56#64) (s0.readReg64 (.gpr 1#5))))
    (by sep_focus) ?_
  have hstack_sf : stackAt (s0.sp - 160#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 160#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_inImage_mid h_concat
    (⟨s0.sp - 136#64, s0.sp - 112#64,
      true, img.base + bv% (ls_xref% 0x58b0c 0x58b10), Authenticator.updateLabel,
      false, s0.sp - 56#64, toBEBytes 8 (s0.readReg64 (.gpr 1#5))⟩ : SliceConcat2Ghost)
    hinv2
  refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
  have hinfo_pos : 0 < (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length := by simp
  refine SepWPp.of_sepWP_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x58ac4)) hF_sf_1 ?_
  refine SepWP.fold (vecU8_expose_entails A (s0.sp - 160#64) (auth.rootKey ++ k)) (by sep_focus) ?_
  refine SepWP.fold (vecU8_nonempty_entails A (s0.sp - 136#64) hinfo_pos) (by sep_focus) ?_
  sep_elim_exists
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hinfo_cap_ne, hinfo_layout, hinfo_ptr, hinfo_le⟩
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hikm_le, hikm_lt, hikm_ptr⟩
  have hikm_len_lt : (auth.rootKey ++ k).length < 2 ^ 63 := Nat.lt_of_le_of_lt hikm_le hikm_lt
  wp_steps
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  wpp_call_inImage_mid h_shim () hinv3
  refine SepWPp.pure_left_focus _ (by sep_focus) fun htr_s1 => ?_
  refine SepWPp.of_sepWP_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc_zeroed" - 0x58ac4)) hF_sf_2 ?_
  wp_steps
  have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
    rw [‹sf_2.sp = sf_1.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv4
  have hlay64 : LayoutOk 64 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  wpp_call_inImage_mid h_allocZeroed (64, 1) hinv4
  by_cases hoom64 : sf_3.readReg64 Reg.x0 = 0#64
  · conv => arg 4; simp only [hoom64, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr3 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x58ac4))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    exact allowPanic_panicked_update
      (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64_beq : (sf_3.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom64
    conv => arg 4; simp only [hoom64, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, htr3⟩
    refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x5de8c - 0x58ac4)) hF_sf_3 ?_
    refine SepWP.fold (pointsToBytes_replicate_64_entails_memRegion (sf_3.readReg64 Reg.x0)) (by sep_focus) ?_
    wp_steps
    have hstack_sf3 : memRegion (s0.sp - BitVec.ofNat 64 totalStk) extra ∗ stackAt sf_2.sp extHookStack =
        stackAt sf_3.sp hkdfStk := by
      rw [‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 160#64›,
        hjoin_hkdf s0.sp]
    refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv5
    have hinfo_ge : 32 ≤ (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length := by simp
    have hinfo_lt : (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length < 55 := by simp
    have hsalt_ro_ok : ¬true ∨ (List.replicate 32 (0#8 : BitVec 8)).length ≤ 64 := Or.inr (by decide)
    wpp_call_inImage_mid h_hkdf
      (⟨true, img.base + bv% (ls_xref% 0x58b5c 0x58b60), List.replicate 32 0#8,
        false, _, auth.rootKey ++ k,
        false, _, Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)),
        sf_3.readReg64 Reg.x0, 64⟩ : HkdfToSliceGhost)
      hinv5
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hkdf_len, htr4⟩
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hokm_all, hokm_take, hokm_drop⟩ :=
      exists_unpack64_of_length_64_split hkdf_len
    refine SepWPp.of_sepWP_inImage
      (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x58ac4)) hF_sf_4 ?_
    wp_steps
    have hstack_sf4 : stackAt sf_3.sp hkdfStk =
        memRegion (s0.sp - BitVec.ofNat 64 totalStk) extra ∗ stackAt sf_4.sp extHookStack := by
      rw [‹sf_4.sp = sf_3.sp›, ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›,
        ‹sf.sp = s0.sp - 160#64›, ← hjoin_hkdf s0.sp]
    refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv6
    wpp_call_inImage_mid h_shim () hinv6
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr_s2 => ?_
    refine SepWPp.of_sepWP_inImage
      (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x58ac4)) hF_sf_5 ?_
    wp_steps
    have hstack_sf5 : stackAt sf_4.sp extHookStack = stackAt sf_5.sp extHookStack := by
      rw [‹sf_5.sp = sf_4.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf5) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv7
    have hlay32 : LayoutOk 32 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
    wpp_call_inImage_mid h_alloc (32, 1) hinv7
    by_cases hoom32_1 : sf_6.readReg64 Reg.x0 = 0#64
    · conv => arg 4; simp only [hoom32_1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr6 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x58ac4))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      exact allowPanic_panicked_update
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom32_1_beq : (sf_6.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom32_1
      conv => arg 4; simp only [hoom32_1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr6⟩
      refine SepWPp.of_sepWP_inImage (mid := entry + 228#64) hF_sf_6 ?_
      refine SepWP.fold (Entails.of_eq (hokm_all (sf_3.readReg64 Reg.x0))) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (memRegion_32_cells (sf_6.readReg64 Reg.x0))) (by sep_focus) ?_
      sep_elim_exists
      wp_steps
      refine SepWP.fold (Entails.of_eq (hokm_take (sf_6.readReg64 Reg.x0)).symm) (by sep_focus) ?_
      refine SepWP.fold (vecBufAt_fold A g.rootKey.cap g.rootKey.ptr auth.rootKey) (by sep_focus) ?_
      have hstack_sf6 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by
        rw [‹sf_6.sp = sf_5.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf6) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv8
      refine SepWPp.seq_frame_inImage
        (mid_pc := entry + 244#64)
        (P_local := vecBufAt A g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
          A.pool ∗ stackAt sf_6.sp extHookStack)
        (Q_local := A.pool ∗ stackAt sf_6.sp extHookStack)
        hinv8 (by sep_focus) ?_ ?_
      · by_cases hcap_rk : g.rootKey.cap = 0#64
        · refine SepWP.fold (vecBufAt_of_cap_zero A hcap_rk hrk_le) (by sep_focus) ?_
          simp only [hcap_rk]
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by wp_norm_goal,
            by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, and_self],
            by wp_norm_goal, Entails.of_eq (emp_sepConj _)⟩
        · have hcap_rk_beq : (g.rootKey.cap == 0#64) = false := beq_false_of_ne hcap_rk
          refine SepWP.fold (vecBufAt_of_cap_ne_zero A hcap_rk hrk_le hrk_lt) (by sep_focus) ?_
          refine SepWP.pure_left_focus _ (by sep_focus) ?_
          intro hrk_lay
          have ⟨_, _, _⟩ := hrk_lay
          apply SepWP.seq_inImage
            (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4)) hinv8
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          rintro ⟨hF_d1, hsym_d1⟩
          wp_call h_dealloc (g.rootKey.ptr, g.rootKey.cap.toNat, 1)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by simp only [wp_norm, arm64_norm, *],
            by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            Entails.refl _⟩
      · intro sm1 hpc_sm1 hrun_sm1 hsp_sm1 hcs_sm1 htr_sm1 hF_sm1
        simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp_sm1 hcs_sm1 htr_sm1
        have hstack_sm1 : stackAt sf_6.sp extHookStack = stackAt sm1.sp extHookStack := by
          rw [hsp_sm1, ‹sf_6.sp = sf_5.sp›, ‹sf_5.sp = sf_4.sp›, ‹sf_4.sp = sf_3.sp›,
            ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 160#64›]
        rcases hcs_sm1 with ⟨hx19_sm1, hx20_sm1, hx21_sm1, hx22_sm1, hx23_sm1, hx24_sm1,
          hx25_sm1, hx26_sm1, hx27_sm1, hx28_sm1, hx29_sm1, hvregs_sm1⟩
        refine SepWPp.of_sepWP_inImage
          (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x58ac4)) hF_sm1 ?_
        refine SepWP.fold (Entails.of_eq hstack_sm1) (by sep_focus) ?_
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv9
        wpp_call_inImage_mid h_shim () hinv9
        refine SepWPp.pure_left_focus _ (by sep_focus) fun htr_s3 => ?_
        refine SepWPp.of_sepWP_inImage
          (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x58ac4)) hF_sf_7 ?_
        wp_steps
        have hstack_sf7 : stackAt sm1.sp extHookStack = stackAt sf_7.sp extHookStack := by
          rw [‹sf_7.sp = sm1.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf7) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv10
        wpp_call_inImage_mid h_alloc (32, 1) hinv10
        by_cases hoom32_2 : sf_8.readReg64 Reg.x0 = 0#64
        · conv => arg 4; simp only [hoom32_2, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
          refine SepWPp.pure_left_focus _ (by sep_focus) fun htr8 => ?_
          apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x58ac4))
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
          exact allowPanic_panicked_update
            (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
        · have hoom32_2_beq : (sf_8.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom32_2
          conv => arg 4; simp only [hoom32_2, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
          refine SepWPp.pure_left_focus _ (by sep_focus) ?_
          rintro ⟨_, htr8⟩
          refine SepWPp.of_sepWP_inImage (mid := entry + 292#64) hF_sf_8 ?_
          refine SepWP.fold (Entails.of_eq (memRegion_32_cells (sf_8.readReg64 Reg.x0))) (by sep_focus) ?_
          sep_elim_exists
          wp_steps
          refine SepWP.fold (Entails.of_eq (hokm_drop (sf_8.readReg64 Reg.x0)).symm) (by sep_focus) ?_
          refine SepWP.fold (vecBufAt_fold A g.macKey.cap g.macKey.ptr auth.macKey) (by sep_focus) ?_
          have hstack_sf8 : stackAt sf_7.sp extHookStack = stackAt sf_8.sp extHookStack := by
            rw [‹sf_8.sp = sf_7.sp›]
          refine SepWP.fold (Entails.of_eq hstack_sf8) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv11
          refine SepWPp.seq_frame_inImage
            (mid_pc := entry + 308#64)
            (P_local := ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ g.macKey.ptr) ∗
              vecBufAt A g.macKey.cap g.macKey.ptr auth.macKey ∗
              A.pool ∗ stackAt sf_8.sp extHookStack)
            (Q_local := ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ g.macKey.ptr) ∗
              A.pool ∗ stackAt sf_8.sp extHookStack)
            hinv11 (by sep_focus) ?_ ?_
          · by_cases hcap_mk : g.macKey.cap = 0#64
            · refine SepWP.fold (vecBufAt_of_cap_zero A hcap_mk hmk_le) (by sep_focus) ?_
              simp only [hcap_mk]
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              refine ⟨by wp_norm_goal,
                by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, and_self],
                by wp_norm_goal, Entails.of_eq (emp_sepConj _)⟩
            · have hcap_mk_beq : (g.macKey.cap == 0#64) = false := beq_false_of_ne hcap_mk
              refine SepWP.fold (vecBufAt_of_cap_ne_zero A hcap_mk hmk_le hmk_lt) (by sep_focus) ?_
              refine SepWP.pure_left_focus _ (by sep_focus) ?_
              intro hmk_lay
              have ⟨_, _, _⟩ := hmk_lay
              apply SepWP.seq_inImage
                (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4)) hinv11
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              rintro ⟨hF_d2, hsym_d2⟩
              wp_call h_dealloc (g.macKey.ptr, g.macKey.cap.toNat, 1)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              refine ⟨by simp only [wp_norm, arm64_norm, *],
                by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                Entails.of_eq (by ac_rfl)⟩
          · intro sm2 hpc_sm2 hrun_sm2 hsp_sm2 hcs_sm2 htr_sm2 hF_sm2
            simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp_sm2 hcs_sm2 htr_sm2
            have hstack_sm2 : stackAt sf_8.sp extHookStack = stackAt sm2.sp extHookStack := by
              rw [hsp_sm2, ‹sf_8.sp = sf_7.sp›, ‹sf_7.sp = sm1.sp›, hsp_sm1]
            rcases hcs_sm2 with ⟨hx19_sm2, hx20_sm2, hx21_sm2, hx22_sm2, hx23_sm2, hx24_sm2,
              hx25_sm2, hx26_sm2, hx27_sm2, hx28_sm2, hx29_sm2, hvregs_sm2⟩
            refine SepWPp.of_sepWP_inImage
              (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4)) hF_sm2 ?_
            refine SepWP.fold (Entails.of_eq hstack_sm2) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (hokm_all (sf_3.readReg64 Reg.x0)).symm) (by sep_focus) ?_
            refine SepWP.fold (pointsToBytes_64_entails_memRegion (sf_3.readReg64 Reg.x0) hkdf_len) (by sep_focus) ?_
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv12
            wpp_call_inImage_mid h_dealloc (sf_3.readReg64 Reg.x0, 64, 1) hinv12
            refine SepWPp.pure_left_focus _ (by sep_focus) fun htr9 => ?_
            have hinfo_cap_beq : (_ == 0#64) = false := beq_false_of_ne hinfo_cap_ne
            have ⟨_, _, _⟩ := hinfo_layout
            refine SepWPp.of_sepWP_inImage
              (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4)) hF_sf_9 ?_
            refine SepWP.fold (pointsToBytes_memRegion_entails _ hinfo_le hinfo_layout) (by sep_focus) ?_
            have hstack_sf9 : stackAt sm2.sp extHookStack = stackAt sf_9.sp extHookStack := by
              rw [‹sf_9.sp = sm2.sp›]
            refine SepWP.fold (Entails.of_eq hstack_sf9) (by sep_focus) ?_
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv13
            wpp_call_inImage_mid h_dealloc (_, _, 1) hinv13
            refine SepWPp.pure_left_focus _ (by sep_focus) fun htr10 => ?_
            refine SepWPp.of_sepWP_inImage (mid := entry + 360#64) hF_sf_10 ?_
            refine SepWP.fold (ikmVecBuf_fold A hikm_le hikm_ptr) (by sep_focus) ?_
            have hstack_sf10 : stackAt sf_9.sp extHookStack = stackAt sf_10.sp extHookStack := by
              rw [‹sf_10.sp = sf_9.sp›]
            refine SepWP.fold (Entails.of_eq hstack_sf10) (by sep_focus) ?_
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv14
            refine SepWPp.seq_frame_inImage
              (mid_pc := entry + 376#64)
              (P_local := ikmDeallocLocal A hikm_le hikm_ptr sf_10.sp)
              (Q_local := A.pool ∗ stackAt sf_10.sp extHookStack)
              hinv14 (by dsimp only [ikmDeallocLocal]; sep_focus) ?_ ?_
            · dsimp only [ikmDeallocLocal]
              rcases dealloc_vecBuf_cases hikm_le with hcap_ikm | hcap_ikm
              · refine SepWP.fold (vecBufAt_of_cap_zero A hcap_ikm hikm_le) (by sep_focus) ?_
                simp only [hcap_ikm]
                wp_steps
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                refine ⟨by wp_norm_goal,
                  by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, and_self],
                  by wp_norm_goal, Entails.of_eq (emp_sepConj _)⟩
              · have hcap_ikm_beq : (_ == 0#64) = false := beq_false_of_ne hcap_ikm
                refine SepWP.fold (vecBufAt_of_cap_ne_zero A hcap_ikm hikm_le hikm_lt) (by sep_focus) ?_
                refine SepWP.pure_left_focus _ (by sep_focus) ?_
                intro hikm_lay
                have ⟨_, _, _⟩ := hikm_lay
                apply SepWP.seq_inImage
                  (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4)) hinv14
                wp_steps
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                rintro ⟨hF_d3, hsym_d3⟩
                wp_call h_dealloc (_, _, 1)
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                refine ⟨by simp only [wp_norm, arm64_norm, *],
                  by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm, *],
                  Entails.refl _⟩
            · intro sm3 hpc_sm3 hrun_sm3 hsp_sm3 hcs_sm3 htr_sm3 _
              have hstack_sm3 : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 160#64) extHookStack := by
                rw [‹sf_10.sp = sf_9.sp›, ‹sf_9.sp = sm2.sp›, hsp_sm2]
              simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp_sm3 hcs_sm3 htr_sm3
              rcases hcs_sm3 with ⟨hx19_sm3, hx20_sm3, hx21_sm3, hx22_sm3, hx23_sm3, hx24_sm3,
                hx25_sm3, hx26_sm3, hx27_sm3, hx28_sm3, hx29_sm3, hvregs_sm3⟩
              apply SepWPp.of_sepWP_ret
              refine SepWP.fold (Entails.of_eq hstack_sm3) (by sep_focus) ?_
              wp_steps
              have hbe_len : (toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length = 8 := by simp
              refine SepWP.fold
                (rejoin_stack_authUpdateX s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ hbe_len _ _ _ _ _ _)
                (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (hsplit_top s0.sp).symm) (by sep_focus) ?_
              have hrk_new_len :
                  (List.take 32 (hkdfToSliceUnchecked F (List.replicate 32 0#8) (auth.rootKey ++ k)
                    (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))) 64)).length = 32 :=
                take_32_length_of_64 hkdf_len
              have hmk_new_len :
                  (List.take 32 (List.drop 32 (hkdfToSliceUnchecked F (List.replicate 32 0#8) (auth.rootKey ++ k)
                    (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))) 64))).length = 32 :=
                drop_32_take_32_length_of_64 hkdf_len
              refine SepWP.fold
                (authenticatorAt_of_32_32 A (s0.readReg64 (.gpr 0#5))
                  (sf_6.readReg64 Reg.x0) (sf_8.readReg64 Reg.x0)
                  _ _ hrk_new_len hmk_new_len hoom32_1 hoom32_2)
                (by sep_focus) ?_
              rw [drop_32_take_32_eq_drop_32_of_length_64 hkdf_len]
              dsimp only [Authenticator.update, hkdfToVecUnchecked_eq_hkdfToSliceUnchecked]
              wp_done

private theorem authHkdf_of_okX {img : Obj.Image} {hkdf : HkdfFn}
    {ext : String → Option (State → State)} (h : HkdfToSliceSpqrOkX img hkdf ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
      ((authHkdfSpecAt extHookStack hkdf).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [Spec.inImage, authHkdfSpecAt, hkdfToSliceSpqrSpec, hkdfToSliceSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢; refine ⟨hpre.1, ?_⟩; have h2 := hpre.2
  rw [sepConj_assoc, satisfies_pure_sepConj] at h2 ⊢
  rcases h2 with ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, hs, hi, _, _, hf1, hf2, ho⟩, hrest⟩
  exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, hs, hi, hf1, hf2, ho⟩, hrest⟩

private theorem authHkdf_of_okExt {img : Obj.Image} {hkdf : HkdfFn}
    {ext : String → Option (State → State)} (h : HkdfToSliceSpqrOkExt img hkdf ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
      ((authHkdfSpecAt hkdfToSliceStackExt hkdf).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [Spec.inImage, authHkdfSpecAt, hkdfToSliceSpecExt] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢; refine ⟨hpre.1, ?_⟩; have h2 := hpre.2
  rw [sepConj_assoc, satisfies_pure_sepConj] at h2 ⊢
  rcases h2 with ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, hs, hi, hsro, hiro, hf1, hf2, ho⟩, hrest⟩
  exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, hs, hi, hf1, hf2, ho, hsro, hiro⟩, hrest⟩

theorem authUpdatePinned_ok_of_contracts_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext) (hA : AllocContractsX img A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
      ((authUpdatePinnedSpec F A).inImage img) :=
  authUpdatePinned_ok_gen (extra := 0) (fun _ => by rw [ProofLib.memRegion_zero, emp_sepConj])
    (fun _ => by rw [ProofLib.memRegion_zero, emp_sepConj]) himg hconcat (authHkdf_of_okX hhkdf) hA hallocZeroed

theorem authUpdatePinned_ok_of_contracts_ext {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext) (hA : AllocContractsX img A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
      ((authUpdatePinnedSpecExt F A).inImage img) :=
  authUpdatePinned_ok_gen (extra := 1232)
    (fun sp => ProofLib.stackAt_split_bottom sp authUpdateStackX 1232 (by decide))
    (fun sp => by
      have h := ProofLib.stackAt_split_bottom (sp - 160#64) extHookStack 1232 (by decide)
      have hsub : sp - 160#64 - BitVec.ofNat 64 (extHookStack + 1232) =
          sp - BitVec.ofNat 64 authUpdateStackExt := by
        dsimp only [extHookStack, authUpdateStackExt, hkdfToSliceStackExt]; bv_kernel
      have hstk : stackAt (sp - 160#64) (extHookStack + 1232) =
          stackAt (sp - 160#64) hkdfToSliceStackExt := rfl
      exact ((hstk.symm.trans h).trans (by rw [hsub])).symm)
    himg hconcat (authHkdf_of_okExt hhkdf) hA hallocZeroed

private def authUpdateSpecAt (stk : Nat) (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) : Spec AuthUpdateGhost where
  pre x s := ⌜s.readReg64 .x0 = x.selfA ∧ s.readReg64 .x1 = x.ep ∧
    s.readReg64 .x2 = x.kA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.k.length ∧
    x.auth.rootKey.length + x.k.length < 2 ^ 63⌝ ∗
    authenticatorAt A x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗ A.pool ∗ stackAt s.sp stk
  post x s0 sf := ⌜sf.trace = s0.trace⌝ ∗
    authenticatorAt A x.selfA (x.auth.update F x.ep x.k) ∗ bytesAt x.kRO x.kA x.k ∗
    A.pool ∗ stackAt s0.sp stk
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem authUpdate_ok_of_pinned {img : Obj.Image} {stk : Nat}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hpinned : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
      ((authUpdatePinnedSpecAt stk F A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
      ((authUpdateSpecAt stk F A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [Spec.inImage, authUpdateSpecAt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨himg_s0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hpure_s0, hpre⟩
  have h1 : s0.mem ⊨ authenticatorAt A x.selfA x.auth ∗
      (bytesAt x.kRO x.kA x.k ∗ A.pool ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hpre ⊢
  rw [authenticatorAt_eq_exists_pinned A x.selfA x.auth,
    sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨g, hg⟩
  let xp : AuthUpdatePinnedGhost := ⟨x.selfA, g, x.auth, x.ep, x.kRO, x.kA, x.k⟩
  have hpre_pin : s0.mem ⊨ ((authUpdatePinnedSpecAt stk F A).inImage img).pre xp s0 ∗ R := by
    dsimp only [Spec.inImage, authUpdatePinnedSpecAt, xp]
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨himg_s0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hpure_s0, ?_⟩
    ac_nf at hg ⊢
  exact hpinned.mono_outcome xp R s0 hpc hrun hpre_pin hsp fun _ hout => hout

/-- `<spqr::authenticator::Authenticator>::update` (`0x5debc`, 107 instructions) meets
`(authUpdateSpec F A).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
theorem authUpdate_ok_of_contracts_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext) (hA : AllocContractsX img A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext) : AuthUpdateOkX img F A ext :=
  authUpdate_ok_of_pinned (authUpdatePinned_ok_of_contracts_x himg hconcat hhkdf hA hallocZeroed)

theorem authUpdate_ok_of_hook_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext) (hA : AllocContractsX img A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) : AuthUpdateOkX img F A ext :=
  authUpdate_ok_of_contracts_x himg hconcat hhkdf hA (allocZeroedWithStackOkX_of_hook hZero)

theorem authUpdate_ok_of_contracts_ext {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext) (hA : AllocContractsX img A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext) : AuthUpdateOkExt img F A ext :=
  authUpdate_ok_of_pinned (authUpdatePinned_ok_of_contracts_ext himg hconcat hhkdf hA hallocZeroed)

theorem authUpdate_ok_of_hook_ext {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext) (hA : AllocContractsX img A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) : AuthUpdateOkExt img F A ext :=
  authUpdate_ok_of_contracts_ext himg hconcat hhkdf hA (allocZeroedWithStackOkX_of_hook hZero)

set_option maxHeartbeats 3200000 in
theorem authUpdatePinned_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_concat : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat2Spec A)))
    (h_hkdf : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 379) (withLsCallInv lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith F))))
    (h_shim : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (h_alloc : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (h_allocZeroed : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
      (rustAllocZeroedSpecWithStack A extHookStack))
    (h_dealloc : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack A extHookStack))
    (h_panic : ((blkPC_341).rebase (blkPl_341).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_341).rebase (blkPl_341).base H) (blkPl_341).base
      (withLsCallInv lsmpl (authUpdatePinnedSpec F A)) := by
  have h_hkdf : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 379) (withLsCallInv lsmpl (hkdfToSliceSpqrSpec (hkdfToSliceUnchecked F))) := h_hkdf
  have h_shim_inv := subroutine_ok_withLsCallInv_of_plain (pl := lsmpl) h_shim
  have h_alloc_inv := subroutine_ok_withLsCallInv_of_plain (pl := lsmpl) h_alloc
  have h_allocZeroed_inv := subroutine_ok_withLsCallInv_of_plain (pl := lsmpl) h_allocZeroed
  have h_dealloc_inv := subroutine_ok_withLsCallInv_of_plain (pl := lsmpl) h_dealloc
  refine subroutine_ok_withLsCallInv_rodata2_keep rodata_updateLabel_placed rodata_zeros32_placed ?_
  wpp_init x s0
  rcases x with ⟨selfA, g, auth, ep, kRO, kA, k⟩
  dsimp only [authUpdatePinnedSpec, withLsCallInv] at hpre h_1 h_2 h_3 h_4 h_5 h ⊢
  have hinv0 : LsCallInv lsmpl s0.mem := h_1
  subst h_2 h_3 h_4
  refine SepWPp.rw_pre (by rw [stackAt_authUpdateX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 386) hinv0 ?_
  refine SepWP.fold (authenticatorPinAt_expose_entails A g (s0.readReg64 (.gpr 0#5)) auth) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨⟨hrk_le, hrk_lt, hrk_ptr⟩, ⟨hmk_le, hmk_lt, hmk_ptr⟩⟩
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  change subroutine_ok _ _ (withLsCallInv lsmpl (sliceConcat2Spec A)) at h_concat
  wpp_call_lsCallInv_mid h_concat
    (⟨s0.sp - 160#64, s0.sp - 112#64, false, g.rootKey.ptr, auth.rootKey,
      kRO, s0.readReg64 (.gpr 2#5), k⟩ : SliceConcat2Ghost)
    hinv1
  refine SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 386) hF_sf ?_
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 56#64) (s0.readReg64 (.gpr 1#5))))
    (by sep_focus) ?_
  have hstack_sf : stackAt (s0.sp - 160#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 160#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_lsCallInv_mid h_concat
    (⟨s0.sp - 136#64, s0.sp - 112#64,
      true, lsρ "spqr:.rodata..Lanon.138", Authenticator.updateLabel,
      false, s0.sp - 56#64, toBEBytes 8 (s0.readReg64 (.gpr 1#5))⟩ : SliceConcat2Ghost)
    hinv2
  refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
  have hinfo_pos : 0 < (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length := by simp
  refine SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hF_sf_1 ?_
  refine SepWP.fold (vecU8_expose_entails A (s0.sp - 160#64) (auth.rootKey ++ k)) (by sep_focus) ?_
  refine SepWP.fold (vecU8_nonempty_entails A (s0.sp - 136#64) hinfo_pos) (by sep_focus) ?_
  sep_elim_exists
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hinfo_cap_ne, hinfo_layout, hinfo_ptr, hinfo_le⟩
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hikm_le, hikm_lt, hikm_ptr⟩
  have hikm_len_lt : (auth.rootKey ++ k).length < 2 ^ 63 := Nat.lt_of_le_of_lt hikm_le hikm_lt
  wp_steps
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  change subroutine_ok _ _ (withLsCallInv lsmpl (withStack sessionShimSpec extHookStack)) at h_shim_inv
  wpp_call_lsCallInv_mid h_shim_inv () hinv3
  refine SepWPp.pure_left_focus _ (by sep_focus) fun htr_s1 => ?_
  refine SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed") hF_sf_2 ?_
  wp_steps
  have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
    rw [‹sf_2.sp = sf_1.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv4
  have hlay64 : LayoutOk 64 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  change subroutine_ok _ _ (withLsCallInv lsmpl (rustAllocZeroedSpecWithStack A extHookStack)) at h_allocZeroed_inv
  wpp_call_lsCallInv_mid h_allocZeroed_inv (64, 1) hinv4
  by_cases hoom64 : sf_3.readReg64 Reg.x0 = 0#64
  · conv => arg 4; simp only [hoom64, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr3 => ?_
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    exact allowPanic_panicked_update
      (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64_beq : (sf_3.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom64
    conv => arg 4; simp only [hoom64, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, htr3⟩
    refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 379) hF_sf_3 ?_
    refine SepWP.fold (pointsToBytes_replicate_64_entails_memRegion (sf_3.readReg64 Reg.x0)) (by sep_focus) ?_
    wp_steps
    have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by
      rw [‹sf_3.sp = sf_2.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv5
    have hinfo_ge : 32 ≤ (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length := by simp
    have hinfo_lt : (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length < 55 := by simp
    change subroutine_ok _ _ (withLsCallInv lsmpl (hkdfToSliceSpqrSpec (hkdfToSliceUnchecked F))) at h_hkdf
    wpp_call_lsCallInv_mid h_hkdf
      (⟨true, lsρ "spqr:.rodata.cst32+0x0", List.replicate 32 0#8,
        false, _, auth.rootKey ++ k,
        false, _, Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)),
        sf_3.readReg64 Reg.x0, 64⟩ : HkdfToSliceGhost)
      hinv5
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hkdf_len, htr4⟩
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hokm_all, hokm_take, hokm_drop⟩ :=
      exists_unpack64_of_length_64_split hkdf_len
    refine SepWPp.of_sepWP_lsCallInv
      (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hF_sf_4 ?_
    wp_steps
    have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt sf_4.sp extHookStack := by
      rw [‹sf_4.sp = sf_3.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv6
    wpp_call_lsCallInv_mid h_shim_inv () hinv6
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr_s2 => ?_
    refine SepWPp.of_sepWP_lsCallInv
      (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") hF_sf_5 ?_
    wp_steps
    have hstack_sf5 : stackAt sf_4.sp extHookStack = stackAt sf_5.sp extHookStack := by
      rw [‹sf_5.sp = sf_4.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf5) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv7
    have hlay32 : LayoutOk 32 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
    change subroutine_ok _ _ (withLsCallInv lsmpl (rustAllocSpecWithStack A extHookStack)) at h_alloc_inv
    wpp_call_lsCallInv_mid h_alloc_inv (32, 1) hinv7
    by_cases hoom32_1 : sf_6.readReg64 Reg.x0 = 0#64
    · conv => arg 4; simp only [hoom32_1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr6 => ?_
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      exact allowPanic_panicked_update
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom32_1_beq : (sf_6.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom32_1
      conv => arg 4; simp only [hoom32_1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr6⟩
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_341).base + 228#64) hF_sf_6 ?_
      refine SepWP.fold (Entails.of_eq (hokm_all (sf_3.readReg64 Reg.x0))) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (memRegion_32_cells (sf_6.readReg64 Reg.x0))) (by sep_focus) ?_
      sep_elim_exists
      wp_steps
      refine SepWP.fold (Entails.of_eq (hokm_take (sf_6.readReg64 Reg.x0)).symm) (by sep_focus) ?_
      refine SepWP.fold (vecBufAt_fold A g.rootKey.cap g.rootKey.ptr auth.rootKey) (by sep_focus) ?_
      have hstack_sf6 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by
        rw [‹sf_6.sp = sf_5.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf6) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv8
      refine SepWPp.seq_frame_lsCallInv
        (mid_pc := (blkPl_341).base + 244#64)
        (P_local := vecBufAt A g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
          A.pool ∗ stackAt sf_6.sp extHookStack)
        (Q_local := A.pool ∗ stackAt sf_6.sp extHookStack)
        hinv8 (by sep_focus) ?_ ?_
      · by_cases hcap_rk : g.rootKey.cap = 0#64
        · refine SepWP.fold (vecBufAt_of_cap_zero A hcap_rk hrk_le) (by sep_focus) ?_
          simp only [hcap_rk]
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by wp_norm_goal,
            by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, and_self],
            by wp_norm_goal, Entails.of_eq (emp_sepConj _)⟩
        · have hcap_rk_beq : (g.rootKey.cap == 0#64) = false := beq_false_of_ne hcap_rk
          refine SepWP.fold (vecBufAt_of_cap_ne_zero A hcap_rk hrk_le hrk_lt) (by sep_focus) ?_
          refine SepWP.pure_left_focus _ (by sep_focus) ?_
          intro hrk_lay
          have ⟨_, _, _⟩ := hrk_lay
          wp_steps
          wp_call h_dealloc (g.rootKey.ptr, g.rootKey.cap.toNat, 1)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by simp only [wp_norm, arm64_norm, *],
            by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            Entails.refl _⟩
      · intro sm1 hpc_sm1 hrun_sm1 hsp_sm1 hcs_sm1 htr_sm1 hF_sm1
        simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp_sm1 hcs_sm1 htr_sm1
        have hstack_sm1 : stackAt sf_6.sp extHookStack = stackAt sm1.sp extHookStack := by
          rw [hsp_sm1, ‹sf_6.sp = sf_5.sp›, ‹sf_5.sp = sf_4.sp›, ‹sf_4.sp = sf_3.sp›,
            ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 160#64›]
        rcases hcs_sm1 with ⟨hx19_sm1, hx20_sm1, hx21_sm1, hx22_sm1, hx23_sm1, hx24_sm1,
          hx25_sm1, hx26_sm1, hx27_sm1, hx28_sm1, hx29_sm1, hvregs_sm1⟩
        refine SepWPp.of_sepWP_lsCallInv
          (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hF_sm1 ?_
        refine SepWP.fold (Entails.of_eq hstack_sm1) (by sep_focus) ?_
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv9
        wpp_call_lsCallInv_mid h_shim_inv () hinv9
        refine SepWPp.pure_left_focus _ (by sep_focus) fun htr_s3 => ?_
        refine SepWPp.of_sepWP_lsCallInv
          (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") hF_sf_7 ?_
        wp_steps
        have hstack_sf7 : stackAt sm1.sp extHookStack = stackAt sf_7.sp extHookStack := by
          rw [‹sf_7.sp = sm1.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf7) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv10
        wpp_call_lsCallInv_mid h_alloc_inv (32, 1) hinv10
        by_cases hoom32_2 : sf_8.readReg64 Reg.x0 = 0#64
        · conv => arg 4; simp only [hoom32_2, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
          refine SepWPp.pure_left_focus _ (by sep_focus) fun htr8 => ?_
          apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
          exact allowPanic_panicked_update
            (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
        · have hoom32_2_beq : (sf_8.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom32_2
          conv => arg 4; simp only [hoom32_2, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
          refine SepWPp.pure_left_focus _ (by sep_focus) ?_
          rintro ⟨_, htr8⟩
          refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_341).base + 292#64) hF_sf_8 ?_
          refine SepWP.fold (Entails.of_eq (memRegion_32_cells (sf_8.readReg64 Reg.x0))) (by sep_focus) ?_
          sep_elim_exists
          wp_steps
          refine SepWP.fold (Entails.of_eq (hokm_drop (sf_8.readReg64 Reg.x0)).symm) (by sep_focus) ?_
          refine SepWP.fold (vecBufAt_fold A g.macKey.cap g.macKey.ptr auth.macKey) (by sep_focus) ?_
          have hstack_sf8 : stackAt sf_7.sp extHookStack = stackAt sf_8.sp extHookStack := by
            rw [‹sf_8.sp = sf_7.sp›]
          refine SepWP.fold (Entails.of_eq hstack_sf8) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv11
          refine SepWPp.seq_frame_lsCallInv
            (mid_pc := (blkPl_341).base + 308#64)
            (P_local := ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ g.macKey.ptr) ∗
              vecBufAt A g.macKey.cap g.macKey.ptr auth.macKey ∗
              A.pool ∗ stackAt sf_8.sp extHookStack)
            (Q_local := ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ g.macKey.ptr) ∗
              A.pool ∗ stackAt sf_8.sp extHookStack)
            hinv11 (by sep_focus) ?_ ?_
          · by_cases hcap_mk : g.macKey.cap = 0#64
            · refine SepWP.fold (vecBufAt_of_cap_zero A hcap_mk hmk_le) (by sep_focus) ?_
              simp only [hcap_mk]
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              refine ⟨by wp_norm_goal,
                by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, and_self],
                by wp_norm_goal, Entails.of_eq (emp_sepConj _)⟩
            · have hcap_mk_beq : (g.macKey.cap == 0#64) = false := beq_false_of_ne hcap_mk
              refine SepWP.fold (vecBufAt_of_cap_ne_zero A hcap_mk hmk_le hmk_lt) (by sep_focus) ?_
              refine SepWP.pure_left_focus _ (by sep_focus) ?_
              intro hmk_lay
              have ⟨_, _, _⟩ := hmk_lay
              wp_steps
              wp_call h_dealloc (g.macKey.ptr, g.macKey.cap.toNat, 1)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              refine ⟨by simp only [wp_norm, arm64_norm, *],
                by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                Entails.of_eq (by ac_rfl)⟩
          · intro sm2 hpc_sm2 hrun_sm2 hsp_sm2 hcs_sm2 htr_sm2 hF_sm2
            simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp_sm2 hcs_sm2 htr_sm2
            have hstack_sm2 : stackAt sf_8.sp extHookStack = stackAt sm2.sp extHookStack := by
              rw [hsp_sm2, ‹sf_8.sp = sf_7.sp›, ‹sf_7.sp = sm1.sp›, hsp_sm1]
            rcases hcs_sm2 with ⟨hx19_sm2, hx20_sm2, hx21_sm2, hx22_sm2, hx23_sm2, hx24_sm2,
              hx25_sm2, hx26_sm2, hx27_sm2, hx28_sm2, hx29_sm2, hvregs_sm2⟩
            refine SepWPp.of_sepWP_lsCallInv
              (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hF_sm2 ?_
            refine SepWP.fold (Entails.of_eq hstack_sm2) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (hokm_all (sf_3.readReg64 Reg.x0)).symm) (by sep_focus) ?_
            refine SepWP.fold (pointsToBytes_64_entails_memRegion (sf_3.readReg64 Reg.x0) hkdf_len) (by sep_focus) ?_
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv12
            change subroutine_ok _ _ (withLsCallInv lsmpl (rustDeallocExternSpecWithStack A extHookStack)) at h_dealloc_inv
            wpp_call_lsCallInv_mid h_dealloc_inv (sf_3.readReg64 Reg.x0, 64, 1) hinv12
            refine SepWPp.pure_left_focus _ (by sep_focus) fun htr9 => ?_
            have hinfo_cap_beq : (_ == 0#64) = false := beq_false_of_ne hinfo_cap_ne
            have ⟨_, _, _⟩ := hinfo_layout
            refine SepWPp.of_sepWP_lsCallInv
              (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hF_sf_9 ?_
            refine SepWP.fold (pointsToBytes_memRegion_entails _ hinfo_le hinfo_layout) (by sep_focus) ?_
            have hstack_sf9 : stackAt sm2.sp extHookStack = stackAt sf_9.sp extHookStack := by
              rw [‹sf_9.sp = sm2.sp›]
            refine SepWP.fold (Entails.of_eq hstack_sf9) (by sep_focus) ?_
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv13
            wpp_call_lsCallInv_mid h_dealloc_inv (_, _, 1) hinv13
            refine SepWPp.pure_left_focus _ (by sep_focus) fun htr10 => ?_
            refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_341).base + 360#64) hF_sf_10 ?_
            refine SepWP.fold (ikmVecBuf_fold A hikm_le hikm_ptr) (by sep_focus) ?_
            have hstack_sf10 : stackAt sf_9.sp extHookStack = stackAt sf_10.sp extHookStack := by
              rw [‹sf_10.sp = sf_9.sp›]
            refine SepWP.fold (Entails.of_eq hstack_sf10) (by sep_focus) ?_
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv14
            refine SepWPp.seq_frame_lsCallInv
              (mid_pc := (blkPl_341).base + 376#64)
              (P_local := ikmDeallocLocal A hikm_le hikm_ptr sf_10.sp)
              (Q_local := A.pool ∗ stackAt sf_10.sp extHookStack)
              hinv14 (by dsimp only [ikmDeallocLocal]; sep_focus) ?_ ?_
            · dsimp only [ikmDeallocLocal]
              rcases dealloc_vecBuf_cases hikm_le with hcap_ikm | hcap_ikm
              · refine SepWP.fold (vecBufAt_of_cap_zero A hcap_ikm hikm_le) (by sep_focus) ?_
                simp only [hcap_ikm]
                wp_steps
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                refine ⟨by wp_norm_goal,
                  by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, and_self],
                  by wp_norm_goal, Entails.of_eq (emp_sepConj _)⟩
              · have hcap_ikm_beq : (_ == 0#64) = false := beq_false_of_ne hcap_ikm
                refine SepWP.fold (vecBufAt_of_cap_ne_zero A hcap_ikm hikm_le hikm_lt) (by sep_focus) ?_
                refine SepWP.pure_left_focus _ (by sep_focus) ?_
                intro hikm_lay
                have ⟨_, _, _⟩ := hikm_lay
                wp_steps
                wp_call h_dealloc (_, _, 1)
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                refine ⟨by simp only [wp_norm, arm64_norm, *],
                  by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm, *],
                  Entails.refl _⟩
            · intro sm3 hpc_sm3 hrun_sm3 hsp_sm3 hcs_sm3 htr_sm3 _
              have hstack_sm3 : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 160#64) extHookStack := by
                rw [‹sf_10.sp = sf_9.sp›, ‹sf_9.sp = sm2.sp›, hsp_sm2]
              simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp_sm3 hcs_sm3 htr_sm3
              rcases hcs_sm3 with ⟨hx19_sm3, hx20_sm3, hx21_sm3, hx22_sm3, hx23_sm3, hx24_sm3,
                hx25_sm3, hx26_sm3, hx27_sm3, hx28_sm3, hx29_sm3, hvregs_sm3⟩
              apply SepWPp.of_sepWP_ret
              refine SepWP.fold (Entails.of_eq hstack_sm3) (by sep_focus) ?_
              wp_steps
              have hbe_len : (toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length = 8 := by simp
              refine SepWP.fold
                (rejoin_stack_authUpdateX s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ hbe_len _ _ _ _ _ _)
                (by sep_focus) ?_
              have hrk_new_len :
                  (List.take 32
                    (hkdfToSliceUnchecked F (List.replicate 32 0#8) (auth.rootKey ++ k)
                      (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))) 64)).length = 32 :=
                take_32_length_of_64 hkdf_len
              have hmk_new_len :
                  (List.take 32
                    (List.drop 32
                      (hkdfToSliceUnchecked F (List.replicate 32 0#8) (auth.rootKey ++ k)
                        (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))) 64))).length = 32 :=
                drop_32_take_32_length_of_64 hkdf_len
              refine SepWP.fold
                (authenticatorAt_of_32_32 A (s0.readReg64 (.gpr 0#5))
                  (sf_6.readReg64 Reg.x0) (sf_8.readReg64 Reg.x0)
                  _ _ hrk_new_len hmk_new_len hoom32_1 hoom32_2)
                (by sep_focus) ?_
              rw [drop_32_take_32_eq_drop_32_of_length_64 hkdf_len]
              dsimp only [Authenticator.update, hkdfToVecUnchecked_eq_hkdfToSliceUnchecked]
              wp_done

/-- Relocatable `<spqr::authenticator::Authenticator>::update` (Block `341`) meets
`withLsCallInv lsmpl (authUpdateSpec F A)` under `[LibsignalPlacement]`. -/
theorem authUpdate_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_concat : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat2Spec A)))
    (h_hkdf : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 379) (withLsCallInv lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith F))))
    (h_shim : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (h_alloc : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (h_allocZeroed : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
      (rustAllocZeroedSpecWithStack A extHookStack))
    (h_dealloc : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack A extHookStack))
    (h_panic : ((blkPC_341).rebase (blkPl_341).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_341).rebase (blkPl_341).base H) (blkPl_341).base
      (withLsCallInv lsmpl (authUpdateSpec F A)) := by
  have hpinned := authUpdatePinned_placed_ok h_concat h_hkdf h_shim h_alloc h_allocZeroed h_dealloc h_panic
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCallInv, authUpdateSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg_s0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure_s0, hpre⟩
  have h1 : s0.mem ⊨ authenticatorAt A x.selfA x.auth ∗
      (bytesAt x.kRO x.kA x.k ∗ A.pool ∗ stackAt s0.sp authUpdateStackX ∗ R) := by
    ac_nf at hpre ⊢
  rw [authenticatorAt_eq_exists_pinned A x.selfA x.auth,
    sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨g, hg⟩
  let xp : AuthUpdatePinnedGhost := ⟨x.selfA, g, x.auth, x.ep, x.kRO, x.kA, x.k⟩
  have hpre_pin : s0.mem ⊨ (withLsCallInv lsmpl (authUpdatePinnedSpec F A)).pre xp s0 ∗ R := by
    dsimp only [withLsCallInv, authUpdatePinnedSpec, xp]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨himg_s0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpure_s0, ?_⟩
    ac_nf at hg ⊢
  exact hpinned.mono_outcome xp R s0 hpc hrun hpre_pin hsp fun _ hout => hout

end CryptoVerification.SpqrV1.Auth
