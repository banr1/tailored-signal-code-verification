/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDec
import ProofLib.SepLogic.WPp

/-!
# Shared Definitions and Segment 8 Helpers for `S7Spec`, `S8Spec`, and `S9Spec`

Shared instruction-fetch macros, `SepWPp` framing/panic bridges, and Segment 8 helpers for the back
segments of `try_decrypt_with_state::<HookRng>`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection
open CryptoVerification.HookTrace

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

namespace BS10

theorem spAligned_of_sp_eq {s1 s2 : State} (heq : s2.sp = s1.sp) (hal : s1.spAligned = true) :
    s2.spAligned = true := by
  unfold State.spAligned at hal ⊢
  rw [heq]
  exact hal

end BS10

open Lean Elab Tactic in
/-- `code_fetches_from <code> <decPrefix> b H hfn off k0 len` adds `<code>_fetch_fnAddr`
    hypotheses for the instructions `k = k0, k0 + 4, …, k0 + len - 4` of the function at offset
    `off` (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:ident
    off:num k0:num len:num : tactic => do
  let off := off.getNat
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let hex := String.ofList (Nat.toDigits 16 (off + k))
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{hex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-- Fetch hypotheses for `try_decrypt_with_state::<HookRng>` (`hfn : fnOff tryDecryptName
  = 0x6eff8`),
    from fn-relative offset `k0`, `len` bytes. -/
macro "decrypt_fetches " b:term:max C:term:max ctl:term:max abs:term:max
    hfn:ident k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode libsignalTripleRatchetBin $b
    (Rust.withPanics (tripleRatchetExterns $C $ctl $abs)) $hfn 0x6eff8 $k0 $len)

/-! ## 1. Entry / PC Rewriting and Callee / Hook Wrappers -/

theorem tryDecryptEntry_eq_fnAddr {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    tryDecryptEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName :=
  entryOf_eq_tripleRatchetProgAt himg tryDecryptName

theorem segS7PC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    segS7PC img
      = (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 0x63c := by
  rw [segS7PC, tryDecryptEntry_eq_fnAddr himg]

theorem segS8PC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    segS8PC img
      = (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 0x678 := by
  rw [segS8PC, tryDecryptEntry_eq_fnAddr himg]

theorem segS9PC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    segS9PC img
      = (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 0x6a4 := by
  rw [segS9PC, tryDecryptEntry_eq_fnAddr himg]

theorem errTailPC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    errTailPC img
      = (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 0x30c := by
  rw [errTailPC, tryDecryptEntry_eq_fnAddr himg]

theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

theorem sessionMemcpyRegion_hookOk : HookOk hookMemcpy sessionMemcpyRegionSpec := by
  refine HookOk.of_trace hookMemcpy_region_ok fun _ _ _ ht hpost => ?_
  simp only [memcpyRegionSpec, sessionMemcpyRegionSpec, sepConj_assoc,
    satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

/-! ## 2. `SepWPp` Segment, Representation & Panic Bridge Lemmas -/

theorem sepWPp_to_reaches_outcome {α : Type} {prog : Program} {spec : Spec α}
    {x : α} {P R : SepProp} {s0 s : State}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp prog (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    reaches_outcome prog spec x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩⟩ := hwp R hm hL
  · exact reaches_outcome_steps hsteps
      (reaches_outcome_refl_return hpc hrun ⟨hq hmf, hsp, hcs⟩)
  · exact reaches_outcome_steps hsteps (reaches_outcome_refl_panic hpan (hqp hmf))
  · exact (not_satisfies_false_sepConj hoom).elim

theorem allocFailedIn_trans {s0 sm sf : State}
    (h0m : s0.trace <+: sm.trace) (hmf : allocFailedIn sm sf) :
    allocFailedIn s0 sf := by
  obtain ⟨t, ht⟩ := h0m
  unfold allocFailedIn at hmf ⊢
  rw [← ht, List.length_append, ← List.drop_drop] at hmf
  exact List.mem_of_mem_drop hmf

theorem tryDecrypt_onPanic_of_callee (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 sm sf : State) (F R : SepProp)
    (h0m : s0.trace <+: sm.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  unfold tryDecryptSpec Spec.inImage
  exact allowPanic_frame
    (fun ⟨haf, hmf⟩ => ⟨Or.inr (Or.inr (allocFailedIn_trans h0m haf)), h0m.trans hmf⟩) hm

theorem tryDecrypt_onPanic_of_direct (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 sf : State) (P R : SepProp)
    (haf : allocFailedIn s0 sf) (htr : s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  unfold tryDecryptSpec Spec.inImage
  exact allowPanic_panicked ⟨Or.inr (Or.inr haf), htr⟩ hm

theorem SepWPp.panic_at {prog : Program} {ret panic_pc : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : prog.externAt? panic_pc = some Rust.panicked)
    (hqp : Qp (Rust.panicked s) P) : SepWPp prog ret s P Q Qp := by
  rw [← hpc] at hext
  exact SepWPp.panic hrun hext hqp

theorem SepWPp.panic_direct (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (abs : String → Option (State → State))
    (x : TryDecryptGhost) (s0 s : State) (ret panic_pc : BitVec 64)
    (P R : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : (tripleRatchetProgAt img.base C ctl abs).externAt? panic_pc = some Rust.panicked)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs) ret s P Q
      (fun sf P_f => sf.status = .Panicked → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R)) := by
  refine SepWPp.panic_at hpc hrun hext fun _ hm_pan => ?_
  have htr_f : (Rust.panicked s).trace = s0.trace ++ [allocFailedEvent] := htr
  have haf : allocFailedIn s0 (Rust.panicked s) := by
    unfold allocFailedIn
    rw [htr_f, List.drop_left]
    exact List.Mem.head _
  have hpre : s0.trace <+: (Rust.panicked s).trace := by
    rw [htr_f]
    exact ⟨[allocFailedEvent], rfl⟩
  exact tryDecrypt_onPanic_of_direct C A ctl S img x s0 (Rust.panicked s) P R haf hpre hm_pan

def boxU8Rest (A : RustAlloc) (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜p ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗ (if bs = [] then emp else A.live p bs.length 1)

theorem boxU8At_eq_rest (A : RustAlloc) (b p : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A b p bs =
      ((b ↦₆₄ p) ∗ ((b + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
       (p ↦ₛ bs) ∗ boxU8Rest A p bs) := by
  unfold boxU8At boxU8Rest
  by_cases h : bs = []
  · subst h
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ↓reduceIte, pointsToBytes_nil, sepConj_emp]
    ac_rfl
  · simp only [h, ↓reduceIte]
    ac_rfl

theorem bytesToKey32_keyToBytes32 (k : BitVec 256) : bytesToKey32 (keyToBytes32 k) = k := by
  have h0 (x : BitVec 8) : ((0 : BitVec 256) <<< 8) ||| x.setWidth 256 = x.setWidth 256 := by simp
  have hstep {w : Nat} (x : BitVec w) (y : BitVec 8) :
      ((x.setWidth 256) <<< 8) ||| y.setWidth 256 = (x ++ y).setWidth 256 := by
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [h8, BitVec.getLsbD_of_ge y i (by omega)]
  have hext (s₂ s₁ n₂ n₁ : Nat) (h : s₂ = s₁ + n₁) :
      k.extractLsb' s₂ n₂ ++ k.extractLsb' s₁ n₁ = k.extractLsb' s₁ (n₂ + n₁) := by
    subst h
    ext i hi
    simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
    split
    · rfl
    · congr 1; omega
  change bytesToKey32
      [k.extractLsb' 0 8, k.extractLsb' 8 8, k.extractLsb' 16 8, k.extractLsb' 24 8,
       k.extractLsb' 32 8, k.extractLsb' 40 8, k.extractLsb' 48 8, k.extractLsb' 56 8,
       k.extractLsb' 64 8, k.extractLsb' 72 8, k.extractLsb' 80 8, k.extractLsb' 88 8,
       k.extractLsb' 96 8, k.extractLsb' 104 8, k.extractLsb' 112 8, k.extractLsb' 120 8,
       k.extractLsb' 128 8, k.extractLsb' 136 8, k.extractLsb' 144 8, k.extractLsb' 152 8,
       k.extractLsb' 160 8, k.extractLsb' 168 8, k.extractLsb' 176 8, k.extractLsb' 184 8,
       k.extractLsb' 192 8, k.extractLsb' 200 8, k.extractLsb' 208 8, k.extractLsb' 216 8,
       k.extractLsb' 224 8, k.extractLsb' 232 8, k.extractLsb' 240 8, k.extractLsb' 248 8] = k
  dsimp only [bytesToKey32, List.foldr, BitVec.zeroExtend]
  rw [h0]
  repeat rw [hstep]
  rw [BitVec.setWidth_eq]
  rw [hext 248 240 _ 8 rfl, hext 240 232 _ 8 rfl, hext 232 224 _ 8 rfl, hext 224 216 _ 8 rfl,
      hext 216 208 _ 8 rfl, hext 208 200 _ 8 rfl, hext 200 192 _ 8 rfl, hext 192 184 _ 8 rfl,
      hext 184 176 _ 8 rfl, hext 176 168 _ 8 rfl, hext 168 160 _ 8 rfl, hext 160 152 _ 8 rfl,
      hext 152 144 _ 8 rfl, hext 144 136 _ 8 rfl, hext 136 128 _ 8 rfl, hext 128 120 _ 8 rfl,
      hext 120 112 _ 8 rfl, hext 112 104 _ 8 rfl, hext 104 96 _ 8 rfl, hext 96 88 _ 8 rfl,
      hext 88 80 _ 8 rfl, hext 80 72 _ 8 rfl, hext 72 64 _ 8 rfl, hext 64 56 _ 8 rfl,
      hext 56 48 _ 8 rfl, hext 48 40 _ 8 rfl, hext 40 32 _ 8 rfl, hext 32 24 _ 8 rfl,
      hext 24 16 _ 8 rfl, hext 16 8 _ 8 rfl, hext 8 0 _ 8 rfl]
  ext i hi
  simp

theorem bytesToBlock_blockToBytesLE (iv : CBC.Block) :
    CBC.bytesToBlock (CBC.blockToBytesLE iv) = iv :=
  CBC.bytesToBlock_blockToBytesLE iv

theorem length_keyToBytes32 (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

theorem length_blockToBytesLE (iv : CBC.Block) : (CBC.blockToBytesLE iv).length = 16 := by
  simp [CBC.blockToBytesLE]

theorem add_one_ne_zero_of_lt_2_63 {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  bv_omega

theorem stackAt_sub_split (sp : BitVec 64) (n : Nat) (hn : n ≤ tryDecryptSubStack) :
    stackAt sp tryDecryptSubStack =
      memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - n) ∗
      stackAt sp n := by
  have h := stackAt_split_bottom sp n (tryDecryptSubStack - n)
    (by unfold tryDecryptSubStack rootStack tryDecryptFrameSize at hn ⊢; omega)
  have hsum : n + (tryDecryptSubStack - n) = tryDecryptSubStack := Nat.add_sub_of_le hn
  rwa [hsum] at h

theorem messageKeysAt_eq (sp : BitVec 64) (mks : MessageKeys) :
    messageKeysAt (sp + 0x500#64) mks =
      (((sp + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
       ((sp + 0x520#64) ↦ₛ keyToBytes32 mks.macKey) ∗
       ((sp + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
       ((sp + 0x550#64) ↦₃₂ mks.counter)) := by
  unfold messageKeysAt
  have h1 : sp + 0x500#64 + 0x20#64 = sp + 0x520#64 := by bv_omega
  have h2 : sp + 0x500#64 + 0x40#64 = sp + 0x540#64 := by bv_omega
  have h3 : sp + 0x500#64 + 0x50#64 = sp + 0x550#64 := by bv_omega
  rw [h1, h2, h3]

theorem messageKeysAt_entails_memRegion (p : BitVec 64) (mks : MessageKeys) :
    messageKeysAt p mks ⊢ memRegion p 0x54 := by
  unfold messageKeysAt
  have h1 := pointsToBytes_entails_memRegion p (keyToBytes32 mks.cipherKey)
  rw [length_keyToBytes32] at h1
  have h2 := pointsToBytes_entails_memRegion (p + 0x20#64) (keyToBytes32 mks.macKey)
  rw [length_keyToBytes32] at h2
  have h3 := pointsToBytes_entails_memRegion (p + 0x40#64) (CBC.blockToBytesLE mks.iv)
  rw [length_blockToBytesLE] at h3
  have h4 := pointsTo32_entails_memRegion (p + 0x50#64) mks.counter
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 h4))) ?_
  rw [show (0x54 : Nat) = 32 + (32 + (16 + 4)) by decide,
      memRegion_split p 32 (32 + (16 + 4)) (by decide),
      memRegion_split (p + 32#64) 32 (16 + 4) (by decide),
      show p + 32#64 + 32#64 = p + 0x40#64 by bv_omega,
      memRegion_split (p + 0x40#64) 16 4 (by decide),
      show p + 0x40#64 + 16#64 = p + 0x50#64 by bv_omega]
  exact Entails.refl _

theorem newPqr_dealloc_prep (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap : cap ≠ 0) (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗
      (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
    A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  simp only [hcap, ↓reduceIte]
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)) ?_
  rw [← memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega),
      Nat.add_sub_of_le hle]
  exact Entails.refl _

theorem sepWPp_to_steps_or_panic {prog : Program} (ret : BitVec 64) {s : State}
    {P R : SepProp} {Goal : State → Prop} {OnPanic : State → SepProp}
    (hm : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hwp : SepWPp prog ret s P
      (fun sf P_f => sf.pc = ret → sf.status = .Running → (sf.mem ⊨ P_f ∗ R) → Goal sf)
      (fun sf P_f => sf.status = .Panicked → (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ OnPanic sf ∗ R))) :
    ∃ s', Steps prog s s' ∧
      (Goal s' ∨ (s'.status = .Panicked ∧ (s'.mem ⊨ OnPanic s' ∗ R))) := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, Or.inl (hq hpc hrun hmf)⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan, hqp hpan hmf⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem SepWPp.call_frame_frozen {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R',
      sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  exact ProofLib.SepWPp.call_frame_frozen hcall hF hsym hpc hrun hsp hlr hspec hφ hP hexit hpanic
    (fun sf hpcm hrunm hspm hcsm hFm hsymm =>
      hnext sf hpcm hrunm hspm (by simpa [State.spAligned, hspm] using hsp) hcsm hFm hsymm)
    hoom

theorem SepWPp.call_inImage_frame {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R',
      sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  exact ProofLib.SepWPp.call_inImage_frame hcall hF hsym hpc hrun hsp hlr hspec hφ hP hexit hpanic
    (fun sf hpcm hrunm hspm hcsm hFm hsymm =>
      hnext sf hpcm hrunm hspm (by simpa [State.spAligned, hspm] using hsp) hcsm hFm hsymm)
    hoom

theorem SepWPp.mono_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : P ⊢ P') (hwp : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  exact SepWPp.weaken_pre h hwp

theorem SepWPp.elim_pure {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem SepWPp.elim_exists {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (Φ a ∗ P) Q Qp) :
    SepWPp prog ret s ((∃∗ a, Φ a) ∗ P) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hm⟩
  exact h a R hm hL

theorem SepWPp.elim_pure_focus {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P = (⌜φ⌝ ∗ Rest))
    (h : φ → SepWPp prog ret s Rest Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hfoc]
  exact SepWPp.elim_pure h

theorem SepWPp.elim_exists_focus {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P = ((∃∗ p, Φ p) ∗ Rest))
    (h : ∀ p, SepWPp prog ret s (Φ p ∗ Rest) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hfoc]
  exact SepWPp.elim_exists h

theorem SepWPp.elim_vecU8_focus {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {a : BitVec 64} {bs : List (BitVec 8)} {P Rest : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfoc : P = (vecU8 A a bs ∗ Rest))
    (h : ∀ cap ptr : BitVec 64,
      bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 →
      SepWPp prog ret s
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗ Rest) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hfoc]
  unfold vecU8
  apply SepWPp.elim_exists; intro cap
  apply SepWPp.elim_exists; intro ptr
  unfold vecU8At vecHeader
  rw [← sepConj_assoc,
      sepConj_comm ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)),
      sepConj_assoc, sepConj_assoc, sepConj_assoc]
  apply SepWPp.elim_pure; rintro ⟨hle, hlt, hnz⟩
  simp only [sepConj_assoc]
  exact h cap ptr hle hlt hnz

/-! ## 3. Segment 8 (`+0x678 → +0x6a4 / +0x30c`) -/

theorem signalMessageAt_ct_lt {A : RustAlloc} {g : SignalMessageGhost} {a : BitVec 64}
    {msg : SignalMessage} {R : SepProp} {m : Memory}
    (h : m ⊨ signalMessageAt A g a msg ∗ R) : msg.ciphertext.length < 2 ^ 40 := by
  unfold signalMessageAt at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.2.1

elab "sep_close" : tactic => do
  SepSolver.closeSat (SepSolver.tacDisch
    (← `(tactic| first | rfl | assumption | (bv_omega_fast; done))))

theorem s8_scr_split (sp : BitVec 64) :
    memRegion (sp + 0x140#64) 0x3c0 =
      (memRegion (sp + 0x140#64) 0x290 ∗ memRegion (sp + 0x3d0#64) 24 ∗
       memRegion (sp + 0x3e8#64) 0x118) := by
  rw [show (0x3c0 : Nat) = 0x290 + (24 + 0x118) by decide,
      memRegion_split (sp + 0x140#64) 0x290 (24 + 0x118) (by decide),
      show sp + 0x140#64 + BitVec.ofNat 64 0x290 = sp + 0x3d0#64 by bv_omega,
      memRegion_split (sp + 0x3d0#64) 24 0x118 (by decide),
      show sp + 0x3d0#64 + BitVec.ofNat 64 24 = sp + 0x3e8#64 by bv_omega]

theorem s9_reg10_split (sp : BitVec 64) :
    memRegion (sp + 0x10#64) 0x18 =
      (memRegion (sp + 0x10#64) 0xc ∗ memRegion (sp + 0x1c#64) 4 ∗ memRegion (sp + 0x20#64) 8) := by
  rw [show (0x18 : Nat) = 0xc + (4 + 8) by decide,
      memRegion_split (sp + 0x10#64) 0xc (4 + 8) (by decide),
      show sp + 0x10#64 + BitVec.ofNat 64 0xc = sp + 0x1c#64 by bv_omega,
      memRegion_split (sp + 0x1c#64) 4 8 (by decide),
      show sp + 0x1c#64 + BitVec.ofNat 64 4 = sp + 0x20#64 by bv_omega]

theorem s9_reg3e8_split (sp : BitVec 64) :
    memRegion (sp + 0x3e8#64) 0x198 =
      (memRegion (sp + 0x3e8#64) 0x118 ∗ memRegion (sp + 0x500#64) 0x54 ∗
        memRegion (sp + 0x554#64) 0x2c) := by
  rw [show (0x198 : Nat) = 0x118 + (0x54 + 0x2c) by decide,
      memRegion_split (sp + 0x3e8#64) 0x118 (0x54 + 0x2c) (by decide),
      show sp + 0x3e8#64 + BitVec.ofNat 64 0x118 = sp + 0x500#64 by bv_omega,
      memRegion_split (sp + 0x500#64) 0x54 0x2c (by decide),
      show sp + 0x500#64 + BitVec.ofNat 64 0x54 = sp + 0x554#64 by bv_omega]

theorem Satisfies.mono_focus {A B P Rest : SepProp} {m : Memory}
    (hAB : A ⊢ B) (hfoc : P = A ∗ Rest) (hm : m ⊨ P) :
    m ⊨ B ∗ Rest := by
  rw [hfoc] at hm
  exact Satisfies.mono (sepConj_mono_left hAB) hm

theorem SepWPp.mono_focus {prog : Program} {ret : BitVec 64} {s : State}
    {A B P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hAB : A ⊢ B) (hfoc : P = A ∗ Rest)
    (hwp : SepWPp prog ret s (B ∗ Rest) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hfoc]
  exact SepWPp.mono_pre (sepConj_mono_left hAB) hwp

theorem vecU8At_parts_entails_vecU8 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hnz : ptr ≠ 0) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
    vecU8 A a bs := by
  unfold vecU8
  refine Entails.trans ?_ (Entails.sepExists_intro cap)
  refine Entails.trans ?_ (Entails.sepExists_intro ptr)
  unfold vecU8At vecHeader
  rw [← sepConj_assoc,
      sepConj_comm ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)),
      sepConj_assoc, sepConj_assoc]
  exact Entails.pure_right
    (⟨hle, hlt, hnz⟩ : bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0)
    (Entails.of_eq (by ac_rfl))

theorem mks_parts_entails_memRegion (sp : BitVec 64) (mks : MessageKeys) :
    ((sp - 224#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
    ((sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
    ((sp - 160#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
    ((sp - 144#64) ↦₃₂ mks.counter) ⊢
    memRegion (sp - 1504#64 + 0x500#64) 0x54 := by
  rw [show sp - 224#64 = sp - 1504#64 + 0x500#64 by bv_omega,
      show sp - 192#64 = sp - 1504#64 + 0x520#64 by bv_omega,
      show sp - 160#64 = sp - 1504#64 + 0x540#64 by bv_omega,
      show sp - 144#64 = sp - 1504#64 + 0x550#64 by bv_omega,
      ← messageKeysAt_eq]
  exact messageKeysAt_entails_memRegion _ _

theorem s9_sp_entails_memRegion (sp : BitVec 64) (msgW : BitVec 32) (locA remA : BitVec 64) :
    ((sp - 1476#64) ↦₃₂ msgW) ∗
    ((sp - 1472#64) ↦₆₄ locA) ∗
    ((sp - 1456#64) ↦₆₄ remA) ⊢
    memRegion (sp - 1476#64) 4 ∗
    memRegion (sp - 1472#64) 8 ∗
    memRegion (sp - 1456#64) 8 :=
  sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

theorem errTail_sp_entails_memRegion (sp : BitVec 64)
    (newPqrCap locA newPqrPtr remA v1104 v1096 v528 v520 v512 v480 v472 : BitVec 64)
    (msgW : BitVec 32) :
    ((sp - 1496#64) ↦₆₄ newPqrCap) ∗
    ((sp - 1476#64) ↦₃₂ msgW) ∗
    ((sp - 1472#64) ↦₆₄ locA) ∗
    ((sp - 1464#64) ↦₆₄ newPqrPtr) ∗
    ((sp - 1456#64) ↦₆₄ remA) ∗
    ((sp - 1104#64) ↦₆₄ v1104) ∗
    ((sp - 1096#64) ↦₆₄ v1096) ∗
    ((sp - 528#64) ↦₆₄ v528) ∗
    ((sp - 520#64) ↦₆₄ v520) ∗
    ((sp - 512#64) ↦₆₄ v512) ∗
    ((sp - 480#64) ↦₆₄ v480) ∗
    ((sp - 472#64) ↦₆₄ v472) ⊢
    memRegion (sp - 1496#64) 8 ∗
    memRegion (sp - 1476#64) 4 ∗
    memRegion (sp - 1472#64) 8 ∗
    memRegion (sp - 1464#64) 8 ∗
    memRegion (sp - 1456#64) 8 ∗
    memRegion (sp - 1104#64) 8 ∗
    memRegion (sp - 1096#64) 8 ∗
    memRegion (sp - 528#64) 8 ∗
    memRegion (sp - 520#64) 8 ∗
    memRegion (sp - 512#64) 8 ∗
    memRegion (sp - 480#64) 8 ∗
    memRegion (sp - 472#64) 8 :=
  sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (pointsTo64_entails_memRegion _ _)))))))))))

theorem s8_none_scr_split (sp : BitVec 64) :
    memRegion (sp - 1184#64) 656 =
      (memRegion (sp - 1184#64) 40 ∗ memRegion (sp - 1144#64) 24 ∗
       memRegion (sp - 1120#64) 1 ∗ memRegion (sp - 1119#64) 15 ∗
       memRegion (sp - 1104#64) 8 ∗ memRegion (sp - 1096#64) 8 ∗
       memRegion (sp - 1088#64) 560) := by
  rw [show (656 : Nat) = 40 + (24 + (1 + (15 + (8 + (8 + 560))))) by decide,
      memRegion_split (sp - 1184#64) 40 _ (by decide),
      show sp - 1184#64 + BitVec.ofNat 64 40 = sp - 1144#64 by bv_omega,
      memRegion_split (sp - 1144#64) 24 _ (by decide),
      show sp - 1144#64 + BitVec.ofNat 64 24 = sp - 1120#64 by bv_omega,
      memRegion_split (sp - 1120#64) 1 _ (by decide),
      show sp - 1120#64 + BitVec.ofNat 64 1 = sp - 1119#64 by bv_omega,
      memRegion_split (sp - 1119#64) 15 _ (by decide),
      show sp - 1119#64 + BitVec.ofNat 64 15 = sp - 1104#64 by bv_omega,
      memRegion_split (sp - 1104#64) 8 _ (by decide),
      show sp - 1104#64 + BitVec.ofNat 64 8 = sp - 1096#64 by bv_omega,
      memRegion_split (sp - 1096#64) 8 560 (by decide),
      show sp - 1096#64 + BitVec.ofNat 64 8 = sp - 1088#64 by bv_omega]

theorem s8_none_reg504_split (sp : BitVec 64) :
    memRegion (sp - 504#64) 280 =
      (memRegion (sp - 504#64) 24 ∗ memRegion (sp - 480#64) 8 ∗
       memRegion (sp - 472#64) 8 ∗ memRegion (sp - 464#64) 240) := by
  rw [show (280 : Nat) = 24 + (8 + (8 + 240)) by decide,
      memRegion_split (sp - 504#64) 24 _ (by decide),
      show sp - 504#64 + BitVec.ofNat 64 24 = sp - 480#64 by bv_omega,
      memRegion_split (sp - 480#64) 8 _ (by decide),
      show sp - 480#64 + BitVec.ofNat 64 8 = sp - 472#64 by bv_omega,
      memRegion_split (sp - 472#64) 8 240 (by decide),
      show sp - 472#64 + BitVec.ofNat 64 8 = sp - 464#64 by bv_omega]

theorem s8_none_prep (sp : BitVec 64) :
    memRegion (sp - 1184#64) 656 ∗ memRegion (sp - 504#64) 280 ⊢
      (memRegion (sp - 1184#64) 40 ∗ memRegion (sp - 1144#64) 24 ∗
       memRegion (sp - 1120#64) 1 ∗ memRegion (sp - 1119#64) 15 ∗
       memRegion (sp - 1104#64) 8 ∗ memRegion (sp - 1096#64) 8 ∗
       memRegion (sp - 1088#64) 560) ∗
      (memRegion (sp - 504#64) 24 ∗ memRegion (sp - 480#64) 8 ∗
       memRegion (sp - 472#64) 8 ∗ memRegion (sp - 464#64) 240) := by
  rw [← s8_none_scr_split sp, ← s8_none_reg504_split sp]
  exact Entails.refl _

theorem SepWPp.elim_memRegion8_focus {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P = (memRegion a 8 ∗ Rest))
    (h : ∀ v : BitVec 64, SepWPp prog ret s ((a ↦₆₄ v) ∗ Rest) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hfoc, memRegion_eight]
  exact SepWPp.elim_exists h

theorem SepWPp.elim_memRegion1_focus {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P = (memRegion a 1 ∗ Rest))
    (h : ∀ v : BitVec 8, SepWPp prog ret s ((a ↦₈ v) ∗ Rest) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hfoc, memRegion_one]
  exact SepWPp.elim_exists h

theorem SepWP.setPC_ite_false {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {c : Prop} [inst : Decidable c] {pc1 pc2 : BitVec 64} (hnc : ¬ c)
    (helse : SepWP prog target_pc (s.setPC pc2) P post) :
    SepWP prog target_pc (s.setPC (@ite _ c inst pc1 pc2)) P post := by
  rw [ite_eq_right_iff.mpr fun hc => (hnc hc).elim]; exact helse

theorem SepWP.setPC_ite_true {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {c : Prop} [inst : Decidable c] {pc1 pc2 : BitVec 64} (hc : c)
    (hthen : SepWP prog target_pc (s.setPC pc1) P post) :
    SepWP prog target_pc (s.setPC (@ite _ c inst pc1 pc2)) P post := by
  rw [ite_eq_left_iff.mpr fun hnc => (hnc hc).elim]; exact hthen

theorem errTail_sp_split (sp : BitVec 64) :
    memRegion (sp - 1504#64) 0x38 =
      (memRegion (sp - 1504#64) 8 ∗ memRegion (sp - 1496#64) 8 ∗
       memRegion (sp - 1488#64) 12 ∗ memRegion (sp - 1476#64) 4 ∗
       memRegion (sp - 1472#64) 8 ∗ memRegion (sp - 1464#64) 8 ∗
       memRegion (sp - 1456#64) 8) := by
  rw [show (0x38 : Nat) = 8 + (8 + (12 + (4 + (8 + (8 + 8))))) by decide,
      memRegion_split (sp - 1504#64) 8 _ (by decide),
      show sp - 1504#64 + BitVec.ofNat 64 8 = sp - 1496#64 by bv_omega,
      memRegion_split (sp - 1496#64) 8 _ (by decide),
      show sp - 1496#64 + BitVec.ofNat 64 8 = sp - 1488#64 by bv_omega,
      memRegion_split (sp - 1488#64) 12 _ (by decide),
      show sp - 1488#64 + BitVec.ofNat 64 12 = sp - 1476#64 by bv_omega,
      memRegion_split (sp - 1476#64) 4 _ (by decide),
      show sp - 1476#64 + BitVec.ofNat 64 4 = sp - 1472#64 by bv_omega,
      memRegion_split (sp - 1472#64) 8 _ (by decide),
      show sp - 1472#64 + BitVec.ofNat 64 8 = sp - 1464#64 by bv_omega,
      memRegion_split (sp - 1464#64) 8 8 (by decide),
      show sp - 1464#64 + BitVec.ofNat 64 8 = sp - 1456#64 by bv_omega]

theorem errTail_reg190_split (sp : BitVec 64) :
    memRegion (sp - 1504#64 + 0x190#64) 0x3f0 =
      (memRegion (sp - 1104#64) 8 ∗ memRegion (sp - 1096#64) 8 ∗
       memRegion (sp - 1088#64) 560 ∗ memRegion (sp - 528#64) 8 ∗
       memRegion (sp - 520#64) 8 ∗ memRegion (sp - 512#64) 8 ∗
       memRegion (sp - 504#64) 24 ∗ memRegion (sp - 480#64) 8 ∗
       memRegion (sp - 472#64) 8 ∗ memRegion (sp - 464#64) 240 ∗
       memRegion (sp - 1504#64 + 0x500#64) 0x54 ∗
       memRegion (sp - 1504#64 + 0x554#64) 0x2c) := by
  rw [show sp - 1504#64 + 0x190#64 = sp - 1104#64 by bv_omega,
      show (0x3f0 : Nat)
        = 8 + (8 + (560 + (8 + (8 + (8 + (24 + (8 + (8 + (240 + (0x54 + 0x2c)))))))))) by decide,
      memRegion_split (sp - 1104#64) 8 _ (by decide),
      show sp - 1104#64 + BitVec.ofNat 64 8 = sp - 1096#64 by bv_omega,
      memRegion_split (sp - 1096#64) 8 _ (by decide),
      show sp - 1096#64 + BitVec.ofNat 64 8 = sp - 1088#64 by bv_omega,
      memRegion_split (sp - 1088#64) 560 _ (by decide),
      show sp - 1088#64 + BitVec.ofNat 64 560 = sp - 528#64 by bv_omega,
      memRegion_split (sp - 528#64) 8 _ (by decide),
      show sp - 528#64 + BitVec.ofNat 64 8 = sp - 520#64 by bv_omega,
      memRegion_split (sp - 520#64) 8 _ (by decide),
      show sp - 520#64 + BitVec.ofNat 64 8 = sp - 512#64 by bv_omega,
      memRegion_split (sp - 512#64) 8 _ (by decide),
      show sp - 512#64 + BitVec.ofNat 64 8 = sp - 504#64 by bv_omega,
      memRegion_split (sp - 504#64) 24 _ (by decide),
      show sp - 504#64 + BitVec.ofNat 64 24 = sp - 480#64 by bv_omega,
      memRegion_split (sp - 480#64) 8 _ (by decide),
      show sp - 480#64 + BitVec.ofNat 64 8 = sp - 472#64 by bv_omega,
      memRegion_split (sp - 472#64) 8 _ (by decide),
      show sp - 472#64 + BitVec.ofNat 64 8 = sp - 464#64 by bv_omega,
      memRegion_split (sp - 464#64) 240 _ (by decide),
      show sp - 464#64 + BitVec.ofNat 64 240 = sp - 1504#64 + 0x500#64 by bv_omega,
      memRegion_split (sp - 1504#64 + 0x500#64) 0x54 0x2c (by decide),
      show sp - 1504#64 + 0x500#64 + BitVec.ofNat 64 0x54 = sp - 1504#64 + 0x554#64 by bv_omega]

theorem formatInner_post_eq_badCiphertext (A : RustAlloc) (sp : BitVec 64) :
    (∃∗ bs : List (BitVec 8), vecU8 A (sp - 1144#64) bs) =
      invalidMessageStrAt A (sp - 1504#64 + 0x168#64) .badCiphertext := by
  unfold invalidMessageStrAt
  rw [show sp - 1504#64 + 0x168#64 = sp - 1144#64 by bv_omega]

theorem newPqr_zero_prep (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap : cap = 0) :
    (if cap = 0 then emp else (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs)) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢ emp := by
  simp only [hcap, ↓reduceIte]; exact Entails.refl _

theorem newPqr_dealloc_prep' (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap : cap ≠ 0) (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    (if cap = 0 then emp else (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs)) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
    A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  simp only [sepConj_assoc]
  exact newPqr_dealloc_prep A cap ptr bs hcap hle hlt

theorem vecU8At_parts_entails_vecU8' (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hnz : ptr ≠ 0) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    (if cap = 0 then emp else (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs)) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
    vecU8 A a bs := by
  simp only [sepConj_assoc]
  exact vecU8At_parts_entails_vecU8 A a cap ptr bs hle hlt hnz

theorem stackAt_ext_split_alloc (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12288 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp 4096 12288 (by decide)

theorem noPanic_callee {F R Q : SepProp} {m : Memory}
    (hm : m ⊨ (⌜False⌝ ∗ F) ∗ R) : m ⊨ Q := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm.1.elim

theorem noExit_callee {F R : SepProp} {m : Memory}
    (hm : m ⊨ ⌜False⌝ ∗ F ∗ R) : False := by
  rw [satisfies_pure_sepConj] at hm
  exact hm.1

theorem writeReg64_trace (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := rfl
theorem writeReg32_trace (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := rfl
theorem setPC_trace (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := rfl
theorem setPState_trace (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := rfl
theorem setMem_trace (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := rfl

theorem boxU8At_msg_ct (A : RustAlloc) (a p : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A (a + 0x18#64) p bs =
      (((a + 0x18#64) ↦₆₄ p) ∗ ((a + 0x20#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
       (p ↦ₛ bs) ∗ boxU8Rest A p bs) := by
  rw [boxU8At_eq_rest, show a + 0x18#64 + 8#64 = a + 0x20#64 by bv_omega]

theorem pointsTo8_msgType_eq (sp : BitVec 64) (msgW : BitVec 32) (t : MessageType)
    (hmsgW : msgW.setWidth 8 = msgTypeByte t) :
    ((sp - 1120#64) ↦₈ msgW.setWidth 8) =
      ((sp - 1504#64 + 0x168#64 + 24#64) ↦₈ msgTypeByte t) := by
  rw [hmsgW, show sp - 1504#64 + 0x168#64 + 24#64 = sp - 1120#64 by bv_omega]

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD
