/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.Defs
public import LibsignalBinary.Proofs.SpqrV1.Kdf.KdfCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Chain.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.Auth.SpqrAuthCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::kdf::hkdf_to_vec`

Separation-logic specifications and proofs for `spqr::kdf::hkdf_to_vec` (`0x631c8`, Block `378`),
which zero-allocates a `Vec<u8>` output buffer and tail-calls `spqr::kdf::hkdf_to_slice`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.SpqrV1.Layout.L3
open Lean Elab Command Tactic ProofLib ProofLib.CodeLookup CryptoVerification.CodeLayout in
elab "gen_decodes_len " tree:ident pfx:ident sym:str len:num : command => do
  let off ← liftTermElabM do
    let cn ← realizeGlobalConstNoOverloadWithInfo pfx
    return (← lookup cn .fnOff sym.getString).val
  let a := Syntax.mkNumLit (toString off)
  let b := Syntax.mkNumLit (toString (off + len.getNat - 4))
  elabCommand (← `(private gen_decodes $tree $pfx [$a:num → $b:num]))

open Lean Elab Tactic ProofLib ProofLib.CodeLookup in
elab "code_fetches_len " codeId:ident decPrefix:ident b:term:max H:term:max sym:str len:num : tactic => do
  let codeName ← realizeGlobalConstNoOverloadWithInfo codeId
  let eOff ← lookup codeName .fnOff sym.getString
  let hfn := mkCIdentFrom sym eOff.decl
  let offStx := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic| code_fetches $codeId $decPrefix $b $H $hfn $offStx $len))
end CryptoVerification.SpqrV1.Layout.L3

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Layout.L3

export CryptoVerification.SpqrV1.ChainProofs
  (hkdfToSliceSpqrSpec HkdfToSliceSpqrOkX
   hkdfToSliceStackExt hkdfToSliceSpecExt hkdfToSliceSpqrSpecExt
   HkdfToSliceSpqrOkExt HkdfToSliceOkExt)

structure HkdfToVecGhost where
  outVec : BitVec 64
  saltRO : Bool
  saltA : BitVec 64
  salt : List (BitVec 8)
  ikmRO : Bool
  ikmA : BitVec 64
  ikm : List (BitVec 8)
  infoRO : Bool
  infoA : BitVec 64
  info : List (BitVec 8)
  okmLen : Nat

/-- Separation-logic specification of `spqr::kdf::hkdf_to_vec` (`0x631c8`, 47 instructions) for
    `okmLen ∈ {32, 64, 96}` and `32 ≤ info.length < 55`: takes `outVec` in `x8` and `(salt, ikm, info, okmLen)`
    in `x0..x6`, writing `hkdf salt ikm info okmLen` as a `Vec<u8>` at `outVec` or panicking on OOM. -/
def hkdfToVecSpec (A : RustAlloc) (hkdf : HkdfFn) : Spec HkdfToVecGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outVec ∧
      s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
      s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
      s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
      s.readReg64 .x6 = BitVec.ofNat 64 x.okmLen ∧
      x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
      32 ≤ x.info.length ∧ x.info.length < 55 ∧
      (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96)⌝ ∗
      memRegion x.outVec 24 ∗
      bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      A.pool ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜(hkdf x.salt x.ikm x.info x.okmLen).length = x.okmLen ∧ sf.trace = s0.trace⌝ ∗
      vecU8 A x.outVec (hkdf x.salt x.ikm x.info x.okmLen) ∗
      bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev hkdfToVecSpqrSpec (A : RustAlloc) (hkdf : HkdfFn) : Spec HkdfToVecGhost :=
  hkdfToVecSpec A hkdf

/-- `spqr::kdf::hkdf_to_vec` meets `(hkdfToVecSpec A hkdf).inImage img` on
`tripleRatchetProgAtExt img.base ext`. -/
def HkdfToVecOkX (img : Obj.Image) (A : RustAlloc) (hkdf : HkdfFn)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToVecName)
    ((hkdfToVecSpec A hkdf).inImage img)

abbrev HkdfToVecSpqrOkX (img : Obj.Image) (A : RustAlloc) (hkdf : HkdfFn)
    (ext : String → Option (State → State)) : Prop :=
  HkdfToVecOkX img A hkdf ext

/-- Stack budget (in bytes) required by `spqr::kdf::hkdf_to_vec` under `CliExternsOk`:
96-byte prologue frame (`sp - 96`) plus `hkdfToSliceStackExt = 17616` (`17712` B total). -/
abbrev hkdfToVecStackExt : Nat := 96 + hkdfToSliceStackExt

/-- Contract-parameterized (`CliExternsOk`) SL specification of `spqr::kdf::hkdf_to_vec`
(`0x631c8`, 47 instructions): threads `(¬x.saltRO ∨ x.salt.length ≤ 64) ∧ (¬x.ikmRO ∨ x.ikm.length < 64)`
and `hkdfToVecStackExt` (`17712` B) to the tail-called `spqr::kdf::hkdf_to_slice`. -/
def hkdfToVecSpecExt (A : RustAlloc) (hkdf : HkdfFn) : Spec HkdfToVecGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outVec ∧
      s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
      s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
      s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
      s.readReg64 .x6 = BitVec.ofNat 64 x.okmLen ∧
      x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
      (¬x.saltRO ∨ x.salt.length ≤ 64) ∧
      (¬x.ikmRO ∨ x.ikm.length < 64) ∧
      32 ≤ x.info.length ∧ x.info.length < 55 ∧
      (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96)⌝ ∗
      memRegion x.outVec 24 ∗
      bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      A.pool ∗ stackAt s.sp hkdfToVecStackExt
  post := fun x s0 sf =>
    ⌜(hkdf x.salt x.ikm x.info x.okmLen).length = x.okmLen ∧ sf.trace = s0.trace⌝ ∗
      vecU8 A x.outVec (hkdf x.salt x.ikm x.info x.okmLen) ∗
      bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      A.pool ∗ stackAt s0.sp hkdfToVecStackExt
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev hkdfToVecSpqrSpecExt (A : RustAlloc) (hkdf : HkdfFn) : Spec HkdfToVecGhost :=
  hkdfToVecSpecExt A hkdf

/-- `spqr::kdf::hkdf_to_vec` meets `(hkdfToVecSpecExt A hkdf).inImage img` on
`tripleRatchetProgAtExt img.base ext`. -/
def HkdfToVecOkExt (img : Obj.Image) (A : RustAlloc) (hkdf : HkdfFn)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToVecName)
    ((hkdfToVecSpecExt A hkdf).inImage img)

abbrev HkdfToVecSpqrOkExt (img : Obj.Image) (A : RustAlloc) (hkdf : HkdfFn)
    (ext : String → Option (State → State)) : Prop :=
  HkdfToVecOkExt img A hkdf ext

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::kdf::hkdf_to_vec")
  (ls_lemma% fnOff "spqr::kdf::hkdf_to_slice")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "alloc::raw_vec::handle_error")

gen_decodes_len libsignalSessionCode_tree libsignalSessionCode "spqr::kdf::hkdf_to_vec" 188

private theorem memRegion_zero (a : BitVec 64) : memRegion a 0 = emp := by
  have hb := IsBlock.pointsToBytes a []
  rw [pointsToBytes_nil] at hb
  exact IsBlock.eq (IsBlock.memRegion a 0) hb
    fun _ => ⟨fun _ => ⟨by simp, by simp⟩, fun _ => trivial⟩

private theorem memRegion_eight (a : BitVec 64) : memRegion a 8 = ∃∗ v, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

private theorem memRegion_cells (a : BitVec 64) (k : Nat) (h : 8 * k ≤ 2 ^ 64) :
    memRegion a (8 * k) = cells a k := by
  induction k generalizing a with
  | zero => exact memRegion_zero a
  | succ k ih =>
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, memRegion_split a 8 (8 * k) (by omega),
      memRegion_eight, ih _ (by omega), cells_succ, sepExists_sepConj_left]

private theorem stackAt_split_cells (sp : BitVec 64) (n k : Nat) (h : n + 8 * k ≤ 2 ^ 64) :
    stackAt sp (n + 8 * k) =
      stackAt (sp - BitVec.ofNat 64 (8 * k)) n ∗ cells (sp - BitVec.ofNat 64 (8 * k)) k := by
  simp only [stackAt]
  rw [memRegion_split _ n (8 * k) h, memRegion_cells _ k (by omega)]
  generalize hj : 8 * k = j at *
  have e1 : sp - BitVec.ofNat 64 (n + j) = sp - BitVec.ofNat 64 j - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + j) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 j := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

private theorem stackAt_hkdfToVec (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12192 ∗
        stackAt (sp - 96#64) allocHookStack ∗
        cells (sp - 96#64) 12 := by
  have h1 : stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12192 ∗ stackAt sp (allocHookStack + 96) :=
    ProofLib.stackAt_split_bottom sp (allocHookStack + 96) 12192 (by decide)
  have h2 : stackAt sp (allocHookStack + 96) =
      stackAt (sp - 96#64) allocHookStack ∗ cells (sp - 96#64) 12 :=
    stackAt_split_cells sp 4096 12 (by decide)
  rw [h1, h2]

private theorem stackAt_hkdfToVec_fold (sp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    memRegion (sp - 16384#64) 12192 ∗
      stackAt (sp - 96#64) allocHookStack ∗
      ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
      ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
      ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗
      ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11) ⊢
      stackAt sp extHookStack := by
  rw [stackAt_hkdfToVec sp]
  cells_unfold
  refine Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
        (Entails.sepExists_right v9 (Entails.sepExists_right v10
          (Entails.sepExists_right v11 (Entails.refl _))))))))))))

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
        (a ↦₆₄ u2) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 16 (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem allocFailedIn_of_eq {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem zeroed_entails_memRegion (ptr : BitVec 64) (n : Nat) :
    (ptr ↦ₛ List.replicate n 0#8) ⊢ memRegion ptr n := by
  have h := pointsToBytes_entails_memRegion ptr (List.replicate n 0#8)
  rwa [List.length_replicate] at h

private theorem vecU8_exact_entails (A : RustAlloc) (v ptr : BitVec 64) (bs : List (BitVec 8))
    (n : Nat) (hpos : 0 < n) (hle : n ≤ 8160) (hlen : bs.length = n) (hptr : ptr ≠ 0) :
    (v ↦₆₄ BitVec.ofNat 64 n) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      A.live ptr n 1 ∗ (ptr ↦ₛ bs) ⊢
      vecU8 A v bs := by
  unfold vecU8
  refine Entails.sepExists_right (BitVec.ofNat 64 n) (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader
  have hcap_toNat : (BitVec.ofNat 64 n).toNat = n :=
    Nat.mod_eq_of_lt (by omega)
  have hcap_ne : BitVec.ofNat 64 n ≠ 0 := by
    intro h0
    have := congrArg BitVec.toNat h0
    rw [hcap_toNat] at this
    change n = 0 at this
    omega
  simp only [hlen, hcap_ne, ↓reduceIte, hcap_toNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  rw [show (v ↦₆₄ BitVec.ofNat 64 n ∗ (v + 8#64) ↦₆₄ ptr ∗ (v + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      ⌜n ≤ n ∧ n < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ A.live ptr n 1 ∗ (ptr ↦ₛ bs) =
    ⌜n ≤ n ∧ n < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ BitVec.ofNat 64 n) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        A.live ptr n 1 ∗ (ptr ↦ₛ bs)) by ac_rfl]
  exact Entails.pure_right ⟨Nat.le_refl n, by omega, hptr⟩ (Entails.refl _)

private theorem okmLen_toNat {n : Nat} (hle : n ≤ 8160) :
    (BitVec.ofNat 64 n).toNat = n :=
  Nat.mod_eq_of_lt (by omega)

private theorem okmLen_getLsbD_63 {n : Nat} (hle : n ≤ 8160) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide)]
  change (BitVec.ofNat 64 n)[63] = false
  rw [BitVec.getElem_eq_testBit_toNat, okmLen_toNat hle]
  exact Nat.testBit_lt_two_pow (by omega)

private theorem okmLen_ne_zero {n : Nat} (hpos : 0 < n) (hle : n ≤ 8160) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [okmLen_toNat hle] at this
  change n = 0 at this
  omega

private theorem okmLen_beq_zero {n : Nat} (hpos : 0 < n) (hle : n ≤ 8160) :
    (BitVec.ofNat 64 n == 0#64) = false :=
  beq_false_of_ne (okmLen_ne_zero hpos hle)

private theorem layoutOk_okmLen {n : Nat} (hpos : 0 < n) (hle : n ≤ 8160) :
    LayoutOk n 1 :=
  ⟨hpos, ⟨0, rfl⟩, by omega⟩

/-! ## Proof of `spqr::kdf::hkdf_to_vec` (`0x631c8`, 47 instructions) -/

private theorem of_sepWP_inImage {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} (img : Obj.Image)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hsteps.frozenLoaded hfl) (hsteps.symtab_eq.trans hsym) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim

/-- `spqr::kdf::hkdf_to_vec` (`0x631c8`, 47 instructions) meets `(hkdfToVecSpec A hkdf).inImage img`
    on `tripleRatchetProgAtExt img.base ext`. -/
theorem hkdf_to_vec_ok_ext (img : Obj.Image) (A : RustAlloc) (hkdf : HkdfFn)
    (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hSlice : HkdfToSliceSpqrOkX img hkdf ext) :
    HkdfToVecOkX img A hkdf ext := by
  unfold HkdfToVecOkX
  have hspec_eq : (hkdfToVecSpec A hkdf).inImage img = {
    pre := fun x s =>
      ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      ⌜s.readReg64 .x8 = x.outVec ∧
        s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
        s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
        s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
        s.readReg64 .x6 = BitVec.ofNat 64 x.okmLen ∧
        x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
        32 ≤ x.info.length ∧ x.info.length < 55 ∧
        (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96)⌝ ∗
        memRegion x.outVec 24 ∗
        bytesAt x.saltRO x.saltA x.salt ∗
        bytesAt x.ikmRO x.ikmA x.ikm ∗
        bytesAt x.infoRO x.infoA x.info ∗
        A.pool ∗
        memRegion (s.sp - 16384#64) 12192 ∗
        stackAt (s.sp - 96#64) allocHookStack ∗
        cells (s.sp - 96#64) 12
    post := (hkdfToVecSpec A hkdf).post
    onPanic := (hkdfToVecSpec A hkdf).onPanic
  } := by
    simp only [hkdfToVecSpec, Spec.inImage, stackAt_hkdfToVec, sepConj_assoc]
  rw [hspec_eq]
  clear hspec_eq
  simp only [hkdfToVecSpec, memRegion_24_cells]
  cells_unfold
  have hshim := hA.shim_ok_at hkdfToVecName
    (ls_rel% "spqr::kdf::hkdf_to_vec" "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  have halloc := alloc_zeroed_ok_at_ext img.base A ext hZero hkdfToVecName
    (ls_rel% "spqr::kdf::hkdf_to_vec" "__rustc::__rust_alloc_zeroed")
  have hpanic := panic_at_handle_error_ext img.base ext hkdfToVecName
    (ls_rel% "spqr::kdf::hkdf_to_vec" "alloc::raw_vec::handle_error")
  have hslice_at := sub_ok_at_of_fnAddr hSlice hkdfToVecName
    (ls_rel% "spqr::kdf::hkdf_to_vec" "spqr::kdf::hkdf_to_slice")
  simp only [hkdfToSliceSpqrSpec, hkdfToSliceSpec] at hslice_at
  clear hA hZero hSlice
  wpp_init x s0
  code_fetches_len CryptoVerification.libsignalSessionCode
    libsignalSessionCode img.base (Rust.withPanics ext) "spqr::kdf::hkdf_to_vec" 188
  have hpc' : s0.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr hkdfToVecName := by
    rw [hpc, Program.fnAddr_rebase]; simp [hkdfToVecName]
  clear hpc
  rename_i hpc
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic hslice_at ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr hkdfToVecName = entry
  examples_hide_fetches
  obtain ⟨outVec, saltRO, saltA, salt, ikmRO, ikmA, ikm, infoRO, infoA, info, okmLen⟩ := x
  dsimp only at *
  have hokm_pos : 0 < okmLen := by
    have := ‹okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96›; omega
  have hokm_le : okmLen ≤ 8160 := by
    have := ‹okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96›; omega
  have htoNat : (BitVec.ofNat 64 okmLen).toNat = okmLen := okmLen_toNat hokm_le
  have hlsb63 : (BitVec.ofNat 64 okmLen).getLsbD 63 = false := okmLen_getLsbD_63 hokm_le
  have hne0 : BitVec.ofNat 64 okmLen ≠ 0#64 := okmLen_ne_zero hokm_pos hokm_le
  have hbeq0 : (BitVec.ofNat 64 okmLen == 0#64) = false := okmLen_beq_zero hokm_pos hokm_le
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk okmLen 1 := layoutOk_okmLen hokm_pos hokm_le
  apply of_sepWP_inImage (mid := entry + 104#64) img ‹img.FrozenLoaded s0› ‹s0.symtab = img.symtab›
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hfl_1 hsym_1
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_rel% "spqr::kdf::hkdf_to_vec" "alloc::raw_vec::handle_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply of_sepWP_inImage (mid := entry + 188#64) img hfl_1 hsym_1
    rw [‹sf.sp = s0.sp - 96#64›]
    wp_steps
    apply SepWP.fold (zeroed_entails_memRegion (sf_1.readReg64 (Reg.gpr 0#5)) okmLen) (by sep_focus)
    apply SepWP.fold (stackAt_hkdfToVec_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfl_2 hsym_2
    apply SepWPp.of_sepWP_ret
    wp_apply
    apply SepWP.fold (vecU8_exact_entails A outVec (sf_1.readReg64 (Reg.gpr 0#5))
      (hkdf salt ikm info okmLen) okmLen hokm_pos hokm_le
      ‹(hkdf salt ikm info okmLen).length = okmLen› hoom) (by sep_focus)
    wp_done

/-! ## Contract-Parameterized (`*Ext`) Proof of `spqr::kdf::hkdf_to_vec` -/

private theorem stackAt_hkdfToVecExt_tail (sp : BitVec 64) :
    stackAt sp hkdfToVecStackExt =
      memRegion (sp - 17712#64) 96 ∗ stackAt sp hkdfToSliceStackExt :=
  ProofLib.stackAt_split_bottom sp hkdfToSliceStackExt 96 (by decide)

private theorem stackAt_hkdfToVecExt_tail_fold (sp : BitVec 64) :
    memRegion (sp - 17712#64) 96 ∗ stackAt sp hkdfToSliceStackExt ⊢
      stackAt sp hkdfToVecStackExt := by
  rw [stackAt_hkdfToVecExt_tail sp]
  exact Entails.refl _

private theorem stackAt_hkdfToVecExt_shim (sp : BitVec 64) :
    stackAt sp hkdfToVecStackExt =
      memRegion (sp - 17712#64) 1232 ∗
        stackAt (sp - 96#64) extHookStack ∗
        cells (sp - 96#64) 12 := by
  have h1 : stackAt sp hkdfToVecStackExt =
      memRegion (sp - 17712#64) 1232 ∗ stackAt sp (extHookStack + 96) :=
    ProofLib.stackAt_split_bottom sp (extHookStack + 96) 1232 (by decide)
  have h2 : stackAt sp (extHookStack + 96) =
      stackAt (sp - 96#64) extHookStack ∗ cells (sp - 96#64) 12 :=
    stackAt_split_cells sp extHookStack 12 (by decide)
  rw [h1, h2]

private theorem stackAt_extHook_split_alloc (sp : BitVec 64) :
    stackAt (sp - 96#64) extHookStack ⊢
      memRegion (sp - 16480#64) 12288 ∗ stackAt (sp - 96#64) allocHookStack := by
  have h : stackAt (sp - 96#64) extHookStack =
      memRegion ((sp - 96#64) - 16384#64) 12288 ∗ stackAt (sp - 96#64) allocHookStack :=
    ProofLib.stackAt_split_bottom (sp - 96#64) allocHookStack 12288 (by decide)
  have hsub : (sp - 96#64) - 16384#64 = sp - 16480#64 := by bv_lin
  rw [h, hsub]
  exact Entails.refl _

private theorem stackAt_hkdfToVecExt_fold (sp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    memRegion (sp - 17712#64) 1232 ∗
      memRegion (sp - 16480#64) 12288 ∗
      stackAt (sp - 96#64) allocHookStack ∗
      ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
      ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
      ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗
      ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11) ⊢
      memRegion (sp - 17712#64) 96 ∗ stackAt sp hkdfToSliceStackExt := by
  rw [← stackAt_hkdfToVecExt_tail sp, stackAt_hkdfToVecExt_shim sp]
  have h1 : stackAt (sp - 96#64) extHookStack =
      memRegion (sp - 16480#64) 12288 ∗ stackAt (sp - 96#64) allocHookStack := by
    have h := ProofLib.stackAt_split_bottom (sp - 96#64) allocHookStack 12288 (by decide)
    have hsub : (sp - 96#64) - 16384#64 = sp - 16480#64 := by bv_lin
    rwa [hsub] at h
  rw [h1]
  simp only [sepConj_assoc]
  cells_unfold
  refine Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
        (Entails.sepExists_right v9 (Entails.sepExists_right v10
          (Entails.sepExists_right v11 (Entails.refl _))))))))))))

/-- `spqr::kdf::hkdf_to_vec` (`0x631c8`, 47 instructions) meets `(hkdfToVecSpecExt A hkdf).inImage img`
    on `tripleRatchetProgAtExt img.base ext` under `AllocContractsX img A ext` and `HkdfToSliceSpqrOkExt`. -/
theorem hkdf_to_vec_ok_extX (img : Obj.Image) (A : RustAlloc) (hkdf : HkdfFn)
    (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hSlice : HkdfToSliceSpqrOkExt img hkdf ext) :
    HkdfToVecOkExt img A hkdf ext := by
  unfold HkdfToVecOkExt
  have hspec_eq : (hkdfToVecSpecExt A hkdf).inImage img = {
    pre := fun x s =>
      ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      ⌜s.readReg64 .x8 = x.outVec ∧
        s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
        s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
        s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
        s.readReg64 .x6 = BitVec.ofNat 64 x.okmLen ∧
        x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
        (¬x.saltRO ∨ x.salt.length ≤ 64) ∧
        (¬x.ikmRO ∨ x.ikm.length < 64) ∧
        32 ≤ x.info.length ∧ x.info.length < 55 ∧
        (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96)⌝ ∗
        memRegion x.outVec 24 ∗
        bytesAt x.saltRO x.saltA x.salt ∗
        bytesAt x.ikmRO x.ikmA x.ikm ∗
        bytesAt x.infoRO x.infoA x.info ∗
        A.pool ∗
        memRegion (s.sp - 17712#64) 1232 ∗
        stackAt (s.sp - 96#64) extHookStack ∗
        cells (s.sp - 96#64) 12
    post := (hkdfToVecSpecExt A hkdf).post
    onPanic := (hkdfToVecSpecExt A hkdf).onPanic
  } := by
    simp only [hkdfToVecSpecExt, Spec.inImage, stackAt_hkdfToVecExt_shim, sepConj_assoc]
  rw [hspec_eq]
  clear hspec_eq
  simp only [hkdfToVecSpecExt, memRegion_24_cells]
  cells_unfold
  have hshim := hA.session_shim_ok_at hkdfToVecName
    (ls_rel% "spqr::kdf::hkdf_to_vec" "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  have halloc := alloc_zeroed_ok_at_ext img.base A ext hZero hkdfToVecName
    (ls_rel% "spqr::kdf::hkdf_to_vec" "__rustc::__rust_alloc_zeroed")
  have hpanic := panic_at_handle_error_ext img.base ext hkdfToVecName
    (ls_rel% "spqr::kdf::hkdf_to_vec" "alloc::raw_vec::handle_error")
  have hslice_at := sub_ok_at_of_fnAddr hSlice hkdfToVecName
    (ls_rel% "spqr::kdf::hkdf_to_vec" "spqr::kdf::hkdf_to_slice")
  simp only [hkdfToSliceSpqrSpecExt, hkdfToSliceSpecExt] at hslice_at
  clear hA hZero hSlice
  wpp_init x s0
  code_fetches_len CryptoVerification.libsignalSessionCode
    libsignalSessionCode img.base (Rust.withPanics ext) "spqr::kdf::hkdf_to_vec" 188
  have hpc' : s0.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr hkdfToVecName := by
    rw [hpc, Program.fnAddr_rebase]; simp [hkdfToVecName]
  clear hpc
  rename_i hpc
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic hslice_at ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr hkdfToVecName = entry
  examples_hide_fetches
  obtain ⟨outVec, saltRO, saltA, salt, ikmRO, ikmA, ikm, infoRO, infoA, info, okmLen⟩ := x
  dsimp only at *
  have hokm_pos : 0 < okmLen := by
    have := ‹okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96›; omega
  have hokm_le : okmLen ≤ 8160 := by
    have := ‹okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96›; omega
  have htoNat : (BitVec.ofNat 64 okmLen).toNat = okmLen := okmLen_toNat hokm_le
  have hlsb63 : (BitVec.ofNat 64 okmLen).getLsbD 63 = false := okmLen_getLsbD_63 hokm_le
  have hne0 : BitVec.ofNat 64 okmLen ≠ 0#64 := okmLen_ne_zero hokm_pos hokm_le
  have hbeq0 : (BitVec.ofNat 64 okmLen == 0#64) = false := okmLen_beq_zero hokm_pos hokm_le
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk okmLen 1 := layoutOk_okmLen hokm_pos hokm_le
  apply of_sepWP_inImage
    (mid := entry + bv% (ls_rel% "spqr::kdf::hkdf_to_vec" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    img ‹img.FrozenLoaded s0› ‹s0.symtab = img.symtab›
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hfl_0 hsym_0
  apply of_sepWP_inImage (mid := entry + 104#64) img hfl_0 hsym_0
  wp_apply
  apply SepWP.fold (stackAt_extHook_split_alloc s0.sp) (by sep_focus)
  wp_steps
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hfl_1 hsym_1
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_rel% "spqr::kdf::hkdf_to_vec" "alloc::raw_vec::handle_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply of_sepWP_inImage (mid := entry + 188#64) img hfl_1 hsym_1
    rw [‹sf.sp = s0.sp - 96#64›]
    wp_steps
    apply SepWP.fold (zeroed_entails_memRegion (sf_1.readReg64 (Reg.gpr 0#5)) okmLen) (by sep_focus)
    apply SepWP.fold (stackAt_hkdfToVecExt_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfl_2 hsym_2
    apply SepWPp.of_sepWP_ret
    wp_apply
    apply SepWP.fold (stackAt_hkdfToVecExt_tail_fold s0.sp) (by sep_focus)
    apply SepWP.fold (vecU8_exact_entails A outVec (sf_1.readReg64 (Reg.gpr 0#5))
      (hkdf salt ikm info okmLen) okmLen hokm_pos hokm_le
      ‹(hkdf salt ikm info okmLen).length = okmLen› hoom) (by sep_focus)
    wp_done

theorem hkdf_to_vec_ok_ext' (img : Obj.Image) (A : RustAlloc) (hkdf : HkdfFn)
    (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hSlice : HkdfToSliceSpqrOkExt img hkdf ext) :
    HkdfToVecOkExt img A hkdf ext :=
  hkdf_to_vec_ok_extX img A hkdf ext (AllocContractsX.of_AllocContracts hA) hZero hSlice

/-! ## Multi-Placed `[LibsignalPlacement]` Proof of `spqr::kdf::hkdf_to_vec` (Block `378`) -/

abbrev spqrRustAllocZeroedSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed"

/-- Block `378` (`spqr::kdf::hkdf_to_vec`, 47 instructions) meets
`withLsCodeRoLoaded lsmpl (hkdfToVecSpec A hkdf)` on `(blkPC_378).rebase (blkPl_378).base H`. -/
theorem hkdf_to_vec_placed_ok [LibsignalPlacement] (A : RustAlloc) (hkdf : HkdfFn)
    {H : LibsignalHooks}
    (h_panic : H Alloc.spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H Alloc.spqrRustNoAllocShimSym noAllocShimSpec)
    (hZero : HookSat H spqrRustAllocZeroedSym (rustAllocZeroedSpec A))
    (hSlice : subroutine_ok ((blkPC_378).rebase (blkPl_378).base H)
      (lsmpl.base 379) (withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec hkdf))) :
    subroutine_ok ((blkPC_378).rebase (blkPl_378).base H)
      (blkPl_378).base (withLsCodeRoLoaded lsmpl (hkdfToVecSpec A hkdf)) := by
  have hspec_eq : withLsCodeRoLoaded lsmpl (hkdfToVecSpec A hkdf) = {
    pre := fun x s =>
      ⌜s.readReg64 .x8 = x.outVec ∧
        s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
        s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
        s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
        s.readReg64 .x6 = BitVec.ofNat 64 x.okmLen ∧
        x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
        32 ≤ x.info.length ∧ x.info.length < 55 ∧
        (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96)⌝ ∗
        memRegion x.outVec 24 ∗
        bytesAt x.saltRO x.saltA x.salt ∗
        bytesAt x.ikmRO x.ikmA x.ikm ∗
        bytesAt x.infoRO x.infoA x.info ∗
        A.pool ∗
        memRegion (s.sp - 16384#64) 12192 ∗
        stackAt (s.sp - 96#64) allocHookStack ∗
        cells (s.sp - 96#64) 12 ∗
        ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝
    post := (hkdfToVecSpec A hkdf).post
    onPanic := (hkdfToVecSpec A hkdf).onPanic
  } := by
    simp only [hkdfToVecSpec, withLsCodeRoLoaded, stackAt_hkdfToVec, sepConj_assoc]
  rw [hspec_eq]
  clear hspec_eq
  simp only [hkdfToVecSpec, memRegion_24_cells]
  cells_unfold
  have hshim_ok : subroutine_ok ((blkPC_378).rebase (blkPl_378).base H)
      (lsρ Alloc.spqrRustNoAllocShimSym) noAllocShimSpec :=
    Alloc.spqr_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_378).rebase (blkPl_378).base H)
      (lsρ spqrRustAllocZeroedSym) (rustAllocZeroedSpec A) :=
    Alloc.spqr_hook_ok_of_mem hZero
  have hpanic : ((blkPC_378).rebase (blkPl_378).base H).externAt?
      (lsρ Alloc.spqrHandleErrorSym) = some Rust.panicked :=
    (Alloc.spqr_externAt?_of_mem).trans h_panic
  have hslice_at := hSlice
  simp only [withLsCodeRoLoaded, hkdfToSliceSpqrSpec, hkdfToSliceSpec] at hslice_at
  clear h_panic hshim hZero hSlice
  wpp_init x s0
  obtain ⟨outVec, saltRO, saltA, salt, ikmRO, ikmA, ikm, infoRO, infoA, info, okmLen⟩ := x
  dsimp only at *
  have hokm_pos : 0 < okmLen := by
    have := ‹okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96›; omega
  have hokm_le : okmLen ≤ 8160 := by
    have := ‹okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96›; omega
  have htoNat : (BitVec.ofNat 64 okmLen).toNat = okmLen := okmLen_toNat hokm_le
  have hlsb63 : (BitVec.ofNat 64 okmLen).getLsbD 63 = false := okmLen_getLsbD_63 hokm_le
  have hne0 : BitVec.ofNat 64 okmLen ≠ 0#64 := okmLen_ne_zero hokm_pos hokm_le
  have hbeq0 : (BitVec.ofNat 64 okmLen == 0#64) = false := okmLen_beq_zero hokm_pos hokm_le
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk okmLen 1 := layoutOk_okmLen hokm_pos hokm_le
  apply sepWPp_seq_lscro (mid := (blkPl_378).base + 104#64) ‹LibsignalCodeRoLoaded lsmpl s0.mem›
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hfr_1
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ Alloc.spqrHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply sepWPp_seq_lscro (mid := lsmpl.base 379) hfr_1
    rw [‹sf.sp = s0.sp - 96#64›]
    wp_steps
    apply SepWP.fold (zeroed_entails_memRegion (sf_1.readReg64 (Reg.gpr 0#5)) okmLen) (by sep_focus)
    apply SepWP.fold (stackAt_hkdfToVec_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfr_2
    simp only [arm64_norm] at hfr_2
    have hcl_2 := hfr_2.1
    have hro_2 := hfr_2.2
    apply SepWPp.of_sepWP_ret
    wp_apply
    apply SepWP.fold (vecU8_exact_entails A outVec (sf_1.readReg64 (Reg.gpr 0#5))
      (hkdf salt ikm info okmLen) okmLen hokm_pos hokm_le
      ‹(hkdf salt ikm info okmLen).length = okmLen› hoom) (by sep_focus)
    wp_done

end CryptoVerification.SpqrV1.Kdf
