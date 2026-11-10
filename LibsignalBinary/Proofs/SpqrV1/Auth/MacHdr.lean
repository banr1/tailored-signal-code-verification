/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.Repr
public import LibsignalBinary.Proofs.SpqrV1.Auth.SpqrAuthCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# `<spqr::authenticator::Authenticator>::mac_hdr`

Verifies `<spqr::authenticator::Authenticator>::mac_hdr` (`0x5e068`, block 342):
concatenates `[Authenticator.hdrLabel, toBEBytes 8 ep, hdr]` via `slice::Concat::concat`,
computes HMAC-SHA256 truncated to 32 bytes (`self.macHdrUnchecked F ep hdr`) via
`libcrux_hmac::hmac`, and deallocates the temporary buffer.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L25

open Lean Meta Elab Term Command Tactic ProofLib ProofLib.CodeLookup
open CryptoVerification.CodeLayout

scoped elab (name := genDecodesLenMacHdr) "gen_decodes_len " tree:ident pfx:ident sym:str len:num : command => do
  let off ← liftTermElabM do
    let cn ← realizeGlobalConstNoOverload (mkIdent `CryptoVerification.libsignalSessionCode)
    return (← lookup cn .fnOff sym.getString).val
  let a := Syntax.mkNumLit (toString off)
  let b := Syntax.mkNumLit (toString (off + len.getNat - 4))
  elabCommand (← `(gen_decodes $tree $pfx [$a:num → $b:num]))

scoped elab (name := codeFetchesLenMacHdr) "code_fetches_len " codeId:ident decPrefix:ident b:term:max H:term:max sym:str len:num : tactic => do
  let codeName ← realizeGlobalConstNoOverloadWithInfo codeId
  let eOff ← lookup codeName .fnOff sym.getString
  let hfn := mkCIdentFrom sym eOff.decl
  let offStx := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic| code_fetches $codeId $decPrefix $b $H $hfn $offStx $len))

scoped syntax:max (name := lsFnXrefMacHdrStx) "ls_fn_xref% " str num num : term

@[term_elab lsFnXrefMacHdrStx] meta def elabLsFnXrefMacHdr : TermElab := fun stx expectedType? => do
  match stx with
  | `(ls_fn_xref% $sym:str $k1:num $k2:num) =>
    let codeName := `CryptoVerification.libsignalSessionCode
    let treeName := `CryptoVerification.libsignalSessionCode_tree
    let eOff ← lookup codeName .fnOff sym.getString
    let v ← xrefTarget treeName (eOff.val + k1.getNat) (some (eOff.val + k2.getNat))
    elabTerm (Syntax.mkNumLit (toString v)) expectedType?
  | _ => throwUnsupportedSyntax

end CryptoVerification.SpqrV1.Layout.L25

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L25
open DoReserveNorm

gen_decodes_len libsignalSessionCode_tree libsignalSessionBin
  "<spqr::authenticator::Authenticator>::mac_hdr" 148

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Specifications and Fixed-Image Proof -/

/-- Stack budget of `Authenticator::mac_hdr` (`112 + extHookStack`). -/
abbrev authMacHdrStackX : Nat := 112 + extHookStack

/-- Pinned ghost arguments for `Authenticator::mac_hdr`. -/
structure AuthMacHdrPinnedGhost where
  /-- Sret pointer (`x8`, 24-byte `Vec<u8>` output `Mac`). -/
  outVec : BitVec 64
  /-- `&Authenticator` pointer (`x0`, 48 bytes). -/
  selfA : BitVec 64
  /-- Ghost `(cap, ptr)` pins of `self`. -/
  g : AuthenticatorGhost
  auth : Authenticator
  /-- Epoch (`x1`, `u64`). -/
  ep : Epoch
  /-- Whether `hdr` is read-only (`true`) or read-write (`false`). -/
  hdrRO : Bool
  /-- `hdr: &[u8]` pointer (`x2`). -/
  hdrA : BitVec 64
  /-- `hdr: &[u8]` contents (`x3 = hdr.length`). -/
  hdr : Bytes

/-- Unpinned ghost arguments for `Authenticator::mac_hdr`. -/
structure AuthMacHdrGhost where
  /-- Sret pointer (`x8`, 24-byte `Vec<u8>` output `Mac`). -/
  outVec : BitVec 64
  /-- `&Authenticator` pointer (`x0`, 48 bytes). -/
  selfA : BitVec 64
  auth : Authenticator
  /-- Epoch (`x1`, `u64`). -/
  ep : Epoch
  /-- Whether `hdr` is read-only (`true`) or read-write (`false`). -/
  hdrRO : Bool
  /-- `hdr: &[u8]` pointer (`x2`). -/
  hdrA : BitVec 64
  /-- `hdr: &[u8]` contents (`x3 = hdr.length`). -/
  hdr : Bytes

/-- Pinned specification of `<spqr::authenticator::Authenticator>::mac_hdr` (`0x5e068`):
writes `vecU8 A outVec (auth.macHdrUnchecked F ep hdr)` on normal return, or panics on
OOM / `u32` HMAC input length overflow. -/
def authMacHdrPinnedSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthMacHdrPinnedGhost where
  pre x s :=
    ⌜s.readReg64 .x8 = x.outVec ∧ s.readReg64 .x0 = x.selfA ∧
      s.readReg64 .x1 = x.ep ∧ s.readReg64 .x2 = x.hdrA ∧
      s.readReg64 .x3 = BitVec.ofNat 64 x.hdr.length ∧
      41 + x.hdr.length < 2 ^ 63⌝ ∗
      memRegion x.outVec 24 ∗
      authenticatorPinAt A x.g x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool ∗ stackAt s.sp authMacHdrStackX
  post x s0 sf :=
    ⌜x.auth.macHdr F x.ep x.hdr = .ok (x.auth.macHdrUnchecked F x.ep x.hdr) ∧
      sf.trace = s0.trace⌝ ∗
      vecU8 A x.outVec (x.auth.macHdrUnchecked F x.ep x.hdr) ∗
      authenticatorPinAt A x.g x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool ∗ stackAt s0.sp authMacHdrStackX
  onPanic x s0 sf :=
    ⌜(allocFailedIn s0 sf ∨
      2 ^ 32 ≤ x.auth.macKey.length ∨
      2 ^ 32 ≤ (Authenticator.hdrLabel ++ toBEBytes 8 x.ep ++ x.hdr).length) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Unpinned specification of `Authenticator::mac_hdr`. -/
def authMacHdrSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthMacHdrGhost where
  pre x s :=
    ⌜s.readReg64 .x8 = x.outVec ∧ s.readReg64 .x0 = x.selfA ∧
      s.readReg64 .x1 = x.ep ∧ s.readReg64 .x2 = x.hdrA ∧
      s.readReg64 .x3 = BitVec.ofNat 64 x.hdr.length ∧
      41 + x.hdr.length < 2 ^ 63⌝ ∗
      memRegion x.outVec 24 ∗
      authenticatorAt A x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool ∗ stackAt s.sp authMacHdrStackX
  post x s0 sf :=
    ⌜x.auth.macHdr F x.ep x.hdr = .ok (x.auth.macHdrUnchecked F x.ep x.hdr) ∧
      sf.trace = s0.trace⌝ ∗
      vecU8 A x.outVec (x.auth.macHdrUnchecked F x.ep x.hdr) ∗
      authenticatorAt A x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool ∗ stackAt s0.sp authMacHdrStackX
  onPanic x s0 sf :=
    ⌜(allocFailedIn s0 sf ∨
      2 ^ 32 ≤ x.auth.macKey.length ∨
      2 ^ 32 ≤ (Authenticator.hdrLabel ++ toBEBytes 8 x.ep ++ x.hdr).length) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `.inImage img` contract proposition for `authMacHdrSpec F A`. -/
def AuthMacHdrOkX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authMacHdrName)
    ((authMacHdrSpec F A).inImage img)

namespace MacHdrFacts

theorem authMacHdr_fnOff :
    libsignalSessionCode.fnOff authMacHdrName =
      ls_off% "<spqr::authenticator::Authenticator>::mac_hdr" :=
  ls_lemma% fnOff "<spqr::authenticator::Authenticator>::mac_hdr"

theorem libcruxHmac_fnOff :
    libsignalSessionCode.fnOff libcruxHmacName =
      ls_off% "libcrux_hmac::hmac" :=
  ls_stub% "libcrux_hmac::hmac"

/-- 33-byte `.rodata` slice `Authenticator.hdrLabel`. -/
theorem rodata_hdrLabel {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_fn_xref% "<spqr::authenticator::Authenticator>::mac_hdr" 24 28)) ↦ᵣ Authenticator.hdrLabel) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_fn_xref% "<spqr::authenticator::Authenticator>::mac_hdr" 24 28)) (n := 33) (bs := Authenticator.hdrLabel)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

@[simp] theorem hdrLabel_length :
    Authenticator.hdrLabel.length = 33 := by decide

theorem macHdrUnchecked_eq_hmacWith (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes) :
    self.macHdrUnchecked F ep hdr =
      hmacWith F self.macKey (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr) := by
  unfold Authenticator.macHdrUnchecked Authenticator.macSize
  exact List.take_of_length_le (by rw [length_hmacWith])

/-- Splits `stackAt sp authMacHdrStackX` into the `ct_mac_data` `Vec<u8>` sret (`[sp - 112, sp - 88)`),
the `[&[u8]; 3]` slice array (`[sp - 88, sp - 40)`), `ep.to_be_bytes()` (`[sp - 40, sp - 32)`),
and four callee-saved registers (`[sp - 32, sp)`). -/
theorem stackAt_authMacHdrX_split (sp : BitVec 64) :
    stackAt sp authMacHdrStackX =
      stackAt (sp - 112#64) extHookStack ∗
        memRegion (sp - 112#64) 24 ∗
        (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
         ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
          ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
          ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
          ((sp - 56#64) ↦₆₄ s4) ∗ ((sp - 48#64) ↦₆₄ s5)) ∗
        (∃∗ e0 : BitVec 64, (sp - 40#64) ↦₆₄ e0) ∗
        (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
          ((sp - 32#64) ↦₆₄ c0) ∗ ((sp - 24#64) ↦₆₄ c1) ∗
          ((sp - 16#64) ↦₆₄ c2) ∗ ((sp - 8#64) ↦₆₄ c3)) := by
  change memRegion (sp - BitVec.ofNat 64 16496) 16496 =
    memRegion (sp - 112#64 - BitVec.ofNat 64 16384) 16384 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16496) (n := 16384) (k := 112)
      (b' := sp - 112#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 112#64) (n := 24) (k := 88)
      (b' := sp - 88#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 88#64) (n := 48) (k := 40)
      (b' := sp - 40#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 40#64) (n := 8) (k := 32)
      (b' := sp - 32#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - BitVec.ofNat 64 16496) 16384 ∗
    (memRegion (sp - 112#64) 24 ∗
      (memRegion (sp - 88#64) (8 * 6) ∗
        (memRegion (sp - 40#64) 8 ∗ memRegion (sp - 32#64) (8 * 4)))) = _
  rw [ProofLib.memRegion_cells (sp - 88#64) 6 (by decide),
    ProofLib.memRegion_eight (sp - 40#64),
    ProofLib.memRegion_cells (sp - 32#64) 4 (by decide)]
  have hsub : sp - 112#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16496 := by bv_kernel
  have hc6 : cells (sp - 88#64) 6 =
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
        ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
        ((sp - 56#64) ↦₆₄ s4) ∗ ((sp - 48#64) ↦₆₄ s5)) := by
    cells_unfold
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ c0) ∗ ((sp - 24#64) ↦₆₄ c1) ∗
        ((sp - 16#64) ↦₆₄ c2) ∗ ((sp - 8#64) ↦₆₄ c3)) := by
    cells_unfold
  rw [hsub, hc6, hc4]

/-- Reassembles the `mac_hdr` frame back into `stackAt sp authMacHdrStackX`. -/
theorem rejoin_stack_authMacHdrX (sp : BitVec 64)
    (v0 v1 v2 : BitVec 64)
    (s0 s1 s2 s3 s4 s5 : BitVec 64)
    {beBytes : List (BitVec 8)} (hbe : beBytes.length = 8)
    (c0 c1 c2 c3 : BitVec 64) :
    stackAt (sp - 112#64) extHookStack ∗
      ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v2) ∗
      ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
      ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
      ((sp - 56#64) ↦₆₄ s4) ∗ ((sp - 48#64) ↦₆₄ s5) ∗
      ((sp - 40#64) ↦ₛ beBytes) ∗
      ((sp - 32#64) ↦₆₄ c0) ∗ ((sp - 24#64) ↦₆₄ c1) ∗
      ((sp - 16#64) ↦₆₄ c2) ∗ ((sp - 8#64) ↦₆₄ c3) ⊢
      stackAt sp authMacHdrStackX := by
  have heq : stackAt sp authMacHdrStackX =
      stackAt (sp - 112#64) extHookStack ∗
        cells (sp - 112#64) 9 ∗
        memRegion (sp - 40#64) 8 ∗
        cells (sp - 32#64) 4 := by
    change memRegion (sp - BitVec.ofNat 64 16496) 16496 =
      memRegion (sp - 112#64 - BitVec.ofNat 64 16384) 16384 ∗ _
    rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16496) (n := 16384) (k := 112)
        (b' := sp - 112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 112#64) (n := 72) (k := 40)
        (b' := sp - 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 8) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide)]
    change memRegion (sp - BitVec.ofNat 64 16496) 16384 ∗
      (memRegion (sp - 112#64) (8 * 9) ∗
        (memRegion (sp - 40#64) 8 ∗ memRegion (sp - 32#64) (8 * 4))) = _
    rw [ProofLib.memRegion_cells (sp - 112#64) 9 (by decide),
      ProofLib.memRegion_cells (sp - 32#64) 4 (by decide)]
    have hsub : sp - 112#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16496 := by bv_kernel
    rw [hsub]
  rw [heq]
  have hc9 :
      (((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v2) ∗
       ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
       ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
       ((sp - 56#64) ↦₆₄ s4) ∗ ((sp - 48#64) ↦₆₄ s5)) ⊢ cells (sp - 112#64) 9 := by
    cells_unfold
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right s0 (Entails.sepExists_right s1 (Entails.sepExists_right s2
        (Entails.sepExists_right s3 (Entails.sepExists_right s4
          (Entails.sepExists_right s5 (Entails.refl _)))))))))
  have hmbe : ((sp - 40#64) ↦ₛ beBytes) ⊢ memRegion (sp - 40#64) 8 :=
    hbe ▸ pointsToBytes_entails_memRegion (sp - 40#64) beBytes
  have hc4 :
      (((sp - 32#64) ↦₆₄ c0) ∗ ((sp - 24#64) ↦₆₄ c1) ∗
       ((sp - 16#64) ↦₆₄ c2) ∗ ((sp - 8#64) ↦₆₄ c3)) ⊢ cells (sp - 32#64) 4 := by
    cells_unfold
    exact Entails.sepExists_right c0 (Entails.sepExists_right c1
      (Entails.sepExists_right c2 (Entails.sepExists_right c3 (Entails.refl _))))
  have hgroup :
      stackAt (sp - 112#64) extHookStack ∗
        ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v2) ∗
        ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
        ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
        ((sp - 56#64) ↦₆₄ s4) ∗ ((sp - 48#64) ↦₆₄ s5) ∗
        ((sp - 40#64) ↦ₛ beBytes) ∗
        ((sp - 32#64) ↦₆₄ c0) ∗ ((sp - 24#64) ↦₆₄ c1) ∗
        ((sp - 16#64) ↦₆₄ c2) ∗ ((sp - 8#64) ↦₆₄ c3) =
      stackAt (sp - 112#64) extHookStack ∗
        (((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v2) ∗
         ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
         ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
         ((sp - 56#64) ↦₆₄ s4) ∗ ((sp - 48#64) ↦₆₄ s5)) ∗
        ((sp - 40#64) ↦ₛ beBytes) ∗
        (((sp - 32#64) ↦₆₄ c0) ∗ ((sp - 24#64) ↦₆₄ c1) ∗
         ((sp - 16#64) ↦₆₄ c2) ∗ ((sp - 8#64) ↦₆₄ c3)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_right (sepConj_mono hc9 (sepConj_mono hmbe hc4))

theorem onPanic_concat_entails_macHdr {s0 s sf : State} {P1 P2 : Prop} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(allocFailedIn s0 sf ∨ P1 ∨ P2) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  refine Entails.pure_left fun ⟨haf, hpref⟩ => ?_
  exact Entails.pure_right ⟨Or.inl haf, hpref⟩ (entails_anyHeap _)

theorem onPanic_hmac_entails_macHdr {s0 s sf : State} {P1 P2 : Prop} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜(allocFailedIn s sf ∨ P1 ∨ P2) ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(allocFailedIn s0 sf ∨ P1 ∨ P2) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

theorem SepWPp.call_allowPanic_inImage_mid {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : ImgCallInv img s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : (∀ code sf, spec.onExit x code s sf = ⌜False⌝) ∧
      (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  exact ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hF.1 hF.2 hpc hrun hsp_align hlr
    (fun R' hm => by
      dsimp only [Spec.inImage]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hF.1, hF.2⟩, hpre R' hm⟩)
    (fun sf code R' _ hm => by
      dsimp only [Spec.inImage] at hm
      rw [hexit_eq.1] at hm
      exact not_satisfies_false_sepConj hm)
    (fun sf _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sf)) hm')
    (fun sf hpcm hrunm hspm hcsm hfz hsym => hnext sf hpcm hrunm hspm hcsm ⟨hfz, hsym⟩)
    (fun sf R' _ hm => by
      dsimp only [Spec.inImage] at hm
      rw [hexit_eq.2] at hm
      exact (not_satisfies_false_sepConj hm).elim)

open Lean Elab Tactic in
elab "wpp_call_inImage_concat_macHdr " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_inImage_mid $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_inImage_concat_macHdr: unexpected subgoals"
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
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_concat_entails_macHdr (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
elab "wpp_call_inImage_hmac_macHdr " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (NextKeyInternalFacts.SepWPp.call_allowPanic_inImage_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_inImage_hmac_macHdr: unexpected subgoals"
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
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_hmac_entails_macHdr (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

end MacHdrFacts

open MacHdrFacts
open NextKeyInternalFacts
open AgreeStateSimp

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length hdrLabel_length
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  authMacHdr_fnOff sliceConcat_fnOff libcruxHmac_fnOff dealloc_fnOff
  (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::mac_hdr")
  (ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]")
  (ls_stub% "libcrux_hmac::hmac")
  (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_hook% "__rustc::__rust_dealloc")

theorem SepWPp.pure_left_focus {prog : Program} {pc : BitVec 64} {s : State}
    {P P' : SepProp} {post post_err : State → SepProp → Prop} (φ : Prop)
    (hf : P = ⌜φ⌝ ∗ P')
    (h : φ → SepWPp prog pc s P' post post_err) :
    SepWPp prog pc s P post post_err := by
  intro R hm hL
  rw [hf, sepConj_assoc, satisfies_pure_sepConj] at hm
  exact (h hm.1) R hm.2 hL

set_option maxHeartbeats 1600000 in
theorem authMacHdrPinned_ok_of_contracts_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhmac : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr libcruxHmacName)
      ((libcruxHmacSpec F A).inImage img))
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authMacHdrName)
      ((authMacHdrPinnedSpec F A).inImage img) := by
  unfold tripleRatchetProgAtExt
  refine subroutine_ok_inImage_rodata1_keep (rodata_hdrLabel himg) ?_
  wpp_init x s0
  have hfn := authMacHdr_fnOff
  code_fetches_len libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) "<spqr::authenticator::Authenticator>::mac_hdr" 148
  have h_concat := sub_ok_at_rebase (name := authMacHdrName) (callee := sliceConcatName)
    (k := ls_rel% "<spqr::authenticator::Authenticator>::mac_hdr"
      "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]")
    (by rw [authMacHdr_fnOff, sliceConcat_fnOff]) hconcat3
  have h_hmac := sub_ok_at_rebase (name := authMacHdrName) (callee := libcruxHmacName)
    (k := ls_rel% "<spqr::authenticator::Authenticator>::mac_hdr" "libcrux_hmac::hmac")
    (by rw [authMacHdr_fnOff, libcruxHmac_fnOff]) hhmac
  have h_dealloc := sub_ok_at_rebase (name := authMacHdrName) (callee := deallocName)
    (k := ls_rel% "<spqr::authenticator::Authenticator>::mac_hdr" "__rustc::__rust_dealloc")
    (by rw [authMacHdr_fnOff, dealloc_fnOff]) hdealloc
  have hadrp : ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      authMacHdrName + 24#64 &&&
      0xffffffff_fffff000#64) + bv% (ls_fn_xref% "<spqr::authenticator::Authenticator>::mac_hdr" 24 28 -
        page% (ls_off% "<spqr::authenticator::Authenticator>::mac_hdr" + 24)) =
      img.base + bv% (ls_fn_xref% "<spqr::authenticator::Authenticator>::mac_hdr" 24 28) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr authMacHdrName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear himg hconcat3 hhmac hdealloc hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      authMacHdrName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rcases x with ⟨outVec, selfA, g, auth, ep, hdrRO, hdrA, hdr⟩
  dsimp only [authMacHdrPinnedSpec] at hpre h_1 h_2 h_3 h_4 h_5 h_6 h_7 h ⊢
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  subst h_3 h_4 h_5 h_6
  have hadd24_8 : (s0.readReg64 (.gpr 0#5) + 0x18#64) + 8#64 = s0.readReg64 (.gpr 0#5) + 32#64 := by bv_omega
  have hadd24_16 : (s0.readReg64 (.gpr 0#5) + 0x18#64) + 16#64 = s0.readReg64 (.gpr 0#5) + 40#64 := by bv_omega
  dsimp only [authenticatorPinAt]
  refine SepWPp.rw_pre (by rw [stackAt_authMacHdrX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.fold
    (vecU8At_expose_entails A (s0.readReg64 (.gpr 0#5) + 0x18#64) g.macKey.cap g.macKey.ptr auth.macKey)
    (by sep_focus) ?_
  refine SepWPp.rw_pre (by rw [hadd24_8, hadd24_16]) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmac_le, hmac_lt63, hmac_ptr_ne⟩
  have hmac_toNat : (BitVec.ofNat 64 auth.macKey.length).toNat = auth.macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPp.of_sepWP_inImage (mid := entry +
    bv% (ls_rel% "<spqr::authenticator::Authenticator>::mac_hdr"
      "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]")) hinv0 ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 40#64) (s0.readReg64 (.gpr 1#5)))) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_inImage_concat_macHdr h_concat
    (⟨s0.sp - 112#64, s0.sp - 88#64,
      true, img.base + bv% (ls_fn_xref% "<spqr::authenticator::Authenticator>::mac_hdr" 24 28), Authenticator.hdrLabel,
      false, s0.sp - 40#64, toBEBytes 8 (s0.readReg64 (.gpr 1#5)),
      hdrRO, s0.readReg64 (.gpr 2#5), hdr⟩ : SliceConcat3Ghost)
    hinv1
  have hdata_pos :
      0 < (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length := by
    simp [List.length_append]
  have hdata_lt64 :
      (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length < 2 ^ 64 := by
    simp only [List.length_append, hdrLabel_length, toBEBytes_8_length]
    omega
  have hdata_toNat :
      (BitVec.ofNat 64 (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length).toNat =
        (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdata_lt64]
  rw [← List.append_assoc Authenticator.hdrLabel]
  refine SepWPp.fold (vecU8_nonempty_entails A (s0.sp - 112#64) hdata_pos) (by sep_focus) ?_
  sep_elim_exists
  rename_i cap ptr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_ne, hlayout, hptr_ne, hle⟩
  have ⟨hpos1, hpow1, hisize⟩ := hlayout
  have hcap_beq : (cap == 0#64) = false := beq_false_of_ne hcap_ne
  refine SepWPp.of_sepWP_inImage (mid := entry +
    bv% (ls_rel% "<spqr::authenticator::Authenticator>::mac_hdr" "libcrux_hmac::hmac")) hF_sf ?_
  wp_steps
  have hstack_sf : stackAt (s0.sp - 112#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 112#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  change subroutine_ok prog _ ((libcruxHmacSpec F A).inImage img) at h_hmac
  wpp_call_inImage_hmac_macHdr h_hmac
    (⟨s0.readReg64 (.gpr 8#5), g.macKey.ptr, auth.macKey,
      ptr, Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr⟩ : LibcruxHmacCall)
    hinv2
  have hk_lt32 : auth.macKey.length < 4294967296 := ‹_›
  have hd_lt32 : (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length < 4294967296 := by
    rwa [List.append_assoc]
  rw [← List.append_assoc Authenticator.hdrLabel]
  apply SepWP.seq_inImage (mid := entry +
    bv% (ls_rel% "<spqr::authenticator::Authenticator>::mac_hdr" "__rustc::__rust_dealloc")) hF_sf_1
  wp_steps
  refine SepWP.fold (pointsToBytes_memRegion_entails _ hle hlayout) (by sep_focus) ?_
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  rintro ⟨hF3, hsym3⟩
  wp_call h_dealloc (_, _, 1)
  wp_steps
  refine SepWP.fold (Entails.of_eq (hstack_sf.trans hstack_sf1).symm) (by sep_focus) ?_
  have hbe_len : (toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length = 8 := by simp
  refine SepWP.fold (rejoin_stack_authMacHdrX s0.sp _ _ _ _ _ _ _ _ _ hbe_len _ _ _ _) (by sep_focus) ?_
  have hmac_rejoin :
      ((s0.readReg64 (.gpr 0#5) + 0x18#64) ↦₆₄ g.macKey.cap) ∗
        ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ g.macKey.ptr) ∗
        ((s0.readReg64 (.gpr 0#5) + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
        (g.macKey.ptr ↦ₛ auth.macKey) ∗
        (if g.macKey.cap = 0 then emp
         else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) ⊢
        vecU8At A (s0.readReg64 (.gpr 0#5) + 0x18#64) g.macKey.cap g.macKey.ptr auth.macKey := by
    rw [← hadd24_8, ← hadd24_16]
    exact vecU8At_unexpose_entails A (s0.readReg64 (.gpr 0#5) + 0x18#64)
      g.macKey.cap g.macKey.ptr auth.macKey hmac_le hmac_lt63 hmac_ptr_ne
  refine SepWP.fold hmac_rejoin (by sep_focus) ?_
  have hmacHdr_ok :
      auth.macHdr F (s0.readReg64 (.gpr 1#5)) hdr =
        .ok (auth.macHdrUnchecked F (s0.readReg64 (.gpr 1#5)) hdr) :=
    Authenticator.macHdr_of_lt F auth (s0.readReg64 (.gpr 1#5)) hdr hk_lt32 hd_lt32
  rw [← List.append_assoc Authenticator.hdrLabel,
    ← macHdrUnchecked_eq_hmacWith F auth (s0.readReg64 (.gpr 1#5)) hdr]
  wp_done

/-- `Authenticator::mac_hdr` meets `AuthMacHdrOkX img F A ext` from callee contracts. -/
theorem authMacHdr_ok_of_contracts_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhmac : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr libcruxHmacName)
      ((libcruxHmacSpec F A).inImage img))
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    AuthMacHdrOkX img F A ext := by
  unfold AuthMacHdrOkX
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpin := authMacHdrPinned_ok_of_contracts_x himg hconcat3 hhmac hdealloc
  simp only [authMacHdrSpec, Spec.inImage, authenticatorAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨
      ((authMacHdrPinnedSpec F A).inImage img).pre
        ⟨x.outVec, x.selfA, g, x.auth, x.ep, x.hdrRO, x.hdrA, x.hdr⟩ s0 ∗ R := by
    simpa only [authMacHdrPinnedSpec, Spec.inImage] using hpre
  refine hpin.mono_outcome ⟨x.outVec, x.selfA, g, x.auth, x.ep, x.hdrRO, x.hdrA, x.hdr⟩ R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hent :
        ((authMacHdrPinnedSpec F A).inImage img).post
          ⟨x.outVec, x.selfA, g, x.auth, x.ep, x.hdrRO, x.hdrA, x.hdr⟩ s0 sf ∗ R ⊢
        ((authMacHdrSpec F A).inImage img).post x s0 sf ∗ R := by
      apply sepConj_mono_left
      dsimp only [authMacHdrPinnedSpec, authMacHdrSpec, Spec.inImage]
      exact sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (authenticatorPinAt_entails_authenticatorAt A g x.selfA x.auth)))
    exact Satisfies.mono hent hpost
  · exact Or.inr (Or.inl ⟨hpan, hpost⟩)
  · exact Or.inr (Or.inr hex)

theorem libcrux_hmac_ok_at_ext (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (ext : String → Option (State → State))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff libcruxHmacName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (libcruxHmacSpec F A) :=
  hook_ok_at (hname := libcruxHmacName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) hhmac

theorem libcrux_hmac_ok_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr libcruxHmacName)
      ((libcruxHmacSpec F A).inImage img) := by
  apply Alloc.subroutine_ok_inImage img
  simpa only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    libcrux_hmac_ok_at_ext img.base F A ext hhmac libcruxHmacName 0 (by simp)

/-- `Authenticator::mac_hdr` meets `AuthMacHdrOkX img F A ext` under `AllocContractsX`. -/
theorem authMacHdr_ok_ext_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A))
    (hA : AllocContractsX img A ext) :
    AuthMacHdrOkX img F A ext :=
  authMacHdr_ok_of_contracts_x himg hconcat3 (libcrux_hmac_ok_x hhmac) hA.dealloc

/-! ## Relocatable Contracts (Block 342) -/

theorem rodata_hdrLabel_placed [LibsignalPlacement] {m : Memory}
    (hF : LsCallInv lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ "spqr:.rodata..Lanon.140") ↦ᵣ Authenticator.hdrLabel) ∗ P :=
  lsro_intro_chk hF.1 (by decide +kernel) hP

open Lean Elab Tactic in
elab "wpp_call_lsCallInv_concat_macHdr " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_lsCallInv_mid $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_lsCallInv_concat_macHdr: unexpected subgoals"
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
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_concat_entails_macHdr (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
elab "wpp_call_lsCallInv_hmac_macHdr " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_lsCallInv_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_lsCallInv_hmac_macHdr: unexpected subgoals"
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
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_hmac_entails_macHdr (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

set_option maxHeartbeats 1600000 in
/-- Block 342 (`Authenticator::mac_hdr`) meets `withLsCallInv lsmpl (authMacHdrPinnedSpec F A)`. -/
theorem authMacHdrPinned_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_concat : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat3Spec A)))
    (h_hmac : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsρ "_RNvCs65XVORQObL2_12libcrux_hmac4hmac")
      (withLsCallInv lsmpl (libcruxHmacSpec F A)))
    (h_dealloc : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack A extHookStack)) :
    subroutine_ok ((blkPC_342).rebase (blkPl_342).base H) (blkPl_342).base
      (withLsCallInv lsmpl (authMacHdrPinnedSpec F A)) := by
  refine subroutine_ok_withLsCallInv_rodata1_keep rodata_hdrLabel_placed ?_
  wpp_init x s0
  rcases x with ⟨outVec, selfA, g, auth, ep, hdrRO, hdrA, hdr⟩
  dsimp only [authMacHdrPinnedSpec] at hpre h_1 h_2 h_3 h_4 h_5 h_6 h ⊢
  have hinv0 : LsCallInv lsmpl s0.mem := h_1
  subst h_2 h_3 h_4 h_5
  have hadd24_8 : (s0.readReg64 (.gpr 0#5) + 0x18#64) + 8#64 = s0.readReg64 (.gpr 0#5) + 32#64 := by bv_omega
  have hadd24_16 : (s0.readReg64 (.gpr 0#5) + 0x18#64) + 16#64 = s0.readReg64 (.gpr 0#5) + 40#64 := by bv_omega
  dsimp only [authenticatorPinAt]
  refine SepWPp.rw_pre (by rw [stackAt_authMacHdrX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.fold
    (vecU8At_expose_entails A (s0.readReg64 (.gpr 0#5) + 0x18#64) g.macKey.cap g.macKey.ptr auth.macKey)
    (by sep_focus) ?_
  refine SepWPp.rw_pre (by rw [hadd24_8, hadd24_16]) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmac_le, hmac_lt63, hmac_ptr_ne⟩
  have hmac_toNat : (BitVec.ofNat 64 auth.macKey.length).toNat = auth.macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 386) hinv0 ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 40#64) (s0.readReg64 (.gpr 1#5)))) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  change subroutine_ok _ _ (withLsCallInv lsmpl (sliceConcat3Spec A)) at h_concat
  wpp_call_lsCallInv_concat_macHdr h_concat
    (⟨s0.sp - 112#64, s0.sp - 88#64,
      true, lsρ "spqr:.rodata..Lanon.140", Authenticator.hdrLabel,
      false, s0.sp - 40#64, toBEBytes 8 (s0.readReg64 (.gpr 1#5)),
      hdrRO, s0.readReg64 (.gpr 2#5), hdr⟩ : SliceConcat3Ghost)
    hinv1
  have hdata_pos :
      0 < (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length := by
    simp [List.length_append]
  have hdata_lt64 :
      (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length < 2 ^ 64 := by
    simp only [List.length_append, hdrLabel_length, toBEBytes_8_length]
    omega
  have hdata_toNat :
      (BitVec.ofNat 64 (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length).toNat =
        (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdata_lt64]
  rw [← List.append_assoc Authenticator.hdrLabel]
  refine SepWPp.fold (vecU8_nonempty_entails A (s0.sp - 112#64) hdata_pos) (by sep_focus) ?_
  sep_elim_exists
  rename_i cap ptr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_ne, hlayout, hptr_ne, hle⟩
  have ⟨hpos1, hpow1, hisize⟩ := hlayout
  have hcap_beq : (cap == 0#64) = false := beq_false_of_ne hcap_ne
  refine SepWPp.of_sepWP_lsCallInv (mid := lsρ "_RNvCs65XVORQObL2_12libcrux_hmac4hmac") hF_sf ?_
  wp_steps
  have hstack_sf : stackAt (s0.sp - 112#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 112#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  change subroutine_ok _ _ (withLsCallInv lsmpl (libcruxHmacSpec F A)) at h_hmac
  wpp_call_lsCallInv_hmac_macHdr h_hmac
    (⟨s0.readReg64 (.gpr 8#5), g.macKey.ptr, auth.macKey,
      ptr, Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr⟩ : LibcruxHmacCall)
    hinv2
  have hk_lt32 : auth.macKey.length < 4294967296 := ‹_›
  have hd_lt32 : (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length < 4294967296 := by
    rwa [List.append_assoc]
  rw [← List.append_assoc Authenticator.hdrLabel]
  wp_steps
  refine SepWP.fold (pointsToBytes_memRegion_entails _ hle hlayout) (by sep_focus) ?_
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  wp_call h_dealloc (_, _, 1)
  wp_steps
  refine SepWP.fold (Entails.of_eq (hstack_sf.trans hstack_sf1).symm) (by sep_focus) ?_
  have hbe_len : (toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length = 8 := by simp
  refine SepWP.fold (rejoin_stack_authMacHdrX s0.sp _ _ _ _ _ _ _ _ _ hbe_len _ _ _ _) (by sep_focus) ?_
  have hmac_rejoin :
      ((s0.readReg64 (.gpr 0#5) + 0x18#64) ↦₆₄ g.macKey.cap) ∗
        ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ g.macKey.ptr) ∗
        ((s0.readReg64 (.gpr 0#5) + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
        (g.macKey.ptr ↦ₛ auth.macKey) ∗
        (if g.macKey.cap = 0 then emp
         else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) ⊢
        vecU8At A (s0.readReg64 (.gpr 0#5) + 0x18#64) g.macKey.cap g.macKey.ptr auth.macKey := by
    rw [← hadd24_8, ← hadd24_16]
    exact vecU8At_unexpose_entails A (s0.readReg64 (.gpr 0#5) + 0x18#64)
      g.macKey.cap g.macKey.ptr auth.macKey hmac_le hmac_lt63 hmac_ptr_ne
  refine SepWP.fold hmac_rejoin (by sep_focus) ?_
  have hmacHdr_ok :
      auth.macHdr F (s0.readReg64 (.gpr 1#5)) hdr =
        .ok (auth.macHdrUnchecked F (s0.readReg64 (.gpr 1#5)) hdr) :=
    Authenticator.macHdr_of_lt F auth (s0.readReg64 (.gpr 1#5)) hdr hk_lt32 hd_lt32
  rw [← List.append_assoc Authenticator.hdrLabel,
    ← macHdrUnchecked_eq_hmacWith F auth (s0.readReg64 (.gpr 1#5)) hdr]
  wp_done

/-- Block 342 (`Authenticator::mac_hdr`) meets `withLsCallInv lsmpl (authMacHdrSpec F A)`. -/
theorem authMacHdr_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_concat : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat3Spec A)))
    (h_hmac : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsρ "_RNvCs65XVORQObL2_12libcrux_hmac4hmac")
      (withLsCallInv lsmpl (libcruxHmacSpec F A)))
    (h_dealloc : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack A extHookStack)) :
    subroutine_ok ((blkPC_342).rebase (blkPl_342).base H) (blkPl_342).base
      (withLsCallInv lsmpl (authMacHdrSpec F A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpin := authMacHdrPinned_placed_ok h_concat h_hmac h_dealloc
  simp only [authMacHdrSpec, withLsCallInv, authenticatorAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨
      (withLsCallInv lsmpl (authMacHdrPinnedSpec F A)).pre
        ⟨x.outVec, x.selfA, g, x.auth, x.ep, x.hdrRO, x.hdrA, x.hdr⟩ s0 ∗ R := by
    simpa only [authMacHdrPinnedSpec, withLsCallInv] using hpre
  refine hpin.mono_outcome ⟨x.outVec, x.selfA, g, x.auth, x.ep, x.hdrRO, x.hdrA, x.hdr⟩ R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hent :
        (withLsCallInv lsmpl (authMacHdrPinnedSpec F A)).post
          ⟨x.outVec, x.selfA, g, x.auth, x.ep, x.hdrRO, x.hdrA, x.hdr⟩ s0 sf ∗ R ⊢
        (withLsCallInv lsmpl (authMacHdrSpec F A)).post x s0 sf ∗ R := by
      apply sepConj_mono_left
      dsimp only [authMacHdrPinnedSpec, authMacHdrSpec, withLsCallInv]
      exact sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (authenticatorPinAt_entails_authenticatorAt A g x.selfA x.auth)))
    exact Satisfies.mono hent hpost
  · exact Or.inr (Or.inl ⟨hpan, hpost⟩)
  · exact Or.inr (Or.inr hex)

end CryptoVerification.SpqrV1.Auth
