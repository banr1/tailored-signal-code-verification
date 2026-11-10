/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonicalDecode
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.ModelProofDefs

/-!
# `<PublicKey>::is_canonical` (`0x3dc60`) and Shared Curve/XEdDSA Hook Bundles

Proves `ecPubKeyIsCanonical_call_ok` (and its contract-backed `tripleRatchetProgAtExt` counterpart)
for `<libsignal_core::curve::PublicKey>::is_canonical` (`0x3dc60`), and defines `StructuralPrims`,
`PqxdhHookContracts`, and `PqxdhHookContractsExt` shared with `VerifySignature`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.E2E.Pqxdh.Shared

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open SignalPqxdh

abbrev Bytes := SignalPqxdh.Bytes

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := rfl

theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setMem m).setPC pc).sp = s.sp := rfl

theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := rfl

theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setMem m).setPC pc).readReg64 r = s.readReg64 r := rfl

theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := rfl

theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setMem m).setPC pc).readReg32 r = s.readReg32 r := rfl

theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := rfl

theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setMem m).setPC pc).readReg w r = s.readReg w r := rfl

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

theorem bv_sub_sub_lit (x : BitVec 64) (a b : Nat) (_h : a + b < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]

theorem bv_add_neg64 (x : BitVec 64) :
    x + -64#64 = x - 64#64 := by bv_omega

attribute [local arm64_norm] bv_sub_sub_lit bv_add_neg64

/-! ## Byte Conversion and Memory Region Helpers -/

@[simp] theorem fitBytes_length (n : Nat) (bs : Bytes) : (fitBytes n bs).length = n := by
  simp [fitBytes]
  omega

theorem fitBytes_of_length_eq {n : Nat} {bs : Bytes} (h : bs.length = n) : fitBytes n bs = bs := by
  subst h
  simp [fitBytes]

def bytesToBv8 (bs : Bytes) : List (BitVec 8) :=
  bs.map (fun b => BitVec.ofNat 8 b.toNat)

def fitBv8 (n : Nat) (bs : Bytes) : List (BitVec 8) :=
  (bytesToBv8 bs).take n ++ List.replicate (n - (bytesToBv8 bs).length) 0#8

@[simp]
theorem fitBv8_length (n : Nat) (bs : Bytes) : (fitBv8 n bs).length = n := by
  simp [fitBv8]
  omega

theorem fitBv8_eq_bytesToBv8 {n : Nat} {bs : Bytes} (h : bs.length = n) :
    fitBv8 n bs = bytesToBv8 bs := by
  have hb : (bytesToBv8 bs).length = n := by simp [bytesToBv8, h]
  simp [fitBv8, hb]

def u64le (w : BitVec 64) : List (BitVec 8) :=
  unpack64 w

abbrev pqxdhHookStack : Nat := 4096
abbrev pqxdhEntryStack : Nat := 16384

theorem memRegion_cells (a : BitVec 64) (k : Nat) (h : 8 * k ≤ 2 ^ 64) :
    memRegion a (8 * k) = cells a k :=
  ProofLib.memRegion_cells a k h

theorem stackAt_split_cells (sp : BitVec 64) (n k : Nat) (h : n + 8 * k ≤ 2 ^ 64) :
    stackAt sp (n + 8 * k) =
      stackAt (sp - BitVec.ofNat 64 (8 * k)) n ∗ cells (sp - BitVec.ofNat 64 (8 * k)) k :=
  ProofLib.stackAt_split_cells sp n k h

/-! ## Curve25519-Dalek and SHA-512 Hook Contracts -/

abbrev ecPubKeyIsCanonicalSym : String :=
  "<libsignal_core::curve::PublicKey>::is_canonical"
abbrev verifySignatureSym : String :=
  "<libsignal_core::curve::PublicKey>::verify_signature"
abbrev verifySignatureMultipartSym : String :=
  "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message"

abbrev sha512CompressStub : String := "sha2::sha512::compress512"
abbrev dalekScalarWideStub : String :=
  "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide"
abbrev dalekScalarModStub : String :=
  "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order"
abbrev dalekCompressStub : String :=
  "<curve25519_dalek::edwards::EdwardsPoint>::compress"
abbrev dalekMontToEdStub : String :=
  "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards"
abbrev dalekTorsionFreeStub : String :=
  "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free"
abbrev dalekEdNegStub : String :=
  "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg"
abbrev dalekDoubleMulStub : String :=
  "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint"

structure CryptoUnaryGhost where
  inPtr   : BitVec 64
  inBytes : Bytes

def cryptoBoolRegStubSpec (pred : Bytes → Bool) (inLen : Nat) (_img : Obj.Image := default) :
    Spec CryptoUnaryGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧
      g.inBytes.length = inLen⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 32 = (if pred g.inBytes then 1#32 else 0#32)⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      stackAt s0.sp pqxdhHookStack

structure CryptoLeafCall where
  inPtr   : BitVec 64
  inBytes : Bytes
  outPtr  : BitVec 64

def cryptoLeafStubSpec (fn : Bytes → Bytes) (inLen outLen : Nat) : Spec CryptoLeafCall where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inBytes.length = inLen⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      memRegion g.outPtr outLen ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      (g.outPtr ↦ₛ fitBv8 outLen (fn g.inBytes)) ∗
      stackAt s0.sp pqxdhHookStack

def revWords64 (bs : Bytes) : Bytes :=
  ((bs.take 8).reverse ++
   ((bs.drop 8).take 8).reverse ++
   ((bs.drop 16).take 8).reverse ++
   ((bs.drop 24).take 8).reverse ++
   ((bs.drop 32).take 8).reverse ++
   ((bs.drop 40).take 8).reverse ++
   ((bs.drop 48).take 8).reverse ++
   ((bs.drop 56).take 8).reverse)

def sha512CompressOutBytes (P : Primitives) (stateBytes blockBytes : Bytes) : Bytes :=
  revWords64 (fitBytes 64
    ((chunkBlocks 128 blockBytes).foldl (sha512Step P) (revWords64 stateBytes)))

structure CryptoCompressGhost where
  statePtr   : BitVec 64
  stateBytes : Bytes
  blocksPtr  : BitVec 64
  blockBytes : Bytes
  nBlocks    : Nat

def compressInPlaceStubSpec (fn : Bytes → Bytes → Bytes) (stateLen blockLen : Nat)
    (_img : Obj.Image := default) : Spec CryptoCompressGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.statePtr ∧
      s.readReg64 .x1 = g.blocksPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 g.nBlocks ∧
      g.nBlocks < 2 ^ 64 ∧
      g.stateBytes.length = stateLen ∧
      g.blockBytes.length = blockLen * g.nBlocks⌝ ∗
      (g.statePtr ↦ₛ bytesToBv8 g.stateBytes) ∗
      (g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.statePtr ↦ₛ fitBv8 stateLen (fn g.stateBytes g.blockBytes)) ∗
      (g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗
      stackAt s0.sp pqxdhHookStack

def dalekMontToEdOutAt (P : Primitives) (outPtr : BitVec 64) (inBytes : Bytes)
    (signBit : UInt8) : SepProp :=
  match P.montToEd inBytes signBit with
  | some edPt => outPtr ↦ₛ (u64le 1#64 ++ fitBv8 160 edPt)
  | none      => (outPtr ↦₆₄ 0#64) ∗ memRegion (outPtr + 8#64) 160

structure DalekMontToEdGhost where
  inBytes : Bytes
  signBit : UInt8
  inPtr   : BitVec 64
  outPtr  : BitVec 64

def dalekMontToEdStubSpec (P : Primitives) (_img : Obj.Image := default) :
    Spec DalekMontToEdGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧
      (s.readReg64 .x1).setWidth 8 = BitVec.ofNat 8 g.signBit.toNat ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inBytes.length = 32⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      memRegion g.outPtr 168 ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      dalekMontToEdOutAt P g.outPtr g.inBytes (g.signBit &&& 1) ∗
      stackAt s0.sp pqxdhHookStack

theorem signBit_shr7_and_one (b : UInt8) :
    (((b &&& 0x80) >>> 7) &&& 1 : UInt8) = ((b &&& 0x80) >>> 7 : UInt8) := by
  have h : ∀ i : Fin 256,
      (((UInt8.ofBitVec (BitVec.ofFin i) &&& 0x80) >>> 7) &&& 1 : UInt8) =
        ((UInt8.ofBitVec (BitVec.ofFin i) &&& 0x80) >>> 7 : UInt8) := by decide
  rcases b with ⟨⟨i⟩⟩
  exact h i

structure DalekDoubleMulGhost where
  hBytes    : Bytes
  negABytes : Bytes
  sBytes    : Bytes
  hPtr      : BitVec 64
  negAPtr   : BitVec 64
  sPtr      : BitVec 64
  outPtr    : BitVec 64

def dalekDoubleMulStubSpec (P : Primitives) (_img : Obj.Image := default) :
    Spec DalekDoubleMulGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.hPtr ∧
      s.readReg64 .x1 = g.negAPtr ∧
      s.readReg64 .x2 = g.sPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.hBytes.length = 32 ∧
      g.negABytes.length = 160 ∧
      g.sBytes.length = 32⌝ ∗
      (g.hPtr ↦ₛ bytesToBv8 g.hBytes) ∗
      (g.negAPtr ↦ₛ bytesToBv8 g.negABytes) ∗
      (g.sPtr ↦ₛ bytesToBv8 g.sBytes) ∗
      memRegion g.outPtr 160 ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.hPtr ↦ₛ bytesToBv8 g.hBytes) ∗
      (g.negAPtr ↦ₛ bytesToBv8 g.negABytes) ∗
      (g.sPtr ↦ₛ bytesToBv8 g.sBytes) ∗
      (g.outPtr ↦ₛ fitBv8 160 (P.doubleScalarMulBasepoint g.hBytes g.negABytes g.sBytes)) ∗
      stackAt s0.sp pqxdhHookStack

theorem zext64_bv32_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    ((b3 ++ (b2 ++ (b1 ++ b0))).zeroExtend 64).setWidth 8 = b0 := by
  rw [BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le _ (by decide)]
  simp only [BitVec.setWidth_append, ↓reduceDIte]
  exact BitVec.setWidth_eq b0

theorem zext64_bv32_shr8_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    (((b3 ++ (b2 ++ (b1 ++ b0))).zeroExtend 64) >>> 8#64).setWidth 8 = b1 := by
  bv_bits

theorem zext64_bv32_shr16_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    (((b3 ++ (b2 ++ (b1 ++ b0))).zeroExtend 64) >>> 16#64).setWidth 8 = b2 := by
  bv_bits

theorem zext64_bv32_shr24_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    (((b3 ++ (b2 ++ (b1 ++ b0))).zeroExtend 64) >>> 24#64).setWidth 8 = b3 := by
  bv_bits

theorem zext64_bv16_setWidth_8 (b0 b1 : BitVec 8) :
    ((b1 ++ b0).zeroExtend 64).setWidth 8 = b0 := by
  rw [BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le _ (by decide)]
  simp only [BitVec.setWidth_append, ↓reduceDIte]
  exact BitVec.setWidth_eq b0

theorem zext64_bv16_shr8_setWidth_8 (b0 b1 : BitVec 8) :
    (((b1 ++ b0).zeroExtend 64) >>> 8#64).setWidth 8 = b1 := by
  bv_bits

theorem zext64_bv8_setWidth_8 (b0 : BitVec 8) :
    (b0.zeroExtend 64).setWidth 8 = b0 := by
  rw [BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- Structural length, totality, and reference-equivalence laws on `SignalPqxdh.Primitives`
used by machine-code refinement proofs. Unlike `SignalPqxdh.WellFormedPrimitives`, these properties
hold unconditionally for `modelPrims X W` (`structuralPrims_modelPrims`). -/
structure StructuralPrims (P : Primitives) : Prop where
  sha256Compress_len           : ∀ st blk, (P.sha256Compress st blk).length = 32
  sha512Compress_len           : ∀ st blk, (P.sha512Compress st blk).length = 64
  aesEncBlock_len              : ∀ k blk, (P.aesEncBlock k blk).length = 16
  aesDecBlock_len              : ∀ k blk, (P.aesDecBlock k blk).length = 16
  sha512_eq_ref                : ∀ m, P.sha512 m = sha512Ref P m
  hkdfDerive96_eq_ref          : ∀ secrets, P.hkdfDerive96 secrets = hkdfDerive96Ref P secrets
  rootCreateChain_eq_ref       : ∀ rk dh, P.rootCreateChain rk dh = rootCreateChainRef P rk dh
  chainKdfSeed_eq_ref          : ∀ ck, P.chainKdfSeed ck = chainKdfSeedRef P ck
  chainKdfNext_eq_ref          : ∀ ck, P.chainKdfNext ck = chainKdfNextRef P ck
  deriveMsgKeys_eq_ref         :
    ∀ mkSeed salt?, P.deriveMsgKeys mkSeed salt? = deriveMsgKeysRef P mkSeed salt?
  aeadEnc_eq_ref               : ∀ mk ad pt, P.aeadEnc mk ad pt = aes256CbcHmacEncRef P mk ad pt
  aeadDec_eq_ref               : ∀ mk ad ct, P.aeadDec mk ad ct = aes256CbcHmacDecRef P mk ad ct
  sigVerify_eq_xeddsaVerifyRef : ∀ pk m sig, P.sigVerify pk m sig = xeddsaVerifyRef P pk m sig
  isCanonical_eq_isCanonicalRef : ∀ pk, P.isCanonical pk = isCanonicalRef P pk
  x25519_len                   : ∀ k p, (P.x25519 k p).length = 32
  x25519Base_len               : ∀ k, (P.x25519Base k).length = 32
  sha512_len                   : ∀ m, (P.sha512 m).length = 64
  scalarFromBytesModOrder_len  : ∀ b, (P.scalarFromBytesModOrder b).length = 32
  scalarFromWide_len           : ∀ b, (P.scalarFromWide b).length = 32
  montToEd_len                 : ∀ u s pt, P.montToEd u s = some pt → pt.length = 160
  edNeg_len                    : ∀ pt, (P.edNeg pt).length = 160
  doubleScalarMulBasepoint_len : ∀ h a s, (P.doubleScalarMulBasepoint h a s).length = 160
  compress_len                 : ∀ pt, (P.compress pt).length = 32
  kemEncaps_isSome             : ∀ pk r, pk.length = 1568 → r.length = 32 →
                                   (P.kemEncaps pk r).isSome = true
  kemEncaps_len                : ∀ pk r ss ct,
                                   P.kemEncaps pk r = some (ss, ct) →
                                   ss.length = 32 ∧ ct.length = 1568
  kemDecaps_isSome             : ∀ sk ct, sk.length = 3168 → ct.length = 1568 →
                                   (P.kemDecaps sk ct).isSome = true
  kemDecaps_len                : ∀ sk ct ss,
                                   P.kemDecaps sk ct = some ss →
                                   ss.length = 32
  spqrInitSend_some            : ∀ k r, (P.spqrInitSend k r).isSome = true

theorem structuralPrims_of_wellFormedPrimitives {P : Primitives}
    (hWF : SignalPqxdh.WellFormedPrimitives P) : StructuralPrims P where
  sha256Compress_len           := hWF.sha256Compress_len
  sha512Compress_len           := hWF.sha512Compress_len
  aesEncBlock_len              := hWF.aesEncBlock_len
  aesDecBlock_len              := hWF.aesDecBlock_len
  sha512_eq_ref                := hWF.sha512_eq_ref
  hkdfDerive96_eq_ref          := hWF.hkdfDerive96_eq_ref
  rootCreateChain_eq_ref       := hWF.rootCreateChain_eq_ref
  chainKdfSeed_eq_ref          := hWF.chainKdfSeed_eq_ref
  chainKdfNext_eq_ref          := hWF.chainKdfNext_eq_ref
  deriveMsgKeys_eq_ref         := hWF.deriveMsgKeys_eq_ref
  aeadEnc_eq_ref               := hWF.aeadEnc_eq_ref
  aeadDec_eq_ref               := hWF.aeadDec_eq_ref
  sigVerify_eq_xeddsaVerifyRef := hWF.sigVerify_eq_xeddsaVerifyRef
  isCanonical_eq_isCanonicalRef := hWF.isCanonical_eq_isCanonicalRef
  x25519_len                   := hWF.x25519_len
  x25519Base_len               := hWF.x25519Base_len
  sha512_len                   := hWF.sha512_len
  scalarFromBytesModOrder_len  := hWF.scalarFromBytesModOrder_len
  scalarFromWide_len           := hWF.scalarFromWide_len
  montToEd_len                 := hWF.montToEd_len
  edNeg_len                    := hWF.edNeg_len
  doubleScalarMulBasepoint_len := hWF.doubleScalarMulBasepoint_len
  compress_len                 := hWF.compress_len
  kemEncaps_isSome             := hWF.kemEncaps_isSome
  kemEncaps_len                := hWF.kemEncaps_len
  kemDecaps_isSome             := hWF.kemDecaps_isSome
  kemDecaps_len                := hWF.kemDecaps_len
  spqrInitSend_some            := hWF.spqrInitSend_some

structure KeyCanonicalGhost where
  keyPtr   : BitVec 64
  keyBytes : Bytes

/-- External hook contracts required by shared curve/signature functions (`is_canonical`,
    `verify_signature_for_multipart_message`, and `verify_signature`). -/
structure PqxdhHookContracts (P : Primitives) (_A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) : Prop where
  dalekMontToEd    : HookSat absHooks dalekMontToEdStub (dalekMontToEdStubSpec P img)
  dalekTorsionFree : HookSat absHooks dalekTorsionFreeStub
                       (cryptoBoolRegStubSpec P.isTorsionFree 160 img)
  sha512Compress   : HookSat absHooks sha512CompressStub
                       (compressInPlaceStubSpec (sha512CompressOutBytes P) 64 128 img)
  dalekScalarWide  : HookSat absHooks dalekScalarWideStub
                       (cryptoLeafStubSpec P.scalarFromWide 64 32)
  dalekScalarMod   : HookSat absHooks dalekScalarModStub
                       (cryptoLeafStubSpec P.scalarFromBytesModOrder 32 32)
  dalekCompress    : HookSat absHooks dalekCompressStub
                       (cryptoLeafStubSpec P.compress 160 32)
  dalekEdNeg       : HookSat absHooks dalekEdNegStub
                       (cryptoLeafStubSpec P.edNeg 160 160)
  dalekDoubleMul   : HookSat absHooks dalekDoubleMulStub
                       (dalekDoubleMulStubSpec P img)

theorem hookSat_tripleRatchetExterns'_trap {α : Type} (C : Crypto)
    (absHooks : String → Option (State → State)) {sym : String} {spec : Spec α}
    (heq : trTrapExterns C absHooks sym = absHooks sym)
    (h : HookSat absHooks sym spec) :
    HookSat (trTrapExterns C absHooks) sym spec := by
  unfold HookSat at *; rwa [heq]

theorem hookSat_tripleRatchetExterns' {α : Type} (C : Crypto) (ctl : BitVec 64)
    (absHooks : String → Option (State → State)) {sym : String} {spec : Spec α}
    (heq : tripleRatchetExterns C ctl absHooks sym = absHooks sym)
    (h : HookSat absHooks sym spec) :
    HookSat (tripleRatchetExterns C ctl absHooks) sym spec := by
  unfold HookSat at *; rwa [heq]

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  libsignalSessionCode_fnOff_0x3dd44
  libsignalSessionCode_fnOff_0x3de30
  libsignalSessionCode_fnOff_0x3de58
  (ls_stub% "memset")
  (ls_stub% "memcpy")
  (ls_stub% "sha2::sha512::compress512")
  (ls_stub% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide")
  (ls_stub% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order")
  (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint>::compress")
  (ls_stub% "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards")
  (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free")
  (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg")
  (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint")
  (ls_hook% "memset")
  (ls_hook% "memcpy")
  (ls_hook% "sha2::sha512::compress512")
  (ls_hook% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide")
  (ls_hook% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order")
  (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint>::compress")
  (ls_hook% "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards")
  (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free")
  (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg")
  (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint")

theorem dalekMontToEd_ok_at_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hH : PqxdhHookContracts P A img absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekMontToEdStub := by fnoff_eq) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr name + BitVec.ofNat 64 k)
      (dalekMontToEdStubSpec P img) :=
  hook_ok_at (hname := dalekMontToEdStub) rfl hk
    (by fnoff_eq)
    (by fnoff_eq) (by simp [Rust.isPanicSymbol, dalekMontToEdStub])
    (hookSat_tripleRatchetExterns'_trap C absHooks rfl hH.dalekMontToEd)

theorem dalekMontToEd_ok_at {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hH : PqxdhHookContracts P A img absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekMontToEdStub := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr name + BitVec.ofNat 64 k)
      (dalekMontToEdStubSpec P img) := by
  rw [← trTrapProgAt_fnAddr_eq img.base C ctl absHooks name]
  exact subroutine_ok_kit_of_trTrap (dalekMontToEd_ok_at_trap hH hk)

theorem dalekTorsionFree_ok_at_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hH : PqxdhHookContracts P A img absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekTorsionFreeStub := by fnoff_eq) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoBoolRegStubSpec P.isTorsionFree 160 img) :=
  hook_ok_at (hname := dalekTorsionFreeStub) rfl hk
    (by fnoff_eq)
    (by fnoff_eq) (by simp [Rust.isPanicSymbol, dalekTorsionFreeStub])
    (hookSat_tripleRatchetExterns'_trap C absHooks rfl hH.dalekTorsionFree)

theorem dalekTorsionFree_ok_at {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hH : PqxdhHookContracts P A img absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekTorsionFreeStub := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoBoolRegStubSpec P.isTorsionFree 160 img) := by
  rw [← trTrapProgAt_fnAddr_eq img.base C ctl absHooks name]
  exact subroutine_ok_kit_of_trTrap (dalekTorsionFree_ok_at_trap hH hk)

/-! ## `<libsignal_core::curve::PublicKey>::is_canonical` (`0x3dc60`) -/

def ecPubKeyIsCanonicalCallSpec (P : Primitives) : Spec KeyCanonicalGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.keyPtr ∧ g.keyBytes.length = 32⌝ ∗
    (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗
    stackAt s.sp (pqxdhHookStack + 400)
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 8 = (if P.isCanonicalEC g.keyBytes then 1#8 else 0#8)⌝ ∗
    (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗
    stackAt s0.sp (pqxdhHookStack + 400)

theorem stackAt_ecPubKeyIsCanonical_call (sp : BitVec 64) :
    stackAt sp (pqxdhHookStack + 400) =
      stackAt (sp - 400#64) pqxdhHookStack ∗
      cells (sp - 400#64) 4 ∗
      memRegion (sp - 368#64) 8 ∗
      memRegion (sp - 360#64) 168 ∗
      memRegion (sp - 192#64) 160 ∗
      cells (sp - 32#64) 4 := by
  rw [show (pqxdhHookStack + 400 : Nat) = pqxdhHookStack + 8 * 50 by decide,
    stackAt_split_cells sp pqxdhHookStack 50 (by decide),
    ← memRegion_cells (sp - 400#64) 50 (by decide)]
  change stackAt (sp - 400#64) pqxdhHookStack ∗ memRegion (sp - 400#64) 400 = _
  rw [memRegion_split (sp - 400#64) 32 368 (by decide),
    memRegion_cells (sp - 400#64) 4 (by decide),
    memRegion_split (sp - 400#64 + 32#64) 8 360 (by decide),
    memRegion_split (sp - 400#64 + 32#64 + 8#64) 168 192 (by decide),
    memRegion_split (sp - 400#64 + 32#64 + 8#64 + 168#64) 160 32 (by decide),
    memRegion_cells (sp - 400#64 + 32#64 + 8#64 + 168#64 + 160#64) 4 (by decide)]
  have h1 : sp - 400#64 + 32#64 = sp - 368#64 := by bv_arith
  have h2 : sp - 400#64 + 32#64 + 8#64 = sp - 360#64 := by bv_arith
  have h3 : sp - 400#64 + 32#64 + 8#64 + 168#64 = sp - 192#64 := by bv_arith
  have h4 : sp - 400#64 + 32#64 + 8#64 + 168#64 + 160#64 = sp - 32#64 := by bv_arith
  rw [h4, h3, h2, h1]

theorem dalekMontToEdOutAt_none (P : Primitives) (keyBytes : Bytes) (signBit : UInt8)
    (hmont : P.montToEd keyBytes signBit = none) (a : BitVec 64) :
    dalekMontToEdOutAt P a keyBytes signBit =
      (a ↦₆₄ 0#64) ∗ memRegion (a + 8#64) 160 := by
  simp only [dalekMontToEdOutAt, hmont]

theorem dalekMontToEdOutAt_some (P : Primitives) (keyBytes edPt : Bytes) (signBit : UInt8)
    (hmont : P.montToEd keyBytes signBit = some edPt) (hlen : edPt.length = 160) (a : BitVec 64) :
    dalekMontToEdOutAt P a keyBytes signBit =
      (a ↦₆₄ 1#64) ∗ ((a + 8#64) ↦ₛ bytesToBv8 edPt) := by
  simp only [dalekMontToEdOutAt, hmont, fitBv8_eq_bytesToBv8 hlen]
  have hu : u64le 1#64 = unpack64 1#64 := rfl
  rw [hu, pointsToBytes_append, show (unpack64 1#64).length = 8 by rfl,
    ← pointsTo64_eq_pointsToBytes]

private theorem memRegion168_of_cell_and_memRegion160 (a : BitVec 64) (v : BitVec 64)
    (R_tail : SepProp) :
    (a ↦₆₄ v) ∗ memRegion (a + 8#64) 160 ∗ R_tail ⊢ memRegion a 168 ∗ R_tail := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right v (Entails.refl _)
  refine Entails.trans (sepConj_mono_left h1) ?_
  rw [← sepConj_assoc, ← memRegion_split a 8 160 (by decide)]
  exact Entails.refl _

private theorem memRegion168_of_cell_and_bytes160 (a : BitVec 64) (v : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) (R_tail : SepProp) :
    (a ↦₆₄ v) ∗ ((a + 8#64) ↦ₛ bs) ∗ R_tail ⊢ memRegion a 168 ∗ R_tail := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right v (Entails.refl _)
  have h2 : ((a + 8#64) ↦ₛ bs) ⊢ memRegion (a + 8#64) 160 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (a + 8#64) bs
  refine Entails.trans (sepConj_mono_left h1) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h2)) ?_
  rw [← sepConj_assoc, ← memRegion_split a 8 160 (by decide)]
  exact Entails.refl _

private theorem memRegion160_of_bytes160 (a : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) (R_tail : SepProp) :
    (a ↦ₛ bs) ∗ R_tail ⊢ memRegion a 160 ∗ R_tail := by
  have h1 : (a ↦ₛ bs) ⊢ memRegion a 160 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion a bs
  exact sepConj_mono_left h1

private theorem exists_unpack64_of_length_160 {bs : List (BitVec 8)} (h : bs.length = 160) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64,
      ∀ a R_tail,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1 ∗ ((a + 16#64) ↦₆₄ w2 ∗ ((a + 24#64) ↦₆₄ w3 ∗
        ((a + 32#64) ↦₆₄ w4 ∗ ((a + 40#64) ↦₆₄ w5 ∗ ((a + 48#64) ↦₆₄ w6 ∗ ((a + 56#64) ↦₆₄ w7 ∗
        ((a + 64#64) ↦₆₄ w8 ∗ ((a + 72#64) ↦₆₄ w9 ∗ ((a + 80#64) ↦₆₄ w10 ∗ ((a + 88#64) ↦₆₄ w11 ∗
        ((a + 96#64) ↦₆₄ w12 ∗ ((a + 104#64) ↦₆₄ w13 ∗ ((a + 112#64) ↦₆₄ w14 ∗
        ((a + 120#64) ↦₆₄ w15 ∗ ((a + 128#64) ↦₆₄ w16 ∗ ((a + 136#64) ↦₆₄ w17 ∗
        ((a + 144#64) ↦₆₄ w18 ∗ ((a + 152#64) ↦₆₄ w19 ∗
         R_tail))))))))))))))))))) =
        (a ↦ₛ bs) ∗ R_tail := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h2 : ((bs.drop 64).take 32).length = 32 := by simp [h]
  have h3 : ((bs.drop 96).take 32).length = 32 := by simp [h]
  have h4 : (bs.drop 128).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w8, w9, w10, w11, _, hp2⟩ := exists_unpack64_of_length_32 h2
  obtain ⟨w12, w13, w14, w15, _, hp3⟩ := exists_unpack64_of_length_32 h3
  obtain ⟨w16, w17, w18, w19, _, hp4⟩ := exists_unpack64_of_length_32 h4
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, fun a R_tail => ?_⟩
  have hsplit : bs = bs.take 32 ++ ((bs.drop 32).take 32 ++
      ((bs.drop 64).take 32 ++ ((bs.drop 96).take 32 ++ bs.drop 128))) := by
    have s4 : bs.drop 96 = (bs.drop 96).take 32 ++ bs.drop 128 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 96)).symm
    have s3 : bs.drop 64 = (bs.drop 64).take 32 ++ bs.drop 96 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 64)).symm
    have s2 : bs.drop 32 = (bs.drop 32).take 32 ++ bs.drop 64 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 32)).symm
    have s1 : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
    rw [s4] at s3
    rw [s3] at s2
    rw [s2] at s1
    exact s1
  symm
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0,
    pointsToBytes_append, h1, hp1,
    pointsToBytes_append, h2, hp2,
    pointsToBytes_append, h3, hp3, hp4]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sepWP_memRegion160_head {prog : Program} {ret : BitVec 64} {s : State}
    (a : BitVec 64) {P_pre F_rest : SepProp}
    (heq : P_pre = memRegion a 160 ∗ F_rest) {Q : State → SepProp → Prop}
    (h : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 : BitVec 64,
      SepWP prog ret s
        ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1 ∗ ((a + 16#64) ↦₆₄ u2 ∗ ((a + 24#64) ↦₆₄ u3 ∗
        ((a + 32#64) ↦₆₄ u4 ∗ ((a + 40#64) ↦₆₄ u5 ∗ ((a + 48#64) ↦₆₄ u6 ∗ ((a + 56#64) ↦₆₄ u7 ∗
        ((a + 64#64) ↦₆₄ u8 ∗ ((a + 72#64) ↦₆₄ u9 ∗ ((a + 80#64) ↦₆₄ u10 ∗ ((a + 88#64) ↦₆₄ u11 ∗
        ((a + 96#64) ↦₆₄ u12 ∗ ((a + 104#64) ↦₆₄ u13 ∗ ((a + 112#64) ↦₆₄ u14 ∗
        ((a + 120#64) ↦₆₄ u15 ∗ ((a + 128#64) ↦₆₄ u16 ∗ ((a + 136#64) ↦₆₄ u17 ∗
        ((a + 144#64) ↦₆₄ u18 ∗ ((a + 152#64) ↦₆₄ u19 ∗
         F_rest)))))))))))))))))))) Q) :
    SepWP prog ret s P_pre Q := by
  rw [heq, memRegion_eq_exists_bytes a 160 (by decide), sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hlen => ?_
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15,
    u16, u17, u18, u19, hbs⟩ :=
    exists_unpack64_of_length_160 hlen
  rw [← hbs a F_rest]
  exact h u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19


private theorem bytesToBv8_getD (bs : Bytes) (i : Nat) :
    (bytesToBv8 bs).getD i 0#8 = (bs.getD i 0).toBitVec := by
  induction bs generalizing i with
  | nil => simp [bytesToBv8]
  | cons b rest ih =>
    cases i with
    | zero => rcases b with ⟨⟨val, isLt⟩⟩; simp [bytesToBv8]
    | succ j => exact ih j

private theorem uint8_getLsbD7_eq_true_iff (b : UInt8) :
    b.toBitVec.getLsbD 7 = true ↔ ((b &&& 0x80) == 0) = false := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_getLsbD7_eq_false_iff (b : UInt8) :
    b.toBitVec.getLsbD 7 = false ↔ ((b &&& 0x80) == 0) = true := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_ult237_eq_true_iff (b : UInt8) :
    (BitVec.zeroExtend 64 b.toBitVec).ult 237#64 = true ↔ decide (b ≥ 0xED) = false := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_ult237_eq_false_iff (b : UInt8) :
    (BitVec.zeroExtend 64 b.toBitVec).ult 237#64 = false ↔ decide (b ≥ 0xED) = true := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_b31_7f_eq (b : UInt8) (h7 : ((b &&& 0x80) == 0) = true) :
    (BitVec.truncate 32 (BitVec.signExtend 64 b.toBitVec) == 127#32) = ((b &&& 0x7F) == 0x7F) := by
  rcases b with ⟨bv⟩
  revert bv h7; decide

private theorem uint8_toBitVec_eq_ff_iff (b : UInt8) :
    (b.toBitVec = 0xff#8) ↔ (b = 0xFF) := by
  rcases b with ⟨bv⟩
  constructor
  · intro h; subst h; rfl
  · intro h; exact congrArg UInt8.toBitVec h

private theorem bv64_add1_eq_zero_iff (x : BitVec 64) :
    (x + 1#64 == 0#64) = (x == 0xffffffffffffffff#64) := by
  bv_bits

private theorem bv64_allOnes_getElem (i : Nat) (hi : i < 64) :
    (0xffffffffffffffff#64 : BitVec 64)[i] = true := by
  revert i hi; decide

private theorem bv64_and_eq_allOnes_iff (a b : BitVec 64) :
    (a &&& b = 0xffffffffffffffff#64) ↔
      (a = 0xffffffffffffffff#64 ∧ b = 0xffffffffffffffff#64) := by
  constructor
  · intro h
    constructor
    · ext i hi
      have hi' := congrArg (fun v : BitVec 64 => v[i]) h
      rw [BitVec.getElem_and, bv64_allOnes_getElem i hi, Bool.and_eq_true] at hi'
      rw [bv64_allOnes_getElem i hi]
      exact hi'.1
    · ext i hi
      have hi' := congrArg (fun v : BitVec 64 => v[i]) h
      rw [BitVec.getElem_and, bv64_allOnes_getElem i hi, Bool.and_eq_true] at hi'
      rw [bv64_allOnes_getElem i hi]
      exact hi'.2
  · rintro ⟨rfl, rfl⟩; rfl

private theorem pack64_eq_allOnes_iff (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7 = 0xffffffffffffffff#64) ↔
      (b0 = 0xff#8 ∧ b1 = 0xff#8 ∧ b2 = 0xff#8 ∧ b3 = 0xff#8 ∧
       b4 = 0xff#8 ∧ b5 = 0xff#8 ∧ b6 = 0xff#8 ∧ b7 = 0xff#8) := by
  unfold pack64
  bv_bits

private theorem list_take_drop_succ (xs : List UInt8) (i n : Nat) (hi : i < xs.length) :
    (xs.drop i).take (n + 1) = xs.getD i 0 :: (xs.drop (i + 1)).take n := by
  have hget : xs.getD i 0 = xs[i] := by simp [List.getD, hi]
  rw [List.drop_eq_getElem_cons hi, ← hget]
  rfl

private theorem list32_drop1_take30_eq (xs : List UInt8) (h : xs.length = 32) :
    (xs.drop 1).take 30 =
      [xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0, xs.getD 6 0,
       xs.getD 7 0, xs.getD 8 0, xs.getD 9 0, xs.getD 10 0, xs.getD 11 0, xs.getD 12 0,
       xs.getD 13 0, xs.getD 14 0, xs.getD 15 0, xs.getD 16 0, xs.getD 17 0, xs.getD 18 0,
       xs.getD 19 0, xs.getD 20 0, xs.getD 21 0, xs.getD 22 0, xs.getD 23 0, xs.getD 24 0,
       xs.getD 25 0, xs.getD 26 0, xs.getD 27 0, xs.getD 28 0, xs.getD 29 0, xs.getD 30 0] := by
  repeat (rw [list_take_drop_succ _ _ _ (by omega)])
  rfl

private theorem list32_drop1_take30_eq_replicate_iff (xs : List UInt8) (h : xs.length = 32) :
    ((xs.drop 1).take 30 == List.replicate 30 0xFF) = true ↔
      (xs.getD 1 0 = 0xFF ∧ xs.getD 2 0 = 0xFF ∧ xs.getD 3 0 = 0xFF ∧ xs.getD 4 0 = 0xFF ∧
       xs.getD 5 0 = 0xFF ∧ xs.getD 6 0 = 0xFF ∧ xs.getD 7 0 = 0xFF ∧ xs.getD 8 0 = 0xFF ∧
       xs.getD 9 0 = 0xFF ∧ xs.getD 10 0 = 0xFF ∧ xs.getD 11 0 = 0xFF ∧ xs.getD 12 0 = 0xFF ∧
       xs.getD 13 0 = 0xFF ∧ xs.getD 14 0 = 0xFF ∧ xs.getD 15 0 = 0xFF ∧ xs.getD 16 0 = 0xFF ∧
       xs.getD 17 0 = 0xFF ∧ xs.getD 18 0 = 0xFF ∧ xs.getD 19 0 = 0xFF ∧ xs.getD 20 0 = 0xFF ∧
       xs.getD 21 0 = 0xFF ∧ xs.getD 22 0 = 0xFF ∧ xs.getD 23 0 = 0xFF ∧ xs.getD 24 0 = 0xFF ∧
       xs.getD 25 0 = 0xFF ∧ xs.getD 26 0 = 0xFF ∧ xs.getD 27 0 = 0xFF ∧ xs.getD 28 0 = 0xFF ∧
       xs.getD 29 0 = 0xFF ∧ xs.getD 30 0 = 0xFF) := by
  rw [beq_iff_eq, list32_drop1_take30_eq xs h]
  change [xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0, xs.getD 6 0,
       xs.getD 7 0, xs.getD 8 0, xs.getD 9 0, xs.getD 10 0, xs.getD 11 0, xs.getD 12 0,
       xs.getD 13 0, xs.getD 14 0, xs.getD 15 0, xs.getD 16 0, xs.getD 17 0, xs.getD 18 0,
       xs.getD 19 0, xs.getD 20 0, xs.getD 21 0, xs.getD 22 0, xs.getD 23 0, xs.getD 24 0,
       xs.getD 25 0, xs.getD 26 0, xs.getD 27 0, xs.getD 28 0, xs.getD 29 0, xs.getD 30 0] =
      [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
       0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
       0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] ↔ _
  simp only [List.cons.injEq, and_true]

private theorem pack64_4_allOnes_eq_drop1_take30 (keyBytes : Bytes) (h : keyBytes.length = 32) :
    ((pack64 ((bytesToBv8 keyBytes).getD 1 0#8) ((bytesToBv8 keyBytes).getD 2 0#8)
              ((bytesToBv8 keyBytes).getD 3 0#8) ((bytesToBv8 keyBytes).getD 4 0#8)
              ((bytesToBv8 keyBytes).getD 5 0#8) ((bytesToBv8 keyBytes).getD 6 0#8)
              ((bytesToBv8 keyBytes).getD 7 0#8) ((bytesToBv8 keyBytes).getD 8 0#8) &&&
            pack64 ((bytesToBv8 keyBytes).getD 9 0#8) ((bytesToBv8 keyBytes).getD 10 0#8)
              ((bytesToBv8 keyBytes).getD 11 0#8) ((bytesToBv8 keyBytes).getD 12 0#8)
              ((bytesToBv8 keyBytes).getD 13 0#8) ((bytesToBv8 keyBytes).getD 14 0#8)
              ((bytesToBv8 keyBytes).getD 15 0#8) ((bytesToBv8 keyBytes).getD 16 0#8) &&&
          (pack64 ((bytesToBv8 keyBytes).getD 17 0#8) ((bytesToBv8 keyBytes).getD 18 0#8)
              ((bytesToBv8 keyBytes).getD 19 0#8) ((bytesToBv8 keyBytes).getD 20 0#8)
              ((bytesToBv8 keyBytes).getD 21 0#8) ((bytesToBv8 keyBytes).getD 22 0#8)
              ((bytesToBv8 keyBytes).getD 23 0#8) ((bytesToBv8 keyBytes).getD 24 0#8) &&&
            pack64 ((bytesToBv8 keyBytes).getD 23 0#8) ((bytesToBv8 keyBytes).getD 24 0#8)
              ((bytesToBv8 keyBytes).getD 25 0#8) ((bytesToBv8 keyBytes).getD 26 0#8)
              ((bytesToBv8 keyBytes).getD 27 0#8) ((bytesToBv8 keyBytes).getD 28 0#8)
              ((bytesToBv8 keyBytes).getD 29 0#8) ((bytesToBv8 keyBytes).getD 30 0#8))) +
        1#64 == 0#64) =
      ((keyBytes.drop 1).take 30 == List.replicate 30 0xFF) := by
  rw [bv64_add1_eq_zero_iff]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, bv64_and_eq_allOnes_iff, bv64_and_eq_allOnes_iff, bv64_and_eq_allOnes_iff,
    pack64_eq_allOnes_iff, pack64_eq_allOnes_iff, pack64_eq_allOnes_iff, pack64_eq_allOnes_iff,
    list32_drop1_take30_eq_replicate_iff keyBytes h]
  simp only [bytesToBv8_getD, uint8_toBitVec_eq_ff_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15, h16⟩⟩,
            ⟨h17, h18, h19, h20, h21, h22, h23, h24⟩, ⟨_, _, h25, h26, h27, h28, h29, h30⟩⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
           h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
            h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩
    exact ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15, h16⟩⟩,
           ⟨h17, h18, h19, h20, h21, h22, h23, h24⟩, ⟨h23, h24, h25, h26, h27, h28, h29, h30⟩⟩

private theorem ecPubKeyIsCanonical_tail_eq (P : Primitives) (keyBytes edPt : Bytes)
    (h : keyBytes.length = 32)
    (hmont : P.montToEd keyBytes 0 = some edPt)
    (htors : P.isTorsionFree edPt = true)
    (hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = true)
    (hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = true) :
    (if isCanonicalRef P keyBytes = true then (1#8 : BitVec 8) else 0#8) =
      BitVec.setWidth 8
        (if
          (if (BitVec.truncate 32
              (BitVec.signExtend 64 ((bytesToBv8 keyBytes).getD 31 0#8)) == 127#32) = true then
            (pack64 ((bytesToBv8 keyBytes).getD 1 0#8) ((bytesToBv8 keyBytes).getD 2 0#8)
                      ((bytesToBv8 keyBytes).getD 3 0#8) ((bytesToBv8 keyBytes).getD 4 0#8)
                      ((bytesToBv8 keyBytes).getD 5 0#8) ((bytesToBv8 keyBytes).getD 6 0#8)
                      ((bytesToBv8 keyBytes).getD 7 0#8) ((bytesToBv8 keyBytes).getD 8 0#8) &&&
                    pack64 ((bytesToBv8 keyBytes).getD 9 0#8) ((bytesToBv8 keyBytes).getD 10 0#8)
                      ((bytesToBv8 keyBytes).getD 11 0#8) ((bytesToBv8 keyBytes).getD 12 0#8)
                      ((bytesToBv8 keyBytes).getD 13 0#8) ((bytesToBv8 keyBytes).getD 14 0#8)
                      ((bytesToBv8 keyBytes).getD 15 0#8) ((bytesToBv8 keyBytes).getD 16 0#8) &&&
                  (pack64 ((bytesToBv8 keyBytes).getD 17 0#8) ((bytesToBv8 keyBytes).getD 18 0#8)
                      ((bytesToBv8 keyBytes).getD 19 0#8) ((bytesToBv8 keyBytes).getD 20 0#8)
                      ((bytesToBv8 keyBytes).getD 21 0#8) ((bytesToBv8 keyBytes).getD 22 0#8)
                      ((bytesToBv8 keyBytes).getD 23 0#8) ((bytesToBv8 keyBytes).getD 24 0#8) &&&
                    pack64 ((bytesToBv8 keyBytes).getD 23 0#8) ((bytesToBv8 keyBytes).getD 24 0#8)
                      ((bytesToBv8 keyBytes).getD 25 0#8) ((bytesToBv8 keyBytes).getD 26 0#8)
                      ((bytesToBv8 keyBytes).getD 27 0#8) ((bytesToBv8 keyBytes).getD 28 0#8)
                      ((bytesToBv8 keyBytes).getD 29 0#8) ((bytesToBv8 keyBytes).getD 30 0#8))) +
                1#64 ==
              0#64
          else false) =
            true then
          (0#64 : BitVec 64)
        else 1#64) := by
  have hlen_beq : (keyBytes.length == 32) = true := beq_iff_eq.mpr h
  rw [pack64_4_allOnes_eq_drop1_take30 keyBytes h, bytesToBv8_getD keyBytes 31,
    uint8_b31_7f_eq (keyBytes.getD 31 0) hb31_u8]
  simp only [isCanonicalRef, scalarIsInRange, hlen_beq, hb31_u8, hb0_u8, hmont, htors]
  cases ((keyBytes.drop 1).take 30 == List.replicate 30 0xFF) <;>
    cases ((keyBytes.getD 31 0 &&& 0x7F) == 0x7F) <;> rfl

@[simp, wp_norm, arm64_norm]
private theorem State_ite_setPState_setPC (c : Prop) [inst : Decidable c] (s : State)
    (ps1 ps2 : PState) (pc : BitVec 64) :
    @_root_.ite State c inst ((s.setPState ps1).setPC pc) ((s.setPState ps2).setPC pc) =
      (s.setPState (@_root_.ite PState c inst ps1 ps2)).setPC pc := by
  by_cases hc : c <;> simp [hc]

@[simp, wp_norm, arm64_norm]
private theorem State_ite_setPState_setPC_setMem (c : Prop) [inst : Decidable c] (s : State)
    (ps1 ps2 : PState) (pc : BitVec 64) (m : Memory) :
    @_root_.ite State c inst (((s.setPState ps1).setPC pc).setMem m)
      (((s.setPState ps2).setPC pc).setMem m) =
      ((s.setPState (@_root_.ite PState c inst ps1 ps2)).setPC pc).setMem m := by
  by_cases hc : c <;> simp [hc]

@[simp, wp_norm, arm64_norm]
private theorem ConditionHolds_ite (cond : CondCode) (c : Prop) [inst : Decidable c]
    (ps1 ps2 : PState) :
    ConditionHolds cond (@_root_.ite PState c inst ps1 ps2) =
      @_root_.ite Bool c inst (ConditionHolds cond ps1) (ConditionHolds cond ps2) := by
  by_cases hc : c <;> simp [hc]

set_option maxHeartbeats 1200000 in
theorem ecPubKeyIsCanonical_call_ok'_trap {P : Primitives} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hisCanon : ∀ k, P.isCanonicalEC k = isCanonicalRef P k)
    (hmontLen : ∀ u s ed, P.montToEd u s = some ed → ed.length = 160)
    (hmontHook : HookSat absHooks dalekMontToEdStub (dalekMontToEdStubSpec P img))
    (htorsHook : HookSat absHooks dalekTorsionFreeStub
      (cryptoBoolRegStubSpec P.isTorsionFree 160 img)) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr ecPubKeyIsCanonicalSym)
      (ecPubKeyIsCanonicalCallSpec P) := by
  unfold ecPubKeyIsCanonicalCallSpec
  simp only [stackAt_ecPubKeyIsCanonical_call]
  cells_unfold
  have hmont_call : subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr ecPubKeyIsCanonicalSym +
        BitVec.ofNat 64 (num% (ls_off% "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards" -
          (ls_off% "<libsignal_core::curve::PublicKey>::is_canonical"))))
      (dalekMontToEdStubSpec P img) :=
    hook_ok_at (hname := dalekMontToEdStub) rfl
      (by fnoff_eq)
      (by fnoff_eq)
    (by fnoff_eq) (by simp [Rust.isPanicSymbol, dalekMontToEdStub])
      (hookSat_tripleRatchetExterns'_trap C absHooks rfl hmontHook)
  have htors_call : subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr ecPubKeyIsCanonicalSym +
        BitVec.ofNat 64 (num% (ls_off% "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free" -
          (ls_off% "<libsignal_core::curve::PublicKey>::is_canonical"))))
      (cryptoBoolRegStubSpec P.isTorsionFree 160 img) :=
    hook_ok_at (hname := dalekTorsionFreeStub) rfl
      (by fnoff_eq)
      (by fnoff_eq)
    (by fnoff_eq) (by simp [Rust.isPanicSymbol, dalekTorsionFreeStub])
      (hookSat_tripleRatchetExterns'_trap C absHooks rfl htorsHook)
  clear hmontHook htorsHook
  have hfn : libsignalSessionCode.fnOff ecPubKeyIsCanonicalSym =
      (ls_off% "<libsignal_core::curve::PublicKey>::is_canonical") :=
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::is_canonical")
  code_fetches CryptoVerification.libsignalSessionCode
    ecPubKeyIsCanonical img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn
    (ls_off% "<libsignal_core::curve::PublicKey>::is_canonical") 236
  wp_init g s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨keyPtr, keyBytes⟩ := g
  dsimp only at *
  subst h_1
  have hcanon_eq : P.isCanonicalEC keyBytes = isCanonicalRef P keyBytes :=
    hisCanon keyBytes
  rw [hcanon_eq]
  have hlen_bv : (bytesToBv8 keyBytes).length = 32 := by simp [bytesToBv8, h]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 hlen_bv
  have hpk_sp_tail (R_tail : SepProp) :
      (s0.sp - 400#64) ↦₆₄ w0 ∗ ((s0.sp - 392#64) ↦₆₄ w1 ∗
      ((s0.sp - 384#64) ↦₆₄ w2 ∗ ((s0.sp - 376#64) ↦₆₄ w3 ∗ R_tail))) =
      (s0.sp - 400#64) ↦ₛ bytesToBv8 keyBytes ∗ R_tail := by
    have hpk_sp := hpk_cells (s0.sp - 400#64)
    have ha1 : s0.sp - 400#64 + 8#64 = s0.sp - 392#64 := by bv_arith
    have ha2 : s0.sp - 400#64 + 16#64 = s0.sp - 384#64 := by bv_arith
    have ha3 : s0.sp - 400#64 + 24#64 = s0.sp - 376#64 := by bv_arith
    rw [ha1, ha2, ha3] at hpk_sp
    rw [hpk_sp, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  have hpk_reg0_tail (R_tail : SepProp) :
      s0.readReg64 (Reg.gpr 0#5) ↦₆₄ w0 ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1 ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2 ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3 ∗ R_tail))) =
      s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ R_tail := by
    rw [hpk_cells (s0.readReg64 (Reg.gpr 0#5)), sepConj_assoc, sepConj_assoc, sepConj_assoc]
  wp_conv_pre => rw [← hpk_reg0_tail]
  wp_steps
  wp_conv_pre => rw [hpk_reg0_tail, hpk_sp_tail]
  wp_call hmont_call ⟨keyBytes, 0, s0.sp - 400#64, s0.sp - 360#64⟩
  wp_conv_pre => rw [show (0 : UInt8) &&& 1 = 0 from rfl, ← hpk_sp_tail]
  cases hmont : P.montToEd keyBytes 0 with
  | none =>
    have hcanon_none : isCanonicalRef P keyBytes = false := by
      simp [isCanonicalRef, hmont]
    rw [hcanon_none]
    wp_conv_pre =>
      rw [dalekMontToEdOutAt_none P keyBytes 0 hmont (s0.sp - 360#64), sepConj_assoc]
    wp_steps
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (memRegion168_of_cell_and_memRegion160 (s0.sp - 360#64) 0#64 _))))) ?_
    wp_done
  | some edPt =>
    have hed_len : edPt.length = 160 := hmontLen keyBytes 0 edPt hmont
    have hed_bv_len : (bytesToBv8 edPt).length = 160 := by simp [bytesToBv8, hed_len]
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
      e16, e17, e18, e19, hed_cells⟩ :=
      exists_unpack64_of_length_160 hed_bv_len
    refine sepWP_memRegion160_head (s0.sp - 192#64)
      (F_rest := (s0.sp - 400#64) ↦₆₄ w0 ∗
        ((s0.sp - 392#64) ↦₆₄ w1 ∗
          ((s0.sp - 384#64) ↦₆₄ w2 ∗
            ((s0.sp - 376#64) ↦₆₄ w3 ∗
              (dalekMontToEdOutAt P (s0.sp - 360#64) keyBytes 0 ∗
                (stackAt (s0.sp - 400#64) pqxdhHookStack ∗
                  (s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗
                    (memRegion (s0.sp - 368#64) 8 ∗
                        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                              (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))))))))))
      (by ac_rfl)
      fun u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 => ?_
    wp_conv_pre =>
      rw [dalekMontToEdOutAt_some P keyBytes edPt 0 hmont hed_len (s0.sp - 360#64),
        sepConj_assoc ((s0.sp - 360#64) ↦₆₄ 1#64),
        ← hed_cells (s0.sp - 360#64 + 8#64)]
    wp_steps
    wp_conv_pre =>
      rw [hed_cells (s0.sp - 192#64), hed_cells (s0.sp - 360#64 + 8#64)]
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (memRegion168_of_cell_and_bytes160
          (s0.sp - 360#64) 1#64 hed_bv_len _)))))) ?_
    wp_call htors_call ⟨s0.sp - 192#64, edPt⟩
    refine SepWP.weaken_pre (memRegion160_of_bytes160 (s0.sp - 192#64) hed_bv_len _) ?_
    cases htors : P.isTorsionFree edPt with
    | false =>
      have hcanon_false : isCanonicalRef P keyBytes = false := by
        simp [isCanonicalRef, hmont, htors]
      rw [hcanon_false]
      simp only [htors, Bool.false_eq_true, ite_false] at hpost_1
      have hx0_8 : BitVec.setWidth 8 (sf_1.readReg64 (Reg.gpr 0#5)) = 0#8 := by
        revert hpost_1; bv_bits
      wp_steps
      wp_done
    | true =>
      simp only [htors, ite_true] at hpost_1
      have hfocus8 (off : Nat) (hoff : off < 32) (R_tail : SepProp) :
          s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ R_tail =
            ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 off) ↦₈
              (bytesToBv8 keyBytes).getD off 0#8) ∗
            ((s0.readReg64 (Reg.gpr 0#5) ↦ₛ (bytesToBv8 keyBytes).take off) ∗
             ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (off + 1)) ↦ₛ
              (bytesToBv8 keyBytes).drop (off + 1) ∗ R_tail)) := by
        rw [pointsToBytes_focus8 (s0.readReg64 (Reg.gpr 0#5)) (bytesToBv8 keyBytes) off
            (by rw [hlen_bv]; exact hoff),
          sepConj_assoc, sepConj_assoc]
      have hfocus64 (off : Nat) (hoff : off + 8 ≤ 32) (R_tail : SepProp) :
          s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ R_tail =
            ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 off) ↦₆₄
              pack64 ((bytesToBv8 keyBytes).getD off 0#8) ((bytesToBv8 keyBytes).getD (off + 1) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 2) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 3) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 4) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 5) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 6) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 7) 0#8)) ∗
            ((s0.readReg64 (Reg.gpr 0#5) ↦ₛ (bytesToBv8 keyBytes).take off) ∗
             ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (off + 8)) ↦ₛ
              (bytesToBv8 keyBytes).drop (off + 8) ∗ R_tail)) := by
        rw [pointsToBytes_focus64 (s0.readReg64 (Reg.gpr 0#5)) (bytesToBv8 keyBytes) off
            (by rw [hlen_bv]; exact hoff),
          sepConj_assoc, sepConj_assoc]
      wp_conv_pre => rw [hfocus8 31 (by decide)]
      wp_steps
      wp_conv_pre => rw [← hfocus8 31 (by decide)]
      cases hb31 : ((bytesToBv8 keyBytes).getD 31 0#8).getLsbD 7 with
      | true =>
        have hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = false := by
          rw [bytesToBv8_getD] at hb31
          exact (uint8_getLsbD7_eq_true_iff _).mp hb31
        have hcanon_b31 : isCanonicalRef P keyBytes = false := by
          unfold isCanonicalRef; rw [hb31_u8]; simp
        rw [hcanon_b31]
        simp only [beq_self_eq_true, ite_true]
        wp_steps
        wp_done
      | false =>
        have hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = true := by
          rw [bytesToBv8_getD] at hb31
          exact (uint8_getLsbD7_eq_false_iff _).mp hb31
        simp only [beq_iff_eq, Bool.false_eq_true, ite_false]
        wp_conv_pre => rw [hfocus8 0 (by decide)]
        wp_steps
        wp_conv_pre => rw [← hfocus8 0 (by decide)]
        cases hb0 : (BitVec.zeroExtend 64 ((bytesToBv8 keyBytes).getD 0 0#8)).ult 237#64 with
        | true =>
          have hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = false := by
            rw [bytesToBv8_getD] at hb0
            exact (uint8_ult237_eq_true_iff _).mp hb0
          have hlen_beq : (keyBytes.length == 32) = true := beq_iff_eq.mpr h
          have hcanon_b0 : isCanonicalRef P keyBytes = true := by
            simp only [isCanonicalRef, scalarIsInRange, hlen_beq, hb31_u8, hb0_u8, hmont, htors]
            rfl
          rw [hcanon_b0]
          simp only [ite_true]
          wp_steps
          wp_done
        | false =>
          have hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = true := by
            rw [bytesToBv8_getD] at hb0
            exact (uint8_ult237_eq_false_iff _).mp hb0
          simp only [Bool.false_eq_true, ite_false]
          wp_conv_pre => rw [hfocus64 1 (by decide)]
          wp_step
          wp_conv_pre => rw [← hfocus64 1 (by decide), hfocus64 9 (by decide)]
          wp_steps
          wp_conv_pre => rw [← hfocus64 9 (by decide), hfocus64 17 (by decide)]
          wp_step
          wp_conv_pre => rw [← hfocus64 17 (by decide), hfocus64 23 (by decide)]
          wp_steps
          wp_conv_pre => rw [← hfocus64 23 (by decide)]
          rw [ecPubKeyIsCanonical_tail_eq P keyBytes edPt h hmont htors hb31_u8 hb0_u8]
          wp_done

theorem ecPubKeyIsCanonical_call_ok' {P : Primitives} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hisCanon : ∀ k, P.isCanonicalEC k = isCanonicalRef P k)
    (hmontLen : ∀ u s ed, P.montToEd u s = some ed → ed.length = 160)
    (hmontHook : HookSat absHooks dalekMontToEdStub (dalekMontToEdStubSpec P img))
    (htorsHook : HookSat absHooks dalekTorsionFreeStub
      (cryptoBoolRegStubSpec P.isTorsionFree 160 img)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr ecPubKeyIsCanonicalSym)
      (ecPubKeyIsCanonicalCallSpec P) := by
  rw [← trTrapProgAt_fnAddr_eq img.base C ctl absHooks ecPubKeyIsCanonicalSym]
  exact subroutine_ok_kit_of_trTrap
    (ecPubKeyIsCanonical_call_ok'_trap hisCanon hmontLen hmontHook htorsHook)

theorem ecPubKeyIsCanonical_call_ok_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr ecPubKeyIsCanonicalSym)
      (ecPubKeyIsCanonicalCallSpec P) :=
  ecPubKeyIsCanonical_call_ok'_trap hWF.isCanonical_eq_isCanonicalRef hWF.montToEd_len
    hH.dalekMontToEd hH.dalekTorsionFree

theorem ecPubKeyIsCanonical_call_ok {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr ecPubKeyIsCanonicalSym)
      (ecPubKeyIsCanonicalCallSpec P) :=
  ecPubKeyIsCanonical_call_ok' hWF.isCanonical_eq_isCanonicalRef hWF.montToEd_len
    hH.dalekMontToEd hH.dalekTorsionFree

/-! ## Contract-Backed `extHookStack` Variants -/

abbrev pqxdhHookStackExt : Nat := extHookStack
abbrev pqxdhEntryStackExt : Nat := 32768
abbrev verifySigHookStackExt : Nat := extHookStack + 48
abbrev verifySigStackExt : Nat := extHookStack + 1328

def cryptoBoolRegStubSpecExt (pred : Bytes → Bool) (inLen : Nat) (_img : Obj.Image := default) :
    Spec CryptoUnaryGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧
      g.inBytes.length = inLen⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      stackAt s.sp pqxdhHookStackExt
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 32 = (if pred g.inBytes then 1#32 else 0#32)⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      stackAt s0.sp pqxdhHookStackExt

def cryptoLeafRefStubSpecExt (fn : Bytes → Bytes) (inLen outLen : Nat) : Spec CryptoLeafCall where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inBytes.length = inLen⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      memRegion g.outPtr outLen ∗
      stackAt s.sp pqxdhHookStackExt
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      (g.outPtr ↦ₛ fitBv8 outLen (fn g.inBytes)) ∗
      stackAt s0.sp pqxdhHookStackExt

def cryptoLeafByValStubSpecExt (fn : Bytes → Bytes) (inLen outLen : Nat) : Spec CryptoLeafCall where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inBytes.length = inLen⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      memRegion g.outPtr outLen ∗
      stackAt s.sp pqxdhHookStackExt
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion g.inPtr inLen ∗
      (g.outPtr ↦ₛ fitBv8 outLen (fn g.inBytes)) ∗
      stackAt s0.sp pqxdhHookStackExt

def compressInPlaceStubSpecExt (fn : Bytes → Bytes → Bytes) (stateLen blockLen : Nat)
    (_img : Obj.Image := default) : Spec CryptoCompressGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.statePtr ∧
      s.readReg64 .x1 = g.blocksPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 g.nBlocks ∧
      g.nBlocks < 2 ^ 64 ∧
      g.stateBytes.length = stateLen ∧
      g.blockBytes.length = blockLen * g.nBlocks⌝ ∗
      (g.statePtr ↦ₛ bytesToBv8 g.stateBytes) ∗
      (g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗
      stackAt s.sp pqxdhHookStackExt
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.statePtr ↦ₛ fitBv8 stateLen (fn g.stateBytes g.blockBytes)) ∗
      (g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗
      stackAt s0.sp pqxdhHookStackExt

def dalekMontToEdStubSpecExt (P : Primitives) (_img : Obj.Image := default) :
    Spec DalekMontToEdGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧
      (s.readReg64 .x1).setWidth 8 = BitVec.ofNat 8 g.signBit.toNat ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inBytes.length = 32⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      memRegion g.outPtr 168 ∗
      stackAt s.sp pqxdhHookStackExt
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      dalekMontToEdOutAt P g.outPtr g.inBytes (g.signBit &&& 1) ∗
      stackAt s0.sp pqxdhHookStackExt

def dalekDoubleMulStubSpecExt (P : Primitives) (_img : Obj.Image := default) :
    Spec DalekDoubleMulGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.hPtr ∧
      s.readReg64 .x1 = g.negAPtr ∧
      s.readReg64 .x2 = g.sPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.hBytes.length = 32 ∧
      g.negABytes.length = 160 ∧
      g.sBytes.length = 32⌝ ∗
      (g.hPtr ↦ₛ bytesToBv8 g.hBytes) ∗
      (g.negAPtr ↦ₛ bytesToBv8 g.negABytes) ∗
      (g.sPtr ↦ₛ bytesToBv8 g.sBytes) ∗
      memRegion g.outPtr 160 ∗
      stackAt s.sp pqxdhHookStackExt
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.hPtr ↦ₛ bytesToBv8 g.hBytes) ∗
      (g.negAPtr ↦ₛ bytesToBv8 g.negABytes) ∗
      (g.sPtr ↦ₛ bytesToBv8 g.sBytes) ∗
      (g.outPtr ↦ₛ fitBv8 160 (P.doubleScalarMulBasepoint g.hBytes g.negABytes g.sBytes)) ∗
      stackAt s0.sp pqxdhHookStackExt

/-- Contract-backed external hook bundle for shared curve/signature functions (`is_canonical`,
    `verify_signature_for_multipart_message`, and `verify_signature`) on `tripleRatchetProgAtExt`
    at `pqxdhHookStackExt = extHookStack = 16384`, with `byVal` `memRegion` postconditions on
    `edNeg` (`160` B) and `scalarMod` (`32` B), 32-bit `w0` return on `torsionFree` and
    `subtle::black_box::<u8>`, and stacked `memcpy`/`memset` (`memHookStack = 4096`). -/
structure PqxdhHookContractsExt (P : Primitives) (_A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) : Prop where
  dalekMontToEd    : HookSat absHooks dalekMontToEdStub (dalekMontToEdStubSpecExt P img)
  dalekTorsionFree : HookSat absHooks dalekTorsionFreeStub
                       (cryptoBoolRegStubSpecExt P.isTorsionFree 160 img)
  sha512Compress   : HookSat absHooks sha512CompressStub
                       (compressInPlaceStubSpecExt (sha512CompressOutBytes P) 64 128 img)
  dalekScalarWide  : HookSat absHooks dalekScalarWideStub
                       (cryptoLeafRefStubSpecExt P.scalarFromWide 64 32)
  dalekScalarMod   : HookSat absHooks dalekScalarModStub
                       (cryptoLeafByValStubSpecExt P.scalarFromBytesModOrder 32 32)
  dalekCompress    : HookSat absHooks dalekCompressStub
                       (cryptoLeafRefStubSpecExt P.compress 160 32)
  dalekEdNeg       : HookSat absHooks dalekEdNegStub
                       (cryptoLeafByValStubSpecExt P.edNeg 160 160)
  dalekDoubleMul   : HookSat absHooks dalekDoubleMulStub
                       (dalekDoubleMulStubSpecExt P img)
  memcpy           : HookSat absHooks memcpyName SignalSession.CliExt.memcpySpec
  memset           : HookSat absHooks memsetName SignalSession.CliExt.memsetSpec
  blackBox         : HookSat absHooks "subtle::black_box::<u8>" SignalSession.CliExt.blackBoxSpec

theorem PqxdhHookContractsExt.of_hooks_eq {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext hooks : String → Option (State → State)}
    (h : PqxdhHookContractsExt P A img ext)
    (hmont : hooks dalekMontToEdStub = ext dalekMontToEdStub)
    (htors : hooks dalekTorsionFreeStub = ext dalekTorsionFreeStub)
    (hsha : hooks sha512CompressStub = ext sha512CompressStub)
    (hwide : hooks dalekScalarWideStub = ext dalekScalarWideStub)
    (hmod : hooks dalekScalarModStub = ext dalekScalarModStub)
    (hcomp : hooks dalekCompressStub = ext dalekCompressStub)
    (hneg : hooks dalekEdNegStub = ext dalekEdNegStub)
    (hdmul : hooks dalekDoubleMulStub = ext dalekDoubleMulStub)
    (hmemcpy : hooks memcpyName = ext memcpyName)
    (hmemset : hooks memsetName = ext memsetName)
    (hbb : hooks "subtle::black_box::<u8>" = ext "subtle::black_box::<u8>") :
    PqxdhHookContractsExt P A img hooks where
  dalekMontToEd    := by unfold HookSat; rw [hmont]; exact h.dalekMontToEd
  dalekTorsionFree := by unfold HookSat; rw [htors]; exact h.dalekTorsionFree
  sha512Compress   := by unfold HookSat; rw [hsha]; exact h.sha512Compress
  dalekScalarWide  := by unfold HookSat; rw [hwide]; exact h.dalekScalarWide
  dalekScalarMod   := by unfold HookSat; rw [hmod]; exact h.dalekScalarMod
  dalekCompress    := by unfold HookSat; rw [hcomp]; exact h.dalekCompress
  dalekEdNeg       := by unfold HookSat; rw [hneg]; exact h.dalekEdNeg
  dalekDoubleMul   := by unfold HookSat; rw [hdmul]; exact h.dalekDoubleMul
  memcpy           := by unfold HookSat; rw [hmemcpy]; exact h.memcpy
  memset           := by unfold HookSat; rw [hmemset]; exact h.memset
  blackBox         := by unfold HookSat; rw [hbb]; exact h.blackBox

private theorem shared_bytesToBv8_eq_ofU8_ext :
    ∀ bs : List UInt8, bytesToBv8 bs = E2E.ofU8 bs
  | [] => rfl
  | b :: rest => congrArg₂ List.cons
      ((BitVec.ofNat_toNat 8 b.toBitVec).trans b.toBitVec.setWidth_eq)
      (shared_bytesToBv8_eq_ofU8_ext rest)

private theorem u8Vec_toList_eq_bytesToBv8_ext {n : Nat} {bs : Bytes} (hlen : bs.length = n) :
    (E2E.u8Vec n bs).toList = bytesToBv8 bs := by
  have hof : (E2E.ofU8 bs).length = n := by simp [E2E.ofU8, hlen]
  dsimp only [E2E.u8Vec, E2E.fitVec, List.Vector.toList]
  rw [shared_bytesToBv8_eq_ofU8_ext,
    List.take_append_of_le_length (Nat.le_of_eq hof.symm),
    List.take_of_length_le (Nat.le_of_eq hof)]

private theorem ofU8_toU8_ext : ∀ bs : List (BitVec 8), E2E.ofU8 (E2E.toU8 bs) = bs
  | [] => rfl
  | _ :: rest => congrArg₂ List.cons rfl (ofU8_toU8_ext rest)

private theorem toU8_ofU8_ext : ∀ bs : Bytes, E2E.toU8 (E2E.ofU8 bs) = bs
  | [] => rfl
  | b :: rest => congrArg₂ List.cons
      (by rcases b with ⟨v⟩; simp [E2E.toU8, E2E.ofU8, UInt8.ofBitVec])
      (toU8_ofU8_ext rest)

private theorem fitBv8_vecU8_eq_ext {n : Nat} (v : List.Vector (BitVec 8) n) :
    fitBv8 n (E2E.vecU8 v) = v.toList := by
  have hlen : (E2E.vecU8 v).length = n := by
    simp [E2E.vecU8, E2E.toU8, v.toList_length]
  rw [fitBv8_eq_bytesToBv8 hlen, shared_bytesToBv8_eq_ofU8_ext, E2E.vecU8, ofU8_toU8_ext]

private theorem pointsToBytes_u64le_append_ext (p : BitVec 64) (v : BitVec 64) (bs : List (BitVec 8)) :
    (p ↦ₛ (u64le v ++ bs)) = ((p ↦₆₄ v) ∗ ((p + 8#64) ↦ₛ bs)) := by
  have hu : u64le v = unpack64 v := rfl
  rw [hu, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]

theorem dalekMontToEd_ext_of_externsOk (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (img : Obj.Image)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    HookSat ext dalekMontToEdStub (dalekMontToEdStubSpecExt (E2E.modelPrims X P0) img) := by
  obtain ⟨fn, hfn, hok⟩ := hOk.toEdwards
  have hname : dalekMontToEdStub = E2E.toEdwardsName := rfl
  refine ⟨fn, hname ▸ hfn, fun g R s0 hrun hpre hsp => ?_⟩
  dsimp only [dalekMontToEdStubSpecExt, pqxdhHookStackExt] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlen⟩, hmem⟩
  let v : List.Vector (BitVec 8) 32 := E2E.u8Vec 32 g.inBytes
  have hv : v.toList = bytesToBv8 g.inBytes := u8Vec_toList_eq_bytesToBv8_ext hlen
  let sb : BitVec 8 := BitVec.ofNat 8 g.signBit.toNat
  have hpre0 : s0.mem ⊨
      (SignalSession.CliExt.toEdwardsSpec P0.Q).pre (g.inPtr, v, sb, g.outPtr) s0 ∗ R := by
    dsimp only [SignalSession.CliExt.toEdwardsSpec, SignalSession.CliExt.withStack]
    rw [hv]
    have h1 : s0.mem ⊨
        ⌜s0.readReg64 .x0 = g.inPtr ∧ (s0.readReg64 .x1).setWidth 8 = sb ∧ s0.readReg64 .x8 = g.outPtr⌝ ∗
        ((g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ memRegion g.outPtr 168 ∗ stackAt s0.sp extHookStack ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx8⟩, by convert hmem using 1⟩
    convert h1 using 1; ac_rfl
  rcases hok (g.inPtr, v, sb, g.outPtr) R s0 hrun hpre0 hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [SignalSession.CliExt.toEdwardsSpec, SignalSession.CliExt.withStack] at hpost
    have hpost' : (fn s0).mem ⊨
        ⌜(fn s0).trace = s0.trace⌝ ∗
        ((g.inPtr ↦ₛ v.toList) ∗
          SignalSession.CliExt.optionEdwardsPointAt g.outPtr (P0.Q.montToEd v (sb &&& 1#8)) ∗
          stackAt s0.sp extHookStack ∗ R) := by
      convert hpost using 1; ac_rfl
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨htr, hmemf⟩
    dsimp only [dalekMontToEdStubSpecExt, pqxdhHookStackExt]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    have hsb : sb &&& 1#8 = (g.signBit &&& 1).toBitVec := by
      dsimp only [sb]
      rcases g.signBit with ⟨bv⟩
      simp only [UInt8.toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, UInt8.toBitVec_and]
      rfl
    have hmte : (E2E.modelPrims X P0).montToEd g.inBytes (g.signBit &&& 1) =
        (P0.Q.montToEd v (sb &&& 1#8)).map E2E.vecU8 := by
      dsimp only [E2E.modelPrims, E2E.blockLevelPrims, v]
      rw [hsb]
    have hout : dalekMontToEdOutAt (E2E.modelPrims X P0) g.outPtr g.inBytes (g.signBit &&& 1) =
        SignalSession.CliExt.optionEdwardsPointAt g.outPtr (P0.Q.montToEd v (sb &&& 1#8)) := by
      unfold dalekMontToEdOutAt
      rw [hmte]
      cases P0.Q.montToEd v (sb &&& 1#8) with
      | none => rfl
      | some ed =>
        dsimp only [SignalSession.CliExt.optionEdwardsPointAt, Option.map]
        rw [fitBv8_vecU8_eq_ext ed, pointsToBytes_u64le_append_ext]
    rw [hv] at hmemf
    rw [hout]
    convert hmemf using 1
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem dalekTorsionFree_ext_of_externsOk (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (img : Obj.Image)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    HookSat ext dalekTorsionFreeStub
      (cryptoBoolRegStubSpecExt (E2E.modelPrims X P0).isTorsionFree 160 img) := by
  obtain ⟨fn, hfn, hok⟩ := hOk.torsionFree
  refine ⟨fn, hfn, fun g R s0 hrun hpre hsp => ?_⟩
  dsimp only [cryptoBoolRegStubSpecExt, pqxdhHookStackExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen⟩, hmem⟩
  let v : List.Vector (BitVec 8) 160 := E2E.u8Vec 160 g.inBytes
  have hv : v.toList = bytesToBv8 g.inBytes := u8Vec_toList_eq_bytesToBv8_ext hlen
  have hpre0 : s0.mem ⊨ (SignalSession.CliExt.torsionFreeSpec P0.Q).pre (g.inPtr, v) s0 ∗ R := by
    dsimp only [SignalSession.CliExt.torsionFreeSpec, SignalSession.CliExt.withStack]
    rw [hv]
    have h1 : s0.mem ⊨ ⌜s0.readReg64 .x0 = g.inPtr⌝ ∗
        ((g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ stackAt s0.sp extHookStack ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨hx0, by convert hmem using 1; ac_rfl⟩
    convert h1 using 1; ac_rfl
  rcases hok (g.inPtr, v) R s0 hrun hpre0 hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [SignalSession.CliExt.torsionFreeSpec, SignalSession.CliExt.withStack] at hpost
    have hpost' : (fn s0).mem ⊨
        ⌜(fn s0).trace = s0.trace ∧
          ((fn s0).readReg64 .x0).setWidth 32 = (if P0.Q.isTorsionFree v then 1#32 else 0#32)⌝ ∗
        ((g.inPtr ↦ₛ v.toList) ∗ stackAt s0.sp extHookStack ∗ R) := by
      convert hpost using 1; ac_rfl
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨⟨htr, hx0f⟩, hmemf⟩
    dsimp only [cryptoBoolRegStubSpecExt, pqxdhHookStackExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    have hpred : (E2E.modelPrims X P0).isTorsionFree g.inBytes = P0.Q.isTorsionFree v := rfl
    refine ⟨⟨htr, hpred ▸ hx0f⟩, ?_⟩
    rw [hv] at hmemf
    convert hmemf using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem cryptoLeafRef_ext_of_hookSat {m n : Nat}
    {f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n}
    {ext : String → Option (State → State)} {sym : String}
    (hLeaf : HookSat ext sym (SignalSession.CliExt.pureByteFunctionSpec f false)) :
    HookSat ext sym (cryptoLeafRefStubSpecExt (fun bs => E2E.vecU8 (f (E2E.u8Vec m bs))) m n) := by
  obtain ⟨fn, hfn, hok⟩ := hLeaf
  refine ⟨fn, hfn, fun g R s0 hrun hpre hsp => ?_⟩
  dsimp only [cryptoLeafRefStubSpecExt, pqxdhHookStackExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hlen⟩, hmem⟩
  let v : List.Vector (BitVec 8) m := E2E.u8Vec m g.inBytes
  have hv : v.toList = bytesToBv8 g.inBytes := u8Vec_toList_eq_bytesToBv8_ext hlen
  have hpre0 : s0.mem ⊨ (SignalSession.CliExt.pureByteFunctionSpec f false).pre (g.inPtr, v, g.outPtr) s0 ∗ R := by
    dsimp only [SignalSession.CliExt.pureByteFunctionSpec, SignalSession.CliExt.withStack]
    rw [hv]
    have h1 : s0.mem ⊨ ⌜s0.readReg64 .x0 = g.inPtr ∧ s0.readReg64 .x8 = g.outPtr⌝ ∗
        ((g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ memRegion g.outPtr n ∗
          stackAt s0.sp extHookStack ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx8⟩, by convert hmem using 1; ac_rfl⟩
    convert h1 using 1; ac_rfl
  rcases hok (g.inPtr, v, g.outPtr) R s0 hrun hpre0 hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    simp only [SignalSession.CliExt.pureByteFunctionSpec, SignalSession.CliExt.withStack,
      SignalSession.CliExt.inputAfter, Bool.false_eq_true, ↓reduceIte] at hpost
    have hpost' : (fn s0).mem ⊨
        ⌜(fn s0).trace = s0.trace⌝ ∗
        ((g.inPtr ↦ₛ v.toList) ∗ (g.outPtr ↦ₛ (f v).toList) ∗
          stackAt s0.sp extHookStack ∗ R) := by
      convert hpost using 1; ac_rfl
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨htr, hmemf⟩
    dsimp only [cryptoLeafRefStubSpecExt, pqxdhHookStackExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [fitBv8_vecU8_eq_ext (f v), ← hv]
    convert hmemf using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem cryptoLeafByVal_ext_of_hookSat {m n : Nat}
    {f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n}
    {ext : String → Option (State → State)} {sym : String}
    (hLeaf : HookSat ext sym (SignalSession.CliExt.pureByteFunctionSpec f true)) :
    HookSat ext sym (cryptoLeafByValStubSpecExt (fun bs => E2E.vecU8 (f (E2E.u8Vec m bs))) m n) := by
  obtain ⟨fn, hfn, hok⟩ := hLeaf
  refine ⟨fn, hfn, fun g R s0 hrun hpre hsp => ?_⟩
  dsimp only [cryptoLeafByValStubSpecExt, pqxdhHookStackExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hlen⟩, hmem⟩
  let v : List.Vector (BitVec 8) m := E2E.u8Vec m g.inBytes
  have hv : v.toList = bytesToBv8 g.inBytes := u8Vec_toList_eq_bytesToBv8_ext hlen
  have hpre0 : s0.mem ⊨ (SignalSession.CliExt.pureByteFunctionSpec f true).pre (g.inPtr, v, g.outPtr) s0 ∗ R := by
    dsimp only [SignalSession.CliExt.pureByteFunctionSpec, SignalSession.CliExt.withStack]
    rw [hv]
    have h1 : s0.mem ⊨ ⌜s0.readReg64 .x0 = g.inPtr ∧ s0.readReg64 .x8 = g.outPtr⌝ ∗
        ((g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ memRegion g.outPtr n ∗
          stackAt s0.sp extHookStack ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx8⟩, by convert hmem using 1; ac_rfl⟩
    convert h1 using 1; ac_rfl
  rcases hok (g.inPtr, v, g.outPtr) R s0 hrun hpre0 hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    simp only [SignalSession.CliExt.pureByteFunctionSpec, SignalSession.CliExt.withStack,
      SignalSession.CliExt.inputAfter, ↓reduceIte] at hpost
    have hpost' : (fn s0).mem ⊨
        ⌜(fn s0).trace = s0.trace⌝ ∗
        (memRegion g.inPtr m ∗ (g.outPtr ↦ₛ (f v).toList) ∗
          stackAt s0.sp extHookStack ∗ R) := by
      convert hpost using 1; ac_rfl
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨htr, hmemf⟩
    dsimp only [cryptoLeafByValStubSpecExt, pqxdhHookStackExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [fitBv8_vecU8_eq_ext (f v)]
    convert hmemf using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem dalekDoubleMul_ext_of_externsOk (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (img : Obj.Image)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    HookSat ext dalekDoubleMulStub (dalekDoubleMulStubSpecExt (E2E.modelPrims X P0) img) := by
  obtain ⟨fn, hfn, hok⟩ := hOk.dsmb
  refine ⟨fn, hfn, fun g R s0 hrun hpre hsp => ?_⟩
  dsimp only [dalekDoubleMulStubSpecExt, pqxdhHookStackExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx8, hh_len, ha_len, hs_len⟩, hmem⟩
  let vh : List.Vector (BitVec 8) 32 := E2E.u8Vec 32 g.hBytes
  let va : List.Vector (BitVec 8) 160 := E2E.u8Vec 160 g.negABytes
  let vs : List.Vector (BitVec 8) 32 := E2E.u8Vec 32 g.sBytes
  have hvh : vh.toList = bytesToBv8 g.hBytes := u8Vec_toList_eq_bytesToBv8_ext hh_len
  have hva : va.toList = bytesToBv8 g.negABytes := u8Vec_toList_eq_bytesToBv8_ext ha_len
  have hvs : vs.toList = bytesToBv8 g.sBytes := u8Vec_toList_eq_bytesToBv8_ext hs_len
  have hpre0 : s0.mem ⊨ (SignalSession.CliExt.dsmbSpec P0.Q).pre
      (g.hPtr, vh, g.negAPtr, va, g.sPtr, vs, g.outPtr) s0 ∗ R := by
    dsimp only [SignalSession.CliExt.dsmbSpec, SignalSession.CliExt.withStack]
    rw [hvh, hva, hvs]
    have h1 : s0.mem ⊨
        ⌜s0.readReg64 .x0 = g.hPtr ∧ s0.readReg64 .x1 = g.negAPtr ∧
          s0.readReg64 .x2 = g.sPtr ∧ s0.readReg64 .x8 = g.outPtr⌝ ∗
        ((g.hPtr ↦ₛ bytesToBv8 g.hBytes) ∗ (g.negAPtr ↦ₛ bytesToBv8 g.negABytes) ∗
          (g.sPtr ↦ₛ bytesToBv8 g.sBytes) ∗ memRegion g.outPtr 160 ∗
          stackAt s0.sp extHookStack ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx8⟩, by convert hmem using 1; ac_rfl⟩
    convert h1 using 1; ac_rfl
  rcases hok (g.hPtr, vh, g.negAPtr, va, g.sPtr, vs, g.outPtr) R s0 hrun hpre0 hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [SignalSession.CliExt.dsmbSpec, SignalSession.CliExt.withStack] at hpost
    have hpost' : (fn s0).mem ⊨
        ⌜(fn s0).trace = s0.trace⌝ ∗
        ((g.hPtr ↦ₛ vh.toList) ∗ (g.negAPtr ↦ₛ va.toList) ∗ (g.sPtr ↦ₛ vs.toList) ∗
          (g.outPtr ↦ₛ (P0.Q.dsmb vh va vs).toList) ∗
          stackAt s0.sp extHookStack ∗ R) := by
      convert hpost using 1; ac_rfl
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨htr, hmemf⟩
    dsimp only [dalekDoubleMulStubSpecExt, pqxdhHookStackExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    have hdsmb : (E2E.modelPrims X P0).doubleScalarMulBasepoint g.hBytes g.negABytes g.sBytes =
        E2E.vecU8 (P0.Q.dsmb vh va vs) := rfl
    rw [hdsmb, fitBv8_vecU8_eq_ext, ← hvh, ← hva, ← hvs]
    convert hmemf using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem sha512State_toList_ext (h : E2E.Sha512State) :
    h.toList = [h.get 0, h.get 1, h.get 2, h.get 3, h.get 4, h.get 5, h.get 6, h.get 7] := by
  rcases h with
    ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩
  all_goals (first | rfl | (simp at hl))

private theorem sha512StateBytesLE_len_ext (h : E2E.Sha512State) :
    (E2E.sha512StateBytesLE h).length = 64 := by
  rw [E2E.sha512StateBytesLE, sha512State_toList_ext]; rfl

private theorem sha512StateBytesBE_len_ext (h : E2E.Sha512State) :
    (E2E.sha512StateBytesBE h).length = 64 := by
  simp only [E2E.sha512StateBytesBE, E2E.toU8, List.length_map, sha512State_toList_ext]
  rfl

private theorem toLEBytes8_read64_ext (m : Memory) (a : BitVec 64) :
    LibsignalAesCbc.toLEBytes 8 (m.read64 a) = m.readBytes a 8 := by
  have h1 : LibsignalAesCbc.toLEBytes 8 (m.read64 a) = unpack64 (m.read64 a) := rfl
  have hrd : m.readBytes a 8 =
      [m.read8 a, m.read8 (a + 1#64), m.read8 (a + 2#64), m.read8 (a + 3#64),
       m.read8 (a + 4#64), m.read8 (a + 5#64), m.read8 (a + 6#64), m.read8 (a + 7#64)] := by
    simp only [Memory.readBytes, BitVec.add_assoc]; rfl
  rw [h1, hrd]
  dsimp only [Memory.read64]
  simp only [BitVec.add_zero]
  exact unpack64_pack64 (m.read8 a) (m.read8 (a + 1#64)) (m.read8 (a + 2#64)) (m.read8 (a + 3#64))
    (m.read8 (a + 4#64)) (m.read8 (a + 5#64)) (m.read8 (a + 6#64)) (m.read8 (a + 7#64))

private theorem sha512StateBytesLE_readSha512State_ext (m : Memory) (a : BitVec 64) :
    E2E.sha512StateBytesLE (E2E.readSha512State m a) = m.readBytes a 64 := by
  have hget (i : Fin 8) :
      LibsignalAesCbc.toLEBytes 8 ((E2E.readSha512State m a).get i) =
        m.readBytes (a + BitVec.ofNat 64 (8 * i.val)) 8 := by
    simp only [E2E.readSha512State, List.Vector.get_ofFn, toLEBytes8_read64_ext]
  rw [E2E.sha512StateBytesLE, sha512State_toList_ext (E2E.readSha512State m a)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hget]
  change
    m.readBytes (a + 0#64) 8 ++
    (m.readBytes (a + 8#64) 8 ++
    (m.readBytes (a + 16#64) 8 ++
    (m.readBytes (a + 24#64) 8 ++
    (m.readBytes (a + 32#64) 8 ++
    (m.readBytes (a + 40#64) 8 ++
    (m.readBytes (a + 48#64) 8 ++
     m.readBytes (a + 56#64) 8)))))) = m.readBytes a 64
  simp only [Memory.readBytes, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
    List.cons_append, List.nil_append]

private theorem ofU8_revWords64_toU8_sha512StateBytesLE_ext (h : E2E.Sha512State) :
    revWords64 (E2E.toU8 (E2E.sha512StateBytesLE h)) = E2E.sha512StateBytesBE h := by
  rw [← toU8_ofU8_ext (revWords64 (E2E.toU8 (E2E.sha512StateBytesLE h)))]
  congr 1
  simp only [revWords64, E2E.ofU8, List.map_append, List.map_reverse, List.map_take, List.map_drop]
  change
    (((E2E.ofU8 (E2E.toU8 (E2E.sha512StateBytesLE h))).take 8).reverse ++
     (((E2E.ofU8 (E2E.toU8 (E2E.sha512StateBytesLE h))).drop 8).take 8).reverse ++
     (((E2E.ofU8 (E2E.toU8 (E2E.sha512StateBytesLE h))).drop 16).take 8).reverse ++
     (((E2E.ofU8 (E2E.toU8 (E2E.sha512StateBytesLE h))).drop 24).take 8).reverse ++
     (((E2E.ofU8 (E2E.toU8 (E2E.sha512StateBytesLE h))).drop 32).take 8).reverse ++
     (((E2E.ofU8 (E2E.toU8 (E2E.sha512StateBytesLE h))).drop 40).take 8).reverse ++
     (((E2E.ofU8 (E2E.toU8 (E2E.sha512StateBytesLE h))).drop 48).take 8).reverse ++
     (((E2E.ofU8 (E2E.toU8 (E2E.sha512StateBytesLE h))).drop 56).take 8).reverse) =
    (h.toList.flatMap (HMAC.toBEBytes 8))
  rw [ofU8_toU8_ext, E2E.sha512StateBytesLE, sha512State_toList_ext h]
  rfl

private theorem ofU8_revWords64_sha512StateBytesBE_ext (h : E2E.Sha512State) :
    E2E.ofU8 (revWords64 (E2E.sha512StateBytesBE h)) = E2E.sha512StateBytesLE h := by
  simp only [revWords64, E2E.ofU8, List.map_append, List.map_reverse, List.map_take, List.map_drop]
  change
    (((E2E.ofU8 (E2E.sha512StateBytesBE h)).take 8).reverse ++
     (((E2E.ofU8 (E2E.sha512StateBytesBE h)).drop 8).take 8).reverse ++
     (((E2E.ofU8 (E2E.sha512StateBytesBE h)).drop 16).take 8).reverse ++
     (((E2E.ofU8 (E2E.sha512StateBytesBE h)).drop 24).take 8).reverse ++
     (((E2E.ofU8 (E2E.sha512StateBytesBE h)).drop 32).take 8).reverse ++
     (((E2E.ofU8 (E2E.sha512StateBytesBE h)).drop 40).take 8).reverse ++
     (((E2E.ofU8 (E2E.sha512StateBytesBE h)).drop 48).take 8).reverse ++
     (((E2E.ofU8 (E2E.sha512StateBytesBE h)).drop 56).take 8).reverse) = E2E.sha512StateBytesLE h
  rw [E2E.sha512StateBytesBE, ofU8_toU8_ext, E2E.sha512StateBytesLE, sha512State_toList_ext h]
  rfl

private theorem beWord64_toBEBytes8_ext (w : BitVec 64) :
    E2E.beWord 64 (HMAC.toBEBytes 8 w) 0 = w := by
  change
    ((((((((0#64 <<< 8 ||| (w.extractLsb' 56 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 48 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 40 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 32 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 24 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 16 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 8 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 0 8).zeroExtend 64) = w
  bv_bits

private theorem sha512StateOf_sha512StateBytesBE_ext (h : E2E.Sha512State) :
    E2E.sha512StateOf (E2E.sha512StateBytesBE h) = h := by
  apply List.Vector.ext
  intro i
  simp only [E2E.sha512StateOf, List.Vector.get_ofFn]
  have hslice :
      E2E.beWord 64 (E2E.ofU8 (E2E.sha512StateBytesBE h)) i.val =
        E2E.beWord 64 (HMAC.toBEBytes 8 (h.get i)) 0 := by
    rw [E2E.sha512StateBytesBE, ofU8_toU8_ext, sha512State_toList_ext h]
    fin_cases i <;> rfl
  rw [hslice, beWord64_toBEBytes8_ext]

private theorem list_ofFn_eq_range_map_ext {α : Type} (n : Nat) (f : Nat → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    rw [ih (fun i => f (i + 1)), List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl

private theorem chunks128_ofU8_ext (bs : Bytes) :
    E2E.chunks128 (E2E.ofU8 bs) = (chunkBlocks 128 bs).map E2E.ofU8 := by
  have hlen : (E2E.ofU8 bs).length = bs.length := by simp [E2E.ofU8]
  unfold E2E.chunks128 chunkBlocks
  rw [list_ofFn_eq_range_map_ext ((E2E.ofU8 bs).length / 128)
      (fun i => ((E2E.ofU8 bs).drop (128 * i)).take 128),
    hlen, List.map_map]
  congr 1; funext i
  simp only [Function.comp_def, E2E.ofU8, ← List.map_drop, ← List.map_take, Nat.mul_comm 128 i]

private theorem foldl_sha512Step_modelPrims_ext (X : E2E.UnreachedPqxdhPrimitives) (P0 : E2E.PEParams)
    (blks : List Bytes) (st : E2E.Sha512State) :
    blks.foldl (sha512Step (E2E.modelPrims X P0)) (E2E.sha512StateBytesBE st) =
      E2E.sha512StateBytesBE ((blks.map E2E.ofU8).foldl P0.Q.F512 st) := by
  induction blks generalizing st with
  | nil => rfl
  | cons blk rest ih =>
    simp only [List.foldl_cons, List.map_cons]
    have hstep :
        sha512Step (E2E.modelPrims X P0) (E2E.sha512StateBytesBE st) blk =
          E2E.sha512StateBytesBE (P0.Q.F512 st (E2E.ofU8 blk)) := by
      unfold sha512Step
      change fitBytes 64
        (E2E.sha512StateBytesBE
          (P0.Q.F512 (E2E.sha512StateOf (fitBytes 64 (E2E.sha512StateBytesBE st))) (E2E.ofU8 blk))) =
        E2E.sha512StateBytesBE (P0.Q.F512 st (E2E.ofU8 blk))
      rw [fitBytes_of_length_eq (sha512StateBytesBE_len_ext st),
        sha512StateOf_sha512StateBytesBE_ext,
        fitBytes_of_length_eq (sha512StateBytesBE_len_ext _)]
    rw [hstep, ih]

theorem sha512Compress_ext_of_externsOk (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (img : Obj.Image)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    HookSat ext sha512CompressStub
      (compressInPlaceStubSpecExt (sha512CompressOutBytes (E2E.modelPrims X P0)) 64 128 img) := by
  obtain ⟨fn, hfn, hok⟩ := hOk.compress512
  refine ⟨fn, hfn, fun g R s0 hrun hpre hsp => ?_⟩
  dsimp only [compressInPlaceStubSpecExt, pqxdhHookStackExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hn_lt, hst_len, hblk_len⟩, hmem⟩
  have hx2_nat : (s0.readReg64 .x2).toNat = g.nBlocks := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn_lt]
  have hst_read : s0.mem.readBytes g.statePtr 64 = E2E.ofU8 g.stateBytes := by
    have hlen' : (bytesToBv8 g.stateBytes).length = 64 := by simp [bytesToBv8, hst_len]
    have hmem_assoc : s0.mem ⊨
        (g.statePtr ↦ₛ bytesToBv8 g.stateBytes) ∗
          ((g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗ stackAt s0.sp extHookStack ∗ R) := by
      simpa only [sepConj_assoc] using hmem
    have hrd := ((IsBlock.pointsToBytes g.statePtr (bytesToBv8 g.stateBytes)).read hmem_assoc).2
    rw [hlen', shared_bytesToBv8_eq_ofU8_ext] at hrd
    exact hrd
  let st0 : E2E.Sha512State := E2E.readSha512State s0.mem g.statePtr
  have hle_st0 : E2E.sha512StateBytesLE st0 = bytesToBv8 g.stateBytes := by
    rw [sha512StateBytesLE_readSha512State_ext, hst_read, ← shared_bytesToBv8_eq_ofU8_ext]
  have hblk_bv_len : (bytesToBv8 g.blockBytes).length = 128 * g.nBlocks := by
    simp [bytesToBv8, hblk_len]
  have hpre0 : s0.mem ⊨ (SignalSession.CliExt.compress512Spec P0.Q).pre
      (g.statePtr, st0, g.blocksPtr, bytesToBv8 g.blockBytes, g.nBlocks) s0 ∗ R := by
    dsimp only [SignalSession.CliExt.compress512Spec, SignalSession.CliExt.withStack]
    rw [hle_st0]
    have h1 : s0.mem ⊨
        ⌜s0.readReg64 .x0 = g.statePtr ∧ s0.readReg64 .x1 = g.blocksPtr ∧
          (s0.readReg64 .x2).toNat = g.nBlocks ∧ (bytesToBv8 g.blockBytes).length = 128 * g.nBlocks⌝ ∗
        ((g.statePtr ↦ₛ bytesToBv8 g.stateBytes) ∗ (g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗
          stackAt s0.sp extHookStack ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2_nat, hblk_bv_len⟩, by convert hmem using 1; ac_rfl⟩
    convert h1 using 1; ac_rfl
  rcases hok (g.statePtr, st0, g.blocksPtr, bytesToBv8 g.blockBytes, g.nBlocks) R s0 hrun hpre0 hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [SignalSession.CliExt.compress512Spec, SignalSession.CliExt.withStack] at hpost
    have hpost' : (fn s0).mem ⊨
        ⌜(fn s0).trace = s0.trace⌝ ∗
        ((g.statePtr ↦ₛ E2E.sha512StateBytesLE
            ((E2E.chunks128 (bytesToBv8 g.blockBytes)).foldl P0.Q.F512 st0)) ∗
          (g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗
          stackAt s0.sp extHookStack ∗ R) := by
      convert hpost using 1; ac_rfl
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨htr, hmemf⟩
    dsimp only [compressInPlaceStubSpecExt, pqxdhHookStackExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    have hrev_st : revWords64 g.stateBytes = E2E.sha512StateBytesBE st0 := by
      have hst_eq : g.stateBytes = E2E.toU8 (E2E.sha512StateBytesLE st0) := by
        rw [hle_st0, shared_bytesToBv8_eq_ofU8_ext, toU8_ofU8_ext]
      rw [hst_eq, ofU8_revWords64_toU8_sha512StateBytesLE_ext]
    let stFinal := (E2E.chunks128 (E2E.ofU8 g.blockBytes)).foldl P0.Q.F512 st0
    have hout_eq :
        fitBv8 64 (sha512CompressOutBytes (E2E.modelPrims X P0) g.stateBytes g.blockBytes) =
          E2E.sha512StateBytesLE stFinal := by
      unfold sha512CompressOutBytes
      rw [hrev_st, foldl_sha512Step_modelPrims_ext, ← chunks128_ofU8_ext,
        fitBytes_of_length_eq (sha512StateBytesBE_len_ext stFinal)]
      have hrev_len : (revWords64 (E2E.sha512StateBytesBE stFinal)).length = 64 := by
        have hlen_ofU8 : (E2E.ofU8 (revWords64 (E2E.sha512StateBytesBE stFinal))).length =
            (revWords64 (E2E.sha512StateBytesBE stFinal)).length := by simp [E2E.ofU8]
        rw [← hlen_ofU8, ofU8_revWords64_sha512StateBytesBE_ext, sha512StateBytesLE_len_ext]
      rw [fitBv8_eq_bytesToBv8 hrev_len, shared_bytesToBv8_eq_ofU8_ext,
        ofU8_revWords64_sha512StateBytesBE_ext]
    rw [hout_eq]
    dsimp only [stFinal]
    rw [← shared_bytesToBv8_eq_ofU8_ext]
    convert hmemf using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem PqxdhHookContractsExt.of_externsOk (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)} (img : Obj.Image)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    PqxdhHookContractsExt (E2E.modelPrims X P0) A img ext where
  dalekMontToEd    := dalekMontToEd_ext_of_externsOk X img hOk
  dalekTorsionFree := dalekTorsionFree_ext_of_externsOk X img hOk
  sha512Compress   := sha512Compress_ext_of_externsOk X img hOk
  dalekScalarWide  := cryptoLeafRef_ext_of_hookSat hOk.scalarWide
  dalekScalarMod   := cryptoLeafByVal_ext_of_hookSat hOk.scalarMod
  dalekCompress    := cryptoLeafRef_ext_of_hookSat hOk.compress
  dalekEdNeg       := cryptoLeafByVal_ext_of_hookSat hOk.edNeg
  dalekDoubleMul   := dalekDoubleMul_ext_of_externsOk X img hOk
  memcpy           := hOk.memcpy
  memset           := hOk.memset
  blackBox         := hOk.blackBox

theorem PqxdhHookContractsExt.of_cliExternsOk (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)} (img : Obj.Image)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    PqxdhHookContractsExt (E2E.modelPrims X P0) A img (SignalSession.cliExternsWith ext) :=
  (PqxdhHookContractsExt.of_externsOk X img hOk).of_hooks_eq
    (by simp [SignalSession.cliExternsWith, E2E.withImagePanics, E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, dalekMontToEdStub])
    (by simp [SignalSession.cliExternsWith, E2E.withImagePanics, E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, dalekTorsionFreeStub])
    (by simp [SignalSession.cliExternsWith, E2E.withImagePanics, E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, sha512CompressStub])
    (by simp [SignalSession.cliExternsWith, E2E.withImagePanics, E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, dalekScalarWideStub])
    (by simp [SignalSession.cliExternsWith, E2E.withImagePanics, E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, dalekScalarModStub])
    (by simp [SignalSession.cliExternsWith, E2E.withImagePanics, E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, dalekCompressStub])
    (by simp [SignalSession.cliExternsWith, E2E.withImagePanics, E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, dalekEdNegStub])
    (by simp [SignalSession.cliExternsWith, E2E.withImagePanics, E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, dalekDoubleMulStub])
    (by simp [SignalSession.cliExternsWith, E2E.withImagePanics, E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, memcpyName])
    (by simp [SignalSession.cliExternsWith, E2E.withImagePanics, E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, memsetName])
    (by simp [SignalSession.cliExternsWith, E2E.withImagePanics, E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol])

def ecPubKeyIsCanonicalCallSpecExt (P : Primitives) : Spec KeyCanonicalGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.keyPtr ∧ g.keyBytes.length = 32⌝ ∗
    (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗
    stackAt s.sp (pqxdhHookStackExt + 400)
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 8 = (if P.isCanonicalEC g.keyBytes then 1#8 else 0#8)⌝ ∗
    (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗
    stackAt s0.sp (pqxdhHookStackExt + 400)

theorem stackAt_ecPubKeyIsCanonical_call_ext (sp : BitVec 64) :
    stackAt sp (pqxdhHookStackExt + 400) =
      stackAt (sp - 400#64) pqxdhHookStackExt ∗
      cells (sp - 400#64) 4 ∗
      memRegion (sp - 368#64) 8 ∗
      memRegion (sp - 360#64) 168 ∗
      memRegion (sp - 192#64) 160 ∗
      cells (sp - 32#64) 4 := by
  rw [show (pqxdhHookStackExt + 400 : Nat) = pqxdhHookStackExt + 8 * 50 by decide,
    stackAt_split_cells sp pqxdhHookStackExt 50 (by decide),
    ← memRegion_cells (sp - 400#64) 50 (by decide)]
  change stackAt (sp - 400#64) pqxdhHookStackExt ∗ memRegion (sp - 400#64) 400 = _
  rw [memRegion_split (sp - 400#64) 32 368 (by decide),
    memRegion_cells (sp - 400#64) 4 (by decide),
    memRegion_split (sp - 400#64 + 32#64) 8 360 (by decide),
    memRegion_split (sp - 400#64 + 32#64 + 8#64) 168 192 (by decide),
    memRegion_split (sp - 400#64 + 32#64 + 8#64 + 168#64) 160 32 (by decide),
    memRegion_cells (sp - 400#64 + 32#64 + 8#64 + 168#64 + 160#64) 4 (by decide)]
  have h1 : sp - 400#64 + 32#64 = sp - 368#64 := by bv_arith
  have h2 : sp - 400#64 + 32#64 + 8#64 = sp - 360#64 := by bv_arith
  have h3 : sp - 400#64 + 32#64 + 8#64 + 168#64 = sp - 192#64 := by bv_arith
  have h4 : sp - 400#64 + 32#64 + 8#64 + 168#64 + 160#64 = sp - 32#64 := by bv_arith
  rw [h4, h3, h2, h1]

theorem dalekMontToEd_ok_at_ext {P : Primitives} {img : Obj.Image}
    {absHooks : String → Option (State → State)}
    (hmont : HookSat absHooks dalekMontToEdStub (dalekMontToEdStubSpecExt P img))
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekMontToEdStub := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base absHooks)
      ((tripleRatchetProgAtExt img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (dalekMontToEdStubSpecExt P img) :=
  hook_ok_at (hname := dalekMontToEdStub) rfl hk
    (by fnoff_eq)
    (by fnoff_eq) (by simp [Rust.isPanicSymbol, dalekMontToEdStub])
    hmont

theorem dalekTorsionFree_ok_at_ext {P : Primitives} {img : Obj.Image}
    {absHooks : String → Option (State → State)}
    (htors : HookSat absHooks dalekTorsionFreeStub (cryptoBoolRegStubSpecExt P.isTorsionFree 160 img))
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekTorsionFreeStub := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base absHooks)
      ((tripleRatchetProgAtExt img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoBoolRegStubSpecExt P.isTorsionFree 160 img) :=
  hook_ok_at (hname := dalekTorsionFreeStub) rfl hk
    (by fnoff_eq)
    (by fnoff_eq) (by simp [Rust.isPanicSymbol, dalekTorsionFreeStub])
    htors

set_option maxHeartbeats 1200000 in
theorem ecPubKeyIsCanonical_call_ok'_ext {P : Primitives} {img : Obj.Image}
    {absHooks : String → Option (State → State)}
    (hisCanon : ∀ k, P.isCanonicalEC k = isCanonicalRef P k)
    (hmontLen : ∀ u s ed, P.montToEd u s = some ed → ed.length = 160)
    (hmontHook : HookSat absHooks dalekMontToEdStub (dalekMontToEdStubSpecExt P img))
    (htorsHook : HookSat absHooks dalekTorsionFreeStub
      (cryptoBoolRegStubSpecExt P.isTorsionFree 160 img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base absHooks)
      ((tripleRatchetProgAtExt img.base absHooks).fnAddr ecPubKeyIsCanonicalSym)
      (ecPubKeyIsCanonicalCallSpecExt P) := by
  unfold ecPubKeyIsCanonicalCallSpecExt
  simp only [stackAt_ecPubKeyIsCanonical_call_ext]
  cells_unfold
  have hmont_call : subroutine_ok (tripleRatchetProgAtExt img.base absHooks)
      ((tripleRatchetProgAtExt img.base absHooks).fnAddr ecPubKeyIsCanonicalSym +
        BitVec.ofNat 64 (num% (ls_off% "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards" -
          (ls_off% "<libsignal_core::curve::PublicKey>::is_canonical"))))
      (dalekMontToEdStubSpecExt P img) :=
    dalekMontToEd_ok_at_ext hmontHook
  have htors_call : subroutine_ok (tripleRatchetProgAtExt img.base absHooks)
      ((tripleRatchetProgAtExt img.base absHooks).fnAddr ecPubKeyIsCanonicalSym +
        BitVec.ofNat 64 (num% (ls_off% "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free" -
          (ls_off% "<libsignal_core::curve::PublicKey>::is_canonical"))))
      (cryptoBoolRegStubSpecExt P.isTorsionFree 160 img) :=
    dalekTorsionFree_ok_at_ext htorsHook
  clear hmontHook htorsHook
  have hfn : libsignalSessionCode.fnOff ecPubKeyIsCanonicalSym =
      (ls_off% "<libsignal_core::curve::PublicKey>::is_canonical") :=
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::is_canonical")
  code_fetches CryptoVerification.libsignalSessionCode
    ecPubKeyIsCanonical img.base
    (Rust.withPanics absHooks) hfn
    (ls_off% "<libsignal_core::curve::PublicKey>::is_canonical") 236
  wp_init g s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨keyPtr, keyBytes⟩ := g
  dsimp only at *
  subst h_1
  have hcanon_eq : P.isCanonicalEC keyBytes = isCanonicalRef P keyBytes :=
    hisCanon keyBytes
  rw [hcanon_eq]
  have hlen_bv : (bytesToBv8 keyBytes).length = 32 := by simp [bytesToBv8, h]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 hlen_bv
  have hpk_sp_tail (R_tail : SepProp) :
      (s0.sp - 400#64) ↦₆₄ w0 ∗ ((s0.sp - 392#64) ↦₆₄ w1 ∗
      ((s0.sp - 384#64) ↦₆₄ w2 ∗ ((s0.sp - 376#64) ↦₆₄ w3 ∗ R_tail))) =
      (s0.sp - 400#64) ↦ₛ bytesToBv8 keyBytes ∗ R_tail := by
    have hpk_sp := hpk_cells (s0.sp - 400#64)
    have ha1 : s0.sp - 400#64 + 8#64 = s0.sp - 392#64 := by bv_arith
    have ha2 : s0.sp - 400#64 + 16#64 = s0.sp - 384#64 := by bv_arith
    have ha3 : s0.sp - 400#64 + 24#64 = s0.sp - 376#64 := by bv_arith
    rw [ha1, ha2, ha3] at hpk_sp
    rw [hpk_sp, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  have hpk_reg0_tail (R_tail : SepProp) :
      s0.readReg64 (Reg.gpr 0#5) ↦₆₄ w0 ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1 ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2 ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3 ∗ R_tail))) =
      s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ R_tail := by
    rw [hpk_cells (s0.readReg64 (Reg.gpr 0#5)), sepConj_assoc, sepConj_assoc, sepConj_assoc]
  wp_conv_pre => rw [← hpk_reg0_tail]
  wp_steps
  wp_conv_pre => rw [hpk_reg0_tail, hpk_sp_tail]
  wp_call hmont_call ⟨keyBytes, 0, s0.sp - 400#64, s0.sp - 360#64⟩
  wp_conv_pre => rw [show (0 : UInt8) &&& 1 = 0 from rfl, ← hpk_sp_tail]
  cases hmont : P.montToEd keyBytes 0 with
  | none =>
    have hcanon_none : isCanonicalRef P keyBytes = false := by
      simp [isCanonicalRef, hmont]
    rw [hcanon_none]
    wp_conv_pre =>
      rw [dalekMontToEdOutAt_none P keyBytes 0 hmont (s0.sp - 360#64), sepConj_assoc]
    wp_steps
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (memRegion168_of_cell_and_memRegion160 (s0.sp - 360#64) 0#64 _))))) ?_
    wp_done
  | some edPt =>
    have hed_len : edPt.length = 160 := hmontLen keyBytes 0 edPt hmont
    have hed_bv_len : (bytesToBv8 edPt).length = 160 := by simp [bytesToBv8, hed_len]
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
      e16, e17, e18, e19, hed_cells⟩ :=
      exists_unpack64_of_length_160 hed_bv_len
    refine sepWP_memRegion160_head (s0.sp - 192#64)
      (F_rest := (s0.sp - 400#64) ↦₆₄ w0 ∗
        ((s0.sp - 392#64) ↦₆₄ w1 ∗
          ((s0.sp - 384#64) ↦₆₄ w2 ∗
            ((s0.sp - 376#64) ↦₆₄ w3 ∗
              (dalekMontToEdOutAt P (s0.sp - 360#64) keyBytes 0 ∗
                (stackAt (s0.sp - 400#64) pqxdhHookStackExt ∗
                  (s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗
                    (memRegion (s0.sp - 368#64) 8 ∗
                        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                              (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))))))))))
      (by ac_rfl)
      fun u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 => ?_
    wp_conv_pre =>
      rw [dalekMontToEdOutAt_some P keyBytes edPt 0 hmont hed_len (s0.sp - 360#64),
        sepConj_assoc ((s0.sp - 360#64) ↦₆₄ 1#64),
        ← hed_cells (s0.sp - 360#64 + 8#64)]
    wp_steps
    wp_conv_pre =>
      rw [hed_cells (s0.sp - 192#64), hed_cells (s0.sp - 360#64 + 8#64)]
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (memRegion168_of_cell_and_bytes160
          (s0.sp - 360#64) 1#64 hed_bv_len _)))))) ?_
    wp_call htors_call ⟨s0.sp - 192#64, edPt⟩
    clear u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19
      e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 hed_cells
    refine SepWP.weaken_pre (memRegion160_of_bytes160 (s0.sp - 192#64) hed_bv_len _) ?_
    cases htors : P.isTorsionFree edPt with
    | false =>
      have hcanon_false : isCanonicalRef P keyBytes = false := by
        simp [isCanonicalRef, hmont, htors]
      rw [hcanon_false]
      simp only [htors, Bool.false_eq_true, ite_false] at hpost_1
      have hx0_8 : BitVec.setWidth 8 (sf_1.readReg64 (Reg.gpr 0#5)) = 0#8 := by
        revert hpost_1; bv_bits
      wp_steps
      wp_done
    | true =>
      simp only [htors, ite_true] at hpost_1
      have hfocus8 (off : Nat) (hoff : off < 32) (R_tail : SepProp) :
          s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ R_tail =
            ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 off) ↦₈
              (bytesToBv8 keyBytes).getD off 0#8) ∗
            ((s0.readReg64 (Reg.gpr 0#5) ↦ₛ (bytesToBv8 keyBytes).take off) ∗
             ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (off + 1)) ↦ₛ
              (bytesToBv8 keyBytes).drop (off + 1) ∗ R_tail)) := by
        rw [pointsToBytes_focus8 (s0.readReg64 (Reg.gpr 0#5)) (bytesToBv8 keyBytes) off
            (by rw [hlen_bv]; exact hoff),
          sepConj_assoc, sepConj_assoc]
      have hfocus64 (off : Nat) (hoff : off + 8 ≤ 32) (R_tail : SepProp) :
          s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ R_tail =
            ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 off) ↦₆₄
              pack64 ((bytesToBv8 keyBytes).getD off 0#8) ((bytesToBv8 keyBytes).getD (off + 1) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 2) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 3) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 4) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 5) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 6) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 7) 0#8)) ∗
            ((s0.readReg64 (Reg.gpr 0#5) ↦ₛ (bytesToBv8 keyBytes).take off) ∗
             ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (off + 8)) ↦ₛ
              (bytesToBv8 keyBytes).drop (off + 8) ∗ R_tail)) := by
        rw [pointsToBytes_focus64 (s0.readReg64 (Reg.gpr 0#5)) (bytesToBv8 keyBytes) off
            (by rw [hlen_bv]; exact hoff),
          sepConj_assoc, sepConj_assoc]
      wp_conv_pre => rw [hfocus8 31 (by decide)]
      wp_steps
      wp_conv_pre => rw [← hfocus8 31 (by decide)]
      cases hb31 : ((bytesToBv8 keyBytes).getD 31 0#8).getLsbD 7 with
      | true =>
        have hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = false := by
          rw [bytesToBv8_getD] at hb31
          exact (uint8_getLsbD7_eq_true_iff _).mp hb31
        have hcanon_b31 : isCanonicalRef P keyBytes = false := by
          unfold isCanonicalRef; rw [hb31_u8]; simp
        rw [hcanon_b31]
        simp only [beq_self_eq_true, ite_true]
        wp_steps
        wp_done
      | false =>
        have hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = true := by
          rw [bytesToBv8_getD] at hb31
          exact (uint8_getLsbD7_eq_false_iff _).mp hb31
        simp only [beq_iff_eq, Bool.false_eq_true, ite_false]
        wp_conv_pre => rw [hfocus8 0 (by decide)]
        wp_steps
        wp_conv_pre => rw [← hfocus8 0 (by decide)]
        cases hb0 : (BitVec.zeroExtend 64 ((bytesToBv8 keyBytes).getD 0 0#8)).ult 237#64 with
        | true =>
          have hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = false := by
            rw [bytesToBv8_getD] at hb0
            exact (uint8_ult237_eq_true_iff _).mp hb0
          have hlen_beq : (keyBytes.length == 32) = true := beq_iff_eq.mpr h
          have hcanon_b0 : isCanonicalRef P keyBytes = true := by
            simp only [isCanonicalRef, scalarIsInRange, hlen_beq, hb31_u8, hb0_u8, hmont, htors]
            rfl
          rw [hcanon_b0]
          simp only [ite_true]
          wp_steps
          wp_done
        | false =>
          have hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = true := by
            rw [bytesToBv8_getD] at hb0
            exact (uint8_ult237_eq_false_iff _).mp hb0
          simp only [Bool.false_eq_true, ite_false]
          wp_conv_pre => rw [hfocus64 1 (by decide)]
          wp_step
          wp_conv_pre => rw [← hfocus64 1 (by decide), hfocus64 9 (by decide)]
          wp_steps
          wp_conv_pre => rw [← hfocus64 9 (by decide), hfocus64 17 (by decide)]
          wp_step
          wp_conv_pre => rw [← hfocus64 17 (by decide), hfocus64 23 (by decide)]
          wp_steps
          wp_conv_pre => rw [← hfocus64 23 (by decide)]
          rw [ecPubKeyIsCanonical_tail_eq P keyBytes edPt h hmont htors hb31_u8 hb0_u8]
          wp_done

theorem ecPubKeyIsCanonical_call_ok_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)}
    (hWF : StructuralPrims P) (hH : PqxdhHookContractsExt P A img absHooks) :
    subroutine_ok (tripleRatchetProgAtExt img.base absHooks)
      ((tripleRatchetProgAtExt img.base absHooks).fnAddr ecPubKeyIsCanonicalSym)
      (ecPubKeyIsCanonicalCallSpecExt P) :=
  ecPubKeyIsCanonical_call_ok'_ext hWF.isCanonical_eq_isCanonicalRef hWF.montToEd_len
    hH.dalekMontToEd hH.dalekTorsionFree

end CryptoVerification.E2E.Pqxdh.Shared
