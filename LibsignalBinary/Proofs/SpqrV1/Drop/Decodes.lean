/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Specifications.RustHeap.Alloc
public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
public import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Instruction Decode Trees and Layout Offsets for SPQR V1 Drop Glue

Isolates `gen_decodes`, `ls_off%`, and `ls_stub%` invocations for SPQR V1 drop-glue functions so
that downstream symbolic execution files do not unpickle `libsignalSessionCode_tree`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.CodeLayout

abbrev deallocName : String := "__rustc::__rust_dealloc"

abbrev deallocStubOff : Nat := num% (ls_off% "__rustc::__rust_dealloc")

@[simp, arm64_norm] theorem dealloc_fnOff_drop :
    libsignalSessionCode.fnOff "__rustc::__rust_dealloc" =
      num% (ls_off% "__rustc::__rust_dealloc") :=
  ls_stub% "__rustc::__rust_dealloc"

/-- `libsignalSessionCode` rebased at `b` with `Rust.withPanics ext`
(definitionally equal to `tripleRatchetProgAtExt b ext` in `Hooks2.lean`, without importing `InImage.*`). -/
noncomputable abbrev dropProgAtExt (b : BitVec 64) (ext : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics ext)

/-- `subroutine_ok` contract for `__rustc::__rust_dealloc` on `dropProgAtExt b ext`
(satisfied directly by `hA.dealloc` for any `hA : AllocContracts b A ext`). -/
abbrev DeallocOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr "__rustc::__rust_dealloc") (rustDeallocSpec A)

abbrev dropChainEpochSliceLocal1Name : String :=
  "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#1]"

abbrev dropChainEpochSliceLocal2Name : String :=
  "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]"

abbrev dropSpqrChainName : String :=
  "core::ptr::drop_glue::<spqr::chain::Chain>"

abbrev dropProtoEpochSliceName : String :=
  "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>"

abbrev dropProtoSpqrChainName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]"

abbrev dropOptProtoSpqrChainName : String :=
  "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>"

abbrev dropPoly16Name : String :=
  "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>"

abbrev dropSortedSetPt16Name : String :=
  "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>"

abbrev dropPolyEncoderLocal1Name : String :=
  "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]"

abbrev dropPolyDecoderName : String :=
  "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]"

abbrev dropPolyEncoderLocal2Name : String :=
  "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]"

abbrev dropProtoPolyEncoderName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"

abbrev dropOptProtoPolyEncoderName : String :=
  "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]"

abbrev dropUnchunkedCt1SentLocal1Name : String :=
  "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]"

abbrev dropUnchunkedCt1SentLocal2Name : String :=
  "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]"

abbrev dropUnchunkedEkSentName : String :=
  "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>"

abbrev dropOptProtoUnchunkedCt1SentName : String :=
  "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#1]"

abbrev dropProtoUnchunkedCt1SentEkReceivedName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>"

abbrev dropChunkedHeaderSentName : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>"

abbrev dropChunkedCt1ReceivedName : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>"

abbrev dropChunkedEkSentCt1ReceivedName : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>"

abbrev dropChunkedEkReceivedCt1SampledName : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>"

abbrev dropChunkedCt2SampledName : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>"

abbrev dropProtoChunkedHeaderSentName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>"

abbrev dropProtoChunkedEkSentCt1ReceivedName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>"

abbrev dropProtoChunkedHeaderReceivedName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>"

abbrev dropProtoChunkedNoHeaderReceivedName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>"

abbrev dropProtoChunkedCt1ReceivedName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>"

@[simp, arm64_norm] theorem dropChainEpochSliceLocal1_fnOff :
    libsignalSessionCode.fnOff dropChainEpochSliceLocal1Name =
      num% (ls_off% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#1]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#1]"

@[simp, arm64_norm] theorem dropChainEpochSliceLocal2_fnOff :
    libsignalSessionCode.fnOff dropChainEpochSliceLocal2Name =
      num% (ls_off% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]"

@[simp, arm64_norm] theorem dropSpqrChain_fnOff :
    libsignalSessionCode.fnOff dropSpqrChainName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::chain::Chain>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::chain::Chain>"

@[simp, arm64_norm] theorem dropProtoEpochSlice_fnOff :
    libsignalSessionCode.fnOff dropProtoEpochSliceName =
      num% (ls_off% "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>"

@[simp, arm64_norm] theorem dropProtoSpqrChain_fnOff :
    libsignalSessionCode.fnOff dropProtoSpqrChainName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]"

@[simp, arm64_norm] theorem dropOptProtoSpqrChain_fnOff :
    libsignalSessionCode.fnOff dropOptProtoSpqrChainName =
      num% (ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>"

@[simp, arm64_norm] theorem dropPoly16_fnOff :
    libsignalSessionCode.fnOff dropPoly16Name =
      num% (ls_off% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>"

@[simp, arm64_norm] theorem dropSortedSetPt16_fnOff :
    libsignalSessionCode.fnOff dropSortedSetPt16Name =
      num% (ls_off% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>"

@[simp, arm64_norm] theorem dropPolyEncoderLocal1_fnOff :
    libsignalSessionCode.fnOff dropPolyEncoderLocal1Name =
      num% (ls_off% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]"

@[simp, arm64_norm] theorem dropPolyDecoder_fnOff :
    libsignalSessionCode.fnOff dropPolyDecoderName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]"

@[simp, arm64_norm] theorem dropPolyEncoderLocal2_fnOff :
    libsignalSessionCode.fnOff dropPolyEncoderLocal2Name =
      num% (ls_off% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]"

@[simp, arm64_norm] theorem dropProtoPolyEncoder_fnOff :
    libsignalSessionCode.fnOff dropProtoPolyEncoderName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"

@[simp, arm64_norm] theorem dropOptProtoPolyEncoder_fnOff :
    libsignalSessionCode.fnOff dropOptProtoPolyEncoderName =
      num% (ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]"

@[simp, arm64_norm] theorem dropUnchunkedCt1SentLocal1_fnOff :
    libsignalSessionCode.fnOff dropUnchunkedCt1SentLocal1Name =
      num% (ls_off% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]"

@[simp, arm64_norm] theorem dropUnchunkedCt1SentLocal2_fnOff :
    libsignalSessionCode.fnOff dropUnchunkedCt1SentLocal2Name =
      num% (ls_off% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]"

@[simp, arm64_norm] theorem dropUnchunkedEkSent_fnOff :
    libsignalSessionCode.fnOff dropUnchunkedEkSentName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>"

@[simp, arm64_norm] theorem dropOptProtoUnchunkedCt1Sent_fnOff :
    libsignalSessionCode.fnOff dropOptProtoUnchunkedCt1SentName =
      num% (ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#1]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#1]"

@[simp, arm64_norm] theorem dropProtoUnchunkedCt1SentEkReceived_fnOff :
    libsignalSessionCode.fnOff dropProtoUnchunkedCt1SentEkReceivedName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>"

@[simp, arm64_norm] theorem dropChunkedHeaderSent_fnOff :
    libsignalSessionCode.fnOff dropChunkedHeaderSentName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>"

@[simp, arm64_norm] theorem dropChunkedCt1Received_fnOff :
    libsignalSessionCode.fnOff dropChunkedCt1ReceivedName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>"

@[simp, arm64_norm] theorem dropChunkedEkSentCt1Received_fnOff :
    libsignalSessionCode.fnOff dropChunkedEkSentCt1ReceivedName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>"

@[simp, arm64_norm] theorem dropChunkedEkReceivedCt1Sampled_fnOff :
    libsignalSessionCode.fnOff dropChunkedEkReceivedCt1SampledName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>"

@[simp, arm64_norm] theorem dropChunkedCt2Sampled_fnOff :
    libsignalSessionCode.fnOff dropChunkedCt2SampledName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>"

@[simp, arm64_norm] theorem dropProtoChunkedHeaderSent_fnOff :
    libsignalSessionCode.fnOff dropProtoChunkedHeaderSentName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>"

@[simp, arm64_norm] theorem dropProtoChunkedEkSentCt1Received_fnOff :
    libsignalSessionCode.fnOff dropProtoChunkedEkSentCt1ReceivedName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>"

@[simp, arm64_norm] theorem dropProtoChunkedHeaderReceived_fnOff :
    libsignalSessionCode.fnOff dropProtoChunkedHeaderReceivedName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>"

@[simp, arm64_norm] theorem dropProtoChunkedNoHeaderReceived_fnOff :
    libsignalSessionCode.fnOff dropProtoChunkedNoHeaderReceivedName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>"

@[simp, arm64_norm] theorem dropProtoChunkedCt1Received_fnOff :
    libsignalSessionCode.fnOff dropProtoChunkedCt1ReceivedName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>"

end CryptoVerification.SpqrV1.Drop

namespace CryptoVerification.SpqrV1.Layout.L1

open Lean Meta Elab Command Arm64 CryptoVerification.CodeLayout

syntax (name := genFnDecodesStx)
  "gen_fn_decodes " ident ident " [" str,* "]" : command

@[command_elab genFnDecodesStx] meta def elabGenFnDecodes : CommandElab := fun stx => do
  match stx with
  | `(gen_fn_decodes $tree:ident $pfx:ident [$syms:str,*]) =>
    let pfxStr := pfx.getId.eraseMacroScopes.toString
    let isPublic := (← getScope).isPublic
    liftTermElabM do
      let treeName ← realizeGlobalConstNoOverloadWithInfo tree
      let codeName := `CryptoVerification.libsignalSessionCode
      let fnEntries ← ProofLib.CodeLookup.entries codeName .fnOff
      let stubEntries ← ProofLib.CodeLookup.entries codeName .stubOff
      let allOffs := (fnEntries ++ stubEntries).map (·.val)
      for sym in syms.getElems do
        let e ← ProofLib.CodeLookup.lookupOff codeName sym.getString
        let a := e.val
        let greater := allOffs.filter (· > a)
        let some nextOff := greater.foldl (fun acc x => match acc with | none => some x | some m => some (min m x)) none
          | throwErrorAt sym "gen_fn_decodes: no symbol after {sym}"
        let count := (nextOff - a) / 4
        for i in [0 : count] do
          let off := a + 4 * i
          let hex := String.ofList (Nat.toDigits 16 off)
          let short := Name.mkSimple (pfxStr ++ "_decode_0" ++ "x" ++ hex)
          let declName ← withExporting (isExporting := isPublic) <|
            mkDeclName (← getCurrNamespace) {} short
          let ty ← decodeStmt treeName off false
          let optInstr := mkApp (mkConst ``Option [.zero]) (mkConst ``Instr)
          let lhs := ty.appFn!.appArg!
          addDecl (.thmDecl {
            name := declName.1
            levelParams := []
            type := ty
            value := mkApp2 (mkConst ``Eq.refl [.succ .zero]) optInstr lhs })
  | _ => throwUnsupportedSyntax

end CryptoVerification.SpqrV1.Layout.L1

namespace CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.Layout.L1

gen_fn_decodes libsignalSessionCode_tree spqrDropChainEpochBin
  ["core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#1]",
   "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]",
   "core::ptr::drop_glue::<spqr::chain::Chain>",
   "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>",
   "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]",
   "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>",
   "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>",
   "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>",
   "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]",
   "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]",
   "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]",
   "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>",
   "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]",
   "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]",
   "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]",
   "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>",
   "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#1]",
   "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>",
   "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>",
   "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>",
   "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>",
   "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>",
   "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>",
   "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>",
   "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>",
   "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>",
   "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>",
   "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>"]

end CryptoVerification.SpqrV1.Drop
