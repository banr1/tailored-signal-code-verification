/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Specifications.LibsignalPublicApi
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTag8
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueDealloc

/-!
# `PreKeySignalMessage::new` Field Encoding and Epilogue

Composes protobuf field encoding across tags 1–8 (`SeamA → SeamB`, `+0x25c..+0x4c4`) with the
`into_boxed_slice` conversion, 248-byte `sret` write, temporary buffer deallocations, and epilogue
(`SeamB → exit`, `+0x4c4..+0x608`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Fields

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

variable {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel}
  {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)}

/-- Field-encoding segment (`+0x25c..+0x4c4`, `SeamA → SeamB`): encodes protobuf tags 1–8 into
`serialized: Vec<u8>` at `sp + 0xe0`, reaching `SeamB` or an OOM panic outcome. -/
theorem fields_encode_ok (_h3 : PublicApiHooks C A S encRecord abs)
    (_himg : Obj.Loads libsignalSessionImage img)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA img A x g R s0 s) :
    PreKeyMsgSegExit img C A ctl abs x R s0 s
      (SeamB img A x g R s0) := by
  exact fields_encode_core_ok x g R s0 s hA

/-- Epilogue segment (`+0x4c4..+0x608`, `SeamB → exit`): converts `serialized` via
`into_boxed_slice`, writes the 248-byte `Ok` result at `x.ret`, frees the four temporary heap
clones, and returns. -/
theorem fields_epilogue_ok (h3 : PublicApiHooks C A S encRecord abs)
    (_himg : Obj.Loads libsignalSessionImage img)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hB : SeamB img A x g R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (preKeyMsgNewSpec A) x R s0 s := by
  exact FieldsEpilogue.fields_epilogue_ok_aux h3.alloc hB

/-- Combined field-encoding and epilogue segment (`+0x25c..+0x608`, `SeamA → exit`). -/
theorem fields_ok (h3 : PublicApiHooks C A S encRecord abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA img A x g R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (preKeyMsgNewSpec A) x R s0 s :=
  preKeyMsgSegExit_chain (fields_encode_ok h3 himg x g R s0 s hA)
    (fun s' hB => fields_epilogue_ok h3 himg x g R s0 s' hB)

theorem fields_encode_ok_ext {ext : String → Option (State → State)}
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (_himg : Obj.Loads libsignalSessionImage img)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA img A x g R s0 s) :
    PreKeyMsgSegExit_ext img A ext x R s0 s (SeamB img A x g R s0) :=
  fields_encode_core_ok_ext hMc x g R s0 s hA

theorem fields_epilogue_ok_ext {ext : String → Option (State → State)}
    (hAlloc : AllocHooks A ext)
    (_himg : Obj.Loads libsignalSessionImage img)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hB : SeamB img A x g R s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext) (preKeyMsgNewSpec A) x R s0 s :=
  FieldsEpilogue.fields_epilogue_ok_aux_ext hAlloc hB

theorem fields_ok_ext {ext : String → Option (State → State)}
    (hAlloc : AllocHooks A ext)
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (himg : Obj.Loads libsignalSessionImage img)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA img A x g R s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext) (preKeyMsgNewSpec A) x R s0 s :=
  preKeyMsgSegExit_chain_ext (fields_encode_ok_ext hMc himg x g R s0 s hA)
    (fields_epilogue_ok_ext hAlloc himg x g R s0)

theorem fields_encode_ok_trap (_h3 : TripleRatchetHooks C A S (trTrapExterns C abs))
    (_himg : Obj.Loads libsignalSessionImage img)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA img A x g R s0 s) :
    PreKeyMsgSegExit_trap img C A abs x R s0 s (SeamB img A x g R s0) :=
  fields_encode_core_ok_trap x g R s0 s hA

theorem fields_epilogue_ok_trap (h3 : TripleRatchetHooks C A S (trTrapExterns C abs))
    (_himg : Obj.Loads libsignalSessionImage img)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hB : SeamB img A x g R s0 s) :
    reaches_outcome (trTrapProgAt img.base C abs) (preKeyMsgNewSpec A) x R s0 s := by
  have hA : AllocHooks A abs :=
    ⟨by simpa only [HookSat, trTrapExterns_of_not_mem C abs (n := "__rustc::__rust_alloc") (by decide) (by decide)] using h3.alloc.alloc,
     by simpa only [HookSat, trTrapExterns_of_not_mem C abs (n := "__rustc::__rust_dealloc") (by decide) (by decide)] using h3.alloc.dealloc,
     by simpa only [HookSat, trTrapExterns_of_not_mem C abs (n := "__rustc::__rust_realloc") (by decide) (by decide)] using h3.alloc.realloc⟩
  exact FieldsEpilogue.fields_epilogue_ok_aux_trap hA hB

theorem fields_ok_trap (h3 : TripleRatchetHooks C A S (trTrapExterns C abs))
    (himg : Obj.Loads libsignalSessionImage img)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA img A x g R s0 s) :
    reaches_outcome (trTrapProgAt img.base C abs) (preKeyMsgNewSpec A) x R s0 s :=
  preKeyMsgSegExit_chain_trap (fields_encode_ok_trap h3 himg x g R s0 s hA)
    (fields_epilogue_ok_trap h3 himg x g R s0)

/-! ## Relocatable Placement Proofs -/

open CryptoVerification.LibsignalPublicApi.Placed

theorem fields_encode_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A x g R s0 s) :
    PreKeyMsgSegExit_placed A H x R s0 s (SeamB_placed A x g R s0) :=
  fields_encode_core_placed_ok hshim halloc hrealloc hmemcpy hpanic x g R s0 s hA

theorem fields_epilogue_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hB : SeamB_placed A x g R s0 s) :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec A) x R s0 s :=
  FieldsEpilogue.fields_epilogue_placed_ok_aux hdealloc hB

theorem fields_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A x g R s0 s) :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec A) x R s0 s :=
  preKeyMsgSegExit_placed_chain
    (fields_encode_placed_ok hshim halloc hrealloc hmemcpy hpanic x g R s0 s hA)
    (fun s' hB => fields_epilogue_placed_ok hdealloc x g R s0 s' hB)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Fields
