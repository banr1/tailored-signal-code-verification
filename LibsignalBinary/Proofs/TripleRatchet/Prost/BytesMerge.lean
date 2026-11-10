/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1

/-!
# Verification of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#1]`

Re-exports the verification of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]`
against `bytesMergeSpec`.
-/

@[expose] public section
