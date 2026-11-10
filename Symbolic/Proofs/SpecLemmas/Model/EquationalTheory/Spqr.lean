/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.EquationalTheory.Spqr

/-!
# Lemmas for the `Spqr` equational theory

Proves direction-parameter round-trip (`spqrParamsDir?_spqrParams`) and characterizes the output
state of a successful `spqrRecv` transition (`spqrRecv_state`).
-/

@[expose] public section

namespace DY.Spqr

section Literals

variable [BytesFunctor] [BytesFunctor.Has Literal.SubF]

@[simp]
theorem spqrParamsDir?_spqrParams (d: Direction) :
    spqrParamsDir? (encodeSpqrDirectionParams d: Bytes) = some d := by
  cases d <;>
    simp [spqrParamsDir?, encodeSpqrDirectionParams, Direction.toByte, Literal.bytesToLiteral_literalToBytes]

end Literals

section Functions

variable [BytesFunctor] [BytesFunctor.Has SubF] [BytesFunctor.Has Literal.SubF]

/-- Every accepting `spqrRecv` transition produces `RecvState{st, msg}` as its updated state. -/
theorem spqrRecv_state (st msg: Bytes) (idx: UInt32) (r: Bytes × Bytes)
    (h: spqrRecv st msg idx = some r) :
    r.1 = ({st, msg}: RecvState.SubF Bytes).pack := by
  unfold spqrRecv at h
  split at h
  · simp at h
  · split at h
    · split at h
      · cases h; rfl
      · simp at h
    · cases h; rfl

end Functions

section AttackerKnowledgeBuild

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge] [AttackerKnowledge]

end AttackerKnowledgeBuild

section AttackerKnowledgeRun

variable [BytesFunctor] [BytesFunctor.Has SubF] [BytesFunctor.Has Literal.SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge] [AttackerKnowledge]

end AttackerKnowledgeRun

end DY.Spqr
