// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

/*
 * Minimal static musl fixture exercising stock `abort()` (`SIGABRT` -> shell status 134,
 * `ProcessOutcome.signal = some 6`) versus `exit(134)` (`ProcessOutcome.signal = none`).
 */
#include <stdlib.h>

int main(int argc, char **argv) {
    (void)argv;
    if (argc > 1) {
        return 134;
    }
    abort();
}
