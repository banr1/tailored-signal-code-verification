// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

#include <stddef.h>
#include <stdint.h>
#include <sys/types.h>
#include <unistd.h>

void *memset(void *dest, int c, size_t n) {
    unsigned char *s = dest;
    if ((unsigned char)c == 0 && ((uintptr_t)s & 7) == 0) {
        while (n >= 8) {
            *(uint64_t *)s = 0;
            s += 8;
            n -= 8;
        }
    }
    for (; n; n--, s++) *s = (unsigned char)c;
    return dest;
}

int main(int argc, char **argv) {
    (void)argc;
    (void)argv;
    unsigned char buf[256];
    for (;;) {
        ssize_t n = read(0, buf, sizeof(buf));
        if (n < 0) return 1;
        if (n == 0) break;
        ssize_t off = 0;
        while (off < n) {
            ssize_t w = write(1, buf + off, (size_t)(n - off));
            if (w <= 0) return 1;
            off += w;
        }
    }
    return 0;
}
