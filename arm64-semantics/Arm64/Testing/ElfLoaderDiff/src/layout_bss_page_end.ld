ENTRY(_start)

PHDRS {
    rx  PT_LOAD FILEHDR PHDRS FLAGS(5);
    rw  PT_LOAD FLAGS(6);
    stk PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    . = 0x700000 + SIZEOF_HEADERS;
    .text : { *(.text*) } :rx

    . = ALIGN(0x1000) + (. & 0xfff);
    .data : { *(.data) } :rw
    /* Pad `.bss` so that `p_vaddr + p_memsz` is exactly page-aligned. */
    .bss (NOLOAD) : { *(.bss) . = ALIGN(0x1000); } :rw

    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
