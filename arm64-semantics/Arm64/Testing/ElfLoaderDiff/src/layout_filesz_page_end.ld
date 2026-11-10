ENTRY(_start)

PHDRS {
    rx  PT_LOAD FILEHDR PHDRS FLAGS(5);
    rw  PT_LOAD FLAGS(6);
    stk PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    . = 0x710000 + SIZEOF_HEADERS;
    .text : { *(.text*) } :rx

    . = ALIGN(0x1000) + (. & 0xfff);
    /* Pad `.data` with a non-zero fill so that `p_vaddr + p_filesz` is exactly page-aligned. */
    .data : { *(.data) . = ALIGN(0x1000); } :rw =0xa5a5a5a5
    .bss (NOLOAD) : { *(.bss) } :rw

    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
