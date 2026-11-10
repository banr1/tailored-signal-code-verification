ENTRY(_start)

PHDRS {
    rx   PT_LOAD FILEHDR PHDRS FLAGS(5);
    rw   PT_LOAD FLAGS(6);
    bss  PT_LOAD FLAGS(6);
    stk  PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    . = 0xb00000 + SIZEOF_HEADERS;
    .text : { *(.text*) } :rx

    . = 0xb01000 + (. & 0xfff);
    .data : { *(.data) } :rw

    . = 0xb03a40;
    .pure_bss (NOLOAD) : { *(.pure_bss) } :bss

    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) *(.bss*) }
}
