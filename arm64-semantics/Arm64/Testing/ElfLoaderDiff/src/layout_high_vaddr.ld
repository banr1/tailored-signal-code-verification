ENTRY(_start)

PHDRS {
    rx  PT_LOAD FILEHDR PHDRS FLAGS(5);
    rw  PT_LOAD FLAGS(6);
    stk PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    . = 0x10000 + SIZEOF_HEADERS;
    .text : { *(.text*) } :rx

    . = 0x100002000 + (. & 0xfff);
    .data : { *(.data) } :rw
    .bss (NOLOAD) : { *(.bss) } :rw

    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
