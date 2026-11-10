ENTRY(_start)

PHDRS {
    rx  PT_LOAD FILEHDR PHDRS FLAGS(5);
    rw  PT_LOAD FLAGS(6);
    stk PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    . = 0xd00000 + SIZEOF_HEADERS;
    .text : { *(.text*) } :rx

    . = 0xd01000 + (. & 0xfff);
    .data : { *(.data) } :rw

    .rw_tail_marker 0 : { KEEP(*(.rw_tail_marker)) }
    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) *(.bss*) }
}
