ENTRY(_start)

PHDRS {
    text PT_LOAD FILEHDR PHDRS FLAGS(5);
    stk  PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    . = 0x500000 + SIZEOF_HEADERS;
    .rodata : { *(.rodata*) } :text
    .text : { *(.text*) } :text

    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) *(.data*) *(.bss*) }
}
