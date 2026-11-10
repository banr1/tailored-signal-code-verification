ENTRY(_start)

PHDRS {
    rx  PT_LOAD FLAGS(5);
    ro  PT_LOAD FLAGS(4);
    rw  PT_LOAD FLAGS(6);
    stk PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    . = 0xa01000;
    .text : { *(.text*) } :rx

    . = 0xa02000;
    .rodata : { *(.rodata*) } :ro

    . = 0xa03000;
    .data : { *(.data) } :rw

    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) *(.bss*) }
}
