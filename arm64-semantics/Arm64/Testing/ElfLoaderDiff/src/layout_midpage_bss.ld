ENTRY(_start)

PHDRS {
    rx  PT_LOAD FLAGS(5);
    rw  PT_LOAD FLAGS(6);
    stk PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    . = 0x400200;
    .text : { *(.text*) } :rx

    . = 0x402380;
    .mid_data : { *(.mid_data) } :rw
    .mid_bss (NOLOAD) : { *(.mid_bss) } :rw

    .file_tail_marker 0 : { KEEP(*(.file_tail_marker)) }
    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
