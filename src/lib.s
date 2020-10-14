.intel_syntax noprefix
.section .text.yield_fiber
.global yield_fiber
.section .text.enter_fiber
.global enter_fiber

enter_fiber:
    mov [rsp-6*8], rbx
    mov [rsp-5*8], rbp
    mov [rsp-4*8], r12
    mov [rsp-3*8], r13
    mov [rsp-2*8], r14
    mov [rsp-1*8], r15
    mov rcx, rdi
    mov rdi, rsp
    mov r8, rsi
    mov rsi, rdx
    mov rsp, rcx
    call r8
    ud2

yield_fiber:
    mov [rsp-6*8], rbx
    mov [rsp-5*8], rbp
    mov [rsp-4*8], r12
    mov [rsp-3*8], r13
    mov [rsp-2*8], r14
    mov [rsp-1*8], r15
    mov rax, rsp
    mov rsp, rdi
    mov rbx, [rsp-6*8]
    mov rbp, [rsp-5*8]
    mov r12, [rsp-4*8]
    mov r13, [rsp-3*8]
    mov r14, [rsp-2*8]
    mov r15, [rsp-1*8]
    ret
