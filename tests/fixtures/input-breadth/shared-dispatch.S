.text
.globl fixture
.type fixture,@function
fixture:
    mov (%rdi),%ecx
    and $3,%ecx
    testq $1,24(%rdi)
    jne .Lchoose_b
    lea .Ltable_a(%rip),%rdx
    jmp .Lguard
.Lchoose_b:
    lea .Ltable_b(%rip),%rdx
.Lguard:
    cmp $1,%ecx
    jbe .Ldispatch
    mov 8(%rdi),%rax
    xor (%rdi),%rax
    jmp .Lfinish
.Ldispatch:
    # Scheduling and block layout may separate a base from its table load.
    .rept 28
    nop
    .endr
    movslq (%rdx,%rcx,4),%rax
    add %rdx,%rax
    notrack jmp *%rax
.La0:
    mov 8(%rdi),%rax
    add 16(%rdi),%rax
    jmp .Lfinish
.La1:
    mov 8(%rdi),%rax
    lea (%rax,%rax,2),%rax
    jmp .Lfinish
.Lb0:
    mov 8(%rdi),%rax
    xor 24(%rdi),%rax
    jmp .Lfinish
.Lb1:
    mov 8(%rdi),%rax
    sub 16(%rdi),%rax
.Lfinish:
    mov %rax,8(%rdi)
    xor 16(%rdi),%rax
    ret
.size fixture,.-fixture
.section .rodata
.align 4
.Ltable_a:
    .long .La0-.Ltable_a,.La1-.Ltable_a
.Ltable_b:
    .long .Lb0-.Ltable_b,.Lb1-.Ltable_b
.section .note.GNU-stack,"",@progbits
