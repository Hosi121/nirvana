.text
.globl fixture
.type fixture,@function
fixture:
    mov 0(%rdi),%rax
    mov 16(%rdi),%r8
    mov $3,%ecx
.Lloop:
    mov %rax,%r10
    xor %edx,%edx
    divq 8(%rdi)
    test $1,%r8b
    jz .Ljoin
    add %rdx,%r8
.Ljoin:
    add %r10,%rax
    dec %ecx
    jnz .Lloop
    mov %rax,0(%rdi)
    mov %rdx,8(%rdi)
    mov %r8,16(%rdi)
    ret
.size fixture,.-fixture
.section .note.GNU-stack,"",@progbits
