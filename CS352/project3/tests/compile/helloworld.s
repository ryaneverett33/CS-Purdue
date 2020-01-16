.section .text

@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
mprint0: .asciz "Hello World\n"
.global main
.balign 4
main:
mov r11, lr
ldr r0, =mprint0
push {lr}
bl printf
pop {lr}
mov pc, r11
