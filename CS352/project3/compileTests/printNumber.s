.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
.global main
.balign 4
main:
	mov r11, lr
	mov r10, #5
	sub r1, r10, #6
	ldr r0, =println
	push {lr}
	bl printf
	pop {lr}
	mov pc, r11
