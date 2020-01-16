.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
.global main
.balign 4
main:
	mov r11, lr
	PUSH #1
	PUSH #2
	LDR r0, =println
	push {lr}
	bl printf
	pop {lr}
	mov pc, r11
Obj_add:
	ADD r1, r1, r2
