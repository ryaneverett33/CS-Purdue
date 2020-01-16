.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
.global main
.balign 4
main:
	mov r11, lr
	LDR r0, =println
	push {lr}
	bl printf
	pop {lr}
	mov pc, r11
Recurse_recurse:
	CMP r1, r1, #3
	MOVLT r1, #1
	MOVGE r1, #0
Recurse_recurse_b0:
Recurse_recurse_b1:
	SUB v1, v1, #1
