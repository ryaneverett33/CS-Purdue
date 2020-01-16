.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
.global main
.balign 4
main:
	mov r11, lr
	PUSH r1
	BL run
	MOV r1, r0
	LDR r0, =println
	push {lr}
	bl printf
	pop {lr}
	mov pc, r11
B_run:
	MOV r9, sp
	ADD r9, r9, #0
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #8
	STR, r1, [r10]
	MOV r0, #1
