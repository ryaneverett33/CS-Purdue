.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
.global main
.balign 4
main:
	mov r11, lr
	PUSH #5
	PUSH r1
	BL run
	MOV r1, r0
	LDR r0, =println
	push {lr}
	bl printf
	pop {lr}
	mov pc, r11
Obj_run:
	MOV r10, r9
	SUB r10, r10, #0
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #4
	ADD r10, r10, #0
	STR, r1, [r10]
	MOV r10, r9
	SUB r10, r10, #4
	LDR r10, [r10]
	ADD r10, r10, #0
	LDR r1, [r10]
