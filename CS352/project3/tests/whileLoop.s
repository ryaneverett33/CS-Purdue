.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
.global main
.balign 4
main:
	MOV r11, lr
	MOV r0, #4
	BL malloc
	MOV r1, r0
	PUSH {r1}
	BL Test_loop
	MOV r1, r0
	LDR r0, =println
	bl printf
	MOV pc, r11
Test_loop:
	MOV r9, sp
	ADD r9, r9, #0
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #0
	MOV r8, #0
	STR r8, [r10]
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #0
	LDR r1, [r10]
	CMP r1, #69
	MOVLT r1, #1
	MOVGE r1, #0
	CMP r1, #1
	BLEQ Test_loop_b0
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #0
	LDR r1, [r10]
	MOV r0, r1
	MOV r10, r9
	SUB r10, #4
	MOV sp, r9
	LDR pc, [r10]
Test_loop_b0:
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #0
	LDR r1, [r10]
	ADD r1, r1, #1
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #0
	STR r1, [r10]
	POP {lr}
	SUB lr, lr, #40
	PUSH {lr}
	POP {pc}
