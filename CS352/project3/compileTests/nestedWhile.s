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
	BL Obj_run
	MOV r1, r0
	LDR r0, =println
	bl printf
	MOV pc, r11
Obj_run:
	MOV r9, sp
	ADD r9, r9, #0
	PUSH {lr}
	SUB sp, sp, #4
	MOV r10, r9
	SUB r10, r10, #8
	MOV r8, #0
	STR r8, [r10]
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #0
	MOV r8, #0
	STR r8, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	CMP r1, #5
	MOVLT r1, #1
	MOVGE r1, #0
	CMP r1, #1
	BLEQ Obj_run_b0
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #0
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r2, [r10]
	MUL r1, r1, r2
	MOV r0, r1
	MOV r10, r9
	SUB r10, #4
	MOV sp, r9
	LDR pc, [r10]
Obj_run_b0:
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #0
	LDR r1, [r10]
	CMP r1, #5
	MOVLT r1, #1
	MOVGE r1, #0
	CMP r1, #1
	BLEQ Obj_run_b0_b0
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	ADD r1, r1, #1
	MOV r10, r9
	SUB r10, r10, #8
	STR r1, [r10]
	POP {lr}
	SUB lr, lr, #32
	PUSH {lr}
	POP {pc}
Obj_run_b0_b0:
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
