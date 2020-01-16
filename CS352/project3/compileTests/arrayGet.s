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
	BL Arr_run
	MOV r1, r0
	LDR r0, =println
	bl printf
	MOV pc, r11
Arr_run:
	MOV r9, sp
	ADD r9, r9, #0
	PUSH {lr}
	SUB sp, sp, #4
	MOV r0, #24
	PUSH {lr}
	BL malloc
	POP {lr}
	MOV r1, r0
	MOV r10, #5
	STR r10, [r0]
	MOV r10, r9
	SUB r10, r10, #8
	STR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r1
	ADD r10, r10, #4
	MOV r6, #10
	STR r6, [r10]
	MOV r10, #1
	ADD r2, r10, #0
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r1
	MOV r6, #4
	MUL r2, r2, r6
	ADD r2, #4
	ADD r10, r10, r2
	MOV r6, #10
	STR r6, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	ADD r1, #8
	LDR r1, [r1]
	LDR r0, =println
	PUSH {lr}
	bl printf
	POP {lr}
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	ADD r1, #4
	LDR r1, [r1]
	MOV r0, r1
	MOV r10, r9
	SUB r10, #4
	MOV sp, r9
	LDR pc, [r10]
