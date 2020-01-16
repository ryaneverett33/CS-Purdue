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
	BL Arr_init
	MOV r1, r0
	LDR r0, =println
	bl printf
	MOV pc, r11
Arr_init:
	MOV r9, sp
	ADD r9, r9, #0
	PUSH {lr}
	SUB sp, sp, #4
	MOV r10, #5
	ADD r2, r10, #5
	MOV r10, #5
	ADD r3, r10, #5
	MOV r0, r2
	MUL r0, r0, r3
	ADD r0, r0, #2
	MOV r10, r2
	MOV r5, r3
	PUSH {lr}
	BL malloc
	POP {lr}
	MOV r1, r0
	STR r10, [r0]
	ADD r0, r0, #4
	STR r5, [r0]
	MOV r10, r9
	SUB r10, r10, #8
	STR r1, [r10]
	MOV r0, #0
	MOV r10, r9
	SUB r10, #4
	MOV sp, r9
	LDR pc, [r10]
