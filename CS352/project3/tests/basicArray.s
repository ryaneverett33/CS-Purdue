.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
mprint0: .asciz ", "
mprint1: .asciz ", "
mprint2: .asciz "
"
mprint3: .asciz "Bool Arr is True\n"
.global main
.balign 4
main:
	MOV r11, lr
	MOV r0, #12
	BL malloc
	MOV r1, r0
	PUSH {r1}
	BL Test_run
	MOV r1, r0
	LDR r0, =println
	bl printf
	MOV pc, r11
Test_run:
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
	STR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #4
	STR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #8
	STR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #0
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #4
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #8
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #8
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #0
	LDR r1, [r10]
	LDR r0, =print
	PUSH {lr}
	bl printf
	POP {lr}
	LDR r0, =mprint0
	PUSH {lr}
	bl printf
	POP {lr}
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #4
	LDR r1, [r10]
	LDR r0, =print
	PUSH {lr}
	bl printf
	POP {lr}
	LDR r0, =mprint1
	PUSH {lr}
	bl printf
	POP {lr}
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #4
	LDR r1, [r10]
	LDR r0, =print
	PUSH {lr}
	bl printf
	POP {lr}
	LDR r0, =mprint2
	PUSH {lr}
	bl printf
	POP {lr}
	MOV r10, r9
	SUB r10, r10, #0
	LDR r10, [r10]
	ADD r10, r10, #8
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r2, [r10]
	CMP r1, #1
	BLEQ Test_run_b0
	MOV r0, #5
	MOV r10, r9
	SUB r10, #4
	MOV sp, r9
	LDR pc, [r10]
Test_run_b0:
	PUSH {lr}
	LDR r0, =mprint3
	PUSH {lr}
	bl printf
	POP {lr}
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	ADD r1, r1, #1
	MOV r10, r9
	SUB r10, r10, #8
	STR r1, [r10]
	POP {lr}
	SUB lr, lr, #40
	PUSH {lr}
	POP {pc}
