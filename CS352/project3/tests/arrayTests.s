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
	BL Runner_run
	MOV r1, r0
	LDR r0, =println
	bl printf
	MOV pc, r11
Runner_run:
	MOV r9, sp
	ADD r9, r9, #0
	PUSH {lr}
	SUB sp, sp, #16
	MOV r0, #4
	PUSH {lr}
	BL malloc
	POP {lr}
	MOV r1, r0
	MOV r10, r9
	SUB r10, r10, #8
	STR r1, [r10]
	MOV r0, #4
	PUSH {lr}
	BL malloc
	POP {lr}
	MOV r1, r0
	MOV r10, r9
	SUB r10, r10, #8
	STR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	STR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r2, [r10]
	PUSH {r2}
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	PUSH {r1}
	PUSH {r9}
	BL returner_size
	POP {r9}
	MOV r1, r0
	LDR r0, =println
	PUSH {lr}
	bl printf
	POP {lr}
	MOV r10, #5
	PUSH {r10}
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	PUSH {r1}
	PUSH {r9}
	BL returner_make
	POP {r9}
	MOV r1, r0
	MOV r10, r9
	SUB r10, r10, #8
	STR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	LDR r0, =println
	PUSH {lr}
	bl printf
	POP {lr}
	MOV r0, #0
	MOV r10, r9
	SUB r10, #4
	MOV sp, r9
	LDR pc, [r10]
arguments_size:
	MOV r9, sp
	ADD r9, r9, #4
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #0
	LDR r1, [r10]
	MOV r0, r1
	MOV r10, r9
	SUB r10, #8
	MOV sp, r9
	LDR pc, [r10]
returner_make:
	MOV r9, sp
	ADD r9, r9, #4
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #4
	LDR r10, [r10]
	ADD r10, r10, #0
	STR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #4
	LDR r10, [r10]
	ADD r10, r10, #0
	LDR r1, [r10]
	MOV r0, r1
	MOV r10, r9
	SUB r10, #8
	MOV sp, r9
	LDR pc, [r10]
