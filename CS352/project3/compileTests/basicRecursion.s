.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
.global main
.balign 4
main:
	MOV r11, lr
	MOV r10, #4
	PUSH {r10}
	MOV r0, #4
	PUSH {lr}
	BL malloc
	POP {lr}
	MOV r0, r1
	PUSH {r1}
	PUSH {r9}
	BL Runner_recurse
	POP {r9}
	MOV r1, r0
	LDR r0, =println
	PUSH {lr}
	bl printf
	POP {lr}
	MOV pc, r11
Runner_recurse:
	MOV r9, sp
	ADD r9, r9, #4
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #0
	LDR r1, [r10]
	CMP r1, #2
	MOVLT r1, #1
	MOVGE r1, #0
	CMP r1, #1
	BLEQ Runner_recurse_b0
	CMP r1, #1
	BLNE Runner_recurse_b1
	MOV r0, #0
	MOV r10, r9
	SUB r10, #8
	MOV sp, r9
	LDR pc, [r10]
Runner_recurse_b0:
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #0
	LDR r1, [r10]
	MOV r0, r1
	MOV r10, r9
	SUB r10, #8
	MOV sp, r9
	LDR pc, [r10]
	POP {pc}
Runner_recurse_b1:
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #0
	LDR r1, [r10]
	SUB r1, r1, #1
	PUSH {r1}
	MOV r1, r9
	SUB r1, #4
	PUSH {r1}
	PUSH {r9}
	BL Runner_recurse
	POP {r9}
	MOV r1, r0
	MOV r0, r1
	MOV r10, r9
	SUB r10, #8
	MOV sp, r9
	LDR pc, [r10]
	POP {pc}
