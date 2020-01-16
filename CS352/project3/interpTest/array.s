.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
mprint0: .asciz "Sort successful\n"
mprint1: .asciz "Sort failed\n"
.global main
.balign 4
main:
	MOV r11, lr
	MOV r0, #4
	BL malloc
	MOV r1, r0
	PUSH {r1}
	BL Sorter_bubblesortDemo
	MOV r2, r0
	CMP r2, #1
	MOVEQ r2, #1
	MOVNE r2, #0
	CMP r2, #1
	BLEQ array_main_b0
	CMP r2, #1
	BLNE array_main_b1
	MOV pc, r11
array_main_b0:
	PUSH {lr}
	LDR r0, =mprint0
	PUSH {lr}
	bl printf
	POP {lr}
	POP {pc}
array_main_b1:
	PUSH {lr}
	LDR r0, =mprint1
	PUSH {lr}
	bl printf
	POP {lr}
	POP {pc}
Sorter_bubblesortDemo:
	MOV r9, sp
	ADD r9, r9, #0
	PUSH {lr}
	SUB sp, sp, #20
	MOV r0, #36
	PUSH {lr}
	BL malloc
	POP {lr}
	MOV r1, r0
	MOV r10, #8
	STR r10, [r0]
	MOV r10, r9
	SUB r10, r10, #8
	STR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r1
	ADD r10, r10, #4
	MOV r6, #60
	STR r6, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r1
	ADD r10, r10, #8
	MOV r6, #40
	STR r6, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r1
	ADD r10, r10, #12
	MOV r6, #20
	STR r6, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r1
	ADD r10, r10, #16
	MOV r6, #0
	STR r6, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r1
	ADD r10, r10, #20
	MOV r6, #50
	STR r6, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r1
	ADD r10, r10, #24
	MOV r6, #70
	STR r6, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r1
	ADD r10, r10, #28
	MOV r6, #10
	STR r6, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r1
	ADD r10, r10, #32
	MOV r6, #30
	STR r6, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	MOV r8, #0
	STR r8, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	MOV r8, #0
	STR r8, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	CMP r1, #8
	MOVLT r1, #1
	MOVGE r1, #0
	CMP r1, #1
	BLEQ Sorter_bubblesortDemo_b0
	MOV r10, r9
	SUB r10, r10, #8
	MOV r8, #0
	STR r8, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	MOV r8, #1
	STR r8, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	CMP r1, #8
	MOVLT r1, #1
	MOVGE r1, #0
	CMP r1, #1
	BLEQ Sorter_bubblesortDemo_b1
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r0, r1
	MOV r10, r9
	SUB r10, #4
	MOV sp, r9
	LDR pc, [r10]
Sorter_bubblesortDemo_b0:
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #8
	MOV r8, #0
	STR r8, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, #8
	SUB r1, r10, r1
	SUB r1, r1, #1
	CMP r1, r1
	MOVLT r1, #1
	MOVGE r1, #0
	CMP r1, #1
	BLEQ Sorter_bubblesortDemo_b0_b0
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
Sorter_bubblesortDemo_b0_b0:
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r2, [r10]
	MOV r6, #4
	MUL r1, r1, r6
	ADD r1, r1, #4
	LDR r1, [r1]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r2, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	ADD r1, r1, #1
	MOV r6, #4
	MUL r2, r2, r6
	ADD r2, r2, #4
	LDR r2, [r2]
	CMP r1, r2
	MOVGT r1, #1
	MOVLE r1, #0
	CMP r1, #1
	BLEQ Sorter_bubblesortDemo_b0_b0_b0
	CMP r1, #1
	BLNE Sorter_bubblesortDemo_b0_b0_b1
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
Sorter_bubblesortDemo_b0_b0_b0:
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	ADD r1, r1, #1
	MOV r6, #4
	MUL r1, r1, r6
	ADD r1, r1, #4
	LDR r1, [r1]
	MOV r10, r9
	SUB r10, r10, #8
	STR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	ADD r1, r1, #1
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r2, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r2, [r10]
	MOV r6, #4
	MUL r2, r2, r6
	ADD r2, r2, #4
	LDR r2, [r2]
	MOV r10, r1
	MOV r6, #4
	MUL r1, r1, r6
	ADD r1, #4
	ADD r10, r10, r1
	STR r2, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r2, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r2, [r10]
	MOV r10, r1
	MOV r6, #4
	MUL r2, r2, r6
	ADD r2, #4
	ADD r10, r10, r2
	STR r2, [r10]
	POP {pc}
Sorter_bubblesortDemo_b0_b0_b1:
	PUSH {lr}
	POP {pc}
Sorter_bubblesortDemo_b1:
	PUSH {lr}
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r2, [r10]
	MOV r6, #4
	MUL r1, r1, r6
	ADD r1, r1, #4
	LDR r1, [r1]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MUL r1, r1, #10
	CMP r1, r1
	MOVEQ r1, #1
	MOVNE r1, #0
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	AND r1, r1, r1
	MOV r10, r9
	SUB r10, r10, #8
	STR r1, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	ADD r1, r1, #1
	MOV r10, r9
	SUB r10, r10, #8
	STR r1, [r10]
	POP {lr}
	SUB lr, lr, #56
	PUSH {lr}
	POP {pc}
