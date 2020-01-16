.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
mprint0: .asciz "Nested true\n"
mprint1: .asciz "Resulted in false\n"
.global main
.balign 4
main:
	MOV r11, lr
	MOV r10, #1
	CMP r10, #1
	BLEQ basicBranch_main_b0
	MOV r10, #1
	CMP r10, #1
	BLNE basicBranch_main_b1
	MOV pc, r11
basicBranch_main_b0:
	PUSH {lr}
	MOV r1, #1
	CMP r1, #0
	MOVEQ r1, #1
	MOVNE r1, #0
	CMP r1, #1
	BLEQ basicBranch_main_b0_b0
	CMP r1, #1
	BLNE basicBranch_main_b0_b1
	POP {pc}
basicBranch_main_b0_b0:
	PUSH {lr}
	LDR r0, =mprint0
	PUSH {lr}
	bl printf
	POP {lr}
	POP {pc}
basicBranch_main_b0_b1:
	PUSH {lr}
	POP {pc}
basicBranch_main_b1:
	PUSH {lr}
	LDR r0, =mprint1
	PUSH {lr}
	bl printf
	POP {lr}
	POP {pc}
