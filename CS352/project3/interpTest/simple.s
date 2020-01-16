.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
mprint0: .asciz "This line should be printed. A bunch of expressions:\n"
mprint1: .asciz "This line should not be printed\n"
.global main
.balign 4
main:
	MOV r11, lr
	MOV r10, #1
	CMP r10, #1
	BLEQ simple_main_b0
	MOV r10, #1
	CMP r10, #1
	BLNE simple_main_b1
	MOV pc, r11
simple_main_b0:
	PUSH {lr}
	LDR r0, =mprint0
	PUSH {lr}
	bl printf
	POP {lr}
	LDR r0, =println
	MOV r1, #5
	PUSH {lr}
	bl printf
	POP {lr}
	LDR r0, =println
	MOV r1, #47
	PUSH {lr}
	bl printf
	POP {lr}
	LDR r0, =println
	MOV r1, #-31
	PUSH {lr}
	bl printf
	POP {lr}
	LDR r0, =println
	MOV r1, #23
	PUSH {lr}
	bl printf
	POP {lr}
	LDR r0, =println
	MOV r1, #136
	PUSH {lr}
	bl printf
	POP {lr}
	POP {pc}
simple_main_b1:
	PUSH {lr}
	LDR r0, =mprint1
	PUSH {lr}
	bl printf
	POP {lr}
	POP {pc}
