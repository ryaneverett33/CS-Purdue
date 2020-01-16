.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
.global main
.balign 4
main:
	mov r11, lr
	MOV r0, #4
	push {lr}
	BL malloc
	pop {lr}
	MOV r0, r1
	PUSH {r1}
	BL Runner_call3
	MOV r1, r0
	LDR r0, =println
	push {lr}
	bl printf
	pop {lr}
	mov pc, r11
Runner_call3:
	MOV r9, sp
	ADD r9, r9, #0
	PUSH {lr}
	SUB sp, sp, #4
	MOV r10, r9
	SUB r10, r10, #8
	MOV r8, #0
	STR r8, [r10]
	MOV r10, r9
	SUB r10, r10, #8
	LDR r1, [r10]
	MOV r0, r1
	MOV r10, r9
	SUB r10, #4
	LDR pc, [r10]
