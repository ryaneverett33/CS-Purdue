.section .text
@ CONSTANTS
println: .asciz "%d\n"
print: .asciz "%d"
.global main
.balign 4
main:
	mov r11, lr
	LDR r0, =println
	push {lr}
	bl printf
	pop {lr}
	LDR r0, =println
	push {lr}
	bl printf
	pop {lr}
	mov pc, r11
Obj_getLength:
Obj_setAndGet:
