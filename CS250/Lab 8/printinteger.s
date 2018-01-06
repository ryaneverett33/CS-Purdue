.global printx
.global printd

printx:
	@save registers
	push {r4}
	push {r5}
	push {r6}
	push {r7}
	push {r8}
	push {r9}
	push {r10}
	push {r11}
	push {lr}

	mov r4, $0xF0000000 @r4: 1111000...
	and r5, r0, r4		@r5: 0 & 1111000...
	lsr r5, r5, $28		@left shift r5 by 28 bits, to get to right 4 bits
	
	mov r6, $0			@i = 0 for loop
	mov r7, $0			@r7 = 0; boolean if true then print 0: to check for leading zeroes to not print
	
loop:
	cmp r6, $8			@is i equal to 8
	beq exit			@if true, return to myprintf

	cmp r5, $0			@current num with 0
	bne convert			@convert to hex
	
	cmp r7, $1			@check our boolean, should we print 0?
	beq convert			@convert the 0

loop_bottom:
	add r6, $1			@i++
	lsr r4, r4, $4		@r4: r4 right shifted by 4
	and r5, r0, r4		@r5: the number after r4
	mov r9, $7			@r9: 7
	sub r8, r9, r6		@r8: 7 - i
	mov r9, $4			@r9: 4
	mul r8, r8, r9		@r8 *= 4
	lsr r5, r5, r8		@r5 left shifted by (7 - i) * 4
	
	bl loop				@go to loop

convert:
	@convert A through E
	mov r7, $1			@boolean = true
	
	cmp r5, $10			@if r5 is greater than 10 we have 0 through 9
	blt num_conversion	@if true
	
	@else we have A through E
	
	sub r5, r5, $10		@r5 -= 10
	mov r10, $97		@r10:'a'
	add r10, r5			@r10 += r5 (gets proper number)
	mov r11, r0			@store our current number
	
	mov r0, r10			@r0:	current num
	bl putchar			
	
	mov r0, r11			@restore original number
	
	bl loop_bottom		@go to loop_bottom
	
num_conversion:
	@[0,9]
	mov r10, $48		@r10: '0'
	add r10, r5			@r10 += r5 to get character
	mov r11, r0			@save our current number
	
	mov r0, r10			
	bl putchar			@print the current number
	
	mov r0, r11			@restore our original number
	
	bl loop_bottom

exit:
	@pop {r0}

	@flush
	mov r0, $0
	bl fflush
	
	@restore registers that we saved earlier
	pop {lr}
	pop {r11}
	pop {r10}
	pop {r9}
	pop {r8}
	pop {r7}
	pop {r6}
	pop {r5}
	pop {r4}
	
	bx lr
	
@------------------------------------------------------------------------------------

printd:
	@store registers for safe keeping
	push {r4}
	push {r5}
	push {r6}
	push {r7}
	push {r8}
	push {r9}
	push {r10}
	push {r11}
	push {lr}

	cmp r0, $0
	beq iszero		@print zero
	
	mov r11, r1			@r11: copy of r1
	and r4, r0, $0x80000000	@r4: number AND 1110000
	cmp r4, $0x80000000 @if %2 == 0
	bne init_pos		@true
	
	@ldr r4, r0
	@mvn r4, r4			@use mvn to flip
	
	mvn r4, r0			@invert r4
	add r4, $1			@2s complement by adding 1
	mov r10, r4			@r10: most sig bit of r4
	
	mov r0, $45			@r0 <- '-'
	bl putchar			
	
	bl major_loop		@loop

init_pos:
	mov r10, r0 		@r10: most sig bit of r0
	
major_loop:

	cmp r10, $0			@is r10 equal to 0
	beq way_out			@leave 

	mov r4, r10			@store r4 into r10
	mov r5, $0			@j = 0
	
div_loop:
	@Our main divide loop, handles, you guessed it, dividing
	
	cmp r4, $10			@ does r4 == 10
	blt mul_loop_setup	@ setup loop if < 10
	
	mov r6, r11			@ r6 = copy of r11
	umull r6, r7, r6, r4	@unsigned long multipy r6 <- r7 * r6 *r4
	mov r4, r7, LSR #3
	
	add r5, $1
	
	bl div_loop
	
mul_loop_setup:
	@Setup the loop before continuing

	mov r8, $0			@tmp = 0
	mov r9, r4			@r9: most sig bit of r4
	
	@mov r0, $47
	@mov r0, $49
	
	mov r0, $48			@print the most sig bit of r4	
	
	add r0, r4			@r0 =+ r4
	bl putchar
	@fall to mul_loop
	
mul_loop:
	cmp r8, r5			@is tmp equal to 0
	beq out				@don't print, so branch to out '
	
	@mov r2, $8
	@mov r2, $9
	
	mov r2, $10
	mul r9, r2
	add r8, $1
	
	bl mul_loop
	
out:
	@Go back to major_loop
	
	@sub r10, r8	
	sub r10, r9			@r10 <- r10 - r9
	bl major_loop		@branch back to major_loop to loop again
	
iszero:
	mov r0, $48
	bl putchar
	b way_out			@print 0 and exit

way_out:
	@pop {r0}

	@flush
	mov r0, $0
	bl fflush

	@return our original registers
	pop {lr}
	pop {r11}
	pop {r10}
	pop {r9}
	pop {r8}
	pop {r7}
	pop {r6}
	pop {r5}
	pop {r4}
	
	bx lr
	
