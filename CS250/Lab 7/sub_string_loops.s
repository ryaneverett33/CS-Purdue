.section        .data
inIndex:                .word 0
debugStr:       .asciz "%d, %c\n"
debugInStr:     .asciz "in_string: %s\n"
debugStart:     .asciz "start index: %d\n"
debugEnd:       .asciz "end index: %d\n"
debugChar:      .asciz "%c\n"
outStr:         .word 100
outIndex:       .word 0
.section        .text
.global         sub_string
sub_string:
        mov r9, r14                            @Copy the lr so we can return back to C
        mov r10, $1                                     @index in our loop
        mov r11, $0                             @index of our substring, moves with the loop

        @Move everything because of paranoia
        mov r4, r0                                      @in_string
        mov r5, r1                                      @start_index
        mov r6, r2                                      @end_index

        add r1, r6, $1                          @r1 = end_index (r6) + 1

        @Debug array access
        @ldr r1, [r4, #0]
        @ldr r0, =debugChar
        @bl printf

        @Debug array access
        @ldr r1, [r4, #1]
        @ldr r0, =debugChar
        @bl printf

        ldr r0, =outStr                         @set working string at return address
        @Debug set array
        @mov r1, $65
        @str r1, [r0, #0]
	b loop
loop:
        cmp r10, r5                                     @is loop index (i) >= start_index
        beq add											@if ==, branch to label add
        bgt add											@if >, branch to label add
        cmp r10, r1                                     @is loop index (i) == (end_index + 1)
        beq end											@if ==, branch to label end
        bne loop										@if !=, loop again
add:
        sub r2, r10, $1                      	@r2 = loop index (i) - 1
        ldr r2, [r4, r2]                        @get character at in_string[i - 1]
        str r2, [r0, r11]                       @store in_string[i - 1] at out_string[outIndex]
        add r11, r11, $1                        @Increment outIndex
        @bx lr
end:
        mov r9, r14
        @bx r14         @Return
        bx lr
        @mov r7, $1     @exit syscall
        @svc $0         @wake kernel
        .end

