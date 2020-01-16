Globals
mprint0=Sort successful\n
mprint1=Sort failed\n

main:
	v1 <- NEW Sorter
	v2 <- v1 CALL bubblesortDemo
	v2 <- v2==1
	IF v2 == 1 GOTO array_main_b0
	ELSE GOTO array_main_b1
array_main_b0:
	CSPRINTLN mprint0
array_main_b1:
	CSPRINTLN mprint1
Sorter_bubblesortDemo:
	v1 <- NEW INT
	v1 <- ARR 8 
	array <- v1
	v1 <- array
	v1 <- ARR 0 
	v1 <- STORE 60
	v1 <- array
	v1 <- ARR 1 
	v1 <- STORE 40
	v1 <- array
	v1 <- ARR 2 
	v1 <- STORE 20
	v1 <- array
	v1 <- ARR 3 
	v1 <- STORE 0
	v1 <- array
	v1 <- ARR 4 
	v1 <- STORE 50
	v1 <- array
	v1 <- ARR 5 
	v1 <- STORE 70
	v1 <- array
	v1 <- ARR 6 
	v1 <- STORE 10
	v1 <- array
	v1 <- ARR 7 
	v1 <- STORE 30
	i <- 0
	j <- 0
	MARK
	v1 <- i
	v1 <- v1<8
	IF v1 == 1 GOTO Sorter_bubblesortDemo_b0
	i <- 0
	isSorted <- 1
	MARK
	v1 <- i
	v1 <- v1<8
	IF v1 == 1 GOTO Sorter_bubblesortDemo_b1
	v1 <- isSorted
	RETURN v1
Sorter_bubblesortDemo_b0:
	j <- 0
	MARK
	v1 <- j
	v1 <- i
	v1 <- 8-v1
	v1 <- v1-1
	v1 <- v1<v1
	IF v1 == 1 GOTO Sorter_bubblesortDemo_b0_b0
	v1 <- i
	v1 <- v1+1
	i <- v1
	GOBACK
Sorter_bubblesortDemo_b0_b0:
	v1 <- array
	v2 <- j
	v1 <- ARR v2 
	v1 <- GET
	v2 <- array
	v1 <- j
	v1 <- v1+1
	v2 <- ARR v1 
	v2 <- GET
	v1 <- v1>v2
	IF v1 == 1 GOTO Sorter_bubblesortDemo_b0_b0_b0
	ELSE GOTO Sorter_bubblesortDemo_b0_b0_b1
	v1 <- j
	v1 <- v1+1
	j <- v1
	GOBACK
Sorter_bubblesortDemo_b0_b0_b0:
	v1 <- array
	v1 <- j
	v1 <- v1+1
	v1 <- ARR v1 
	v1 <- GET
	tmp <- v1
	v1 <- j
	v1 <- v1+1
	v1 <- array
	v2 <- array
	v2 <- j
	v2 <- ARR v2 
	v2 <- GET
	v1 <- ARR v1 
	v1 <- STORE v2
	v2 <- j
	v1 <- array
	v2 <- tmp
	v1 <- ARR v2 
	v1 <- STORE v2
Sorter_bubblesortDemo_b0_b0_b1:
Sorter_bubblesortDemo_b1:
	v1 <- array
	v2 <- i
	v1 <- ARR v2 
	v1 <- GET
	v1 <- i
	v1 <- v1*10
	v1 <- v1==v1
	v1 <- isSorted
	v1 <- v1&&v1
	isSorted <- v1
	v1 <- i
	v1 <- v1+1
	i <- v1
	GOBACK
