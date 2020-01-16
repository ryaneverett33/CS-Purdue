class ifelse {
    public static void main(String[] args) {
        {
            if (1 + 1 == 2) {
                System.out.println("true");
            }
            else {
                System.out.println("false");
            }
        }
    }
}
/*
lnmessage1: "true"
lnmessage2: "false"

main:
	v1 <- 1 + 1
	if v1 == 2 goto ifelse_main_b0
	else goto ifelse_main_b1
ifelse_main_b0:
    SPRINTLN lnmessage1
ifelse_main_b1:
	SPRINTLN lnmessage2
*/