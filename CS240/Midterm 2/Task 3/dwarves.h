/*
 *  dwarves.h -- include file for managing the schedule at Magic Dwarves, Inc.
 *
 * Snow White is managing mine operations for Magic Dwarves, Inc.  Business is booming,
 * and the dwarves have 5 of their cousins working with them.  So, in addition to Doc,
 * Grumpy, Happy, Sleepy, Bashful, Sneezy, and Dopey, the mine is also employing (for
 * now) Grouchy, Smiley, Lazy, Chubby, and Bombur.
 *
 * Snow White needs to schedule the elves so that there are always at least four
 * elves working every day, but they each get one day off every week, if they wish.
 * She keeps a list of the day each dwarf takes off as a statically-allocated table and
 * initially each dwarf gets no day off. Then, every week each dwarf can request a specific
 * day off.  Snow White will grant the request unless it results in too few elves working that day.
 *
 * You need to code the routines to help Ms. White manage the schedule.
 *
 * C does not have dynamic multidimensional arrays that can be passed as arguments.  Thus, in this
 * implementation the list of days off is actually a single dimensional array.  You must determine
 * how to make it stand in for a 2-dimensional array of [MAXDWARVES][2] where freeDays[N][0] is
 * a pointer to the name of the dwarf and freeDays[N][1] is a pointer to the day (if any) that the dwarf
 * is taking off.

*  At the end it should look similar to this:
*  	Doc	 | No Day
*  	Grumpy | No Day
*  	Happy	 | No Day
*	...
*   and so on

 */

/*
 *  YOU CANNOT CHANGE ANYTHING IN THIS FILE!
 */

 /*
  *  You ARE allowed to use <string.h> routines in your solution to these
  */

#define S_format "Dwarf %s has %s off.\n"
#define MAXDWARVES 12

extern char *DaysOfW[8];// = {"No day", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"};

/*  init_schedule()
 *
 *  Allocates a weekly list of free days, initializes it, and return a pointer to it
 *  The list of free days is initialized so that each freeDays[N][0] is one of the dwarves' names in
 *  alphabetic order, and freeDays[N][1] is set to "No day" from the DaysOfW list, above.
 *
 *  You must enter the names from Roster into the new schedule in alphabetic order. Hint:
 *  you already know how to do a bubble sort.
 *
 *  IMPORTANT: Do NOT write code that assumes that the dwarves given in the argument are
 *  the dwarves named in the comment block, above!  There are many more cousins, and some
 *  them may swap free days!
 *
 *  Input: an array of MAXDWARVES char pointers, each pointing to a name of a dwarf. These
*   names are not guaranteed to be in alphabetical order
 *
 *  Return value: a pointer to a list of dwarf names and free days, as above which is implemented as a single-dimensional array of char pointers
 *  If the list of free days can't be created, the return is NULL
 */

char ** init_schedule(char *working[MAXDWARVES]);

/* request_day ()
 *
 * The named dwarf requests the given day off. There must be at least 4 dwarves working on that day
 *
 *  Input: pointer to the current schedule, dwarf name, day off requested
 *
 *  Return value: integer as follows:
 *   The return value is 0 if the schedule request is granted and the schedule is updated.
 *   The return value is 1 if the name of the dwarf doesn't match one in the schedule
 *   The return value is 2 if the day off doesn't match an entrya day of the week as in DaysOfW
 *   The return value is 3 if too many dwarves already have that day off.
 *
* Remark: You can assume no argument will be null
 */

int request_day(char **freeDays, char *dwarf, char *day);

/* hard_working()
 *
 * Given a list of free days, this function allocates an integer array containing the
 * row numbers in the free days array of the hard-working dwarves. For this function,
 * that means each dwarf with no day off.
 *
 * Input: pointer to the current schedule, and the address of a pointer to an
 * integer array
 *
 *  Return: the pointer is filled in with the address of the integer array.  The function
 *  value is the number of valid entries in that array (hwork).
*
* Remark: The size of hwork can be <= MAXDWARVES
 */

 int hard_working(char **freeDays, int **hwork);

 /* print_schedule()
  *
  * Prints to stdout, using the S_Format string above, the list of freeDays and
  * days off. The alphabetic order of names should be retained!
  */

 void print_schedule (char **freeDays);
