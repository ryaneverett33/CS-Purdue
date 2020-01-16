/* readln.c - readln, recvln */

#include <stdio.h>

/*------------------------------------------------------------------------
 * readln - read from stdin until newline or EOF, or buffer is full.
 * Flush to newline or EOF and return on full buffer. Returns data length.
 *------------------------------------------------------------------------
 */
int
readln (char *buff, int buffsz)
{
    char  *bp = buff, c;
    int  n;

    while (bp - buff < buffsz &&
           (n = read (STDIN_FILENO, bp, 1)) > 0) {
        if (*bp++ == '\n')
            return (bp - buff);
    }

    if (n < 0)
        return -1;

    if (bp - buff == buffsz)
        while (read (STDIN_FILENO, &c, 1) > 0 && c != '\n');

    return (bp - buff);
}
