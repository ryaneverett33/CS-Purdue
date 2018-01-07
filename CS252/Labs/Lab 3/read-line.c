/*
 * CS354: Operating Systems. 
 * Purdue University
 * Example that shows how to read one line with simple editing
 * using raw terminal.
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <termios.h>

#define MAX_BUFFER_LINE 2048

extern void tty_raw_mode(void);

// Buffer where line is stored
int line_length;
char line_buffer[MAX_BUFFER_LINE];

// Simple history array
// This history does not change. 
// Yours have to be updated.
char ** history;
int history_max = 2;
int history_length = 0;
int history_index = 0;
int line_pos;

void add_hist_line( const char * input ) {
	char * line = strdup(input);
	// realloc if necessary
	if ( history_length == history_max + 1) {
		history_max *= 2;
		history = (char**) realloc (history, history_max * sizeof(char*));
	}

	// add the new line
	line[ strlen(line) ] = '\0'; // remove newline at the end
	//printf("\tadding line: \"%s\"", line);
	history[ history_length ] = line;
	history_length++;
	history_index++; // index tracks most recently added line
}

void read_line_print_usage()
{
  char * usage = "\n"
    " ctrl-?       Print usage\n"
    " Backspace    Deletes last character\n"
    " up arrow     See last command in the history\n";

  write(1, usage, strlen(usage));
}
void init_hist() {
	history = (char**)malloc( history_max * sizeof(char*) );
	const char * empty = "";
	add_hist_line( empty );
}

// backspace n times
void backspace(int n) {
	int i;
	char ch = 8;
	for (i = 0; i < n; i++) {
		write( 1, &ch, 1 );
	}
}

/* 
 * Input a line with some basic editing.
 */
char * read_line() {
// save terminal settings
	struct termios orig_attr;
	tcgetattr(0, &orig_attr);

	// Set terminal in raw mode
	tty_raw_mode();

	line_length = 0;
	line_pos = 0;

	// reset the line buffer
	int t = 0;
	for (t = 0; t < MAX_BUFFER_LINE; t++) {
		line_buffer[t] = '\0';
	}

	// Read one line until enter is typed
	while (1) {

		// init history if necessary
		if (history == NULL) {
			init_hist();
		}

		// Read one character in raw mode.
		char ch;
		read(0, &ch, 1);
		/*if (ch == 1) {
			//Ctrl-A 
			//cursor moves to beginning
			line_pos = 0;
		}
		else if (ch == 4) {
			//Ctrl-D
			backspace(1);
		}
		else if (ch == 5) {
			//Ctrl-E
			int newindex = line_pos;
			while (line_buffer[newindex] != 0) {
				newindex++;
			}
			line_pos = newindex -1;
			for (int i = 0; i < newindex; i++) {
				write(0,line_buffer[i], 1);
			}
		}
		else if (ch == 8) {
			//Ctrl-H
		}*/
		
		if (ch>=32 && ch < 127) {
			// It is a printable character. 

			if (line_pos == line_length) {
				// we're at the end of the line
				// Do echo
				write(1,&ch,1);

				// If max number of character reached return.
				if (line_length==MAX_BUFFER_LINE-2) break; 

				// add char to buffer.
				line_buffer[line_pos]=ch;
				line_length++;
				line_pos++;
			} else {
				// in the middle of the line somewhere
				char * temp = (char*)malloc(MAX_BUFFER_LINE * sizeof(char));
				int i;
				// copy all the characters after where we're at
				for ( i = 0; i < MAX_BUFFER_LINE; i++) {

					if (line_buffer[line_pos + i] == '\0' ) {
						// if we see the null char, we've gotten it all
						break;
					}
					temp[i] = line_buffer[line_pos + i];
				}

				// write the character we want to add
				write (1, &ch, 1);

				// If max number of character reached return.
				if (line_length==MAX_BUFFER_LINE-2) break; 
				
				// add char to buffer.
				line_buffer[line_pos]=ch;
				line_length++;
				line_pos++;

				// print all the rest of the characters afterwards
				int chars_added = 0;
				for (i = 0; i < MAX_BUFFER_LINE; i++) {
					chars_added+=1;
					write(1, &temp[i], 1);
					if (line_buffer[line_pos + i] == '\0' ) {
						// if we see the null char, we've gotten it all
						break;
					}
				}
				// go back to where we were
				backspace(chars_added);
			}
		}
		else if (ch==10) {
			// <Enter> was typed. Return line

			// add line to history linked list if it's not empty
			if ( strlen(line_buffer) != 0 ) {
				add_hist_line(line_buffer);
			}

			// Print newline
			write(1,&ch,1);

			break;
		}
		else if (ch == 31) {
			// ctrl-?
			read_line_print_usage();
			line_buffer[0]=0;
			break;
		}
		else if (ch == 127) {
			// <backspace> was typed. Remove previous character read.

			// don't do anything if we're already at the beginning 
			if (line_pos <= 0) {
				continue;
			}

			// Go back one character
			backspace(1);

			// Write a space to erase the last character read
			ch = ' ';
			write(1,&ch,1);

			// Go back one character
			backspace(1);

			// Remove one character from buffer
			line_buffer[ line_pos ] = '\0';
			line_length--;
			line_pos--;
		}
		else if (ch==27) {
			// Escape sequence. Read two chars more
			//
			// HINT: Use the program "keyboard-example" to
			// see the ascii code for the different chars typed.
			//
			char ch1; 
			char ch2;
			read(0, &ch1, 1);
			read(0, &ch2, 1);
			if (ch1==91 && ch2==65) {
				// Up arrow. Print next line in history.

				// Erase old line
				// Print backspaces
				int i = 0;
				for (i =0; i < line_length; i++) {
					ch = 8;
					write(1,&ch,1);
				}

				// Print spaces on top
				for (i =0; i < line_length; i++) {
					ch = ' ';
					write(1,&ch,1);
				}

				// Print backspaces
				for (i =0; i < line_length; i++) {
					ch = 8;
					write(1,&ch,1);
				}

				// if history is uninitialized, do nothing
				// Copy line from history
				history_index -= 1;
				if (history_index <= 0) {
					// loop back to the most recent command
					history_index = history_length - 1;
				}

				if (history[history_index] == NULL) {
					const char * empty = "";
					strcpy(line_buffer, empty);
				} else {
					strcpy(line_buffer, history[history_index]);
				}
				line_length = strlen(line_buffer);

				// echo line
				write(1, line_buffer, line_length);
			}
			else if (ch1 == 91 && ch2 == 66) {
				// down arrow. print previous line in history

				// Erase old line
				// Print backspaces
				backspace( line_length );

				// Print spaces on top
				int i = 0;
				for (i =0; i < line_length; i++) {
					ch = ' ';
					write(1,&ch,1);
				}

				// Print backspaces
				backspace( line_length );

				// increment index accordingly
				if (history_index <= 0) {
					// stay at 0
					history_index = 0;
				} else {
					history_index += 1;
					if (history_index >= history_length ) {
						history_index = 0;
					} 
				}

				// Copy line from history
				if (history[history_index] == NULL) {
					const char * empty = "";
					strcpy(line_buffer, empty);
				} else {
					strcpy(line_buffer, history[history_index]);
				}
				line_length = strlen(line_buffer);

				// echo line
				write(1, line_buffer, line_length);
			}
			else if (ch1 == 91 && ch2 == 68) {
				// left arrow
				if (line_pos <= 0) {
					continue;
				}
				if (line_pos > 0) {
					line_pos--;
					backspace(1);
				}
			}
			else if (ch1 == 91 && ch2 == 67) {
				// right arrow
				if (line_pos < line_length) {

					// grab current char
					char c = line_buffer[line_pos];

					// print grabbed char
					write( 1, &c, 1);

					line_pos++;
				}
			}
		}
	}

	// Add eol and null char at the end of string
	line_buffer[line_length]=10;
	line_length++;
	line_buffer[line_length]=0;

	// set the terminal back to orig settings
	tcsetattr(0, TCSANOW, &orig_attr);

return line_buffer;
}

