import jdk.nashorn.internal.runtime.Debug;

import java.util.*;

public class Connect4 {

    public static final char NONE = ' ';
    public static final char RED = 'O';
    public static final char YELLOW = 'X';

    char[][] board = new char[6][7];

    /**
     * Initializes the instance variables.
     */
    public Connect4() {
        //Fill up the board with empty chars
        //Do Columns
        for (int i = 0; i < 6; i++) {
            //Do Rows
            for (int foo = 0; foo < 7; foo++) {
                board[i][foo] = NONE;
            }
        }
    }

    /**
     * Returns a copy of the current board
     * @return a char matrix
     */
    public char[][] getBoard()
    {
        return Arrays.copyOf(board, board.length);
    }

    /**
     * Put a piece of the given color in the given column
     * The function returns the row where the piece have been
     * put. If the column is full it return -1.
     *
     * @param column a column of the board
     * @param color RED or YELLOW
     */
    public int putPiece(int column, char color) {
        int rowAmount = board.length;
        int height = rowAmount; //If loop doesn't return anything, this value is the default
        if (column > board[0].length || column < 0) {
            return -1;
        }
        for (int i = 0; i < rowAmount; i++) {
            //at first instance of a player char, we set the height position
            if (board[i][column] == RED || board[i][column] == YELLOW) {
                height = i;
                break;
            }
        }
        if (height - 1 < 0) {
            return -1;
        }
        height--;   //Decrement height to fix all sorts of bugs.
        board[height][column] = color;

        return height;
    }

    /**
     * Print the screen in the standard output
     */
    public void printScreen() {
        // Make the header of the board
        System.out.printf("\n ");
        for (int i = 0; i < board[0].length; ++i)
            System.out.printf("   %d", i);
        System.out.println();

        System.out.printf("  ");
        for (int i = 0; i < board[0].length; ++i)
            System.out.printf("----");
        System.out.println("-");

        // Print the board contents
        for (int i = 0; i < board.length; ++i) {
            System.out.printf("%c ", 'A' + i);
            for (int k = 0; k < board[0].length; ++k)
                System.out.printf("| %c ", board[i][k]);
            System.out.println("|");

            // print the line between each row
            System.out.printf("  ");
            for (int k = 0; k < board[0].length; ++k)
                System.out.printf("----");
            System.out.println("-");
        }
    }

    /**
     * Check if an alignment has been made using the given tile
     *
     * @param row
     * @param column
     * @return the color if there is an alignment, NONE otherwise.
     */
    //Checks if a position is within the grid.
    private boolean isValid(int column, int row) {
        //This is cheating, I know it's cheating. But darn it, it works.
        try {
            char name = board[column][row];
        }
        catch (Exception e) {
            return false;
        }
        return true;

    }
    char diagonals(int row, int column) {
        int red1 = 0;
        int yellow1 = 0;
        int red2 = 0;
        int yellow2 = 0;
        row--;
        //column, row
        if (board[row][column] == RED) {
            red1++;
            red2++;
        }
        if (board[row][column] == YELLOW) {
            yellow1++;
            yellow2++;
        }
        for (int i = 1; i < 10; i++) {
            if (!isValid(row - i, column + i)) {
                break;
            }
            if (board[row - i][column + i] == YELLOW) {
                yellow1++;
                continue;
            }
            else if (board[row - i][column + i] == RED) {
                red1++;
                continue;
            }
        }
        for (int i = 1; i < 10; i++) {
            if (!isValid(row + i, column - i)) {
                break;
            }
            if (board[row + i][column - i] == YELLOW) {
                yellow1++;
                continue;
            }
            else if (board[row + i][column - i] == RED) {
                red1++;
                continue;
            }
        }
        if (red1 >= 4) {
            return RED;
        }
        else if (yellow1 >= 4) {
            return YELLOW;
        }

        for (int i = 1; i < 10; i++) {
            if (!isValid(row - i, column - i)) {
                break;
            }
            if (board[row - i][column - i] == YELLOW) {
                yellow2++;
                continue;
            }
            else if (board[row - i][column - i] == RED) {
                red2++;
                continue;
            }
        }
        for (int i = 1; i < 10; i++) {
            if (!isValid(row + i, column + i)) {
                break;
            }
            if (board[row + i][column + i] == YELLOW) {
                yellow2++;
                continue;
            }
            else if (board[row + i][column + i] == RED) {
                red2++;
                continue;
            }
        }
        if (red2 >= 4) {
            return RED;
        }
        else if (yellow2 >= 4) {
            return YELLOW;
        }
        return NONE;
    }
    public char checkAlignment(int row, int column) {
        //Check to see if a piece has neighbors
        //Do Vertical first. it's easiest. Only check neighbors until webcat says that's an inappropriate approach
        int cascadeP1 = 0; //Amount of player one colors immediately after each other
        int cascadeP2 = 0;
        row++;
        for (int i = 0; i < board.length; i++) {
            if (cascadeP1 == 0) {
                if (board[i][column] == RED) {
                    cascadeP1++;
                    continue;
                }
            }
            if (board[i][column] == RED) {
                cascadeP1++;
            } 
			else if (board[i][column] != RED) {
                cascadeP1 = 0;
            }
            if (cascadeP1 >= 4) {
                return RED;
            }
        }
        //Check Player 2
        for (int i = 0; i < board.length; i++) {
            if (cascadeP2 == 0) {
                if (board[i][column] == YELLOW) {
                    cascadeP2++;
                    continue;
                }
            }
            if (board[i][column] == YELLOW) {
                cascadeP2++;
            } else if (board[i][column] != YELLOW) {
                cascadeP2 = 0;
            }
            if (cascadeP2 >= 4) {
                return YELLOW;
            }
        }
        //Do horizontal
        cascadeP1 = 0;
        cascadeP2 = 0;
        for (int x = 0; x < board[0].length; x++) {
            if (cascadeP1 == 0) {
                if (board[row - 1][x] == YELLOW) {
                    cascadeP1++;
                    continue;
                } else {
                    continue;
                }
            }
            if (board[row - 1][x] == YELLOW) {
                cascadeP1++;
            } else if (board[row - 1][x] != YELLOW) {
                cascadeP1 = 0;
            }
            if (cascadeP1 >= 4) {
                return YELLOW;
            }
        }
        for (int x = 0; x < board[0].length; x++) {
            if (cascadeP2 == 0) {
                if (board[row - 1][x] == RED) {
                    cascadeP2++;
                    continue;
                } else {
                    continue;
                }
            }
            if (board[row - 1][x] == RED) {
                cascadeP2++;
            } else if (board[row - 1][x] != RED) {
                cascadeP2 = 0;
            }
            if (cascadeP2 >= 4) {
                return RED;
            }
        }
        return diagonals(row, column);
    }

    /**
     * Launch the game for one game.
     */
    public void play() {
        char currentPlayer = RED;

        // Begin playing the game
        Scanner in = new Scanner(System.in);
        int col = -1;
        int row = -1;

        do {
            currentPlayer = currentPlayer == RED ? YELLOW : RED;
            this.printScreen();
            System.out.printf("Current player: '%c'\n", currentPlayer);

            // read and validate the input
            col = -1;
            row = -1;

            do {
                System.out.printf("Choose a column: ");
                String line = in.nextLine();


                if (line == null || line.length() != 1) {
                    // Invalid input, reask for one.
                    continue;
                }

                col = line.charAt(0) - '0';
                row = this.putPiece(col, currentPlayer);

            } while (row < 0);

        } while (this.checkAlignment(row, col) == NONE);

        this.printScreen();
        System.out.printf("\n!!! Winner is Player '%c' !!!\n", currentPlayer);
        in.close();

    }
}