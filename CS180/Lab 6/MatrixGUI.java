import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.EventQueue;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.List;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.UIManager;
import javax.swing.UnsupportedLookAndFeelException;

//import misc.Matrix;

/**
 * The MatrixGUI class provides a graphical way of creating a matrix of certain
 * dimensions, selecting which elements are 0 and non-zero, and displaying some
 * information about the matrix using methods from the Matrix class.
 *
 */
public class MatrixGUI {

	int[][] clicked;

	public void setResultText(JTextArea textArea) {
		// TODO: set the text in the JTextArea using the setText(String) method
    	//			to show the properties of the instance variable matrix 'clicked'.
    	//			Properties should include symmetric, diagonal, identity, upper
    	//			triangular, and tridiagonal.
    	Matrix m = new Matrix();
    	// Change the contents of message so that it provides meaningful results to the user.
    	// You can use \n in your string to start a newline. At the very least, you must make
    	// 5 method calls to the methods you implemented in Matrix and display their results.
    	String message = "Symmetric: \n Diagonal: \n Identity: \n Upper Triangle: \n TriDiagonal: ";
		boolean symmetric = m.isSymmetric(clicked);
		boolean diagonal = m.isDiagonal(clicked);
		boolean identity = m.isIdentity(clicked);
		boolean uppertriangle = m.isUpperTriangular(clicked);
		boolean tridiagonal = m.isTridiagonal(clicked);
		String result = String.valueOf(symmetric) + "\n" + String.valueOf(diagonal) + "\n" + String.valueOf(identity);
		result = result + "\n" + String.valueOf(uppertriangle) + "\n" + String.valueOf(tridiagonal);
		textArea.setText(result);
	}

	public void resetResultText(JTextArea textArea) {
		// TODO: reset the text in the JTextArea using the setText(String) method
    	// Change the contents of message so that any results are cleared. Don't just leave it 
    	// blank. Provide some dialog for the user to read or instructions. Use \n as needed to
    	// start newlines in your string.
		String message = "Symmetric: \n" +
				" Diagonal: \n" +
				" Identity: \n" +
				" Upper Triangle: \n" +
				" TriDiagonal: ";
		textArea.setText(message);
	}
	
	public MatrixGUI(int rows, int columns) {

		EventQueue.invokeLater(new Runnable() {
			@Override
			public void run() {
				try {
					UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
				} catch (ClassNotFoundException | InstantiationException | IllegalAccessException | UnsupportedLookAndFeelException ex) {
				}

				JFrame frame = new JFrame("MatrixGUI");  // create a new frame
				frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE); // make the frame close when you hit the 'X' button ontop right corner
				// A border layout lays out a container, arranging and resizing its components to fit in five regions: north, south, east, west, and center.
				frame.setLayout(new BorderLayout()); 

				// Add TestPane(s) to the frame
				TestPane pane = new TestPane(rows,columns);
				frame.add(pane);

				// Create east panel and its components
				JPanel eastPanel = new JPanel(new BorderLayout());
				JPanel buttonPanel = new JPanel(new FlowLayout());

				JTextArea text = new JTextArea();
				JScrollPane scroll = new JScrollPane(text);
				scroll.setPreferredSize(new Dimension(250, frame.getHeight()));

				text.setFont(new Font("Arial", Font.PLAIN, 14));
				resetResultText(text);
				
				// Add done JButton and set listener
				JButton done = new JButton("Done");
				done.addMouseListener(new MouseAdapter() {
					@Override
					public void mouseClicked(MouseEvent e) {
						clicked = pane.getClickedCells();
						for (int i = 0; i < clicked.length; i++) {
							for (int j = 0; j < clicked[i].length; j++) {
								System.out.print(clicked[i][j] + " ");
							}
							System.out.println();
						}
						System.out.println();
						setResultText(text);
					}
				});

				// Add clear JButton and set listener
				JButton clear = new JButton("Clear");
				clear.addMouseListener(new MouseAdapter() {
					@Override
					public void mouseClicked(MouseEvent e) {
						resetResultText(text);
						pane.clearClickedCells();
					}
				});

				buttonPanel.add(clear);
				buttonPanel.add(done);

				eastPanel.add(scroll);
				eastPanel.add(buttonPanel, BorderLayout.SOUTH);

				frame.add(eastPanel, BorderLayout.EAST);
				frame.pack();
				frame.setLocationRelativeTo(null);
				frame.setVisible(true);  // make the frame visible
			}
		});
	}

	@SuppressWarnings("serial")
	private class TestPane extends JPanel {

		private int columnCount;
		private int rowCount;
		private List<Rectangle> cells;
		private Point selectedCell;
		private boolean[] clickedCells;

		public TestPane(int row, int col) {
			columnCount = col;
			rowCount = row;

			clickedCells = new boolean[row * col];

			cells = new ArrayList<>(columnCount * rowCount);
			MouseAdapter mouseHandler;
			mouseHandler = new MouseAdapter() {
				@Override
				public void mouseMoved(MouseEvent e) {
					int width = getWidth();
					int height = getHeight();

					int cellWidth = width / columnCount;
					int cellHeight = height / rowCount;

					int column = Math.min(e.getX() / cellWidth, columnCount - 1);
					int row = Math.min(e.getY() / cellHeight, rowCount - 1);

					selectedCell = new Point(column, row);
					repaint();

				}
			};
			addMouseMotionListener(mouseHandler);

			MouseAdapter mouseClickedHandler = new MouseAdapter() {
				@Override
				public void mouseClicked(MouseEvent e) {
					int width = getWidth();
					int height = getHeight();

					int cellWidth = width / columnCount;
					int cellHeight = height / rowCount;

					int column = e.getX() / cellWidth;
					int row = e.getY() / cellHeight;

					clickedCells[row * columnCount + column] = !clickedCells[row * columnCount + column];
					repaint();
				}
			};
			addMouseListener(mouseClickedHandler);
		}

		public int[][] getClickedCells() {
			int[][] clicked = new int[rowCount][columnCount];
			for (int i = 0; i < clickedCells.length; i++) {
				clicked[i / columnCount][i % columnCount] = clickedCells[i] ? 1 : 0;
			}
			return clicked;
		}

		public void clearClickedCells() {
			for (int i = 0; i < clickedCells.length; i++) {
				clickedCells[i] = false;
			}
			repaint();
		}

		@Override
		public Dimension getPreferredSize() {
			return new Dimension(columnCount * 70, rowCount * 70);
		}

		@Override
		public void invalidate() {
			cells.clear();
			selectedCell = null;
			super.invalidate();
		}

		@Override
		protected void paintComponent(Graphics g) {
			super.paintComponent(g);
			Graphics2D g2d = (Graphics2D) g.create();

			int width = getWidth();
			int height = getHeight();

			int cellWidth = width / columnCount;
			int cellHeight = height / rowCount;

			int xOffset = (width - (columnCount * cellWidth)) / 2;
			int yOffset = (height - (rowCount * cellHeight)) / 2;

			// Populate the Rectangles on the grid
			if (cells.isEmpty()) {
				for (int row = 0; row < rowCount; row++) {
					for (int col = 0; col < columnCount; col++) {
						Rectangle cell = new Rectangle(
								xOffset + (col * cellWidth),
								yOffset + (row * cellHeight),
								cellWidth,
								cellHeight);
						cells.add(cell);
					}
				}
			}

			// Paint the cell the mouse is currently in
			if (selectedCell != null && !clickedCells[selectedCell.x + (selectedCell.y * columnCount)]) {
				int index = selectedCell.x + (selectedCell.y * columnCount);
				Rectangle cell = cells.get(index);
				g2d.setColor(Color.BLACK);
				g2d.fill(cell);

			}

			// Paint the cells that were clicked by the user
			g2d.setColor(new Color(0xDAA520));
			for (int i = 0; i < clickedCells.length; i++) {
				if (clickedCells[i]) {
					g2d.fill(cells.get(i));
				}
			}

			// Paint all other cells
			g2d.setColor(Color.GRAY);
			for (Rectangle cell : cells) {
				g2d.draw(cell);
			}

			g2d.dispose();
		}
	}
	
	public static void main(String[] args) {
		int rows = Integer.parseInt(JOptionPane.showInputDialog("Number of rows"));
		int cols = Integer.parseInt(JOptionPane.showInputDialog("Number of columns"));
		new MatrixGUI(rows, cols);
	}
}