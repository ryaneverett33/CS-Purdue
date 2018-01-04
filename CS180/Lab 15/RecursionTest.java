import static org.junit.Assert.assertEquals;

import java.io.File;
import java.util.ArrayList;
import java.util.Random;

import org.junit.Test;

/**
 * JUnit tests for the Recursion class.
 * 
 * @author Neil Allison, nalliso@purdue.edu
 *
 */
public class RecursionTest {


	@Test(timeout = 100)
	public void testDeterminantOneByOneZero() {
		int[][] matrix = {{0}};

		int actual = Recursion.determinant(matrix);
		int expected = 0;

		String message = "determinant(): check for matrix of size 1 x 1";

		assertEquals(message, expected, actual);
	}

	@Test(timeout = 100)
	public void testDeterminantOneByOneNegative() {
		int[][] matrix = {{-6}};

		int actual = Recursion.determinant(matrix);
		int expected = -6;

		String message = "determinant(): check for matrix of size 1 x 1";

		assertEquals(message, expected, actual);
	}

	@Test(timeout = 100)
	public void testDeterminantOneByOnePositive() {
		int[][] matrix = {{9}};

		int actual = Recursion.determinant(matrix);
		int expected = 9;

		String message = "";

		assertEquals(message, expected, actual);
	}

	@Test(timeout = 100)
	public void testDeterminantTwoByTwoAllZero() {
		int[][] matrix = {{0, 0}, {0, 0}};

		int actual = Recursion.determinant(matrix);
		int expected = 0;

		String message = "determinant(): check for matrix of size 2 x 2";

		assertEquals(message, expected, actual);
	}

	@Test(timeout = 100)
	public void testDeterminantTwoByTwoFirstRowZero() {
		int[][] matrix = {{0, 0}, {-11, 16}};

		int actual = Recursion.determinant(matrix);
		int expected = 0;

		String message = "determinant(): check for matrix of size 2 x 2";

		assertEquals(message, expected, actual);
	}

	@Test(timeout = 100)
	public void testDeterminantTwoByTwoSecondRowZero() {
		int[][] matrix = {{7, 4}, {0, 0}};

		int actual = Recursion.determinant(matrix);
		int expected = 0;

		String message = "determinant(): check for matrix of size 2 x 2";

		assertEquals(message, expected, actual);
	}

	@Test(timeout = 100)
	public void testDeterminantTwoByTwoDetZero1() {
		int[][] matrix = {{4, 2}, {4, 2}};

		int actual = Recursion.determinant(matrix);
		int expected = 0;

		String message = "determinant(): check for alternating signs on even/odd index for 2 x 2 matrix";

		assertEquals(message, expected, actual);
	}

	@Test(timeout = 100)
	public void testDeterminantTwoByTwoDetZero2() {
		int[][] matrix = {{-6, 7}, {6, -7}};

		int actual = Recursion.determinant(matrix);
		int expected = 0;

		String message = "determinant(): check for alternating signs on even/odd index for 2 x 2 matrix";

		assertEquals(message, expected, actual);
	}

	@Test(timeout = 100)
	public void testDeterminantTwoByTwoDetNonZero1() {
		int[][] matrix = {{4, 2}, {1, 9}};

		int actual = Recursion.determinant(matrix);
		int expected = 34;

		String message = "determinant(): check for matrix of size 2 x 2";

		assertEquals(message, expected, actual);
	}

	@Test(timeout = 100)
	public void testDeterminantTwoByTwoDetNonZero2() {
		int[][] matrix = {{7, 4}, {11, 2}};

		int actual = Recursion.determinant(matrix);
		int expected = -30;

		String message = "determinant(): check for matrix of size 2 x 2";

		assertEquals(message, expected, actual);
	}

	@Test(timeout = 100)
	public void testDeterminantDiagonalZero1() {
		int[][] matrix = {{0, 5}, {-4, 0}};

		int actual = Recursion.determinant(matrix);
		int expected = 20;

		String message = "determinant(): check for matrix of size 2 x 2";

		assertEquals(message, expected, actual);
	}

	@Test(timeout = 100)
	public void testDeterminantDiagonalZero2() {
		int[][] matrix = {{5, 0}, {0, -4}};

		int actual = Recursion.determinant(matrix);
		int expected = -20;

		String message = "determinant(): check for matrix of size 2 x 2";

		assertEquals(message, expected, actual);
	}

	@Test(timeout = 100)
	public void testDeterminantThreeByThreeAllZero() {
		int[][] matrix = {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};

		int actual = Recursion.determinant(matrix);
		int expected = 0;

		String message = "determinant(): check for matrix of size 3 x 3";

		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testDeterminantThreeByThreeFirstRowZero() {
		int[][] matrix = {{0, 0, 0}, {1, 4, -2}, {-3, 1, 2}};

		int actual = Recursion.determinant(matrix);
		int expected = 0;

		String message = "determinant(): check for matrix of size 3 x 3";

		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testDeterminantThreeByThreeSecondRowZero() {
		int[][] matrix = {{1, 4, -2}, {0, 0, 0}, {-3, 1, 2}};

		int actual = Recursion.determinant(matrix);
		int expected = 0;

		String message = "determinant(): check for matrix of size 3 x 3";

		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testDeterminantThreeByThreeThirdRowZero() {
		int[][] matrix = {{1, 4, -2}, {-3, 1, 2}, {0, 0, 0}};

		int actual = Recursion.determinant(matrix);
		int expected = 0;

		String message = "determinant(): check for matrix of size 3 x 3";

		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testDeterminantThreeByThree1() {
		int[][] matrix = {{-4, 2, 2}, {-1, -3, 7}, {6, 5, -1}};

		int actual = Recursion.determinant(matrix);
		int expected = 236;

		String message = "determinant(): check for matrix of size 3 x 3";

		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testDeterminantThreeByThree2() {
		int[][] matrix = {{5, -2, 1}, {4, 0, 2}, {3, -1, -5}};

		int actual = Recursion.determinant(matrix);
		int expected = -46;

		String message = "determinant(): check for matrix of size 3 x 3";

		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testDeterminantThreeByThree3() {
		int[][] matrix = {{1, 2, 3}, {0, 4, 5}, {0, 0, 6}};

		int actual = Recursion.determinant(matrix);
		int expected = 24;

		String message = "determinant(): check for matrix of size 3 x 3";

		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testDeterminantThreeByThree4() {
		int[][] matrix = {{5, 0, 0}, {0, 2, 0}, {0, 0, -4}};

		int actual = Recursion.determinant(matrix);
		int expected = -40;

		String message = "determinant(): check for matrix of size 3 x 3";

		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testDeterminantFiveByFive1() {
		int[][] matrix = {{1, 0, 0, 0, 0}, {0, 2, 0, 0, 0}, {0, 0, -3, 0, 0}, {0, 0, 0, 4, 0}, {0, 0, 0, 0, 5}};

		int actual = Recursion.determinant(matrix);
		int expected = -120;

		String message = "determinant(): check for matrix of size 5 x 5";

		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testDeterminantFiveByFive2() {
		int[][] matrix = {{1, 3, 2, -1, -5}, {0, 2, -1, 3, 1}, {2, 4, 0, 0, 1}, {-1, -2, 0, 3, 1}, {1, 1, -1, 0, -1}};

		int actual = Recursion.determinant(matrix);
		int expected = 138;

		String message = "determinant(): check for matrix of size 5 x 5";

		assertEquals(message, expected, actual);
	}

	/*
	 * JUnit tests for filecount().
	 */

	@Test(timeout = 100)
	public void testFilecountRootDirIsFile() throws Exception {
		File root = new File("root_dir1");
		root.createNewFile();
		
		int actual = Recursion.filecount(root);
		int expected = 1;

		String message = "filecount(): check when root is a file";

		root.delete();
		
		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testFilecountRootDirOneFile() throws Exception {
		File root = new File("root_dir2");
		root.mkdir();
		File f1 = new File(root, "file");
		f1.createNewFile();
		
		int actual = Recursion.filecount(root);
		int expected = 1;

		String message = "filecount(): check when root contains just one file";
		
		f1.delete();
		root.delete();

		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testFilecountEmptyRoot() throws Exception {
		File root = new File("root_dir3");
		root.mkdir();
		
		int actual = Recursion.filecount(root);
		int expected = 0;

		String message = "filecount(): check when root is an empty directory";

		root.delete();
		
		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testFilecountNestedDir() throws Exception {
		File root = new File("root_dir4");
		root.mkdir();
		
		File f1 = new File(root, "file1");
		f1.createNewFile();
		File d1 = new File(root, "dir1");
		d1.mkdir();
		File f2 = new File(d1, "file2");
		f2.createNewFile();
		File f3 = new File(d1, "file3");
		f3.createNewFile();
		File f4 = new File(d1, "file4");
		f4.createNewFile();
		
		int actual = Recursion.filecount(root);
		int expected = 4;

		String message = "filecount(): check when root directory has files and nested directory with files";
		
		f2.delete();
		f3.delete();
		f4.delete();
		d1.delete();
		f1.delete();
		root.delete();

		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 100)
	public void testFilecountMultiLevel() throws Exception {
		File parentDir = new File("root_dir5");
		parentDir.mkdir();
		
		File parentDirFile1 = new File(parentDir, "parentDirFile1");
		parentDirFile1.createNewFile();
		File subDir1Level1 = new File(parentDir, "subDir1Level1");
		subDir1Level1.mkdir();
		File subDir1Level2File1 = new File(subDir1Level1, "subDir1Level2File1");
		subDir1Level2File1.createNewFile();
		File subDir1Level2File2 = new File(subDir1Level1, "subDir1Level2File2");
		subDir1Level2File2.createNewFile();
		File subDir1Level2File3 = new File(subDir1Level1, "subDir1Level2File3");
		subDir1Level2File3.createNewFile();
		File subDir1Level2 = new File(subDir1Level1, "subDir1Level2");
		subDir1Level2.mkdir();
		File subDir1Level3File1 = new File(subDir1Level2, "subDir1Level3File1");
		subDir1Level3File1.createNewFile();
		File subDir2Level1 = new File(parentDir, "subDir2Level1");
		subDir2Level1.mkdir();
		File subDir2Level1File1 = new File(subDir2Level1, "subDir2Level1File1");
		subDir2Level1File1.createNewFile();
		
		int actual = Recursion.filecount(parentDir);
		int expected = 6;
		
		String message = "filecount(): check when there are multiple levels of subdirectories with files";
		
		
		subDir1Level3File1.delete();
		subDir1Level2.delete();
		subDir1Level2File1.delete();
		subDir1Level2File2.delete();
		subDir1Level2File3.delete();
		subDir1Level2.delete();
		subDir2Level1File1.delete();
		subDir2Level1.delete();
		parentDirFile1.delete();
		subDir1Level1.delete();
		parentDir.delete();
		
		assertEquals(message, expected, actual);
	}
	
	@Test(timeout = 150)
	public void testFilecountRandomFiles() throws Exception {
		Random r = new Random();
		int numFiles1 = r.nextInt(20) + 1;
		
		File root = new File("root_dir1");
		root.mkdir();
		
		ArrayList<File> files = new ArrayList<File>();
		
		for (int i = 1; i <= numFiles1; i++) {
			File f = new File(root, "file" + i);
			f.createNewFile();
			files.add(f);
		}
		
		File subDir = new File(root, "sub_dir");
		subDir.mkdir();
		
		int numFiles2 = r.nextInt(20) + 1;
		
		for (int i = 1; i <= numFiles2; i++) {
			File f = new File(subDir, "file" + i);
			f.createNewFile();
			files.add(f);
		}
		
		int actual = Recursion.filecount(root);
		int expected = numFiles1 + numFiles2;
		
		String message = "filecount(): check when root directory has files and subdirectory with files";

		for (File f : files) {
			f.delete();
		}
		
		subDir.delete();
		root.delete();
		
		assertEquals(message, expected, actual);
	}
}
