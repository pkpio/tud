package problem3;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

/**
 * Some selected test cases
 * 
 */
public class TestSystemArrayCopyExceptional {

	private int[] srcIntArray = new int[5];
	private int[] destIntArray = new int[5];
	
	@Before
	public void init() {
		for (int i = 0; i<srcIntArray.length;i++) {
			srcIntArray[i] = i;
		}

		for (int i = 0; i<destIntArray.length;i++) {
			destIntArray[i] = destIntArray.length + i;
		}

	}
	
	
	@Test(expected=java.lang.NullPointerException.class)
	public void testSourceIsNull() {
		try {
			java.lang.System.arraycopy(null, 0, destIntArray ,0, 3);
		} finally {
			for (int i = 0; i<destIntArray.length; i++) {
				assertEquals(destIntArray.length + i, destIntArray[i]);
			}
		}
	}

	

	@Test(expected=java.lang.NullPointerException.class)
	public void testDestIsNull() {
		java.lang.System.arraycopy(srcIntArray, 0, null, 0, 3);
	}

	
	@Test(expected=java.lang.ArrayIndexOutOfBoundsException.class)
	public void testSrcTooShortIndexOutOfBounds() {
		try {
			java.lang.System.arraycopy(srcIntArray, 4, destIntArray ,0, 2);
		} finally {
			for (int i = 0; i<destIntArray.length; i++) {
				assertEquals(destIntArray.length + i, destIntArray[i]);
			}
		}
	}
	
	@Test(expected=java.lang.ArrayIndexOutOfBoundsException.class)
	public void testDestTooShortIndexOutOfBounds() {
		try {
			java.lang.System.arraycopy(srcIntArray, 0, destIntArray, 4, 2);
		} finally {
			for (int i = 0; i<destIntArray.length; i++) {
				assertEquals(destIntArray.length + i, destIntArray[i]);
			}
		}
	}
	
		
	@Test(expected=java.lang.ArrayStoreException.class)
	public void testSrcIsNoArray() {
		try {
			java.lang.System.arraycopy("Hello World", 0, destIntArray ,0, 3);
		} finally {
			for (int i = 0; i<destIntArray.length; i++) {
				assertEquals(destIntArray.length + i, destIntArray[i]);
			}
		}
	}
	
	@Test(expected=java.lang.ArrayStoreException.class)
	public void testTwoRefArraysWithIncompatibleElement() {
		String[] dest = new String[3];
		Object[] src  = new Object[] {null, "a", new Integer(3)};
		try {
			java.lang.System.arraycopy(src, 0, dest , 0, 3);
		} finally {
			for (int i = 0; i<destIntArray.length; i++) {
				assertEquals(destIntArray.length + i, destIntArray[i]);
			}
		}
	}
	
}
