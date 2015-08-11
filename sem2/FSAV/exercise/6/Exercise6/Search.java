class Search {

    public int[] search(int[][] array, int value) {
	    int x = 0;
	    int y = array[0].length - 1;

	    while(x < array.length && y >= 0) {

	         if(array[x][y] == value) {
	        		return new int[] { x, y };
	        }

	         if(array[x][y] < value) {
	         	x++;
	         } else {
	         	y--;
	         }

	    }

	    return null;
    }
}
