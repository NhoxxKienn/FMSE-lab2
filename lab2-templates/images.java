public class images {
	/*@ public invariant (height > 0);@*/
	private /*@spec_public*/ int height;

	/*@ public invariant width > 0; @*/
	private /*@spec_public*/ int width;

	/*@ public invariant (image.length == height && image[0].length == width); @*/
	private /*@spec_public*/ int[][] image;
	
	private /*@spec_public*/ int[] coordinates;
	
	
	public images(int[][] image) {
		throw new RuntimeException("No implementation given");
	}
	
	/*@	public normal_behavior
		requires column >= 0 && column < width;
		requires row >= 0 && row < height;
		assignable image[row][column];
		ensures image[row][column] == newValue;
		ensures \result == newValue;

		also 

		public exceptional_behavior
		requires column <0 || column >= width || row < 0 || row >= height;
		signals_only ArrayIndexOutOfBoundsException;
		assignable \nothing;

	@*/
	public int replacePixel(int row, int column, int newValue) {
    	throw new RuntimeException("No implementation given");
	}
	

	/*@ public normal_behavior
		assignable image[*];
		ensures (\forall int i, j; i >=0 && i < height && j >= 0 && j < width; 
							image[i][j] == \old(image[height-1-i][width - 1 - j]));
	@*/
    public void mirrorImage() {
    	throw new RuntimeException("No implementation given");
    }
    

	/*@ public normal_behavior
		requires startRow <= endRow && startColumn <= endColumn;
		requires startRow >= 0 && startRow < height;
		requires endRow >= 0 && endRow < height;
		requires startColumn >= 0 && startColumn < width;
		requires endColumn >= 0 && endColumn < width;
		assignable image, height, width;
		ensures height == (endRow - startRow + 1);
		ensures width == (endColumn - startColumn + 1);
		ensures (\forall int i, j; i >=0 && i < height && j >= 0 && j < width; 
							image[i][j] == \old(image)[startRow + i][startColumn + j]);

		also

		public exceptional_behavior
		requires startRow > endRow || startColumn > endColumn 
				|| startRow < 0 || endRow >= height || startColumn < 0 || endColumn >= width; 
		assignable coordinates, coordinates[*];
		signals_only ArrayIndexOutOfBoundsException;
		signals (ArrayIndexOutOfBoundsException) 
				(coordinates.length == 4 
				&& coordinates[0] == startRow && coordinates[1] == startColumn 
				&& coordinates[2] == endRow && coordinates[3] == endColumn);
 
	@*/
    public void minimizeImage(int startRow, int startColumn, int endRow, int endColumn) {
    	throw new RuntimeException("No implementation given");
    }
    

	/*@ public normal_behavior
		assignable \nothing;
		ensures \result.length == height && \result[0].length == width;
		ensures (\forall int i, j; i >=0 && i < height && j >= 0 && j < width && image[i][j] >= threshold; 
							image[i][j] == \result[i][j]);
		ensures (\forall int i, j; i >=0 && i < height && j >= 0 && j < width && image[i][j] < threshold; 
							\result[i][j] == 0);
	@*/
    public int[][] thresholdFilter(int threshold) {
    	int[][] newImage = new int[height][width];
    	for (int i = 0; i < height; i++) {
    		for (int j = 0; j < width; j++) {
    			if (image[i][j] < threshold) newImage[i][j] = 0;
    			else newImage[i][j] = image[i][j];
    		}
    	}
    	return newImage;
    }
    

	/*@ public normal_behavior
		assignable image[*];
		ensures (\forall int i, j; i>=0 && i < height && j>=0 && j < width && 
				(\forall int m, n; m >= 0 && m <height && n >= 0 && n < width  ;\old(image[i][j]) >= \old(image[m][n])); 
				(\forall int x, y; x >= -1 && x <= 1 && y >= -1 && y <= 1 && (x + i >= 0) && (x + i < height) && (y + j >= 0) && (y + j < width);
								image[x + i][y + j] == \old(image[i][j])));
	@*/
    public void replaceHighestNeighbour() {
	    int[][] newImage = new int[height][width];
	    for (int i = 0; i < height; i++) {
	    	for (int j = 0; j < width; j++) {
	    		int highestValue = 0;
	    		for (int k = 0; k < 3; k++) {
	    			for (int l = 0; l < 3; l++) {
	    				int x = i + (k - 1);
	    				int y = j + (l - 1);
	    				if (x >= 0 && x < height && y >= 0 && y < width) 
	    					if (highestValue < image[x][y]) highestValue = image[x][y];
	    			}
	    		}
	    		newImage[i][j] = highestValue;
	    	}
	    }
	    image = newImage;
    }
	
}

