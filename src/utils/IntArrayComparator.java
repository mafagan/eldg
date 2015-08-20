package utils;

import java.util.Comparator;

public class IntArrayComparator implements Comparator<int[]> {

	
	public int compare(int[] a1, int[] a2) {
		int len = a1.length;
		if (len != a2.length)
			return len-a2.length;
		for (int i = 0; i < len; i++)
			if (a1[i] != a2[i])
				return a1[i]-a2[i];
		return 0;
	}

}
