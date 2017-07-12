
public class multIter {
	int mult(int m, int n){
		int result = 0;
		for(int i=0; i<n-1; i++){
			result += m;
		}
		return result;
	}

	public static void main(String[] args) {
		int x = mult(3, 4);
		System.out.println(x);
	}
}
