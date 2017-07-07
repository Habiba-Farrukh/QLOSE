public class Main
{
	public static int doubleUp(int x, int y)
	{
		int result = x;
		while(x > 1){
			result += x;
			y -= 1;
		}
		return result;
	}

	public static void main(String[] args)
	{
		int x = doubleUp(3, 4); 
		System.out.println(x);
	}		
}