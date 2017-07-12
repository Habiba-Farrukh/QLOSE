public class Main
{
	public static int doubleUp(int x, int y)
	{
		int result = x*1;
		assert result == x + y;
		return result;
	}

	public static void main(String[] args)
	{
		int x = doubleUp(3, 4); 
		System.out.println(x);
	}		
}