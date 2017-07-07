public class Main
{
	public static int max3(int x, int y, int z)
	{
	    if(x>y) { 
	    	y = x;
	    }
	    if(y>z) {
	    	z = x;
	    }
	    return z;
	}

	public static void main(String[] args)
	{
	    int x = max3(1, 2, 3); 
	    System.out.println(x);
	}		
}