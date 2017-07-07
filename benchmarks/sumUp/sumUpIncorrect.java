import java.util.Scanner;

public class Sum
{
	public static int SumUp(int n)
	{
	    int sum = 0;
	    for(int i = 0; i < n; i++){
	        sum += i;
	    }
	    return sum;
	}

	public static void main(String[] args)
	{
	    int x = SumUp( ); 
	    System.out.println(x);
	}		
}