public class Main
{
	public static int iterPower(int base, int exp){
	    int result = base;
	    while(exp > 0){
	    	result += base;
	    	exp -= 1;
	    }
	    return result;
	}
	public static void main(String[] args)
	{
	    int x = iterPower(2, 4); 
	    System.out.println(x);
	}		
}