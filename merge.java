
import java.math.*;


class merge {

    public static void mergesort (int[] A, final int inf, final int sup)
    
    {
		
		if (inf < sup) {
			int q=(int)Math.floor((sup+inf)/2);
			mergesort(A, inf, q);
			mergesort(A, q+1, sup);
			merge(A, inf, q, sup);
		}
		
    }

    public static void merge (int[] A, final int inf, final int q, final int sup)
   
    {
		
        int n1 = (q-inf)+1;
        int n2 = sup-q;
		
        int[] L = new int[n1 + 1];
		int[] R = new int[n2 + 1];

        /*@ loop_invariant
          @    0 <= i && i <= n1
          @    &&
          @    (\forall int j ; 0 <= j && j < i ; L[j] == A[inf + j]);
          @*/
        //@ decreasing n1 - i;
        for (int i = 0; i < n1; i++) {
            L[i] = A[inf + i];
        }
		
		for (int j = 0; j < n2; j++) {
            R[j] = A[(q+1) + j];
        }
		
        L[n1] = Integer.MAX_VALUE;
		R[n2] = Integer.MAX_VALUE;
		
        int i = 0;
        int j = 0;
        
        
        for (int k = inf; k<sup+1; k++) {
			if (L[i]<=R[j]) {
				A[k]=L[i]; i++;
			}
			
			else {
				A[k]=R[j]; j++;
			}
        }
		
    }
	
	public static void main(String[] args) {

 
        int[] A = {10,9,8,7,6,5,4,3,2,1};
        
        mergesort(A,0,A.length-1);
        System.out.println("El arreglo ordenado es: ");
           for(int i=0;i<A.length;i++) {
            System.out.print(A[i]+" ");
            	
           }
    }

}