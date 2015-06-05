

//@ model import org.jmlspecs.models.*;
//@ import org.jmlspecs.models.JMLString;
//@ import org.jmlspecs.models.JMLValueSet;

import org.jmlspecs.models.JMLString;
import org.jmlspecs.models.JMLValueSet;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.File;
import java.io.IOException;
import java.util.StringTokenizer;
import java.io.PrintWriter;
import java.io.FileOutputStream;
import java.io.File;
import java.util.Iterator;
	


public class ConsultOrtArreglos implements ConsultOrt, Iterable
{
    final static int TAM_INIC = 1;
    private /*@ spec_public @*/ String va[];
    private /*@ spec_public @*/ int tam;

    /*@ public invariant 
            (\forall int i, j ; 0 <= i && i < this.tam 
				 && 
				0 <= j && j < this.tam 
				 && 
				i != j
			      ; !this.va[i].equals(this.va[j])
            )
             &&
	    (\forall int i ; 0 <= i && i < this.tam - 1
			   ; this.va[i].compareTo(this.va[i + 1]) < 0
	    )
             &&
            0 <= this.tam && this.tam <= this.va.length	
             &&
            this.va.length > 0;						 
      @*/
	  
    //@ public represents  vocabulario <- JMLValueSet.convertFrom(transformar(this.va, this.tam));
	    //COMPLETAR RELACION DE ACOPLAMIENTO

	  
    /*@ 
      @ requires 
            true;
      @ ensures 
            this.tam == 0 && this.va.length == 1;
      @*/	
    public ConsultOrtArreglos()
    {
        this.va = new String[TAM_INIC];
	this.tam = 0;
    }
	
    /*@ also normal_behavior
	    requires 
                tam < va.length && bf(p) && !(this.va[(bb(this.va,p))].equals(p));
	    ensures 
                tam == \old(tam) + 1 
	         && 
		va[bb(va, p)].equals(p);
	    ensures 
                (\forall int i ; 0 <= i && i < bb(va, p)
                               ; \old(va[i]).equals(va[i])
                )		
                 &&
  		(\forall int i ; bb(va, p) < i && i < \old(tam)
                               ; \old(va[i-1]).equals(va[i])
                ); 
	    assignable 
                va, tam;		
      @ also normal_behavior 
	    requires  
                tam == va.length && bf(p) && !(this.va[(bb(this.va,p))].equals(p));
            ensures 
                va.length == 2 * \old(va).length;
	    ensures 
                (\forall int i ; 0 <= i && i < bb(va, p)
                               ; \old(va[i]).equals(va[i])
                )		
                 &&
		(\forall int i ; bb(va, p) < i && i < \old(tam)
                               ; \old(va[i-1]).equals(va[i])
                );
            ensures 
                tam == \old(tam) + 1 && va[bb(va, p)].equals(p);
	    assignable 
                \nothing;			
			
      @*/	  
    public void agregar(String p) throws 
        ExcepcionPalabraNoBienFormada, 
	ExcepcionPalabraYaRegistrada 
    {
        if (!bf(p)) throw new ExcepcionPalabraNoBienFormada
                              ("Palabra no bien formada");
	int posi = bb(va, p);	
	if (posi < this.tam && va[posi].equals(p))	
            throw new ExcepcionPalabraYaRegistrada
                      ("Palabra en vocabulario");	
	if (this.tam == this.va.length)
        {
            String vtemp[] = new String[2 * va.length];
            for (int i = 0; i < va.length; i++)
                vtemp[i] = va[i];
            va = vtemp;				
        }	
        for (int i = this.tam; i > posi; i--) 
            va[i] = va[i-1];	
	va[posi] = p;
        tam++;
        
	
						
					    
        
        
    }	
			
    /*@ 
      @ requires 
            true;
      @ ensures 
            true;
      @*/
    private /*@ spec_public pure @*/ int bb(String a[], String s)
    {
       int pos = 0;

       int izq=0;

       int der=this.tam;

        int med=(izq+der)/2;

		/*@ decreases der-izq;
		  @*/
        while(izq!=der) {

            if(s.compareTo(a[med])>0) {

               izq=med+1;
               med=(izq+der)/ 2;

            }

            else if(s.compareTo(a[med])<0) {

                der=med;
                med=(izq+der)/2;

            }

            else if(s.compareTo(a[med])==0) {

                izq=der; // se sale del ciclo

            }
        }
        
		pos = med;

        return pos;
   }
   
	
    
    public /*@ pure @*/ boolean  bf(String p)
    {
        
	     boolean is=true;


             if (p.equals("")) {

                 is=false;


             } else {

             
	     
	     char[] aa= p.toCharArray();
	     
	     int k=0;

            	
			   /*@ decreases aa.length-k;
               @*/
	     
	     while (k<aa.length && is) {
			 
			     is= Character.isLowerCase(aa[k]); 
			     
			     k++;
			 
			 }

         }
			 
			 
	  return is;
					 
					   
	     		
    }
	
    	
    public /*@ pure @*/ boolean  ipf(String p, String q)
    {
        boolean is=true;
	   
	   int i=0;
	   
	   if (q.length()<p.length()) {
		   
		   return false;
		   
		   } else {
			   
					
	     /*@ decreases p.length()-i;
	     @*/
	   while (i<p.length() && is) {
		   
		   if (!(p.charAt(i)-q.charAt(i)==0)) {
			   
			   is=false;
			   
			   
			   
		   }
		   
		   
		   i++;
		   
		   
	   }
	   
		   }
		   
	    
	    
	    
	    return is;
	    				
    
    
    }

    /*@ also
      @ requires 
            true;
      @ ensures 
            true;
      @*/
    public String[] consultarPorPrefijo(String pr) throws 
    ExcepcionPalabraNoBienFormada
    
    {
    
    if (!bf(pr)) throw new ExcepcionPalabraNoBienFormada
                              ("Palabra no bien formada");
    
    String[] palabra= new String [0];
    
    int k;
    int j=0;
    
	int posi=bb(va,pr);
	
	k=posi;
	
    /*@ decreases this.tam-k;
      @*/
    while (k<this.tam) {
    	
    	
    	                          
    	 
    	 
    	 if (ipf(pr,this.va[k])) {

                String vtemp[] = new String[ palabra.length+1];
            for (int i = 0; i < palabra.length; i++) {
                vtemp[i] = palabra[i];
            }
            
            palabra = vtemp;	
                
    	 	
    	 	palabra[j]=va[k];

               
                k++;
                j++;
               

               
    	 	
    	 } else {

          k++;


        }
    	 
    	 
    	 
    }
    
    
    return palabra;
	
    }	
    /*@ also
      @ requires 
            true;
      @ ensures 
            true;
      @*/
    public String prefijoMasLargo(String pl) throws 
        ExcepcionPalabraNoBienFormada
    {
        if (!bf(pl)) throw new ExcepcionPalabraNoBienFormada
                                ("Palabra no bien formada");
                                
        int i=pl.length();
        
        String pr="";
		
		
        
		
       
        
        
        while (i>=0) {
			
			String a=pl.substring(0,i);
			
			
			
			
			if (consultarPorPrefijo(a).length!=0) {
				
				pr=a;
				
				i=-1;
				
				} 
			
			i--;
			
		}
		
			
		
			




	return pr;
    }	
    /*@
	      @ requires (tam <= ns.length);
	      @ ensures \result.length == tam;
	      @ ensures (\forall int i ; 0 <= i && i < tam ; \result[i].equals(new JMLString(ns[i])));
	      @*/
	    private static /*@ pure spec_public @*/ JMLString[] transformar(
	                                                              String[] ns, int tam) {

	        JMLString[] res = new JMLString[tam];

                
                 /*@ decreases tam-i;
                  @*/
	        for (int i = 0; i < tam; i++) {
	            res[i] = new JMLString(ns[i]);
	        }
	        return res;
	    } 
		
		

	/*@ also
      @ requires (new File(nombre)).exists() && 
      @          (new File(nombre)).isFile() &&
      @          (new File(nombre)).canRead();
      @ ensures (* se ha leido el archivo y se ha agregado las palabras al consultor *);
      @*/															       
	public void leerArchivo(String nombre) throws NoTextFoundException	{
	  
          BufferedReader br = null;
	      String linea="";
	      try {
              br = new BufferedReader(new FileReader(nombre));
          } catch (IOException e) {
              System.out.println("");
				  
			  throw new NoTextFoundException
			  ("Archivo no encontrado");
          }
	
	      StringTokenizer s;
		
		  String a="";
	      while(linea!=null) {
              try { 
			   
                  linea=br.readLine();
              } catch (IOException f) {
				   
                  linea = null;
              }
              if (linea!=null) {
					 
		          s=new StringTokenizer(linea);
					 
				  while (s.hasMoreTokens()) {
				      a=s.nextToken();
					   
					 try {
						  
						  this.agregar(a);
						  
						  } catch (ExcepcionPalabraNoBienFormada e) {
							  
							 
							  
							  } catch (ExcepcionPalabraYaRegistrada e) {
								  
							
								  
							  }
							 
			     }
			}
	   }
	   
	  

 
}

    private class Iter implements Iterator {

        private /*@ spec_public @*/ ConsultOrtArreglos a1;
        private /*@ spec_public @*/ int pos;
       

        public Iter (ConsultOrtArreglos a) {

            a1=a;
            pos=0;
           

       }

       /*@ also
         @ assignable pos;
         @*/
       public Object next () {

            
            
         String s=a1.va[pos++];

           

          return new String (s);




      }

      public boolean hasNext() {

           return pos<(a1.tam);

      }

      public void remove() {
     }



   }

   

     public Iterator iterator() {

          return new Iter(this);

     }

    
            
             


      /*@ also 
	    @ ensures (*Se imprimen todas las palabras del vocabulario en pantalla *);
	    @*/
     public void listar (ConsultOrt a) {
	
	
             Iterator it;

             it=a.iterator();

             while (it.hasNext()) {

                 System.out.println(((String)it.next()));


             }
	
     }
	


    
	
}


