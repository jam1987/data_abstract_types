//@ import org.jmlspecs.models.JMLString;
import org.jmlspecs.models.JMLString;
import org.jmlspecs.models.JMLValueSequence;

public class Cola implements ColaInterface {

    
	//@ public model JMLValueSequence seq;
	private /*@ spec_public nullable @*/ Nodo elementos;

    //@ represents seq <- deColaASequence(elementos);
	
	 private class Nodo {
	
	   private /*@spec_public@*/ String cont;
		private /*@ spec_public @*/ Nodo sig;
		
		/*@ 
		  @ ensures this.cont.equals(s)  && 
          @         ((this.sig == null && s == null) || (this.sig.equals(t))); 
          @*/
		public Nodo (String s, Nodo t) {
		
		    cont=s;
		
		    sig=t;
			
		}
		
	}
	
	private /*@ spec_public @*/ Nodo cabeza;
	private /*@ spec_public @*/ Nodo Final;
	
	public Cola() {
	
	    
		cabeza=new Nodo("",null);
		Final=new Nodo("",null);
		
		
		
	
	}
	
	
	/*@ also
	  @ assignable \everything;
	  @*/
	public void encolar (String e) {
	
	    Nodo nuevo= new Nodo(e,null);
	    if (cabeza.sig==null && cabeza.cont=="") {
		
		    cabeza=nuevo;
			
        } else {
		
		    
			
			
		
			Final.sig=nuevo;
			
			
			
		}
		
		Final=nuevo;
			
		
	}
	
	public int tamano () {
	
	    int tam=0;
		
		Nodo aux=cabeza;
		
		while (aux.sig!=null) {
		
		    tam++;
			
			aux=aux.sig;
			
		}
		
		return tam+1;
			
		}
		
	
		public String[] FromQeueToArray () {
		
		    Nodo aux=this.cabeza;
		    String[] array=new String[this.tamano()];
			
			for (int k=0;k <this.tamano();k++) {
			
			    array[k]=aux.cont;
				
				aux=aux.sig;
				
				
				
			}
			
			return array;
			
		
		}
		
		public static /*@ pure @*/ JMLValueSequence deColaASequence (
                    final Nodo l) {

        JMLValueSequence seq = new JMLValueSequence();

        Nodo aux = l;

        while (aux != null) {

            JMLString p = new JMLString(aux.cont);

            aux = aux.sig;

            seq = seq.insertBack(p);

        }
        return seq;
    }
		
	public static void main (String[] args) {

    Cola a=new Cola();

    a.encolar("ama");
	a.encolar("ame");
	a.encolar("mama");
	a.encolar("sama");
	a.encolar("asna");
	a.encolar("apa");
	a.encolar("ata");
	a.encolar("cama");
	a.encolar("casa");
	a.encolar("casta");
	a.encolar("delta");
	a.encolar("delco");
	String[] b= new String[1];
	
	b=a.FromQeueToArray();
	
	for (int k=0; k<b.length;k++) {
	
	    System.out.println("{ "+b[k]+" }");
		
	}
	
	
	}
		
	
    
		
}
			
			
		
		
	

