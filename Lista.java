public class Lista <E> implements List {

	private Nodo elementos;
	private int tamano;

	private class Nodo {

	    private E info;
	    private Nodo siguiente;
	    private Nodo anterior;

	    public Nodo() {
	        info=null;
		siguiente= null;
		anterior= null;
	    }
		
	}

	public Lista  () {
	    elementos= null;
	    tamano=0;
	}

   /**
     * Agrega <i>element</i> a la lista.
     *
     * @param element de tipo E, con el que se declaro el objeto
     * lista particular,
     * @return true si el elemento fue insertado, false en caso contrario
     */

    public boolean add(Object element) {
	Nodo nuevo = new Nodo();
	nuevo.info = (E)element;
	
	if (elementos == null){
		elementos = nuevo;
		tamano++;
	}
	else{
		nuevo.siguiente = elementos;
		elementos.anterior = nuevo;
		elementos = nuevo;
		tamano++;
	}
	
	return true;
    }
    /**
     * Agrega <i>element</i> a la lista en la posicion <i>i</i>, si <i>i</i> &gt;
     * que size() el elemento se agrega al final de lista.
     *
     * @param element de tipo E, con el que se declaro el objeto
     * lista particular,
     * @return true si el elemento fue insertado, false en caso contrario
     */

    public boolean add(int index, Object element) {
		int k = 0;
		Nodo nuevo = new Nodo();
		nuevo.info = (E)element;
		Nodo auxiliar = this.elementos;
		
		for(k = 0 ; k < index && auxiliar.siguiente != null ; k++){
			auxiliar = auxiliar.siguiente;
		
		}
		
		if (auxiliar.siguiente == null && k < index){
			auxiliar.siguiente = nuevo;
			nuevo.anterior = auxiliar;
			nuevo.siguiente = null;
			tamano++;
			return true;
		
		}
		
		else{
			nuevo.siguiente = auxiliar;	
			nuevo.anterior = auxiliar.anterior;
			if (auxiliar.anterior != null) auxiliar.anterior.siguiente = nuevo;
			auxiliar.anterior = nuevo;
			tamano++;
			return true;
		}
	}

    /**
     * Elimina todos los elementos de la lista. La lista debe quedar como recien creada.
     *
     */

    public void clear() {
	this.elementos = null;
	this.tamano = 0;
    }


    /**
     * Retorna una nueva {@code List} con los mismos elementos que esta
     * {@code List}.
     *
     * @return una lista con los mismos elementosque esta lista
     * @see java.lang.Cloneable
     */

    public List clone() {
	List clon= new Lista();
	Nodo aux=this.elementos;
	while (aux!=null) {
	    clon.add(aux.info);
	    aux=aux.siguiente;
	}
	return clon;
    }


    /**
     * Determina si el objeto <i>o</i> esta contenido en la lista. {@code Object equals}
     *
     * @see Object#equals
     */
    public boolean contains(Object o) {
	boolean pertenece=false;
	Nodo aux=this.elementos;
       	while (aux!=null && !pertenece) {
	    pertenece = aux.info.equals(o);
	    aux=aux.siguiente;
	}
	return pertenece;
    }
	
   /**
     * Determina si la lista <i>o</i> es igual a la lista actual. 
     *
     * @param o la lista con la que se desea comparar
     * 
     * @return true si las dos listas tienen el mismo tamano y contienen los mismos
     * objetos en el mismo orden. false en caso contrario
     *
     */

     public boolean equals(List o) {
         boolean igual=true;
	 Nodo lista1=this.elementos;
	 while (lista1!=null  && igual) {
	     igual=igual && (o.contains(lista1.info)) &&
	         (this.indexOf((E)lista1.info)==o.indexOf((E)lista1.info));
	     lista1=lista1.siguiente;
	 }
	return igual;
	}
	
	

  

    /**
     * Devuelve el elemento al macenado en la posicion index de la lista.
     *
     * @param index posicion del elemento a devolver.
     * 
     * @return null si index &gt; size()
     */
    public E get(int index){
	Nodo lista=this.elementos;
	E ele=null;
	for (int k=1; k<index && lista!=null; k++) {
	    lista=lista.siguiente;
	}
	if (lista!=null) {
	    ele=lista.info;
	}
	return ele;
    }


    /**
     * Determina la posicion del elemento <i>o</i> en la lista
     * 
     * @param o el objeto
     * @return si el elemento esta en la lista retorna suy posicion, sino -1
     */
    public int indexOf(Object o) {
	
        Nodo lista=this.elementos;
	int posi=-1;
	while (lista!=null && !(lista.info.equals(o))) { 
	    lista=lista.siguiente;
	    posi++;
	}
	if (lista!=null) {
	    return posi;
	} else {
	    return -1;	
	}
    }

    /**
     * Determina si la lista no tiene elementos.
     *
     * @return true si size() &e; 0. falso en caso contrario
     */
    public boolean isEmpty() {
	return (tamano == 0);
    }

    /**
     * Elimina el elemento en la posicion index.
     *
     * @param index la posicion del elemento a eliminar, 0 &le; index &lt; size()
     * @return el elemento eliminado, si no se elimino ningun elemento retorna
     * null
     */
    public E remove(int index) {
	int k = 0;
	Nodo deleted = this.elementos;
	
	while(k < index && k < tamano){
		deleted = deleted.siguiente;
		k++;
	}

	if (k >= index) return null;

	remove(deleted.info);
	return deleted.info;
	
    }
    
    /**
     * Elimina el elemento <i>o</i>.
     *
     * @param o el elemento a eliminar.
     * @return true si el elemento existia y fue eliminado, false en caso contrario.
     * null
     */
    public boolean remove(Object o) {
	Nodo lista=this.elementos;
	if (this.elementos==null) {
	    return false;
	} 
	else {
	    while (lista!=null && !(lista.info.equals(o))) { 
		 lista=lista.siguiente;
	    }
	    if (lista == null) {
		 return false;			
	    }     
	    else {
	        if (lista.anterior!=null) lista.anterior.siguiente=lista.siguiente;
		    if (lista.siguiente!=null) lista.siguiente.anterior=lista.anterior;
		        tamano--;
			return true;
		    }		
	    }
    }

    /**
     * Retorna el numero de elementos enla lista
     *
     * @return el numero de elementos en la lista
     */
    public int size() {
	return tamano;
    }

    /**
     * Retorna un nuevo arreglo que contiene todos los elementos
     * en esta lista {@code List}.
     *
     * @return an array of the elements from this {@code LinkedList}.
     */

    public Object[] toArray() {
	Object[] cont= new Object[this.tamano];
	Nodo lista=this.elementos;
	for (int k=0; k<this.tamano;k++) {
		cont[k]=lista.info;
		lista=lista.siguiente;
	}
	return cont;
    }

    /**
     * Retorna la retpresentacion en String de esta {@code List}
     *
     * @return la retpresentacion en String de esta {@code List}
     */
    @Override
    public String toString() {
	String cont="";
	Nodo aux=this.elementos;
	while (aux!=null) {
		cont=cont+aux.info.toString();
		aux=aux.siguiente; 
	}
	cont = cont + "\n";
	return cont;
    }

}

	
