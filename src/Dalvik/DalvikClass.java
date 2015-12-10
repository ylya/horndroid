package Dalvik;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class DalvikClass extends GeneralClass {
	private GeneralClass superClass;
	private Set<DalvikClass> childClasses;
	private Set<GeneralClass> interfaces;
	private Set<DalvikField> fields;
	private Map<Integer,DalvikMethod> methods;
	
	public DalvikClass(final String name){
		super(name);
		childClasses = Collections.synchronizedSet(new HashSet<DalvikClass>());
	}
	public void putSuperClass(final GeneralClass superClass){
		this.superClass = superClass;
	}
	public void putChildClass(final DalvikClass childClass){
		childClasses.add(childClass);
	}
	public void putInterfaces(final Set<GeneralClass> interfaces){
		this.interfaces = interfaces;
	}
	public void putFields(final Set<DalvikField> fields){
		this.fields = fields; 
	}
	public void putMethods(final Set<DalvikMethod> methods){
		this.methods = new HashMap<Integer,DalvikMethod>();
		for (DalvikMethod dm : methods){
		    this.methods.put(dm.getName().hashCode(), dm);
		}
	}
	
	/*
	 * Return the superClass of the class. If no superClass were set return Ljava/lang/Object; by default
	 * If the current class is Ljava/lang/Object; return null
	 */
	public GeneralClass getSuperClass(){
	    if (superClass == null){
	        if (!(this.getType().equals("Ljava/lang/Object;"))){
	            return new GeneralClass("Ljava/lang/Object;");
	        }else{
	            return null;
	        }
	    }
		return superClass;
	}
	public Set<GeneralClass> getInterfaces(){
		return interfaces;
	}
	
	/*
	 * Return the fields of the class, always in the same order.
	 */
	public Set<DalvikField> getFields(){
	    TreeSet<DalvikField> f = new TreeSet<DalvikField>(fields);
	    if (this.superClass instanceof DalvikClass){
	        f.addAll(((DalvikClass) this.superClass).getFields());
	    }
		return f;
	}
	public Set<DalvikField> getExactFields(){
        return fields;
    }
	public Collection<DalvikMethod> getMethods(){
		return methods.values();
	}
    public DalvikMethod getMethod(int m){
        return methods.get(m);
    }	
	public Set<DalvikClass> getChildClasses(){
		return childClasses;
	}
}