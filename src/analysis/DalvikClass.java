package analysis;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;

public class DalvikClass extends GeneralClass {
	private GeneralClass superClass;
	private Set<DalvikClass> childClasses;
	private Set<GeneralClass> interfaces;
	private Set<DalvikField> fields;
	private Set<DalvikMethod> methods;
	DalvikClass(final String name){
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
		this.methods = methods;
	}
	
	/*
	 * Return the superClass of the class. If no superClass were set return Ljava/lang/Object; by default
	 * If the current class is Ljava/lang/Object; return null
	 */
	public GeneralClass getSuperClass(){
	    //TODO: this is a quick fix, need to check that this does not break anything
	    if (superClass == null){
	        if (!(this.getType().equals("Ljava/lang/Object;"))){
	            System.out.println("Warning: DalvikClass " + this.getType() + " has no superClass. Set ot Ljava/lang/Object; by default");
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
	public Set<DalvikMethod> getMethods(){
		return methods;
	}
	public Set<DalvikClass> getChildClasses(){
		return childClasses;
	}
}