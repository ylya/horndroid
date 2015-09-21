package analysis;

import java.util.Collections;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

public class DalvikClass extends GeneralClass {
	private GeneralClass superClass;
	private Set<DalvikClass> childClasses;
	private Set<GeneralClass> interfaces;
	private Set<DalvikField> fields;
	private Set<DalvikMethod> methods;
	DalvikClass(final String name){
		super(name);
		childClasses = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<DalvikClass, Boolean>()));
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
	public GeneralClass getSuperClass(){
		return superClass;
	}
	public Set<GeneralClass> getInterfaces(){
		return interfaces;
	}
	public Set<DalvikField> getFields(){
		return fields;
	}
	public Set<DalvikMethod> getMethods(){
		return methods;
	}
	public Set<DalvikClass> getChildClasses(){
		return childClasses;
	}
}