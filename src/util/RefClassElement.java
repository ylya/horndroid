
package util;

import gen.Gen;
import gen.CallRef;
import util.iface.IndStr;

import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import javax.annotation.Nonnull;

import org.apache.commons.lang3.builder.EqualsBuilder;
import org.apache.commons.lang3.builder.HashCodeBuilder;
import org.jf.dexlib2.dexbacked.DexBackedClassDef;
import org.jf.dexlib2.iface.ClassDef;
import org.jf.dexlib2.iface.Field;
import org.jf.dexlib2.iface.Method;
import org.jf.dexlib2.util.ReferenceUtil;

import com.google.common.collect.Lists;

final class ClassDefGen{
	final private int type;
	private int numField;
	@Nonnull private final Map<Integer, Integer> fieldMapping;
	public ClassDefGen(int type){
		this.type = type;
		this.fieldMapping = Collections.synchronizedMap(new HashMap <Integer, Integer>());
	}
	public int getType(){
		return type;
	}
	public void putField(int fieldInd){
		if (fieldMapping.isEmpty()) numField = 0;
			else numField += 1;
		fieldMapping.put(fieldInd, numField);
	}
	public int getFieldNum(int fieldInd){
		if (fieldMapping.containsKey(fieldInd))
			return fieldMapping.get(fieldInd);
		else return -1;
	}
	public int getNumberOfFields(){
		return fieldMapping.size();
	}
	@Override
	public int hashCode() {
        return new HashCodeBuilder(17, 31). // two randomly chosen prime numbers
            // if deriving: appendSuper(super.hashCode()).
            append(type).
            toHashCode();
    }
	@Override
    public boolean equals(Object obj) {
       if (!(obj instanceof ClassDefGen))
            return false;
        if (obj == this)
            return true;

        ClassDefGen p = (ClassDefGen) obj;
        return new EqualsBuilder().
            // if deriving: appendSuper(super.equals(obj)).
            append(type, p.type).
            isEquals();
    }
}

final class Instance {
	final private int c;
	final private int m;
	final private int line;
	final private int type;
	final private boolean isObj;
	public Instance (int c, int m, int line, int type, boolean isObj){
		this.c = c;
		this.m = m;
		this.line = line;
		this.type = type;
		this.isObj = isObj;
	}
	public int getC(){
		return c;
	}
	public int getM(){
		return m;
	}
	public int getLine(){
		return line;
	}
	public int getType(){
		return type;
	}
	public boolean isObj(){
		return isObj;
	}
}

final class ConcurInstance {
	final private int c;
	final private int m;
	final private int line;
	final private int type;
	final private int register;
	final private boolean isObj;
	public ConcurInstance (int c, int m, int line, int type, int register, boolean isObj){
		this.c = c;
		this.m = m;
		this.line = line;
		this.type = type;
		this.register = register;
		this.isObj = isObj;
	}
	public int getC(){
		return c;
	}
	public int getM(){
		return m;
	}
	public int getLine(){
		return line;
	}
	public int getType(){
		return type;
	}
	public int getRegister(){
		return register;
	}
	public boolean isObj(){
		return isObj;
	}
}



final class Pair{
	final String className;
	final String item;
	public Pair (String className, String item){
		this.className = className;
		this.item = item;
	}
	@Override
	public int hashCode() {
        return new HashCodeBuilder(17, 31). // two randomly chosen prime numbers
            // if deriving: appendSuper(super.hashCode()).
            append(className).
            append(item).
            toHashCode();
    }
	@Override
    public boolean equals(Object obj) {
       if (!(obj instanceof Pair))
            return false;
        if (obj == this)
            return true;

        Pair p = (Pair) obj;
        return new EqualsBuilder().
            // if deriving: appendSuper(super.equals(obj)).
            append(className, p.className).
            append(item, p.item).
            isEquals();
    }
}

public class RefClassElement {
	@Nonnull private int synRange;
	@Nonnull private int synConcurRange;
	@Nonnull private final Set<Pair> refClassField;
	@Nonnull public final Set<CallRef> callRefs;
	@Nonnull private final Set<Pair> refClassMethod;
	@Nonnull private final Map<Integer, Instance> instanceMapping;
	@Nonnull private final Map<Integer, ConcurInstance> instanceConcurMapping;
	@Nonnull private final Set<ClassDefGen> classDefSet;
	//@Nonnull private final Map<Integer, Integer> implementations;
	public RefClassElement(){
		this.synConcurRange = 0;
		this.refClassField = Collections.synchronizedSet(new HashSet <Pair>());
		this.refClassMethod = Collections.synchronizedSet(new HashSet <Pair>());
		this.classDefSet = Collections.synchronizedSet(new HashSet <ClassDefGen>());
		this.callRefs = Collections.synchronizedSet(new HashSet <CallRef>());
		this.instanceMapping = Collections.synchronizedMap(new ConcurrentHashMap <Integer, Instance>());
		this.instanceConcurMapping = Collections.synchronizedMap(new HashMap <Integer, ConcurInstance>());
		//this.implementations = Collections.synchronizedMap(new HashMap <Integer, Integer>());
	}
	private void addImplementationsFromSuperClass(final int c, final int m, final List<? extends ClassDef> classDefs, final IndStr indStr, 
			final int iNum, final int cSuper, final int iType, final Gen gen, final Map<Integer, Integer> implementations){
		String superClassName = "";
		for (final ClassDef classDef: classDefs) {
			if (indStr.get(classDef.getType(), 'c') == cSuper){
				superClassName = classDef.getSuperclass();
				break;
				}			
			}
		if (superClassName != ""){
			int superClassInd = indStr.get(superClassName, 'c');
			if (superClassInd == c)
				if (gen.isDefined(iType, m)){
					implementations.put(iNum, iType);
				}
			else
				addImplementationsFromSuperClass(c, m, classDefs, indStr, iNum, superClassInd, iType, gen, implementations);
		}
	}
	
	private void addImplementationsFromInterface(final int c, final int m, final List<? extends ClassDef> classDefs, final IndStr indStr, 
			final int iNum, final int iType, final Gen gen, final Map<Integer, Integer> implementations){
		for (final ClassDef classDef: classDefs) {
			if (indStr.get(classDef.getType(), 'c') == iType){
				for (final String interfaceName: classDef.getInterfaces()){
					int interfaceInd = indStr.get(interfaceName, 'c'); 
					if (interfaceInd == c){
						if (gen.isDefined(iType, m)){
							implementations.put(iNum, iType);
						}
					}			
				}
			}
		}
	}
	private void addChild(int superClass, final List<? extends ClassDef> classDefs, final IndStr indStr, final int c, final Map<Integer, Integer> implementations){
		for (final ClassDef classDef: classDefs) {
			if (indStr.get(classDef.getSuperclass(), 'c') == superClass){
				for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet()){	
					if (entry.getValue().getType() == indStr.get(classDef.getType(), 'c'))
							implementations.put(entry.getKey(), c);
				}
				addChild(indStr.get(classDef.getType(), 'c'), classDefs, indStr, c, implementations);
			}
		}
	}
	public final Map<Integer, Integer> getImplementations(final int c, final int m, final List<? extends ClassDef> classDefs, final IndStr indStr, final Gen gen){
		final Map<Integer, Integer> implementations = Collections.synchronizedMap(new HashMap <Integer, Integer>());
		//implementations.clear();
		final Map<Integer, Instance> instanceMappingUn = Collections.unmodifiableMap(instanceMapping);
		final Iterator it = instanceMappingUn.entrySet().iterator();
		while(it.hasNext()){	
			Map.Entry<Integer, Instance> entry = (Map.Entry<Integer, Instance>) it.next();
			if (entry.getValue().getType() == c)
				if (gen.isDefined(c, m)){
					implementations.put(entry.getKey(), c);
					addChild(c, classDefs, indStr, c, implementations);
				}
			addImplementationsFromSuperClass(c, m, classDefs, indStr, entry.getKey(), entry.getValue().getType(), entry.getValue().getType(), gen, implementations);
			addImplementationsFromInterface(c, m, classDefs, indStr, entry.getKey(), entry.getValue().getType(), gen, implementations);
		}
		return implementations;
	}

	public void addCallRef(final int calleeC, final int calleeM, final int callerC, final int callerM, final int callerNextLine){
		callRefs.add(new CallRef(calleeC, calleeM, callerC, callerM, callerNextLine));
	}

	public int staticFieldLookup(List<? extends ClassDef> classDefs, IndStr indStr, int c, int f){
		for (final ClassDef classDef: classDefs) {
			int curc = indStr.get(classDef.getType(), 'c');
			if (curc == c) {
				Iterable<? extends Field> staticFields;
				if (classDef instanceof DexBackedClassDef) {
					staticFields = ((DexBackedClassDef)classDef).getStaticFields(false);
				} else {
					staticFields = classDef.getStaticFields();
				}
			
				for (Field field: staticFields) {
					int fieldNum = indStr.get(ReferenceUtil.getShortFieldDescriptor(field), 'f');
					if (fieldNum == f) {
						return c;	
					}
				}
				String superClassName = classDef.getSuperclass();
				if (superClassName !=null)
					return staticFieldLookup(classDefs, indStr, indStr.get(superClassName, 'c'), f);
			}
		}
		return -1;
	}
	public void formClassDefGen(List<? extends ClassDef> classDefs, IndStr indStr){
		for (final ClassDef classDef: classDefs) {
			int c = indStr.get(classDef.getType(), 'c');
			putClassDefGen(c);
			Iterable<? extends Field> instanceFields;
	        if (classDef instanceof DexBackedClassDef) 
	            instanceFields = ((DexBackedClassDef)classDef).getInstanceFields(false);
	        else 
	            instanceFields = classDef.getInstanceFields();
	        
	        for (Field field: instanceFields) 
	        	putClassDefField(c, indStr.get(Utils.getShortReferenceString(field), 'f'));  
	        addFieldsFromSuperClass(classDefs, indStr, classDef, c);
		}
	}
	
	public int getHeapElementOrder(final int iNum, final int elNum, final Gen gen, final IndStr indStr){
		int prev = 0;
		boolean found;
		int order = -1;
		for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet()){
			found = false;
			if (entry.getValue().isObj()){
				for (ClassDefGen cldef : classDefSet)
					if (cldef.getType() == entry.getValue().getType()){
						if ((cldef.getFieldNum(elNum) != -1) && (entry.getKey() == iNum))
							order = prev + cldef.getFieldNum(elNum);
						else
							prev = prev + cldef.getNumberOfFields();
						found = true;
						break;
					}
				if (!found){
					int j = 0;
	    			for (Pair p : refClassField){
	    				if (indStr.get(p.className, 'c') == entry.getValue().getType()){
	    					if (indStr.get(p.item, 'f') == elNum){
	    						order = j;
	    						break;
	    					}
	    					else j++;
	    				}
	    			}
				}
			}
			else
				if (entry.getKey() == iNum)
					order = prev + elNum;
				else
					prev = prev + gen.verRange;
		}
		return order;			
	}
	
	public boolean isObj(final int iNum){
		for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet())
			if (entry.getKey() == iNum) 
				if (entry.getValue().isObj())
					return true;
				else 
					return false;
		return false;
	}
	
	
	private void addFieldsFromSuperClass(List<? extends ClassDef> classDefs, IndStr indStr, ClassDef classDef, int c){
		String superClassName = classDef.getSuperclass();
		if (superClassName != null)
			for (final ClassDef superClassDef: classDefs) {
				if (superClassName.equals(superClassDef.getType())){
					Iterable<? extends Field> instanceFields;
			        if (superClassDef instanceof DexBackedClassDef) 
			            instanceFields = ((DexBackedClassDef)superClassDef).getInstanceFields(false);
			        else 
			            instanceFields = superClassDef.getInstanceFields();
			        
			        for (Field field: instanceFields) 
			        	putClassDefField(c, indStr.get(Utils.getShortReferenceString(field), 'f')); 
			        addFieldsFromSuperClass(classDefs, indStr, superClassDef, c);
				}
			}
	}
	
	public int getSynRange(){
		return synRange;
	}
	public int getSynConcurRange(){
		return synConcurRange;
	}
	public void putConcurSynRange(int i){
		this.synConcurRange = i;
	}
	public void putInstance (int c, int m, int line, int type, boolean isObj){
		if (instanceMapping.isEmpty()) synRange = 1;
			else synRange += 1;
		instanceMapping.put(synRange, new Instance(c, m, line, type, isObj));	
	}
	public void putConcurInstance (int c, int m, int line, int type, int register, boolean isObj){
		if (instanceConcurMapping.isEmpty()) synConcurRange = synRange + 1;
			else synConcurRange += 1;
		instanceConcurMapping.put(synConcurRange, new ConcurInstance(c, m, line, type, register, isObj));	
	}
	public int getInstNum(int c, int m, int line){
		for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet())
	    	if ((entry.getValue().getC() == c) && (entry.getValue().getM() == m) && (entry.getValue().getLine() == line)) 
	    		return entry.getKey();
		return -1;
	}
	public int getNumberOfInstances(){
		return instanceMapping.size();
	}
	public int getNumberOfConcurInstances(){
		return instanceConcurMapping.size();
	}
	public int getConcurInstNum(final int c, final int m, final int line){
		for (Map.Entry<Integer, ConcurInstance> entry : instanceConcurMapping.entrySet())
	    	if ((entry.getValue().getC() == c) && (entry.getValue().getM() == m) && (entry.getValue().getLine() == line)) 
	    		return entry.getKey();
		return -1;
	}
	public int getConcurInstNumI(final int c, final int m, final int i){
		for (Map.Entry<Integer, ConcurInstance> entry : instanceConcurMapping.entrySet())
	    	if ((entry.getValue().getRegister() == i) && (entry.getValue().getC() == c) && (entry.getValue().getM() == m))
	    		return entry.getKey();
		return -1;
	}
	
	public int getConcurInstPc(final int c, final int m, final int i){
		for (Map.Entry<Integer, ConcurInstance> entry : instanceConcurMapping.entrySet())
	    	if ((entry.getValue().getRegister() == i) && (entry.getValue().getC() == c) && (entry.getValue().getM() == m))
	    		return entry.getValue().getLine();
		return -1;
	}
	public int getNumberOfAllConcurFields(final Gen gen){
		int size = 0;
		boolean found;
		for (Map.Entry<Integer, ConcurInstance> entry : instanceConcurMapping.entrySet()){
			found = false;
			if (entry.getValue().isObj()){
				for (ClassDefGen cldef : classDefSet)
					if (cldef.getType() == entry.getValue().getType()){
						size = size + cldef.getNumberOfFields();
						found = true;
						break;
					}
				if (!found){
					size = size + refClassField.size();
				}
			}
			else
				size = size + gen.verRange;
		}
		return size;
	}
	public int getNumberOfAllFields(final Gen gen){
		int size = 0;
		boolean found;
		for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet()){
			found = false;
			if (entry.getValue().isObj()){
				for (ClassDefGen cldef : classDefSet)
					if (cldef.getType() == entry.getValue().getType()){
						size = size + cldef.getNumberOfFields();
						found = true;
						break;
					}
				if (!found){
					size = size + refClassField.size();
				}
			}
			else
				size = size + gen.verRange;	
		}
		return size;
	}
	public int getInstType(int i){
		for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet())
	    	if (entry.getKey() == i) 
	    		return entry.getValue().getType();
		return -1;
	}
	public void putClassDefGen(final int c){
		classDefSet.add(new ClassDefGen(c));
	}
	public void putClassDefField (final int c, final int f){
		for (ClassDefGen cldef : classDefSet)
			if (cldef.getType() == c)
				cldef.putField(f);
	}
	public int getFieldNum(int i, int f, final IndStr indStr){
		boolean found;
		int fnum = -1;
		for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet()){
			found = false;
	    	if (entry.getKey() == i){
	    		for (ClassDefGen cldef : classDefSet)
	    			if (cldef.getType() == entry.getValue().getType()){
	    				fnum = cldef.getFieldNum(f);
	    				found = true;
	    				break;
	    			}
	    		if (!found){
	    			int j = 0;
	    			for (Pair p : refClassField){
	    				if (indStr.get(p.className, 'c') == entry.getValue().getType()){
	    					if (indStr.get(p.item, 'f') == f){
	    						fnum = j;
	    						break;
	    					}
	    					else j++;
	    				}
	    			}
	    		}
	    	}
		}
		return fnum;
	}
	public int getConcurType(int i){
		for (Map.Entry<Integer, ConcurInstance> entry : instanceConcurMapping.entrySet())
	    	if (entry.getKey() == i)
	    		return entry.getValue().getType();
		return -1;
	}
	public int getConcurFieldNum(int i, int f, final IndStr indStr){
		boolean found;
		int fnum = -1;
		for (Map.Entry<Integer, ConcurInstance> entry : instanceConcurMapping.entrySet()){
			found = false;
	    	if (entry.getKey() == i){
	    		for (ClassDefGen cldef : classDefSet)
	    			if (cldef.getType() == entry.getValue().getType()){
	    				fnum = cldef.getFieldNum(f);
	    				found = true;
	    				break;
	    			} 
	    		if (!found){
	    			int j = 0;
	    			for (Pair p : refClassField){
	    				if (indStr.get(p.className, 'c') == entry.getValue().getType()){
	    					if (indStr.get(p.item, 'f') == f){
	    						fnum = j;
	    						break;
	    					}
	    					else j++;
	    				}
	    			}
	    		}
	    	}
		}
		return fnum;
	}
	
	public void putField(String className, String fieldName){
		this.refClassField.add(new Pair(className, fieldName));
	}
	
	public void putMethod(String className, String methodName){
		this.refClassMethod.add(new Pair(className, methodName));
		
	}
	
	private static boolean lookInDirectMethods(ClassDef classDef, String methodName){
    	//look in direct methods
  		Iterable<? extends Method> directMethods;
        if (classDef instanceof DexBackedClassDef) {
            directMethods = ((DexBackedClassDef)classDef).getDirectMethods(false);
        } else {
            directMethods = classDef.getDirectMethods();
        }
        for (Method method: directMethods) {
        	if (methodName.equals(Utils.getShortReferenceString(method)) && (method.getImplementation() != null))
        		return true;
        }
        return false;
    }
    private static boolean lookInVirtualMethods(ClassDef classDef, String methodName){
    	Iterable<? extends Method> virtualMethods;
    	if (classDef instanceof DexBackedClassDef) {
    		virtualMethods = ((DexBackedClassDef)classDef).getVirtualMethods(false);
    		} else {
    		virtualMethods = classDef.getVirtualMethods();
    		}

    	for (Method method: virtualMethods) {
    		if (methodName.equals(Utils.getShortReferenceString(method)) && (method.getImplementation() != null))  
    			    				return true;
    			
    		
    	}
    	return false;
    }
    
    private static boolean findMissedInterfaceMethod(List<? extends ClassDef> classDefs, String className, String methodName){
    	for (final ClassDef classDef: classDefs) {
    		List<String> interfaces = Lists.newArrayList(classDef.getInterfaces());
            Collections.sort(interfaces);
            if (interfaces.size() != 0) {
            	for (String interfaceName: interfaces) {
            		if (interfaceName.equals(className)) {
            			for (final ClassDef classDefImpl: classDefs) {
            				if (interfaceName.equals(classDefImpl.getType())){
            				   if (lookInDirectMethods(classDefImpl, methodName)) return true;
            				   if (lookInVirtualMethods(classDefImpl, methodName)) return true;
            				}
            			}
            		}
            	}
            }
            else continue;
    	}
    	return false;
    }
    
    private static boolean findMissedSuperMethod(List<? extends ClassDef> classDefs, ClassDef classDef, String methodName){
    	String superClassName = classDef.getSuperclass();
    	if (superClassName != null)
    	{
    		for (final ClassDef superClassDef: classDefs) {
    			if (superClassName.equals(superClassDef.getType())){
    				if (lookInDirectMethods(superClassDef, methodName)) return true;
    				if (lookInVirtualMethods(superClassDef, methodName)) return true;
    				return findMissedSuperMethod(classDefs, superClassDef, methodName);
    			}
    		}
    	}
    	return false;
    }

    
    public int getNumArg(final int c, final int m, final List<? extends ClassDef> classDefs, final IndStr indStr){
    	int numArg = 0;
    	String superClassName;
		Iterable<? extends Method> directMethods;
        Iterable<? extends Method> virtualMethods;
    	for (final ClassDef classDef: classDefs) {
    		if (c != indStr.get(classDef.getType(), 'c')) continue;
            if (classDef instanceof DexBackedClassDef) {
                directMethods = ((DexBackedClassDef)classDef).getDirectMethods(false);
            } else {
                directMethods = classDef.getDirectMethods();
            }
            for (Method method: directMethods) {
            	if (m == indStr.get(Utils.getShortReferenceString(method), 'm')){
            		if (method.getParameters().size() != 0)
            			return method.getParameters().size() - 1;
            		else{
            			superClassName = classDef.getSuperclass();
            	    	if (superClassName != null){
            	    		return getNumArg(indStr.get(superClassName, 'c'), m, classDefs, indStr);
            	    	}
            		}
            	}
            }
        	if (classDef instanceof DexBackedClassDef) {
        		virtualMethods = ((DexBackedClassDef)classDef).getVirtualMethods(false);
        		} else {
        		virtualMethods = classDef.getVirtualMethods();
        		}

        	for (Method method: virtualMethods) {
        		if (m == indStr.get(Utils.getShortReferenceString(method), 'm')) 
        		{
        			if (method.getParameters().size() != 0)
        				return method.getParameters().size() - 1;
        			else{
        				superClassName = classDef.getSuperclass();
            	    	if (superClassName != null){
            	    		return getNumArg(indStr.get(superClassName, 'c'), m, classDefs, indStr);
            	    	}
        			}
        		}
        	}
    	}
    	return numArg;
    }
    
   
    
    public Map<Integer, Boolean> getClassFields(final List<? extends ClassDef> classDefs, final IndStr indStr, final String className, final int instanceNum){
    	Map<Integer, Boolean> result = Collections.synchronizedMap(new HashMap <Integer, Boolean>());
    	boolean found = false;
    	boolean prim;
    	for (final ClassDef classDef: classDefs) {
    		if (classDef.getType().equals(className)){
    			found = true;
    			Iterable<? extends Field> instanceFields;
    	        if (classDef instanceof DexBackedClassDef) 
    	            instanceFields = ((DexBackedClassDef)classDef).getInstanceFields(false);
    	        else 
    	            instanceFields = classDef.getInstanceFields();
    	        for (Field field: instanceFields) {
    	        	prim = false;
    	        	switch (field.getType()){
    	        		case "Z": case "B": case "S": case "C": case "I": case "J": case "F": case "D": 
    	        			prim = true;
    	        	}
    	        	result.put(indStr.get(Utils.getShortReferenceString(field), 'f'), prim);
    	        }
    	    }
        }
    	if (!found){
    		String javaName = Utils.toStandardJavaClassName(className);
    		try {
    		Class<?> c = Class.forName(javaName);
    		
    		java.lang.reflect.Field[] fields = c.getFields();
    		
    			if (fields.length != 0)
    				for (java.lang.reflect.Field f: fields){
    					result.put(indStr.get(className + "->" + f.getName() + ':' + Utils.toDalvikType(f.getType().toString()), 'f'), f.getType().isPrimitive());
    				}
    		}
    		
    		catch (Exception e) {
				return null;
			}
    		catch(Error e){
    			return null;
    		} 
    		
    	}
    	if (result.isEmpty()) return null;
    	return result;
    }
    
    private void addVar(String var, final Gen gen){
		if (var.equals((String) "true") || var.equals((String) "false")) return;
		char firstLetter = var.charAt(0);
		switch (firstLetter){
			case 'l': case 'b': gen.addVar("(declare-var " + var + " Bool)"); break;
			case 'v': gen.addVar("(declare-var " + var + " bv64)"); break;
		}		
	}
    
    private void rPredDef(final String c, final String m, final int pc, final int size, final Gen gen){
    	String v = "", l = "", b = "";
    	for (int i = 0; i <= size; i++){
    		if (!v.isEmpty()) v = v + ' ' + "bv64";
    		else v = "bv64";
    		if (!l.isEmpty()) l = l + ' ' + "Bool";
    		else l = "Bool";
    		if (!b.isEmpty()) b = b + ' ' + "Bool";
    		else b = "Bool";
    	}
    	gen.addDef("(declare-rel R_" + c + '_' + m + '_' + Integer.toString(pc) + '(' + v + ' ' + l + ' ' + b + ") interval_relation bound_relation)");
    }
    
    public String rPred(final String c, final String m, final int pc, final Map<Integer, String> rUp, final Map<Integer, String> rUpL, final Map<Integer, String> rUpB, final int numArg, final int numReg, final Gen gen){
    	rPredDef(c, m , pc, numArg + numReg, gen);
    	String ret = "(R" + '_' + c + '_' + m + '_' + Integer.toString(pc) + ' ';
    	String v = "", l = "", b = "", var;
    	for (int i = 0; i <= (numArg + numReg); i++){
    		var = rUp.get(i);
			if (var == null) var = 'v' + Integer.toString(i);	
			if (!v.isEmpty()) v = v + ' ' + var;
			else v = var;
			addVar(var, gen);
			var = rUpL.get(i);
			if (var == null) var = 'l' + Integer.toString(i);	
			if (!l.isEmpty()) l = l + ' ' + var;
			else l = var;
			addVar(var, gen);
			var = rUpB.get(i);
			if (var == null) var = 'b' + Integer.toString(i);	
			if (!l.isEmpty()) b = b + ' ' + var;
			else b = var;
			addVar(var, gen);
    	}
    	return ret + v + ' ' + l + ' ' + b + ')';
    }
    
    public String rInvokePred(final String c, final String m, final int pc, final Map<Integer, String> rUp, final Map<Integer, String> rUpL, final Map<Integer, String> rUpB, final int numArg, final int numReg, final Gen gen,
    		final int size){
    	rPredDef(c, m , pc, numArg + numReg, gen);
    	String ret = "(R" + '_' + c + '_' + m + '_' + Integer.toString(pc) + ' ';
    	String v = "", l = "", b = "", var;
    	for (int i = 0; i <= (numArg + numReg); i++){
    		var = rUp.get(i);
			if (var == null) var = "(_ bv0 "+ Integer.toString(size) + ")";	
			if (!v.isEmpty()) v = v + ' ' + var;
			else v = var;
			//addVar(var, gen);
			var = rUpL.get(i);
			if (var == null) var = "false";	
			if (!l.isEmpty()) l = l + ' ' + var;
			else l = var;
			//addVar(var, gen);
			var = rUpB.get(i);
			if (var == null) var = "false";	
			if (!l.isEmpty()) b = b + ' ' + var;
			else b = var;
			//addVar(var, gen);
    	}
    	return ret + v + ' ' + l + ' ' + b + ')';
    }
    
    private void resPredDef(final String c, final String m, final int size, final Gen gen){
    	String v = "", l = "", b = "";
    	for (int i = 0; i <= size; i++){
    		if (!v.isEmpty()) v = v + ' ' + "bv64";
    		else v = "bv64";
    		if (!l.isEmpty()) l = l + ' ' + "Bool";
    		else l = "Bool";
    		if (!b.isEmpty()) b = b + ' ' + "Bool";
    		else b = "Bool";
    	}
    	gen.addDef("(declare-rel RES_" + c + '_' + m + ' ' + '(' + v + ' ' + l + ' ' + b + ") interval_relation bound_relation)");
    }
    
    public String resPred(final String c, final String m, final Map<Integer, String> rUp, final Map<Integer, String> rUpL, final Map<Integer, String> rUpB, final int numArg, final Gen gen){
    	resPredDef(c, m , numArg, gen);
    	String ret = "(RES" + '_' + c + '_' + m + ' ';
    	String v = "", l = "", b = "", var;
    	for (int i = 0; i <= numArg; i++){
    		var = rUp.get(i);
			if (var == null) var = 'v' + Integer.toString(i);	
			if (!v.isEmpty()) v = v + ' ' + var;
			else v = var;
			addVar(var, gen);
			var = rUpL.get(i);
			if (var == null) var = 'l' + Integer.toString(i);	
			if (!l.isEmpty()) l = l + ' ' + var;
			else l = var;
			addVar(var, gen);
			var = rUpB.get(i);
			if (var == null) var = 'b' + Integer.toString(i);	
			if (!b.isEmpty()) b = b + ' ' + var;
			else b = var;
			addVar(var, gen);
    	}
    	return ret + v + ' ' + l + ' ' + b + ')';
    }
    
    public String hPred(final String cname, final String inst, final String element, final String value, final String label, final String block){
    	return ("(H " + cname + ' ' + inst + ' ' + element + ' ' + value + ' ' + label + ' ' + block + ')');
    }
    
    public String hiPred(final String cname, final String inst, final String value, final String label, final String block){
    	return ("(HI " + cname + ' ' + inst +  ' ' + value + ' ' + label + ' ' + block + ')');
    }
    
    public String iPred(final String cname, final String inst, final String value, final String label, final String block){
    	return ("(I " + cname + ' ' + inst + ' ' + value + ' ' + label + ' ' + block + ')');
    }
    
    public static void addSourceSink(final String originalClassName, final List<? extends ClassDef> classDefs, final String className, final String methodName, final IndStr indStr, final Set<SourceSinkMethod> sourcesSinks, final Gen gen)
    		{
    	
    	
    	final int originalClassIndex = indStr.get(originalClassName, 'c');
    	final int classIndex = indStr.get(className, 'c');
		final int methodIndex = indStr.get(methodName, 'm');
		final String classNameFormat = className.substring(1, className.length()-1);
		final String methodNameFormat = methodName.substring(0, methodName.indexOf('('));
		
    	for (SourceSinkMethod sourceSink: sourcesSinks){
    		
    		if (classNameFormat.equals(sourceSink.className)){
    			
    			if (methodNameFormat.equals(sourceSink.name)){
    				if (sourceSink.source)
    					gen.putSource(originalClassIndex, methodIndex);
    				else
    					gen.putSink(originalClassIndex, methodIndex);
    				break;
    			}
    		}	
    	}
    	
    	for (final ClassDef classDef: classDefs){
			if (classIndex == indStr.get(classDef.getType(), 'c')){
				if (classDef.getSuperclass()!= null){
					addSourceSink(originalClassName, classDefs, classDef.getSuperclass(), methodName, indStr, sourcesSinks, gen);
					break;
				}
			}
		}
    	//gen.putSink(indStr.get("Ljava/lang/ProcessBuilder;", 'c'), indStr.get("command([Ljava/lang/String;)Ljava/lang/ProcessBuilder;", 'm'));
    }
    
    public void formGen(List<? extends ClassDef> classDefs, IndStr indStr, String outputDirectory, Set<SourceSinkMethod> sourcesSinks, Gen gen) throws IOException{ 
        String className, methodName;
        boolean found;
        Iterator<Pair> it = this.refClassMethod.iterator();
    	while (it.hasNext()){
    		found = false;
    		Pair p = it.next();
    		className = p.className;
    		methodName = p.item;
    		addSourceSink(className, classDefs, className, methodName, indStr, sourcesSinks, gen);
      		for (final ClassDef classDef: classDefs) {
    		  if (found) break;
    		  	if (className.equals(classDef.getType())) {
    		  		found = lookInDirectMethods(classDef, methodName);
    		  		if ((Utils.isThread(classDefs, classDef, indStr)) && (indStr.get(methodName, 'm') == indStr.get("execute([Ljava/lang/Object;)Landroid/os/AsyncTask;", 'm'))){
    		  			methodName = "doInBackground([Ljava/lang/Object;)Ljava/lang/Object;";
    		  		}
    		  		if ((Utils.isThread(classDefs, classDef, indStr)) && (indStr.get(methodName, 'm') == indStr.get("start()V", 'm'))){
    		  			methodName = "run()V";
    		  		}
    		        if (!found) found = lookInVirtualMethods(classDef, methodName);
    		        //look in the interface implementations
    		        if ((!found) && classDef.getClass().isInterface()){
    		        	found = findMissedInterfaceMethod(classDefs, className, methodName);
    		        }
    		        if (!found) {
    		        		found = findMissedSuperMethod(classDefs, classDef, methodName);
    		        }
    		  	}
    		}
    		if (found) 
    			gen.putDefined(indStr.get(className, 'c'), indStr.get(methodName, 'm'));
    	}
    }
}
