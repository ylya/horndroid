package analysis;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import horndroid.options;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
//import java.util.concurrent.Executors;

import org.jf.baksmali.Adaptors.ClassDefinition;
import org.jf.baksmali.Adaptors.MethodDefinition;
import org.jf.baksmali.Adaptors.MethodDefinition.InvalidSwitchPayload;
import org.jf.dexlib2.AccessFlags;
import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.dexbacked.DexBackedClassDef;
import org.jf.dexlib2.iface.ClassDef;
import org.jf.dexlib2.iface.Field;
import org.jf.dexlib2.iface.Method;
import org.jf.dexlib2.iface.MethodImplementation;
import org.jf.dexlib2.iface.MethodParameter;
import org.jf.dexlib2.iface.instruction.FiveRegisterInstruction;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.OneRegisterInstruction;
import org.jf.dexlib2.iface.instruction.ReferenceInstruction;
import org.jf.dexlib2.iface.instruction.SwitchElement;
import org.jf.dexlib2.iface.instruction.formats.ArrayPayload;
import org.jf.dexlib2.iface.instruction.formats.Instruction31t;
import org.jf.dexlib2.iface.instruction.formats.PackedSwitchPayload;
import org.jf.dexlib2.iface.instruction.formats.SparseSwitchPayload;
import org.jf.dexlib2.iface.reference.FieldReference;
import org.jf.dexlib2.iface.reference.MethodReference;
import org.jf.dexlib2.iface.reference.Reference;
import org.jf.dexlib2.iface.value.EncodedValue;
import org.jf.dexlib2.util.ReferenceUtil;
import org.jf.dexlib2.util.TypeUtils;
import org.jf.util.ExceptionWithContext;

import com.google.common.collect.ImmutableList;

import payload.ArrayData;
import payload.PackedSwitch;
import payload.SparseSwitch;
import strings.ConstString;
import util.*;
import z3.Z3Engine;
import z3.Z3Variable;

public class Analysis {
	final private Set<GeneralClass> classes;
	final private Set<DalvikInstance> instances;
	final private Set<Integer> disabledActivities;
	final private Set<Integer> activities;
    final private Set<Integer> applications;
	final private Set<Integer> launcherActivities;
	final private Set<ConstString> constStrings;
    final private Set<Integer> callbackImplementations;
    final private Set<String> callbacks;
    final private Set<ArrayData> arrayDataPayload;
    final private Set<PackedSwitch> packedSwitchPayload;
    final private Set<SparseSwitch> sparseSwitchPayload;
    final private Set<Integer> overapprox;
    final private Set<SourceSinkMethod> sourcesSinks;
    final private options options;
//    final private Gen gen;
    final private Z3Engine z3engine;
    final private Z3Variable var;
    final ExecutorService instructionExecutorService;
    private final Set<CMPair> refSources;
    private final Set<CMPair> refSinks;

	public Analysis(final Z3Engine z3engine, final Set<SourceSinkMethod> sourcesSinks, final options options, final ExecutorService instructionExecutorService){
		this.classes = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<GeneralClass, Boolean>()));
		this.instances = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<DalvikInstance, Boolean>()));
		this.disabledActivities = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <Integer, Boolean>()));
		this.activities = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <Integer, Boolean>()));
		this.applications = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <Integer, Boolean>()));
		this.launcherActivities = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <Integer, Boolean>()));
		this.constStrings = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <ConstString, Boolean>()));
		this.callbackImplementations = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <Integer, Boolean>()));
		this.callbacks = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <String, Boolean>()));
		this.arrayDataPayload = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <ArrayData, Boolean>()));
		this.packedSwitchPayload = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <PackedSwitch, Boolean>()));
		this.sparseSwitchPayload = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <SparseSwitch, Boolean>()));
		this.overapprox = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <Integer, Boolean>()));
		this.instructionExecutorService = instructionExecutorService;
		this.sourcesSinks = sourcesSinks;
        //HERE
//		this.gen = gen;
        this.z3engine = z3engine;
        this.var = z3engine.getVars();
		this.options = options;
		
		
		this.refSources = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <CMPair, Boolean>()));
		this.refSinks = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <CMPair, Boolean>()));
		
		this.overapprox.add("Landroid/content/ContentProvider;".hashCode());
		this.overapprox.add("Landroid/app/Service;".hashCode());
		this.overapprox.add("Landroid/content/BroadcastReceiver;".hashCode());
		this.overapprox.add("Landroid/app/Fragment;".hashCode());
		this.overapprox.add("Landroid/support/v4/app/FragmentActivity;".hashCode());
		this.overapprox.add("Landroid/support/v4/app/Fragment;".hashCode());
	    this.overapprox.add("Landroid/app/ListFragment;".hashCode());
	    this.overapprox.add("Landroid/support/v4/app/ListFragment;".hashCode());
	    this.overapprox.add("Landroid/os/Handler;".hashCode());
	}
	public  Set<Integer> getDisabledActivities(){
		return disabledActivities;
	}
	public  Set<Integer> getActivities(){
		return activities;
	}
	public  Set<Integer> getApplications(){
		return applications;
	}
	public  Set<String> getCallbacks(){
		return callbacks;
	}
	public  Set<Integer> getCallbackImplementations(){
		return callbackImplementations;
	}
	public  Set<Integer> getLauncherActivities(){
		return launcherActivities;
	}
//	public Gen getGen(){
//		return gen;
//	}
    public Z3Engine getZ3Engine(){
    return z3engine;
}
	public int getSize(){
		return options.bitvectorSize;
	}
	public boolean optionArrays(){
		return options.arrays;
	}
	public boolean optionVerbose(){
		return options.verboseResults;
	}
	public Set<ArrayData> getArrayData(){
		return arrayDataPayload;
	}
	public Set<PackedSwitch> getPackedSwitch(){
		return packedSwitchPayload;
	}
	public Set<SparseSwitch> getSparseSwitch(){
		return sparseSwitchPayload;
	}
	public Integer staticFieldsLookup(final GeneralClass ci, final int fi){
		if (ci instanceof DalvikClass){
		final DalvikClass dc = (DalvikClass) ci;
		for (final DalvikField f: dc.getFields()){
			if (f.getName().hashCode() == fi)
				return ci.getType().hashCode();
		}
		return staticFieldsLookup(dc.getSuperClass(), fi);
		}
		else return null;
	}
	public Integer staticFieldsLookup(final int ci, final int fi){
		for (final GeneralClass c: classes){
			if ((c instanceof DalvikClass) && (c.getType().hashCode() == ci)){
				final DalvikClass dc = (DalvikClass) c;
				for (final DalvikField f: dc.getFields()){
					if (f.getName().hashCode() == fi)
						return ci;
				}
				return staticFieldsLookup(dc.getSuperClass(), fi);
			}
		}
		return null;
	}
	public DalvikMethod getExactMethod(final int ci, final int mi){
		for (final GeneralClass c: classes){
			if ((c instanceof DalvikClass) && c.getType().hashCode() == ci){
				for (final DalvikMethod m: ((DalvikClass) c).getMethods()){
					if (m.getName().hashCode() == mi){
						return m;
					}
				}
			}
		}
		return null;
	}
	public Map<Integer, Boolean> getClassFields(final String className, final int instanceNum){
    	Map<Integer, Boolean> result = Collections.synchronizedMap(new HashMap <Integer, Boolean>());
    	boolean found = false;
    	boolean prim;
    	for (final GeneralClass c: classes) {
    		if ((c.getType().hashCode() == className.hashCode()) && (c instanceof DalvikClass)){
    			final DalvikClass dc = (DalvikClass) c;
    			found = true;
    	        for (DalvikField field: dc.getFields()) {
    	        	prim = false;
    	        	final String fieldName = field.getName();
    	        	switch (fieldName){
    	        		case "Z": case "B": case "S": case "C": case "I": case "J": case "F": case "D": 
    	        			prim = true;
    	        	}
    	        	result.put(fieldName.hashCode(), prim);
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
    					result.put((className + "->" + f.getName() + ':' + Utils.toDalvikType(f.getType().toString())).hashCode(), f.getType().isPrimitive());
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
	public Integer getInstNum(final int c, final int m, final int pc){
		for (final DalvikInstance instance: instances)
	    	if ((instance.getC() == c) && (instance.getM() == m) && (instance.getPC() == pc)) 
	    		return instance.hashCode();
		return null;
	}
	private void addToMain(final DalvikClass dc, final int methodIndex, final int numRegCall, final int regCount){
		final int classIndex = dc.getType().hashCode();
		Map<Integer, BitVecExpr> regUpdate = new HashMap<>();
        Map<Integer, BoolExpr> regUpdateL = new HashMap<>();
        Map<Integer, BoolExpr> regUpdateB = new HashMap<>();
		for (int i = 0; i<= numRegCall + regCount; i++){
			regUpdateL.put(i, z3engine.mkFalse());
		}

        BoolExpr b1 = z3engine.rPred(Integer.toString(classIndex), Integer.toString(methodIndex),
                0, regUpdate, regUpdateL, regUpdateB, regCount, numRegCall);
        z3engine.addRule(b1, dc.toString() + methodIndex + "zz");
	}
	private void addToMainHeap(final DalvikClass dc, final int methodIndex, final int numRegCall, final int regCount){
		final int classIndex = dc.getType().hashCode();
        Map<Integer, BitVecExpr> regUpdate = new HashMap<>();
        Map<Integer, BoolExpr> regUpdateL = new HashMap<>();
        Map<Integer, BoolExpr> regUpdateB = new HashMap<>();
        for (int i = 0; i<= numRegCall + regCount; i++){
			regUpdateL.put(i, z3engine.mkFalse());
		}

        BoolExpr b1 = z3engine.rPred(Integer.toString(classIndex), Integer.toString(methodIndex),
                0, regUpdate, regUpdateL, regUpdateB, regCount, numRegCall);
        z3engine.addRule(b1, null);

        BoolExpr b2 = z3engine.hPred( z3engine.mkBitVector(classIndex, options.bitvectorSize),
                                      var.getFpp(), var.getF(), var.getVal(),
                                      z3engine.mkFalse(), z3engine.mkTrue());
        z3engine.addRule(b2, null);
	}
	

	public void processClass(final DalvikClass dc, final boolean isDisabledActivity, final boolean isCallbackImplementation,
			final boolean isLauncherActivity, final boolean isApplication, final boolean isOverApprox){
			for (final DalvikMethod m: dc.getMethods()){
				boolean isCallback = false;
				for (final String callback: callbacks){
		    		if (m.getName().contains(callback)){
		    			isCallback = true;
		    		}
				}
				final boolean isEntryPoint = testEntryPoint(dc, m.getName().hashCode());
				if (isCallbackImplementation){
					addToMain(dc, m.getName().hashCode(), m.getNumReg(), m.getNumArg());
				}

				if (isEntryPoint){
                    Map<Integer, BitVecExpr> regUpdate = new HashMap<>();
                    Map<Integer, BoolExpr> regUpdateL = new HashMap<>();
                    Map<Integer, BoolExpr> regUpdateB = new HashMap<>();
                    final int numRegCall = m.getNumReg();
		            final int regCount = m.getNumArg();
		    		int i;
		    		for (i = 0; i<= numRegCall + regCount; i++){
						regUpdateL.put(i, z3engine.mkFalse());
					}

                    BoolExpr b1 = z3engine.iPred(var.getCn(),
                                                 z3engine.mkBitVector(dc.getType().hashCode(), options.bitvectorSize),
                                                var.getVal(), var.getLf(), var.getBf());

                    BoolExpr b2 = z3engine.rPred(Integer.toString(dc.getType().hashCode()),
                            Integer.toString(m.getName().hashCode()),
                            0, regUpdate, regUpdateL, regUpdateB, regCount, numRegCall);

                    BoolExpr b1tob2 = z3engine.implies(b1, b2);

                    z3engine.addRule(b1tob2, null);


//		    		gen.addMain("(rule (=> " + Utils.iPred(
//						"cn", Utils.hexDec64(dc.getType().hashCode(), options.bitvectorSize), "val", "lf", "bf") + ' ' +
//				         		Utils.rPred(Integer.toString(dc.getType().hashCode()), Integer.toString(m.getName().hashCode()),
//							0, regUpdate, regUpdateL, regUpdateB, regCount, numRegCall, gen)
//				         		+ "))", dc.getType().hashCode());
				}

				if (!isDisabledActivity && isEntryPoint && (isLauncherActivity || isApplication || isOverApprox)){
                    addToMainHeap(dc, m.getName().hashCode(), m.getNumReg(), m.getNumArg());
				}

				if (isCallback){
					addToMain(dc, m.getName().hashCode(), m.getNumReg(), m.getNumArg());
				}

				int codeAddress = 0;
		        for (final Instruction instruction: m.getInstructions()){
		        	InstructionAnalysis ia = new InstructionAnalysis(this, instruction, dc, m, codeAddress);
		        	ia.CreateHornClauses();
		        	codeAddress += instruction.getCodeUnits();
		        }
			}
	}
	private String makeName(final GeneralClass c){
		final String formatClassName = c.getType().replaceAll("\\.", "/").substring(1, c.getType().replaceAll("\\.", "/").length() -1);
        final String[] parts = formatClassName.split("/");
		final String classN =  parts[parts.length - 1];
		return classN;
	}
	private boolean testOverapprox(final GeneralClass c){
		if (overapprox.contains(c.getType().hashCode())){
			return true;
		}
		else{
			if (c instanceof DalvikClass){
				final DalvikClass dc = (DalvikClass) c;
				boolean launcherChild = false;
				for (final DalvikClass childClass: dc.getChildClasses()){
					if (overapprox.contains(childClass.getType().hashCode())){
						launcherChild = true;
					}
				}
				if (launcherChild) return true;
				else 
					return testOverapprox(dc.getSuperClass());
			}
		}
		return false;
	}
	private boolean testLauncherActivity(final GeneralClass c){
		if (launcherActivities.contains(makeName(c).hashCode())){
			return true;
		}
		else{
			if (c instanceof DalvikClass){
				final DalvikClass dc = (DalvikClass) c;
				boolean launcherChild = false;
				for (final DalvikClass childClass: dc.getChildClasses()){
					if (launcherActivities.contains(makeName(childClass).hashCode())){
						launcherChild = true;
					}
				}
				if (launcherChild) return true;
				else 
					return testLauncherActivity(dc.getSuperClass());
			}
		}
		return false;
	}
	private boolean testDisabledActivity(final GeneralClass c){
		if (disabledActivities.contains(makeName(c).hashCode())){
			return true;
		}
		return false;
	}
	private boolean testApplication(final GeneralClass c){
		if (applications.contains(makeName(c).hashCode())){
			return true;
		}
		else{
			if (c instanceof DalvikClass){
				final DalvikClass dc = (DalvikClass) c;
				boolean launcherChild = false;
				for (final DalvikClass childClass: dc.getChildClasses()){
					if (applications.contains(makeName(childClass).hashCode())){
						launcherChild = true;
					}
				}
				if (launcherChild) return true;
				else 
					return testApplication(dc.getSuperClass());
			}
		}
		return false;
	}
	public void createHornClauses(){
		for (final GeneralClass c: classes){
			if ((c instanceof DalvikClass) && (!c.getType().contains("Landroid"))){
				final DalvikClass dc = (DalvikClass) c;

				final boolean isDisabledActivity = testDisabledActivity(dc);
				final boolean isLauncherActivity = testLauncherActivity(dc);
				final boolean isApplication = testApplication(dc);
				final boolean isOverapprox = testOverapprox(dc);
				boolean isCallbackImplementation = false;
				for (final GeneralClass interfaceC: dc.getInterfaces()){
					if (callbackImplementations.contains(interfaceC.getType().hashCode())){
						isCallbackImplementation = true;
					}
				}

				final boolean isci = isCallbackImplementation;
//				instructionExecutorService.submit(new Runnable() {
//		   			 @Override
//		   			 public void run() {
//		   				 try {
//		   					 processClass(dc, isDisabledActivity, isci, isLauncherActivity, isApplication, isOverapprox);
//		   				 } catch (Exception e1) {
//							e1.printStackTrace();
//		   				 }
//		   			 }
//		        });
                processClass(dc, isDisabledActivity, isci, isLauncherActivity, isApplication, isOverapprox);
            }
		}
	}
	private boolean testEntryPoint(final GeneralClass c, final int methodIndex){
		if (c instanceof DalvikClass){
			final DalvikClass dc = (DalvikClass) c;
			final GeneralClass superClass = dc.getSuperClass();
    		if (z3engine.isEntryPoint(superClass.getType().hashCode(), methodIndex)){
    			return true;
    		}
    		else{	
    			return testEntryPoint(superClass, methodIndex);
    		}
		}
    	return false;
		
    }
	private void addEntryPointsInstances(){
        for (final GeneralClass c: classes){
        	if (c instanceof DalvikClass){
        		final DalvikClass dc = (DalvikClass) c;
        		boolean execByDefault = false;
        		for (final DalvikMethod method: dc.getMethods()){
        			final int methodIndex = method.getName().hashCode();
        			if (!testDisabledActivity(dc) && testEntryPoint(dc, methodIndex)
              				 && (testLauncherActivity(dc) || testApplication(dc) || testOverapprox(dc))){
              			 execByDefault = true;
              			 break;
              		 }
        		}
        		
        		if (execByDefault){
    			instances.add(new DalvikInstance(0, 0, 0, dc, true));
        		}
        	}
        }
	}
	private void formClassStructure(){
		for (final GeneralClass c: classes){
			if (c instanceof DalvikClass){
				final DalvikClass cd = (DalvikClass) c;
				final int superClass = cd.getSuperClass().getType().hashCode();
				for (final GeneralClass cs: classes){
					if (cs instanceof DalvikClass){
						if (cs.getType().hashCode() == superClass){
							cd.putSuperClass(cs);
							((DalvikClass) cs).putChildClass(cd);
							break;
						}
					}
				}
				final Set<GeneralClass> interfaces = cd.getInterfaces();
				for (final GeneralClass ic: interfaces){
					final int interfaceClass = ic.getType().hashCode();
					for (final GeneralClass cs: classes){
						if (cs instanceof DalvikClass){
							if (cs.getType().hashCode() == interfaceClass){
								interfaces.remove(ic);
								interfaces.add(cs);
								cd.putInterfaces(interfaces);
								break;
							}
						}
					}
				}
				for (final DalvikInstance i: instances){
					final int type = i.getType().getType().hashCode();
					if (cd.getType().hashCode() == type){
								i.changeType(cd);
					}
				}
			}
		}
	}
	
	public Set<DalvikImplementation> getImplementations(final int ci, final int mi){
		final Set<DalvikImplementation> implementations = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<DalvikImplementation, Boolean>()));
		final Map<DalvikClass, DalvikMethod> definitions = isDefined(ci, mi);
		if (definitions == null) return null;
		for (Map.Entry<DalvikClass, DalvikMethod> entry : definitions.entrySet()){
			final DalvikImplementation di = new DalvikImplementation(entry.getKey(), entry.getValue());
			for (final DalvikInstance instance: instances){
				if (entry.getKey().getType().hashCode() == instance.getType().getType().hashCode()){
					di.putInstance(instance);
					for (final DalvikClass child: entry.getKey().getChildClasses()){
						for (final DalvikInstance childInstance: instances){
							if (child.getType().hashCode() == childInstance.getType().getType().hashCode()){
								di.putInstance(childInstance);
							}
						}
					}
				}
			}
			implementations.add(di);

		}
		return implementations;
	}
	
	public Map<DalvikClass, DalvikMethod> isDefined(final int ci, int mi){	
		Map<DalvikClass, DalvikMethod> resolvents = new ConcurrentHashMap<DalvikClass, DalvikMethod>();
		if (isThread(ci) && (mi == "execute([Ljava/lang/Object;)Landroid/os/AsyncTask;".hashCode())){
  			mi = "doInBackground([Ljava/lang/Object;)Ljava/lang/Object;".hashCode();
  		}
  		if (isThread(ci) && (mi == "start()V".hashCode())){
  			mi = "run()V".hashCode();
  		}
		for (final GeneralClass c: classes){
			if ((c instanceof DalvikClass)){
				final DalvikClass cd = ((DalvikClass) c);	
				if (c.getType().hashCode() == ci){
					for (final DalvikMethod m: cd.getMethods()){
						if (m.getName().hashCode() == mi){
							resolvents.put(cd, m);
							break;
						}
					}
					for (final DalvikClass sc: cd.getChildClasses()){
						if (sc != null){
							final Map<DalvikClass, DalvikMethod> resolventsChild = isDefined(sc.getType().hashCode(), mi);
							if (resolventsChild != null)
								resolvents.putAll(resolventsChild);
						}
					}
				}
				for (final GeneralClass cint: cd.getInterfaces()){
					if ((cint.getType().hashCode() == ci)){
						for (final DalvikMethod m: 
							cd.getMethods()){
							if (m.getName().hashCode() == mi){
								resolvents.put(cd, m);
								break;
							}
						}
					}
				}				
			}
		}
		if (resolvents.isEmpty()) return null;
		return resolvents;
	}
	
	public boolean isThread(final GeneralClass c){
		 if (c instanceof DalvikClass){
			 final DalvikClass dc = (DalvikClass) c;
			 final GeneralClass sc = dc.getSuperClass();
			 final int superClass = sc.getType().hashCode();
			 if ((superClass == "Ljava/lang/Thread;".hashCode()) || (superClass == "Landroid/os/AsyncTask;".hashCode())){
				 return true;
			 }
			 else{
				 return isThread(sc);
			 }
		 }
	     return false;
	    }
	public boolean isThread(final int classInd){
			for (final GeneralClass c : classes) {
	    		if ((c instanceof DalvikClass) && (c.getType().hashCode() == classInd)){
	    			final DalvikClass dc = (DalvikClass) c;
	    			final Set <GeneralClass> interfaces = dc.getInterfaces();
	    			
	    	        if (interfaces.size() != 0) {
	    	        	for (final GeneralClass interfaceName: interfaces){
	    	        		if (interfaceName.getType().hashCode() == "Ljava/lang/Runnable;".hashCode())
	    	        			return true;
	    	        	}
	    	        }
	    			return isThread(c);
	    		}			
	    	} 
	    	return false;
    }
	public void collectDataFromApk(final List<? extends ClassDef> classDefs) {
        for (final ClassDef classDef: classDefs) {
        	if (classDef.getType().contains("Landroid")) continue;
                classes.add(collectDataFromClass(classDefs, classDef));
        }
        formClassStructure();
        addEntryPointsInstances();
	}	    
    private DalvikClass collectDataFromClass(final List<? extends ClassDef> classDefs, final ClassDef classDef) {
    	final DalvikClass dc = new DalvikClass(classDef.getType());
    	dc.putSuperClass(new GeneralClass(classDef.getSuperclass()));
		final Set<GeneralClass> inter = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <GeneralClass, Boolean>()));
    	for (final String interfaceName: classDef.getInterfaces()){
    		inter.add(new GeneralClass(interfaceName));
    	}
    	dc.putInterfaces(inter);
    	
    	Set<DalvikField> dalvikFields = collectDataFromFields(classDef, false);
    	dalvikFields.addAll(collectDataFromFields(classDef, true));
    	dc.putFields(dalvikFields);
    	Set<DalvikMethod> dalvikMethods = collectDataFromMethods(classDefs, classDef, false); //direct
        dalvikMethods.addAll(collectDataFromMethods(classDefs, classDef, true)); //virtual
        dc.putMethods(dalvikMethods);
        return dc;
    }
    
    private Set<DalvikField> collectDataFromFields(final ClassDef classDef, final boolean dynamic){
    	final Set<DalvikField> dalvikFields = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <DalvikField, Boolean>()));
		Iterable<? extends Field> fields;
    	if (!dynamic){
    		if (classDef instanceof DexBackedClassDef) {
    			fields = ((DexBackedClassDef)classDef).getStaticFields(false);
    		} else {
    			fields = classDef.getStaticFields();
    		}
    	}
        else{
            if (classDef instanceof DexBackedClassDef) {
                fields = ((DexBackedClassDef)classDef).getInstanceFields(false);
            } else {
                fields = classDef.getInstanceFields();
            }
        }

        for (Field field: fields) {
        	EncodedValue initialValue = field.getInitialValue();
            if (initialValue != null) {
            	final String fieldName = ReferenceUtil.getShortFieldDescriptor(field);
            	final int classIndex = classDef.getType().hashCode();
//        		gen.addMain("(rule (S " + Utils.Dec(classIndex) + ' ' + Utils.Dec(fieldName.hashCode())+ " " + FormatEncodedValue.toString(initialValue, options.bitvectorSize) + " false bf))",
//        				classIndex);
                BoolExpr rule = z3engine.sPred( z3engine.mkInt(Utils.Dec(classIndex)),
                                             z3engine.mkInt(Utils.Dec(fieldName.hashCode())),
//                                             z3engine.mkBitVector(FormatEncodedValue.toString(initialValue, options.bitvectorSize), options.bitvectorSize),
                                            FormatEncodedValue.toBitVec(z3engine, initialValue, options.bitvectorSize),
                                            z3engine.mkFalse(), var.getBf());
                z3engine.addRule(rule, null);
        		
            	DalvikStaticField dsf = new DalvikStaticField(ReferenceUtil.getShortFieldDescriptor(field), FormatEncodedValue.toString(initialValue, options.bitvectorSize));
            		dalvikFields.add(dsf);
            	}
            else{
            		final String fieldName = ReferenceUtil.getShortFieldDescriptor(field);            		
            		dalvikFields.add(new DalvikField(fieldName));
            	}
        }
        return dalvikFields;
    }
    
    private Set<DalvikMethod> collectDataFromMethods(final List<? extends ClassDef> classDefs, final ClassDef classDef, final boolean virtual) {
		 final Set<DalvikMethod> dalvikMethods = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <DalvikMethod, Boolean>()));
         Iterable<? extends Method> methods;
         if (!virtual){
        	 if (classDef instanceof DexBackedClassDef) {
        		 methods = ((DexBackedClassDef)classDef).getDirectMethods(false);
        	 } else {
        		 methods = classDef.getDirectMethods();
        	 }
         }
         else{
        	 if (classDef instanceof DexBackedClassDef) {
                 methods = ((DexBackedClassDef)classDef).getVirtualMethods(false);
             } else {
                 methods = classDef.getVirtualMethods();
             } 
         }
         for (Method method: methods) {
             String methodString = Utils.getShortMethodDescriptor(method);             
             String methodIndex  = Utils.Dec(methodString.hashCode());
             String classIndex  = Utils.Dec(classDef.getType().hashCode());
             MethodImplementation methodImpl = method.getImplementation();
             if (methodImpl == null) {
             } else {
                 dalvikMethods.add(collectDataFromMethod(classDefs, method, methodImpl, methodString, classIndex, methodIndex, classDef));
             }
         }
         return dalvikMethods;
    }
    private DalvikMethod collectDataFromMethod(final List<? extends ClassDef> classDefs, final Method method, final MethodImplementation methodImpl, 
    		final String methodString, final String classIndex, 
    		final String methodIndex,
    		final ClassDef classDef){
    	int parameterRegisterCount = 0;
        if (!AccessFlags.STATIC.isSet(method.getAccessFlags())) {
            parameterRegisterCount++;
        }
        //refClassElement.putMethod(method.getDefiningClass(), methodString);
            	
    	if (methodString.equals((String) "<clinit>()V")){
    		z3engine.putStaticConstructor(method.getDefiningClass().hashCode());
    	}
    	ImmutableList<MethodParameter> methodParameters = ImmutableList.copyOf(method.getParameters());
        for (MethodParameter parameter: methodParameters) {
            String type = parameter.getType();
            parameterRegisterCount++;
            if (TypeUtils.isWideType(type)) {
                parameterRegisterCount++;
            }
        }
        final boolean callReturns;
        final String returnType = method.getReturnType();
        if (returnType.equals((String) "V")) callReturns = false;
        	else callReturns = true;
        
        //numLoc.putp(Integer.parseInt(classIndex), Integer.parseInt(methodIndex), parameterRegisterCount);
        //numLoc.put(Integer.parseInt(classIndex), Integer.parseInt(methodIndex), methodImpl.getRegisterCount());
        Iterable<? extends Instruction> instructions = methodImpl.getInstructions();
        DalvikMethod dm = new DalvikMethod(methodString, parameterRegisterCount, methodImpl.getRegisterCount(), returnType, callReturns, ImmutableList.copyOf(instructions));
        int codeAddress = 0;
        for (Instruction instruction: instructions){
        	collect(classDefs, instruction, codeAddress, Integer.parseInt(classIndex), Integer.parseInt(methodIndex), classDef, method);
            codeAddress += instruction.getCodeUnits();
        }    
        return dm;
    }
    
    public Boolean isSourceSink(final List<? extends ClassDef> classDefs, final String className, final String methodName){
    	if (!refSources.isEmpty())
    		if (refSources.contains(new CMPair(className.hashCode(), methodName.hashCode())))
    				return true;
    	if (!refSinks.isEmpty())
    		if (refSinks.contains(new CMPair(className.hashCode(), methodName.hashCode())))
    				return false;
    	final int classIndex = className.hashCode();
    	final String classNameFormat = className.substring(1, className.length()-1);
    	final String methodNameFormat = methodName.substring(0, methodName.indexOf('('));
    	for (SourceSinkMethod sourceSink: sourcesSinks){
    		if (classNameFormat.hashCode() == sourceSink.className.hashCode()){		
    			if (methodNameFormat.hashCode() == sourceSink.name.hashCode()){
    				if (sourceSink.source)
    					return true;
    				else
    					return false;
    			}
    		}	
    	}
    	for (final ClassDef classDef: classDefs){
    		if (classIndex == classDef.getType().hashCode()){
    			for (final String interfaceName: classDef.getInterfaces()){
    				final String interfaceNameFormat = interfaceName.substring(1, interfaceName.length()-1);
    				for (SourceSinkMethod sourceSink: sourcesSinks){
    		    		if (interfaceNameFormat.hashCode() == sourceSink.className.hashCode()){		
    		    			if (methodNameFormat.hashCode() == sourceSink.name.hashCode()){
    		    				if (sourceSink.source)
    		    					return true;
    		    				else
    		    					return false;
    		    			}
    		    		}	
    		    	}
    			}
    		}
    	}
    	for (final ClassDef classDef: classDefs){
    		if (classIndex == classDef.getType().hashCode()){
    			if (classDef.getSuperclass()!= null){
    				return isSourceSink(classDefs, classDef.getSuperclass(), methodName);
    			}
    		}
    	}
    	return null;
}
    
    public boolean isSource(final int c, final int m){
    	return refSources.contains(new CMPair(c,m));
    }
    
    public boolean isSink(final int c, final int m){
    	return refSinks.contains(new CMPair(c,m));
    }
    
    
    private void collect(final List<? extends ClassDef> classDefs, final Instruction instruction, final int codeAddress, final int c, final int m, 
    		final ClassDef classDef, final Method method){
        String referenceString = null;
    	String referenceStringClass = null;
    	int referenceClassIndex = -1;
    	int referenceIntIndex = -1;
        String returnType = null;
    	//int nextCode;
		if (instruction instanceof ReferenceInstruction) {
			ReferenceInstruction referenceInstruction = (ReferenceInstruction)instruction;
			Reference reference = referenceInstruction.getReference();
	        referenceString = Utils.getShortReferenceString(reference);
	        if (reference instanceof FieldReference) {
	        	referenceStringClass = ((FieldReference) reference).getDefiningClass();
	        	referenceClassIndex = referenceStringClass.hashCode();
	        }
	        else 
	        	if (reference instanceof MethodReference){
	        		referenceStringClass = ((MethodReference) reference).getDefiningClass();
	        		referenceClassIndex = referenceStringClass.hashCode();
	        		returnType = ((MethodReference) reference).getReturnType();
	            }
	        referenceIntIndex = referenceString.hashCode();
	        assert referenceString != null;
		 }
		
		if (instruction instanceof Instruction31t) {
            try {
        	ClassDefinition clD = new ClassDefinition(null, classDef);
        	MethodDefinition methodDef = new MethodDefinition(clD, method, method.getImplementation());
            Opcode payloadOpcode;
            final int payloadAddress = codeAddress + ((Instruction31t)instruction).getCodeOffset();
            switch (instruction.getOpcode()) {
                case PACKED_SWITCH:
                    payloadOpcode = Opcode.PACKED_SWITCH_PAYLOAD;
                    PackedSwitchPayload psInst = (PackedSwitchPayload) methodDef.findSwitchPayload(codeAddress + ((Instruction31t)instruction).getCodeOffset(),
                            payloadOpcode);
                    boolean first = true;
                    int firstKey = -1;
                    final int basePCodeAddress = methodDef.getPackedSwitchBaseAddress(payloadAddress);
                    final List<Number> targets = new ArrayList<Number>();
                    for (SwitchElement switchElement: psInst.getSwitchElements()) {
                        if (first) {
                            firstKey = switchElement.getKey();
                            first = false;
                        }
                        targets.add(basePCodeAddress + switchElement.getOffset());
                    }
                    packedSwitchPayload.add(new PackedSwitch(c, m, payloadAddress, targets, firstKey));
                    break;
                case SPARSE_SWITCH:
                    payloadOpcode = Opcode.SPARSE_SWITCH_PAYLOAD;
                    final int baseSCodeAddress = methodDef.getSparseSwitchBaseAddress(codeAddress);
                    SparseSwitchPayload ssInst = (SparseSwitchPayload) methodDef.findSwitchPayload(codeAddress + ((Instruction31t)instruction).getCodeOffset(),
                            payloadOpcode);
                    final Map<Integer, Integer> sTargets  = Collections.synchronizedMap(new HashMap <Integer, Integer>());
                    for (SwitchElement switchElement: ssInst.getSwitchElements()) {
                        sTargets.put(switchElement.getKey(), baseSCodeAddress + switchElement.getOffset());
                    }
                    sparseSwitchPayload.add(new SparseSwitch(c, m, payloadAddress, sTargets));
                    break;
                case FILL_ARRAY_DATA:
                    payloadOpcode = Opcode.ARRAY_PAYLOAD;
                    ArrayPayload apInst = (ArrayPayload) methodDef.findSwitchPayload(codeAddress + ((Instruction31t)instruction).getCodeOffset(),
                            payloadOpcode);
                    List<Number> elements = apInst.getArrayElements();
                    //for (Number number: elements) {
                    //	elements.add(number.longValue());
                    //}
                    arrayDataPayload.add(new ArrayData(c, m, payloadAddress, elements));
                    break;
                default:
                    throw new ExceptionWithContext("Invalid 31t opcode: %s", instruction.getOpcode());
            }
            } catch (InvalidSwitchPayload ex) {
            }
        }
		
        Opcode opcode = instruction.getOpcode();
		switch (instruction.getOpcode().format) {  
		case Format21c:
			if (opcode.name.equals((String)"const-string")){
				if (referenceString.contains(".")){
					final String[] parts = referenceString.split("\\.");
					final String classN = parts[parts.length -1].substring(0, parts[parts.length -1].length()-1);
					final String dalvikName = "L" + referenceString.substring(1, referenceString.length()-1).replaceAll("\\.", "/") + ";";
		    		constStrings.add(new ConstString(c, m, codeAddress, ((OneRegisterInstruction)instruction).getRegisterA(), classN.hashCode(), dalvikName));
				}
				break;
			}
        	if (opcode.name.equals((String)"new-instance"))
        		instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(referenceString), true));
        	break;
		 case Format22c:
         	if (opcode.name.equals((String) "new-array"))
         		instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(referenceString), false));
         	break;
		 case Format35c:
			 
			if (opcode.name.equals((String) "filled-new-array")){
				instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(referenceString), false));
	         		break;
			}
			
         	//int nextCode = codeAddress + instruction.getCodeUnits();
         	
         	//reflection
         	if  ((referenceClassIndex == "Ljava/lang/Class;".hashCode()) && 
        			("newInstance()Ljava/lang/Object;".hashCode() == referenceIntIndex)){
    			FiveRegisterInstruction instruction1 = (FiveRegisterInstruction)instruction;
    			for (final ConstString constString: constStrings){
    				if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction1.getRegisterC())){
    					instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(constString.getDalvikName()), true));
    					break;
    				}
    			}
            }
         	//
         	
         	if  ((referenceClassIndex == "Landroid/content/ComponentName;".hashCode()) && 
        			("<init>(Landroid/content/Context;Ljava/lang/String;)V".hashCode() == referenceIntIndex)){
    			FiveRegisterInstruction instruction1 = (FiveRegisterInstruction)instruction;
    			for (final ConstString constString: constStrings){
    				if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction1.getRegisterE())){
    					constString.putPC(codeAddress);
    					constString.putV(instruction1.getRegisterC());
    				}
    			}
            }
         	
         	if  ((referenceClassIndex == "Landroid/content/Intent;".hashCode()) && 
        			("setComponent(Landroid/content/ComponentName;)Landroid/content/Intent;".hashCode() == referenceIntIndex)){
    			FiveRegisterInstruction instruction1 = (FiveRegisterInstruction)instruction;
    			for (final ConstString constString: constStrings){
    				if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction1.getRegisterD())){
    					constString.putPC(codeAddress);
    					constString.putV(instruction1.getRegisterC());
    				}
    			}
            }
         
         	if  ("startActivity(Landroid/content/Intent;)V".hashCode() == referenceIntIndex){
    			FiveRegisterInstruction instruction1 = (FiveRegisterInstruction)instruction;
    			for (final ConstString constString: constStrings){
    				if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction1.getRegisterD())){
    					launcherActivities.add(constString.getVAL());
    				}
    			}
            }
         	
         	/*refClassElement.addCallRef(referenceClassIndex, referenceIntIndex, c, m, nextCode);
         	 * */
         	if (referenceStringClass != null){
         		final Boolean isSourceSink = isSourceSink(classDefs, referenceStringClass, referenceString);
         		if (isSourceSink != null){
         			if (isSourceSink)
         				refSources.add(new CMPair(referenceStringClass.hashCode(), referenceString.hashCode()));
         			else
         				refSinks.add(new CMPair(referenceStringClass.hashCode(), referenceString.hashCode()));
         		}
         		
         	}
             
             if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
             		&& (referenceIntIndex == "<init>(Landroid/content/Context;Ljava/lang/Class;)V".hashCode())){
            	 instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true));
             }
             
             if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
             		&& (referenceIntIndex == "<init>(Ljava/lang/String;)V".hashCode())){
            	 instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true));
             }
             
             if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
             		&& (referenceIntIndex == "<init>()V".hashCode())){
            	 instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true));
             }
             try{
             if (returnType.length() > 0){
             	if (returnType.contains("[")){
             		instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(returnType), false));
                 	break;
                 }
             	if (returnType.charAt(returnType.length() - 1) == ';'){
             		instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(returnType), true));
             		break;
             	}
             }
             }
             catch (NullPointerException e){
            	 System.err.println("While parsing instruction: " + instruction.toString());
             }
             break;
		 case Format3rc:
			 if (opcode.name.equals((String) "filled-new-array/range")){
				 instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(referenceString), false));
	         		break;
				}
			//nextCode = codeAddress + instruction.getCodeUnits();
			
         	/*refClassElement.addCallRef(referenceClassIndex, referenceIntIndex, c, m, nextCode);
         	*/
         	if (referenceStringClass != null){
             		final Boolean isSourceSink = isSourceSink(classDefs, referenceStringClass, referenceString);
             		if (isSourceSink != null){
             			if (isSourceSink)
             				refSources.add(new CMPair(referenceStringClass.hashCode(), referenceString.hashCode()));
             			else
             				refSinks.add(new CMPair(referenceStringClass.hashCode(), referenceString.hashCode()));
             		}
             		        		
         	}
             if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
             		&& (referenceIntIndex == "<init>(Landroid/content/Context;Ljava/lang/Class;)V".hashCode())){
            	 instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true));
             }
             
             if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
             		&& (referenceIntIndex == "<init>(Ljava/lang/String;)V".hashCode())){
            	 instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true));
             }
             
             if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
             		&& (referenceIntIndex == "<init>()V".hashCode())){
            	 instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true));
             }
             
             if (returnType.charAt(returnType.length() - 1) == ';'){
            	 instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(returnType), true));
             	break;
             }
             if (returnType.contains("["))
            	 instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(returnType), false));
             break;
		default:
			break;
		}
	}
}
