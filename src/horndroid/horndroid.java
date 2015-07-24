/*
 * [The "BSD licence"]
 * Copyright (c) 2015 Ilya Grishchenko
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package horndroid;

import gen.Gen;

import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ExecutorService;

import org.jf.dexlib2.AccessFlags;
import org.jf.dexlib2.dexbacked.DexBackedClassDef;
import org.jf.dexlib2.iface.ClassDef;
import org.jf.dexlib2.iface.DexFile;
import org.jf.dexlib2.iface.Field;
import org.jf.dexlib2.iface.Method;
import org.jf.dexlib2.iface.MethodImplementation;
import org.jf.dexlib2.iface.MethodParameter;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.value.EncodedValue;
import org.jf.dexlib2.util.ReferenceUtil;
import org.jf.dexlib2.util.TypeUtils;

import payload.ArrayData;
import payload.PackedSwitch;
import payload.SparseSwitch;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Ordering;

import strings.ConstString;
import util.FormatEncodedValue;
import util.InstructionDataCollector;
import util.NumLoc;
import util.RefClassElement;
import util.Utils;
import util.iface.IndStr;

public class horndroid {
	
	private static boolean isActivity(final List<? extends ClassDef> classDefs, ClassDef classDef, final IndStr indStr){
    	final String superClass = classDef.getSuperclass();
    	if (superClass != null){
    		if (indStr.get(superClass, 'c') == indStr.get("Landroid/app/Activity;", 'c')){
    			return true;
    		}
    		else{
    			for (final ClassDef classDef1: classDefs) {
    				if (indStr.get(classDef1.getType(), 'c') == indStr.get(superClass, 'c')){
    					return isActivity(classDefs, classDef1, indStr);
    					}			
    				}
    		}
    	}
    	return false;
    }
	
	public static void collectDataFromApk(final NumLoc numLoc, final RefClassElement refClassElement, 
		    final IndStr indStr, 
    		final DexFile dexFile, final options options, final Gen gen, final Set<Integer> activities, final Set<ConstString> constStrings, final Set<Integer> launcherActivities,
    		final Set<ArrayData> arrayDataPayload, final Set<PackedSwitch> packedSwitchPayload, 
			final Set<SparseSwitch> sparseSwitchPayload) {

        List<? extends ClassDef> classDefs = Ordering.natural().sortedCopy(dexFile.getClasses());
      
        for (final ClassDef classDef: classDefs) {
        	if (!classDef.getType().contains("Landroid"))
        		collectDataFromClass(numLoc, refClassElement, classDef, indStr, options, gen, constStrings, launcherActivities,
        				arrayDataPayload, packedSwitchPayload, 
        				sparseSwitchPayload);
        }
	}
	
	 
	    
    
    private static void collectDataFromClass(final NumLoc numLoc, 
    		final RefClassElement refClassElement, final ClassDef classDef, final IndStr indStr, 
                                            final options options, final Gen gen, final Set<ConstString> constStrings, final Set<Integer> launcherActivities,
                                            final Set<ArrayData> arrayDataPayload, final Set<PackedSwitch> packedSwitchPayload, 
                                			final Set<SparseSwitch> sparseSwitchPayload) {
        collectDataFromMethods(classDef, gen, false, indStr, refClassElement, numLoc, constStrings, launcherActivities,
        		arrayDataPayload, packedSwitchPayload, 
    			sparseSwitchPayload); //direct
        collectDataFromMethods(classDef, gen, true, indStr, refClassElement, numLoc, constStrings, launcherActivities,
        		arrayDataPayload, packedSwitchPayload, 
    			sparseSwitchPayload); //virtual
    }
    
    private static void collectDataFromMethods(final ClassDef classDef, final Gen gen, final boolean virtual, 
    		final IndStr indStr, final RefClassElement refClassElement, final NumLoc numLoc, final Set<ConstString> constStrings, final Set<Integer> launcherActivities,
    		final Set<ArrayData> arrayDataPayload, final Set<PackedSwitch> packedSwitchPayload, 
			final Set<SparseSwitch> sparseSwitchPayload) {
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
             String methodIndex  = Utils.Dec(indStr.get(methodString, 'm'));
             String classIndex  = Utils.Dec(indStr.get(classDef.getType(), 'c'));
             MethodImplementation methodImpl = method.getImplementation();
             if (methodImpl == null) {
             } else {
                 collectDataFromMethod(method, methodImpl, methodString, classIndex, methodIndex, refClassElement, indStr, gen, numLoc, constStrings, launcherActivities,
                		arrayDataPayload,  packedSwitchPayload, 
             			sparseSwitchPayload, classDef);
             }
         }
    }
    private static void collectDataFromMethod(final Method method, final MethodImplementation methodImpl, 
    		final String methodString, final String classIndex, 
    		final String methodIndex,
    		final RefClassElement refClassElement, final IndStr indStr, final Gen gen, final NumLoc numLoc, final Set<ConstString> constStrings, final Set<Integer> launcherActivities,
    		final Set<ArrayData> arrayDataPayload, final Set<PackedSwitch> packedSwitchPayload, 
			final Set<SparseSwitch> sparseSwitchPayload, ClassDef classDef){
    	
    	int parameterRegisterCount = 0;
        if (!AccessFlags.STATIC.isSet(method.getAccessFlags())) {
            parameterRegisterCount++;
        }
        refClassElement.putMethod(method.getDefiningClass(), methodString);
            	
    	if (methodString.equals((String) "<clinit>()V")){
    		gen.putStaticConstructor(indStr.get(method.getDefiningClass(), 'c')); 
    	}
    	ImmutableList<MethodParameter> methodParameters = ImmutableList.copyOf(method.getParameters());
        for (MethodParameter parameter: methodParameters) {
            String type = parameter.getType();
            parameterRegisterCount++;
            if (TypeUtils.isWideType(type)) {
                parameterRegisterCount++;
            }
        }
        numLoc.putp(Integer.parseInt(classIndex), Integer.parseInt(methodIndex), parameterRegisterCount);
        numLoc.put(Integer.parseInt(classIndex), Integer.parseInt(methodIndex), methodImpl.getRegisterCount());
        Iterable<? extends Instruction> instructions = methodImpl.getInstructions();
        int codeAddress = 0;
        for (Instruction instruction: instructions){
        	InstructionDataCollector idc = new InstructionDataCollector(codeAddress, Integer.parseInt(classIndex), 
        			Integer.parseInt(methodIndex), instruction);
        	idc.collect(indStr, refClassElement, ImmutableList.of(instructions), constStrings, launcherActivities,
        			classDef, method,
        			arrayDataPayload, packedSwitchPayload, 
        		    sparseSwitchPayload);
            codeAddress += instruction.getCodeUnits();
        }    
    }
    
    private static boolean parentActivity(final  List<? extends ClassDef> classDefs, final Set<Integer> activities, final int classIndex, final IndStr indStr){
    	for (final ClassDef classDef: classDefs) {
    		if (indStr.get(classDef.getSuperclass(), 'c') == classIndex)
    		{
    			final String[] parts = classDef.getType().split("/");
            	final String formatClassName = parts[parts.length -1].substring(0, parts[parts.length -1].length()-1);
            			
        		if (activities.contains(indStr.get(formatClassName, 'c'))){
        			return true;
        		}
    		}
    	}
    	return false;
    }
	
	public static void smtApkFile(final NumLoc numLoc, final RefClassElement refClassElement, final IndStr indStr, 
    		DexFile dexFile, final options options, final Gen gen,  final Set<String> callbacks,  final Set<Integer> disabledActivities, final Set<Integer> activities,  
    		final Set<Integer> launcherActivities, final Set<Integer> callbackImplementations, final Set<Integer> applications, final int size,
    		final Set<ArrayData> arrayDataPayload, final Set<PackedSwitch> packedSwitchPayload, 
			final Set<SparseSwitch> sparseSwitchPayload, final ExecutorService instructionExecutorService) throws Exception {
        final List<? extends ClassDef> classDefs = Ordering.natural().sortedCopy(dexFile.getClasses());
        for (final ClassDef classDef: classDefs) {
        	if (isActivity(classDefs, classDef, indStr)){
        		final String[] parts = classDef.getType().split("/");
            	final String formatClassName = parts[parts.length -1].substring(0, parts[parts.length -1].length()-1);
            			
        		if (activities.contains(indStr.get(formatClassName, 'c'))){
        			 if (!classDef.getType().contains("Landroid"))
        				 
        				 instructionExecutorService.submit(new Runnable() {
        		   			 @Override
        		   			 public void run() {
        		   				 try {
									smtClass(numLoc, refClassElement, classDef, indStr, options, gen, classDefs, callbacks, disabledActivities, activities, launcherActivities, callbackImplementations,
											 applications, size,
											 arrayDataPayload,  packedSwitchPayload, 
												sparseSwitchPayload, instructionExecutorService);
								} catch (Exception e1) {
									// TODO Auto-generated catch block
									e1.printStackTrace();
								}
        		   			 }
        		        	});
        				 
        				
        		}
        		else{
        			if (parentActivity(classDefs,  activities, indStr.get(classDef.getType(), 'c'),  indStr)){
        				if (!classDef.getType().contains("Landroid"))
        					instructionExecutorService.submit(new Runnable() {
           		   			 @Override
           		   			public void run() {
        					try {
								smtClass(numLoc, refClassElement, classDef, indStr, options, gen, classDefs, callbacks, disabledActivities, activities, launcherActivities, callbackImplementations,
										applications, size,
										arrayDataPayload, packedSwitchPayload, 
										sparseSwitchPayload, instructionExecutorService);
							} catch (Exception e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
           		   			 }
        					});
        			}
        			else{
        				if (!classDef.getType().contains("Landroid"))
        					System.out.println("\n(Warning) activity " + classDef.getType() + " is not declared in the manifest");
        			}
        		}
        	}
        	else{
        		if (!isActivity(classDefs, classDef, indStr)){
        			if (!classDef.getType().contains("Landroid")){
        				instructionExecutorService.submit(new Runnable() {
          		   			 @Override
          		   			public void run() {
                   	 try {
						smtClass(numLoc, refClassElement, classDef, indStr, options, gen, classDefs, callbacks, disabledActivities, activities, launcherActivities, callbackImplementations,
								 applications, size,
								arrayDataPayload, packedSwitchPayload, 
								sparseSwitchPayload, instructionExecutorService);
					} catch (Exception e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
          		   			 }
        				}); 
        			}
        		}
        		
        	}	
        }
	}

    private static void smtClass(final NumLoc numLoc, RefClassElement refClassElement, ClassDef classDef, IndStr indStr,
                                            options options, final Gen gen, final List<? extends ClassDef> classDefs,  final Set<String> callbacks,  final Set<Integer> disabledActivities,
                                            final Set<Integer> activities, final Set<Integer> launcherActivities, final Set<Integer> callbackImplementations,
                                            final Set<Integer> applications, final int size,
                                            final Set<ArrayData> arrayDataPayload, final Set<PackedSwitch> packedSwitchPayload, 
                                			final Set<SparseSwitch> sparseSwitchPayload, final ExecutorService instructionExecutorService) throws Exception {
    	smtFields(classDef, gen, false, indStr, refClassElement, numLoc, size); //static
    	smtFields(classDef, gen, true, indStr, refClassElement, numLoc, size); //dynamic
    	smtMethods(classDef, gen, false, indStr, refClassElement, numLoc, classDefs, options, callbacks, disabledActivities, activities, launcherActivities, callbackImplementations,
    			applications, size,
    			 arrayDataPayload,  packedSwitchPayload, 
    			 sparseSwitchPayload); //direct
        smtMethods(classDef, gen, true, indStr, refClassElement, numLoc, classDefs, options, callbacks, disabledActivities, activities, launcherActivities, callbackImplementations,
        		applications, size,
        		arrayDataPayload, packedSwitchPayload, 
    			sparseSwitchPayload); //virtual
    }
    
    private static void smtFields(final ClassDef classDef, final Gen gen, final boolean dynamic, 
    		final IndStr indStr, final RefClassElement refClassElement, final NumLoc numLoc, final int size) throws IOException {
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
     
            String fieldIndex = Utils.Dec(indStr.get(ReferenceUtil.getShortFieldDescriptor(field), 'f'));
            String classIndex = Utils.Dec(indStr.get(classDef.getType(), 'c'));
            
            	if (initialValue != null) {
            		gen.addMain("(rule (S " + classIndex + ' ' + fieldIndex + " " + FormatEncodedValue.toString(initialValue, indStr, size) + " false bf))"); 
            	}
        }
    }
    
    private static void smtMethods(final ClassDef classDef, final Gen gen, final boolean virtual, 
    		final IndStr indStr, final RefClassElement refClassElement, final NumLoc numLoc,
    		final List<? extends ClassDef> classDefs, final options options,  final Set<String> callbacks,  final Set<Integer> disabledActivities, final Set<Integer> activities,
    		final Set<Integer> launcherActivities, final Set<Integer> callbackImplementations, final Set<Integer> applications, final int size,
    		final Set<ArrayData> arrayDataPayload, final Set<PackedSwitch> packedSwitchPayload, 
			final Set<SparseSwitch> sparseSwitchPayload) throws Exception {
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
                String methodIndex  = Utils.Dec(indStr.get(methodString, 'm'));
                String classIndex = Utils.Dec(indStr.get(classDef.getType(), 'c'));
                MethodImplementation methodImpl = method.getImplementation();
                if (methodImpl == null) {
                } else {
                	 smtMethod(method, methodImpl, methodString, classIndex, methodIndex, refClassElement, indStr, gen, numLoc,
                			 classDefs, options, classDef, callbacks, disabledActivities, activities, launcherActivities, callbackImplementations, applications, size,
                			 arrayDataPayload, packedSwitchPayload, 
                				sparseSwitchPayload);
                }
        }
    }
    
    public static boolean testEntryPoint(final List<? extends ClassDef> classDefs, ClassDef classDef, int methodIndex, final Gen gen, final IndStr indStr){
    	final String superClass = classDef.getSuperclass();
    	if (superClass != null){
    		if (gen.isEntryPoint(indStr.get(superClass, 'c'), methodIndex)){
    			return true;
    		}
    		else{
    			for (final ClassDef classDef1: classDefs) {
    				if (indStr.get(classDef1.getType(), 'c') == indStr.get(superClass, 'c')){
    					return testEntryPoint(classDefs, classDef1, methodIndex, gen, indStr);
    					}			
    				}
    		}
    	}
    	return false;
    }
    
    private static void smtMethod(final Method method, final MethodImplementation methodImpl, 
    		final String methodString, final String classIndex, 
    		final String methodIndex,
    		final RefClassElement refClassElement, final IndStr indStr, final Gen gen, final NumLoc numLoc,
    		final List<? extends ClassDef> classDefs, final options options, final ClassDef classDef,  final Set<String> callbacks,  final Set<Integer> disabledActivities,
    		final Set<Integer> activities, final Set<Integer> launcherActivities, final Set<Integer> callbackImplementations, final Set<Integer> applications,
    		final int size, final Set<ArrayData> arrayDataPayload, final Set<PackedSwitch> packedSwitchPayload, 
			final Set<SparseSwitch> sparseSwitchPayload) throws Exception{
    	List<String> interfaces = Lists.newArrayList(classDef.getInterfaces());
        Collections.sort(interfaces);
        if (interfaces.size() != 0) {
            for (String interfaceName: interfaces) {
            	if (callbackImplementations.contains(indStr.get(interfaceName, 'c'))){
            		Map<Integer, String> regUpdate = new HashMap<Integer, String>();
                    Map<Integer, String> regUpdateL = new HashMap<Integer, String>();
                    Map<Integer, String> regUpdateB = new HashMap<Integer, String>();
                    final int numRegCall = numLoc.get(Integer.parseInt(classIndex), Integer.parseInt(methodIndex));
                    final int regCount = numLoc.getp(Integer.parseInt(classIndex), Integer.parseInt(methodIndex));
            		int i;
            		for (i = 0; i<= numRegCall + regCount; i++){
        				regUpdateL.put(i, "false");
        			}            		
            		gen.addMain("(rule " + refClassElement.rPred(classIndex, methodIndex, 
        					0, regUpdate, regUpdateL, regUpdateB, regCount, numRegCall, gen) + ")");
            	}
            }
        }
        String formatClassName = classDef.getType().replaceAll("\\.", "/").substring(1, classDef.getType().replaceAll("\\.", "/").length() -1);
        String[] parts = formatClassName.split("/");
		String classN =  parts[parts.length - 1];
		if ((isActivity(classDefs, classDef, indStr)) && (testEntryPoint(classDefs, classDef, Integer.parseInt(methodIndex), gen, indStr))){
			Map<Integer, String> regUpdate = new HashMap<Integer, String>();
            Map<Integer, String> regUpdateL = new HashMap<Integer, String>();
            Map<Integer, String> regUpdateB = new HashMap<Integer, String>();
            final int numRegCall = numLoc.get(Integer.parseInt(classIndex), Integer.parseInt(methodIndex));
            final int regCount = numLoc.getp(Integer.parseInt(classIndex), Integer.parseInt(methodIndex));
    		int i;
    		for (i = 0; i<= numRegCall + regCount; i++){
				regUpdateL.put(i, "false");
			}		
    		gen.addMain("(rule (=> " + refClassElement.iPred(
				"cn", Utils.hexDec64(Integer.parseInt(classIndex), size), "val", "lf", "bf") + ' ' +
		         		refClassElement.rPred(classIndex, methodIndex, 
					0, regUpdate, regUpdateL, regUpdateB, regCount, numRegCall, gen)
		         		+ "))");		
		}
    	if ((!disabledActivities.contains(indStr.get(classN, 'c'))) && (testEntryPoint(classDefs, classDef, Integer.parseInt(methodIndex), gen, indStr))
    			&& (launcherActivities.contains(indStr.get(classN, 'c')))){
    		Map<Integer, String> regUpdate = new HashMap<Integer, String>();
            Map<Integer, String> regUpdateL = new HashMap<Integer, String>();
            Map<Integer, String> regUpdateB = new HashMap<Integer, String>();
            final int numRegCall = numLoc.get(Integer.parseInt(classIndex), Integer.parseInt(methodIndex));
            final int regCount = numLoc.getp(Integer.parseInt(classIndex), Integer.parseInt(methodIndex));
    		int i;
    		for (i = 0; i<= numRegCall + regCount; i++){
				regUpdateL.put(i, "false");
			}
			
    		gen.addMain("(rule " + refClassElement.rPred(classIndex, methodIndex, 
					0, regUpdate, regUpdateL, regUpdateB, regCount, numRegCall, gen) + ")");
    		
    		/*//!create an instance of the entrypoint class
    		refClassElement.putInstance(0, 0, 0, Integer.parseInt(classIndex), true);    		
    		//even more: if an activity implements an interface we should add instance also
    		List<String> interfaces1 = Lists.newArrayList(classDef.getInterfaces());
    		for (final String interfaceName: interfaces1){
    			refClassElement.putInstance(0, 0, 0, indStr.get(interfaceName, 'c'), true);
    		}*/
    		
    		gen.addMain("(rule " + refClassElement.hPred(Utils.hexDec64(indStr.get(classDef.getType(), 'c'), size), "fpp", "f", "val", "false", "true") + ")");
    	}
    	if (parentActivity(classDefs,  activities, indStr.get(classDef.getType(), 'c'),  indStr)){
    		Map<Integer, String> regUpdate = new HashMap<Integer, String>();
            Map<Integer, String> regUpdateL = new HashMap<Integer, String>();
            Map<Integer, String> regUpdateB = new HashMap<Integer, String>();
            final int numRegCall = numLoc.get(Integer.parseInt(classIndex), Integer.parseInt(methodIndex));
            final int regCount = numLoc.getp(Integer.parseInt(classIndex), Integer.parseInt(methodIndex));
    		int i;
    		for (i = 0; i<= numRegCall + regCount; i++){
				regUpdateL.put(i, "false");
			}
    		
    		//create an instance of the entrypoint class
    		refClassElement.putInstance(0, 0, 0, Integer.parseInt(classIndex), true);
			
    		gen.addMain("(rule " + refClassElement.rPred(classIndex, methodIndex, 
					0, regUpdate, regUpdateL, regUpdateB, regCount, numRegCall, gen) + ")");
    		
    		gen.addMain("(rule " + refClassElement.hPred(Utils.hexDec64(indStr.get(classDef.getType(), 'c'), size), "fpp", "f", "val", "false", "true") + ")");
    	}
    	
    	if ((testEntryPoint(classDefs, classDef, Integer.parseInt(methodIndex), gen, indStr))
    			&& (!isActivity(classDefs, classDef, indStr))){
    		Map<Integer, String> regUpdate = new HashMap<Integer, String>();
            Map<Integer, String> regUpdateL = new HashMap<Integer, String>();
            Map<Integer, String> regUpdateB = new HashMap<Integer, String>();
            final int numRegCall = numLoc.get(Integer.parseInt(classIndex), Integer.parseInt(methodIndex));
            final int regCount = numLoc.getp(Integer.parseInt(classIndex), Integer.parseInt(methodIndex));
    		int i;
    		for (i = 0; i<= numRegCall + regCount; i++){
				regUpdateL.put(i, "false");
			}
    		//create an instance of the entrypoint class
    		refClassElement.putInstance(0, 0, 0, Integer.parseInt(classIndex), true);
			
    		gen.addMain("(rule " + refClassElement.rPred(classIndex, methodIndex, 
					0, regUpdate, regUpdateL, regUpdateB, regCount, numRegCall, gen) + ")");
    		
    		gen.addMain("(rule " + refClassElement.hPred(Utils.hexDec64(indStr.get(classDef.getType(), 'c'), size), "fpp", "f", "val", "false", "true") + ")");
    	}
    	for (final String callback: callbacks){
    		if (methodString.contains(callback)){
    			Map<Integer, String> regUpdate = new HashMap<Integer, String>();
                Map<Integer, String> regUpdateL = new HashMap<Integer, String>();
                Map<Integer, String> regUpdateB = new HashMap<Integer, String>();
                final int numRegCall = numLoc.get(Integer.parseInt(classIndex), Integer.parseInt(methodIndex));
                final int regCount = numLoc.getp(Integer.parseInt(classIndex), Integer.parseInt(methodIndex));
        		int i;
        		for (i = 0; i<= numRegCall + regCount; i++){
    				regUpdateL.put(i, "false");
    			}
    			
        		gen.addMain("(rule " + refClassElement.rPred(classIndex, methodIndex, 
    					0, regUpdate, regUpdateL, regUpdateB, regCount, numRegCall, gen) + ")");
    		}
    	}
        final Iterable<? extends Instruction> instructions = methodImpl.getInstructions();
        final ImmutableList<Instruction> instructionsIL = ImmutableList.<Instruction>builder().addAll(instructions).build();
        int codeAddress = 0;
        for (final Instruction instruction: instructions){
        	InstructionDataCollector idc = new InstructionDataCollector(codeAddress, Integer.parseInt(classIndex), 
	        			Integer.parseInt(methodIndex), instruction);
        	idc.process(indStr, refClassElement, instructionsIL, classDefs, method, numLoc, gen, options, classDef, activities, size,
					arrayDataPayload,  packedSwitchPayload, 
					 sparseSwitchPayload);
            codeAddress += instruction.getCodeUnits();
        }    
    } 
}