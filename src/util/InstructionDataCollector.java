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

package util;

import gen.Clause;
import gen.Gen;
import horndroid.options;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.annotation.Nonnull;

import org.jf.dexlib2.iface.instruction.OffsetInstruction;
import org.jf.baksmali.Adaptors.ClassDefinition;
import org.jf.baksmali.Adaptors.MethodDefinition;
import org.jf.baksmali.Adaptors.MethodDefinition.InvalidSwitchPayload;
import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.iface.ClassDef;
import org.jf.dexlib2.iface.Method;
import org.jf.dexlib2.iface.instruction.FiveRegisterInstruction;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.OneRegisterInstruction;
import org.jf.dexlib2.iface.instruction.ReferenceInstruction;
import org.jf.dexlib2.iface.instruction.RegisterRangeInstruction;
import org.jf.dexlib2.iface.instruction.SwitchElement;
import org.jf.dexlib2.iface.instruction.ThreeRegisterInstruction;
import org.jf.dexlib2.iface.instruction.TwoRegisterInstruction;
import org.jf.dexlib2.iface.instruction.WideLiteralInstruction;
import org.jf.dexlib2.iface.instruction.formats.ArrayPayload;
import org.jf.dexlib2.iface.instruction.formats.Instruction31t;
import org.jf.dexlib2.iface.instruction.formats.PackedSwitchPayload;
import org.jf.dexlib2.iface.instruction.formats.SparseSwitchPayload;
import org.jf.dexlib2.iface.reference.FieldReference;
import org.jf.dexlib2.iface.reference.MethodReference;
import org.jf.dexlib2.iface.reference.Reference;
import org.jf.dexlib2.iface.reference.StringReference;
import org.jf.dexlib2.iface.reference.TypeReference;
import org.jf.util.ExceptionWithContext;

import payload.ArrayData;
import payload.PackedSwitch;
import payload.SparseSwitch;

import com.google.common.collect.ImmutableList;

import strings.ConstString;
import util.iface.IndStr;

public class InstructionDataCollector<T extends Instruction> {
	@Nonnull private final T instruction;
	@Nonnull private final int codeAddress;
	@Nonnull private final int c;
	@Nonnull private final int m;
	public InstructionDataCollector(int codeAddress, int c, int m, @Nonnull T instruction) {
		this.codeAddress = codeAddress;
		this.instruction = instruction;
		this.c = c;
		this.m = m;
	}
	
	public void collect(final IndStr indStr, final RefClassElement refClassElement, final ImmutableList<Instruction> instructions, final Set<ConstString> constStrings, final Set<Integer> launcherActivities,
			final ClassDef classDef, final Method method, final Set<ArrayData> arrayDataPayload, final Set<PackedSwitch> packedSwitchPayload, 
			final Set<SparseSwitch> sparseSwitchPayload){
        char mode = 'n';
        String referenceString = null;
    	String referenceStringClass = null;
    	int referenceClassIndex = -1;
    	int referenceIntIndex = -1;
        String returnType = null;
    	int nextCode;
		if (instruction instanceof ReferenceInstruction) {
			ReferenceInstruction referenceInstruction = (ReferenceInstruction)instruction;
			Reference reference = referenceInstruction.getReference();
			if (reference instanceof StringReference) {mode = 's';}
			if (reference instanceof TypeReference)   {mode = 'c';}
			if (reference instanceof FieldReference)  {mode = 'f';}
			if (reference instanceof MethodReference) {mode = 'm';}
	        referenceString = Utils.getShortReferenceString(reference);
	        if (reference instanceof FieldReference) {
	        	referenceStringClass = ((FieldReference) reference).getDefiningClass();
	        	referenceClassIndex = indStr.get(referenceStringClass, 'c');
	        }
	        else 
	        	if (reference instanceof MethodReference){
	        		referenceStringClass = ((MethodReference) reference).getDefiningClass();
	        		referenceClassIndex = indStr.get(referenceStringClass, 'c');
	        		returnType = ((MethodReference) reference).getReturnType();
	            }
	        referenceIntIndex = indStr.get(referenceString, mode);
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
                    PackedSwitchPayload psInst = (PackedSwitchPayload) methodDef.findSwitchPayload(this.codeAddress + ((Instruction31t)instruction).getCodeOffset(),
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
                    SparseSwitchPayload ssInst = (SparseSwitchPayload) methodDef.findSwitchPayload(this.codeAddress + ((Instruction31t)instruction).getCodeOffset(),
                            payloadOpcode);
                    final Map<Integer, Integer> sTargets  = Collections.synchronizedMap(new HashMap <Integer, Integer>());
                    for (SwitchElement switchElement: ssInst.getSwitchElements()) {
                        sTargets.put(switchElement.getKey(), baseSCodeAddress + switchElement.getOffset());
                    }
                    sparseSwitchPayload.add(new SparseSwitch(c, m, payloadAddress, sTargets));
                    break;
                case FILL_ARRAY_DATA:
                    payloadOpcode = Opcode.ARRAY_PAYLOAD;
                    ArrayPayload apInst = (ArrayPayload) methodDef.findSwitchPayload(this.codeAddress + ((Instruction31t)instruction).getCodeOffset(),
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
		    		constStrings.add(new ConstString(c, m, codeAddress, ((OneRegisterInstruction)instruction).getRegisterA(), indStr.get(classN, 'c'), indStr.get(dalvikName, 'c')));
				}
				break;
			}
        	if (opcode.name.equals((String)"new-instance"))
        		refClassElement.putInstance(c, m, codeAddress, referenceIntIndex, true);
        	break;
		 case Format22c:
         	if (opcode.name.equals((String) "new-array"))
         		refClassElement.putInstance(c, m, codeAddress, referenceIntIndex, false);
         	break;
		 case Format35c:
			 
			if (opcode.name.equals((String) "filled-new-array")){
	         		refClassElement.putInstance(c, m, codeAddress, referenceIntIndex, false);
	         		break;
			}
			
         	nextCode = codeAddress + instruction.getCodeUnits();
         	
         	//reflection
         	if  (referenceClassIndex == (indStr.get("Ljava/lang/Class;", 'c')) && 
        			(indStr.get("newInstance()Ljava/lang/Object;", 'm') == referenceIntIndex)){
    			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    			for (final ConstString constString: constStrings){
    				if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction.getRegisterC())){
    					refClassElement.putInstance(c, m, codeAddress, constString.getDalvikName(), true);
    					break;
    				}
    			}
            }
         	//
         	
         	if  (referenceClassIndex == (indStr.get("Landroid/content/ComponentName;", 'c')) && 
        			(indStr.get("<init>(Landroid/content/Context;Ljava/lang/String;)V", 'm') == referenceIntIndex)){
    			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    			for (final ConstString constString: constStrings){
    				if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction.getRegisterE())){
    					constString.putPC(codeAddress);
    					constString.putV(instruction.getRegisterC());
    				}
    			}
            }
         	
         	if  (referenceClassIndex == (indStr.get("Landroid/content/Intent;", 'c')) && 
        			(indStr.get("setComponent(Landroid/content/ComponentName;)Landroid/content/Intent;", 'm') == referenceIntIndex)){
    			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    			for (final ConstString constString: constStrings){
    				if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction.getRegisterD())){
    					constString.putPC(codeAddress);
    					constString.putV(instruction.getRegisterC());
    				}
    			}
            }
         
         	if  (indStr.get("startActivity(Landroid/content/Intent;)V", 'm') == referenceIntIndex){
    			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    			for (final ConstString constString: constStrings){
    				if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction.getRegisterD())){
    					launcherActivities.add(constString.getVAL());
    				}
    			}
            }
         	
         	refClassElement.addCallRef(referenceClassIndex, referenceIntIndex, c, m, nextCode);
         	if (referenceStringClass != null)
         	{
             	refClassElement.putMethod(referenceStringClass, referenceString);
         	}
             
             if (referenceClassIndex == indStr.get("Landroid/content/Intent;", 'c')
             		&& referenceIntIndex == indStr.get("<init>(Landroid/content/Context;Ljava/lang/Class;)V", 'm')){
             	refClassElement.putInstance(c, m, codeAddress, indStr.get("Landroid/content/Intent;", 'c'), true);
             }
             
             if (referenceClassIndex == indStr.get("Landroid/content/Intent;", 'c')
             		&& referenceIntIndex == indStr.get("<init>(Ljava/lang/String;)V", 'm')){
             	refClassElement.putInstance(c, m, codeAddress, indStr.get("Landroid/content/Intent;", 'c'), true);
             }
             
             if (referenceClassIndex == indStr.get("Landroid/content/Intent;", 'c')
             		&& referenceIntIndex == indStr.get("<init>()V", 'm')){
             	refClassElement.putInstance(c, m, codeAddress, indStr.get("Landroid/content/Intent;", 'c'), true);
             }
             try{
             if (returnType.length() > 0){
             	if (returnType.contains("[")){
                 	refClassElement.putInstance(c, m, codeAddress, indStr.get(returnType, 'c'), false);
                 	break;
                 }
             	if (returnType.charAt(returnType.length() - 1) == ';'){
             		refClassElement.putInstance(c, m, codeAddress, indStr.get(returnType, 'c'), true);
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
	         		refClassElement.putInstance(c, m, codeAddress, referenceIntIndex, false);
	         		break;
				}
			nextCode = codeAddress + instruction.getCodeUnits();
			
         	refClassElement.addCallRef(referenceClassIndex, referenceIntIndex, c, m, nextCode);
         	
         	if (referenceStringClass != null){
             	refClassElement.putMethod(referenceStringClass, referenceString);
         	}
             if (referenceClassIndex == indStr.get("Landroid/content/Intent;", 'c')
             		&& referenceIntIndex == indStr.get("<init>(Landroid/content/Context;Ljava/lang/Class;)V", 'm')){
             	refClassElement.putInstance(c, m, codeAddress, indStr.get("Landroid/content/Intent;", 'c'), true);
             }
             
             if (referenceClassIndex == indStr.get("Landroid/content/Intent;", 'c')
             		&& referenceIntIndex == indStr.get("<init>(Ljava/lang/String;)V", 'm')){
             	refClassElement.putInstance(c, m, codeAddress, indStr.get("Landroid/content/Intent;", 'c'), true);
             }
             
             if (referenceClassIndex == indStr.get("Landroid/content/Intent;", 'c')
             		&& referenceIntIndex == indStr.get("<init>()V", 'm')){
             	refClassElement.putInstance(c, m, codeAddress, indStr.get("Landroid/content/Intent;", 'c'), true);
             }
             
             if (returnType.charAt(returnType.length() - 1) == ';'){
             	refClassElement.putInstance(c, m, codeAddress, indStr.get(returnType, 'c'), true);
             	break;
             }
             if (returnType.contains("["))
             	refClassElement.putInstance(c, m, codeAddress, indStr.get(returnType, 'c'), false);
             break;
		default:
			break;
		}
	}
	public void process(final IndStr indStr, final RefClassElement refClassElement, final ImmutableList<Instruction> instructions,
			final List<? extends ClassDef> classDefs, final Method method, final NumLoc numLoc, final Gen gen, final options options, final ClassDef classDef, final Set<Integer> activities, final int size,
			final Set<ArrayData> arrayDataPayload, final Set<PackedSwitch> packedSwitchPayload, 
			final Set<SparseSwitch> sparseSwitchPayload) throws Exception{
		String negationString = null;
		boolean moreToNegate = false;
	  	int jump = 0;
    	int referenceReg;
    	boolean isDefined;
    	Map<Integer, Integer> implementations;
    	int instanceNum;
    	boolean callReturns = false;
    	int numRegCall;
    	int numRegCallp;
    	int numArgCall;
    	String referenceStringClass = null;
    	String referenceStringClassIndex = null;
    	String returnType = null;
    	int returnTypeInt = 0;
    	int referenceClassIndex = -1;
    	int referenceIntIndex = -1;
        Opcode opcode = instruction.getOpcode();
        String referenceString = null;
        char mode = 'n';
        String referenceIndex = null;
        int nextCode = codeAddress + instruction.getCodeUnits();        
        
        Map<Integer, Boolean> fields = Collections.synchronizedMap(new HashMap <Integer, Boolean>());

        if (instruction instanceof ReferenceInstruction) {
            ReferenceInstruction referenceInstruction = (ReferenceInstruction)instruction;
            Reference reference = referenceInstruction.getReference();
                
                if (reference instanceof StringReference) {mode = 's';}
                if (reference instanceof TypeReference)   {mode = 'c';}
                if (reference instanceof FieldReference)  {mode = 'f';}
                if (reference instanceof MethodReference) {mode = 'm';}
                
            referenceString = Utils.getShortReferenceString(reference);
            if (reference instanceof FieldReference) {
                		referenceStringClass = ((FieldReference) reference).getDefiningClass();
                		referenceClassIndex = indStr.get(referenceStringClass, 'c');
                		referenceStringClassIndex = Utils.Dec(referenceClassIndex);
            }
            else 
                	if (reference instanceof MethodReference){
                		referenceStringClass = ((MethodReference) reference).getDefiningClass();
                		referenceClassIndex = indStr.get(referenceStringClass, 'c');
                		referenceStringClassIndex = Utils.Dec(referenceClassIndex);
                		returnType = ((MethodReference) reference).getReturnType();
                		returnTypeInt = indStr.get(returnType, 'c');
                		if (returnType.equals((String) "V")) callReturns = false;
                		else callReturns = true;
                	}
             referenceIntIndex = indStr.get(referenceString, mode);
             referenceIndex = Utils.Dec(referenceIntIndex);      
        assert referenceString != null;
        }    
            
        

        String methodName = Utils.getShortMethodDescriptor(method);
        String className = method.getDefiningClass();
        int mi = indStr.get(methodName, 'm');
        String methodIndex = Utils.Dec(mi);
        int ci = indStr.get(className, 'c');
        String classIndex = Utils.Dec(ci);  
        final int numRegLoc = method.getImplementation().getRegisterCount();
        final int numParLoc = numLoc.getp(ci, mi);
        Clause cl = new Clause();
        Clause cl2 = new Clause();
        Clause cl3 = new Clause();
        String head = "";
        String returnLabel = "";
        Map<Integer, String> regUpdate = new HashMap<Integer, String>();
        Map<Integer, String> regUpdateL = new HashMap<Integer, String>();
        Map<Integer, String> regUpdateB = new HashMap<Integer, String>();
        switch (opcode){
        	case NOP: 
           	case MONITOR_ENTER://((short)0x1d, "monitor-enter", ReferenceType.NONE, Format.Format11x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case MONITOR_EXIT://((short)0x1e, "monitor-exit", ReferenceType.NONE, Format.Format11x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0x00, "nop", ReferenceType.NONE, Format.Format10x, Opcode.CAN_CONTINUE),
        	case MOVE://((short)0x01, "move", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MOVE_FROM16://((short)0x02, "move/from16", ReferenceType.NONE, Format.Format22x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MOVE_16://((short)0x03, "move/16", ReferenceType.NONE, Format.Format32x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MOVE_WIDE://((short)0x04, "move-wide", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case MOVE_WIDE_FROM16://((short)0x05, "move-wide/from16", ReferenceType.NONE, Format.Format22x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case MOVE_WIDE_16://((short)0x06, "move-wide/16", ReferenceType.NONE, Format.Format32x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case MOVE_OBJECT://((short)0x07, "move-object", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MOVE_OBJECT_FROM16://((short)0x08, "move-object/from16", ReferenceType.NONE, Format.Format22x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MOVE_OBJECT_16:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "b" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0x09, "move-object/16", ReferenceType.NONE, Format.Format32x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MOVE_RESULT://((short)0x0a, "move-result", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MOVE_RESULT_WIDE://((short)0x0b, "move-result-wide", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case MOVE_RESULT_OBJECT:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), 'v' + Integer.toString(numRegLoc));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), 'l' + Integer.toString(numRegLoc));
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), 'b' + Integer.toString(numRegLoc));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0x0c, "move-result-object", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MOVE_EXCEPTION:
        		int previousCode = 0;
        		for (final Instruction ins: instructions){
        			if ((previousCode + ins.getCodeUnits()) == codeAddress){
        				cl2.appendHead(refClassElement.rPred(classIndex, methodIndex, previousCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                		cl2.appendBody(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                		gen.addClause(cl2);
        			}
        			previousCode += ins.getCodeUnits();
        		}
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
                
        		//System.out.println("Unsupported Intsruction! MOVE_EXCEPTION");
        		break;//((short)0x0d, "move-exception", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case RETURN_VOID:
    			break;
        		//((short)0x0e, "return-void", ReferenceType.NONE, Format.Format10x),
        	case RETURN://((short)0x0f, "return", ReferenceType.NONE, Format.Format11x),
        	case RETURN_WIDE://((short)0x10, "return-wide", ReferenceType.NONE, Format.Format11x),
        	case RETURN_OBJECT:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(numParLoc, 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()));
        		regUpdateL.put(numParLoc, 'l' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()));
        		regUpdateB.put(numParLoc, 'b' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()));
        		int count = 0;
        		for (int i = numRegLoc + 1; i <= numRegLoc + numParLoc; i++){
        			regUpdate.put(count, 'v' + Integer.toString(i));
            		regUpdateL.put(count, 'l' + Integer.toString(i));
            		regUpdateB.put(count, 'b' + Integer.toString(i));
        			count ++;
        		}
        		cl.appendBody(refClassElement.resPred(classIndex, methodIndex, regUpdate, regUpdateL, regUpdateB, numParLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0x11, "return-object", ReferenceType.NONE, Format.Format11x),
        	case CONST_4://((short)0x12, "const/4", ReferenceType.NONE, Format.Format11n, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CONST_16://((short)0x13, "const/16", ReferenceType.NONE, Format.Format21s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CONST://((short)0x14, "const", ReferenceType.NONE, Format.Format31i, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CONST_HIGH16://((short)0x15, "const/high16", ReferenceType.NONE, Format.Format21ih, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CONST_WIDE_16://((short)0x16, "const-wide/16", ReferenceType.NONE, Format.Format21s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case CONST_WIDE_32://((short)0x17, "const-wide/32", ReferenceType.NONE, Format.Format31i, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case CONST_WIDE://((short)0x18, "const-wide", ReferenceType.NONE, Format.Format51l, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case CONST_WIDE_HIGH16:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), Utils.hexDec64(((WideLiteralInstruction)instruction).getWideLiteral(), size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "false");
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "false");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0x19, "const-wide/high16", ReferenceType.NONE, Format.Format21lh, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case CONST_STRING://((short)0x1a, "const-string", ReferenceType.STRING, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER, (short)0x1b),
        	case CONST_STRING_JUMBO:
        	case CONST_CLASS://break;//((short)0x1c, "const-class", ReferenceType.TYPE, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), Utils.hexDec64(referenceIntIndex, size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "false");
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "false");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0x1b, "const-string/jumbo", ReferenceType.STRING, Format.Format31c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),	
        	case CHECK_CAST:
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) + 
        				" (= b" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " true) " + "(bvugt v" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " " + Utils.hexDec64(0, size) + "))");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0x1f, "check-cast", ReferenceType.TYPE, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case INSTANCE_OF:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), Utils.hexDec64(0, size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "false");
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "false");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		regUpdate.clear();
        		regUpdateL.clear();
        		regUpdateB.clear();
        		cl3.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), Utils.hexDec64(1, size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "false");
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "false");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		break;//((short)0x20, "instance-of", ReferenceType.TYPE, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case ARRAY_LENGTH:
        		//cl.appendHead("(and (P_" + classIndex + '_' + methodIndex + '_' + Integer.toString(codeAddress) + getRegsDefs(ci, mi, codeAddress, gen, regUpdate, regUpdateL, returns, numRegLoc)
        		//		+ " (ARR-LEN v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + " f lf))");
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "f");
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "lf");
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "false");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0x21, "array-length", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case NEW_INSTANCE:
        		if (referenceIntIndex == indStr.get("Landroid/content/Intent;", 'c')){
        			cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
            		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
            		gen.addClause(cl);
        			break;
        		}
        		instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), Utils.hexDec64(instanceNum, size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "false");
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "true");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		regUpdate.clear();
        		regUpdateL.clear();
        		regUpdateB.clear();
				fields = refClassElement.getClassFields(classDefs, indStr, referenceString, instanceNum);
				if (fields != null)
        		for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
        			Clause cl12 = new Clause();
        			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        			cl12.appendBody(refClassElement.hPred(
        					Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size), Utils.hexDec64(fieldN.getKey(), size), Utils.hexDec64(0, size), "false", Boolean.toString(fieldN.getValue())));
        			gen.addClause(cl12);
        		}
				else{
					Clause cl12 = new Clause();
        			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size), "f", Utils.hexDec64(0, size), "false", "bf"));
        			gen.addClause(cl12);
				}
        		
        		regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
        		if (gen.hasStaticConstructor(referenceIntIndex)){
            		cl3.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        			int staticConstNum = indStr.get("<clinit>()V", 'm');
        			//cl3.appendBody(refClassElement.rPred(Integer.toString(referenceIntIndex), Integer.toString(staticConstNum), 0, regUpdate, regUpdateL,
        			//		refClassElement.getNumArg(referenceIntIndex, staticConstNum, classDefs, indStr), numLoc.get(referenceIntIndex, staticConstNum), gen));
        			cl3.appendBody(refClassElement.rPred(Integer.toString(referenceIntIndex), Integer.toString(staticConstNum), 0, regUpdate, regUpdateL, regUpdateB,
        					numLoc.getp(referenceIntIndex, staticConstNum), numLoc.get(referenceIntIndex, staticConstNum), gen));
        			gen.addClause(cl3);
        		}
        		break;//((short)0x22, "new-instance", ReferenceType.TYPE, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case NEW_ARRAY:
        		instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), Utils.hexDec64(instanceNum, size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "false");
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "true");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
        		if (options.arrays){
        		cl2.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (bvuge " + Utils.hexDec64(0, size) + " f) " + "(bvult f " + 'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) +"))");
        		cl2.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size), "f", Utils.hexDec64(0, size), "false", "false"));
        		gen.addClause(cl2);
        		}
        		else{
        		cl2.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		cl2.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size), Utils.hexDec64(0, size), Utils.hexDec64(0, size), "false", "false"));
        		gen.addClause(cl2);
        		}
        		break;//((short)0x23, "new-array", ReferenceType.TYPE, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case FILLED_NEW_ARRAY:
        		Clause clf1 = new Clause();
        		Clause clf2 = new Clause();
        		Clause clf3 = new Clause();
        		Clause clf4 = new Clause();
        		Clause clf5 = new Clause();
        		FiveRegisterInstruction instructionA = (FiveRegisterInstruction)this.instruction;
                final int regCount = instructionA.getRegisterCount();
        		instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(numRegLoc, Utils.hexDec64(instanceNum, size));
        		regUpdateL.put(numRegLoc, "false");
        		regUpdateB.put(numRegLoc, "true");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
        		if (options.arrays){
        			switch(regCount){
        			case 1:
        				clf1.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf1.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterC(), "l" + instructionA.getRegisterC(), "b" + instructionA.getRegisterC()));
        				gen.addClause(clf1);
        				break;
        			case 2:
        				clf1.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf1.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterC(), "l" + instructionA.getRegisterC(), "b" + instructionA.getRegisterC()));
        				gen.addClause(clf1);
        				clf2.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf2.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(1, size), "v" + instructionA.getRegisterD(), "l" + instructionA.getRegisterD(), "b" + instructionA.getRegisterD()));
        				gen.addClause(clf2);
        				break;
        			case 3:
        				clf1.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf1.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterC(), "l" + instructionA.getRegisterC(), "b" + instructionA.getRegisterC()));
        				gen.addClause(clf1);
        				clf2.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf2.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(1, size), "v" + instructionA.getRegisterD(), "l" + instructionA.getRegisterD(), "b" + instructionA.getRegisterD()));
        				gen.addClause(clf2);
        				clf3.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf3.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(2, size), "v" + instructionA.getRegisterE(), "l" + instructionA.getRegisterE(), "b" + instructionA.getRegisterE()));
        				gen.addClause(clf3);
        				break;
        			case 4:
        				clf1.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf1.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterC(), "l" + instructionA.getRegisterC(), "b" + instructionA.getRegisterC()));
        				gen.addClause(clf1);
        				clf2.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf2.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(1, size), "v" + instructionA.getRegisterD(), "l" + instructionA.getRegisterD(), "b" + instructionA.getRegisterD()));
        				gen.addClause(clf2);
        				clf3.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf3.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(2, size), "v" + instructionA.getRegisterE(), "l" + instructionA.getRegisterE(), "b" + instructionA.getRegisterE()));
        				gen.addClause(clf3);
        				clf4.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf4.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(3, size), "v" + instructionA.getRegisterF(), "l" + instructionA.getRegisterF(), "b" + instructionA.getRegisterF()));
        				gen.addClause(clf4);
        				break;
        			case 5:
        				clf1.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf1.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterC(), "l" + instructionA.getRegisterC(), "b" + instructionA.getRegisterC()));
        				gen.addClause(clf1);
        				clf2.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf2.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(1, size), "v" + instructionA.getRegisterD(), "l" + instructionA.getRegisterD(), "b" + instructionA.getRegisterD()));
        				gen.addClause(clf2);
        				clf3.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf3.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(2, size), "v" + instructionA.getRegisterE(), "l" + instructionA.getRegisterE(), "b" + instructionA.getRegisterE()));
        				gen.addClause(clf3);
        				clf4.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf4.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(3, size), "v" + instructionA.getRegisterF(), "l" + instructionA.getRegisterF(), "b" + instructionA.getRegisterF()));
        				gen.addClause(clf4);
        				clf5.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf5.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(4, size), "v" + instructionA.getRegisterG(), "l" + instructionA.getRegisterG(), "b" + instructionA.getRegisterG()));
        				gen.addClause(clf5);
        				break;
        			}
        		}
        		else{
        			switch(regCount){
        			case 1:
        				clf1.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf1.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterC(), "l" + instructionA.getRegisterC(), "b" + instructionA.getRegisterC()));
        				gen.addClause(clf1);
        				break;
        			case 2:
        				clf1.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf1.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterC(), "l" + instructionA.getRegisterC(), "b" + instructionA.getRegisterC()));
        				gen.addClause(clf1);
        				clf2.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf2.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterD(), "l" + instructionA.getRegisterD(), "b" + instructionA.getRegisterD()));
        				gen.addClause(clf2);
        				break;
        			case 3:
        				clf1.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf1.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterC(), "l" + instructionA.getRegisterC(), "b" + instructionA.getRegisterC()));
        				gen.addClause(clf1);
        				clf2.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf2.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterD(), "l" + instructionA.getRegisterD(), "b" + instructionA.getRegisterD()));
        				gen.addClause(clf2);
        				clf3.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf3.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterE(), "l" + instructionA.getRegisterE(), "b" + instructionA.getRegisterE()));
        				gen.addClause(clf3);
        				break;
        			case 4:
        				clf1.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf1.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterC(), "l" + instructionA.getRegisterC(), "b" + instructionA.getRegisterC()));
        				gen.addClause(clf1);
        				clf2.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf2.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterD(), "l" + instructionA.getRegisterD(), "b" + instructionA.getRegisterD()));
        				gen.addClause(clf2);
        				clf3.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf3.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterE(), "l" + instructionA.getRegisterE(), "b" + instructionA.getRegisterE()));
        				gen.addClause(clf3);
        				clf4.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf4.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterF(), "l" + instructionA.getRegisterF(), "b" + instructionA.getRegisterF()));
        				gen.addClause(clf4);
        				break;
        			case 5:
        				clf1.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf1.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterC(), "l" + instructionA.getRegisterC(), "b" + instructionA.getRegisterC()));
        				gen.addClause(clf1);
        				clf2.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf2.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterD(), "l" + instructionA.getRegisterD(), "b" + instructionA.getRegisterD()));
        				gen.addClause(clf2);
        				clf3.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf3.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterE(), "l" + instructionA.getRegisterE(), "b" + instructionA.getRegisterE()));
        				gen.addClause(clf3);
        				clf4.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf4.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterF(), "l" + instructionA.getRegisterF(), "b" + instructionA.getRegisterF()));
        				gen.addClause(clf4);
        				clf5.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clf5.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + instructionA.getRegisterG(), "l" + instructionA.getRegisterG(), "b" + instructionA.getRegisterG()));
        				gen.addClause(clf5);
        				break;
        			}
        		}
        		//System.out.println("Unsupported Intsruction! FILLED_NEW_ARRAY");
        		break;//((short)0x24, "filled-new-array", ReferenceType.TYPE, Format.Format35c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        	case FILLED_NEW_ARRAY_RANGE:
        		instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(numRegLoc, Utils.hexDec64(instanceNum, size));
        		regUpdateL.put(numRegLoc, "false");
        		regUpdateB.put(numRegLoc, "true");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
        		
        		RegisterRangeInstruction instructionAr = (RegisterRangeInstruction)this.instruction;
        		int regCountr = instructionAr.getRegisterCount();
    			int startRegister = instructionAr.getStartRegister();
            	int endRegister   =   startRegister+regCountr-1;
            	int cr = 0;
            	
            	if (options.arrays){
            		for (int reg = startRegister; reg <= endRegister; reg++){
            			Clause clR = new Clause();
            			clR.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clR.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(cr, size), "v" + reg, "l" + reg, "b" + reg));
        				gen.addClause(clR);
            			cr++;
            		}
            	}
                else{
                	for (int reg = startRegister; reg <= endRegister; reg++){
            			Clause clR = new Clause();
            			clR.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				clR.appendBody(refClassElement.hPred(Utils.hexDec64(referenceIntIndex, size), Utils.hexDec64(instanceNum, size),
        						Utils.hexDec64(0, size), "v" + reg, "l" + reg, "b" + reg));
        				gen.addClause(clR);
            		}
                }
        		//System.out.println("Unsupported Intsruction! FILLED_NEW_ARRAY_RANGE");
        		break;//((short)0x25, "filled-new-array/range", ReferenceType.TYPE, Format.Format3rc, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        	case FILL_ARRAY_DATA:
        		for (final ArrayData ad: arrayDataPayload){
        			List<Number> elements = ad.getElements(c, m, codeAddress + ((Instruction31t)instruction).getCodeOffset());
        			if (elements != null){
        				int elNum = 0;
    					Clause cl16 = new Clause();
        				cl16.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
		        		cl16.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				for (final Number element: elements){
        					Clause cl17 = new Clause();      					
        					if (options.arrays){     		
        		        		gen.addClause(cl16);
        		        		cl17.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        		        				+ ' ' + refClassElement.hPred("cn", "v" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()), Utils.hexDec64(0, size), Utils.hexDec64(0, size), "lf", "bf") +')');
        		        		cl17.appendBody(refClassElement.hPred("cn", "v" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()), 
        		        				Utils.hexDec64(elNum, size), 
        		        				Utils.hexDec64(element.intValue(), size), "false",
        		        				"false"));
        		        		gen.addClause(cl17);
        		        		}
        		        		else{
        		        		cl17.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        		        				+ ' ' + refClassElement.hPred("cn", "v" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()), Utils.hexDec64(0, size), Utils.hexDec64(0, size), "lf", "bf") +')');
        		        		cl17.appendBody(refClassElement.hPred("cn", "v" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()), 
        		        				Utils.hexDec64(0, size), 
        		        				Utils.hexDec64(element.intValue(), size), 
        		        				"false",
        		        				"false"));
        		        		gen.addClause(cl17);
        		        		}
        					
        					
        					elNum++;
        				}
        			break;
        			}
        		}
        		//System.out.println("Unsupported Intsruction! FILL_ARRAY_DATA");
        		break;//((short)0x26, "fill-array-data", ReferenceType.NONE, Format.Format31t, Opcode.CAN_CONTINUE),
        	case THROW:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		//System.out.println("Unsupported Intsruction! THROW");
        		break;//((short)0x27, "throw", ReferenceType.NONE, Format.Format11x, Opcode.CAN_THROW),
        	case GOTO://((short)0x28, "goto", ReferenceType.NONE, Format.Format10t),
        	case GOTO_16://((short)0x29, "goto/16", ReferenceType.NONE, Format.Format20t),
        	case GOTO_32:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl3.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		break;//((short)0x2a, "goto/32", ReferenceType.NONE, Format.Format30t),
        	case PACKED_SWITCH:
        		for (final PackedSwitch ps: packedSwitchPayload){
        			List<Number> targets = ps.getTargets(c, m, codeAddress + ((Instruction31t)instruction).getCodeOffset());
        			if (targets != null){
        				if (targets.size() > 1){
        					negationString = " (and";
        					moreToNegate = true;
        				}
        				else
        					negationString = "";
        				int t = 0;
        				final int payloadAddress = codeAddress + ((Instruction31t)instruction).getCodeOffset();
        				for (final Number target: targets){
        					Clause cl16 = new Clause();
        					cl16.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        							+ " (= " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           Utils.hexDec64(ps.getFirstKey(c, m, payloadAddress) + t, size) + ")"
        				           + ")");
        					cl16.appendBody(refClassElement.rPred(classIndex, methodIndex, target.intValue(), 
        					regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        					gen.addClause(cl16);
        					
        					negationString = negationString +  " (= " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
         				           Utils.hexDec64(ps.getFirstKey(c, m, payloadAddress) + t, size) + ")";
        					t++;
        				}
        			break;
        			}
        		}
        		if (moreToNegate)
        			negationString = negationString + ')';
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not" + negationString + ")"
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		//System.out.println("Unsupported Intsruction! PACKED_SWITCH");
        		break;//((short)0x2b, "packed-switch", ReferenceType.NONE, Format.Format31t, Opcode.CAN_CONTINUE),
        	case SPARSE_SWITCH:
        		for (final SparseSwitch ss: sparseSwitchPayload){
        			Map<Integer, Integer> targets = ss.getTargets(c, m, codeAddress + ((Instruction31t)instruction).getCodeOffset());
        			if (targets != null){
        				if (targets.size() > 1){
        					negationString = " (and";
        					moreToNegate = true;
        				}
        				else
        					negationString = "";
        				for (final Map.Entry<Integer, Integer> target: targets.entrySet()){
        					Clause cl16 = new Clause();
        					cl16.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        							+ " (= " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           Utils.hexDec64(target.getKey(), size) + ")"
        				           + ")");
        					cl16.appendBody(refClassElement.rPred(classIndex, methodIndex, target.getValue(), 
        					regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        					gen.addClause(cl16);
        					
        					negationString = negationString +  " (= " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
         				           Utils.hexDec64(target.getKey(), size) + ")";
        				}
        			break;
        			}
        		}
        		if (moreToNegate)
        			negationString = negationString + ')';
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not" + negationString + ")"
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		//System.out.println("Unsupported Intsruction! SPARSE_SWITCH");
        		break;//((short)0x2c, "sparse-switch", ReferenceType.NONE, Format.Format31t, Opcode.CAN_CONTINUE),
        	case CMPL_FLOAT://((short)0x2d, "cmpl-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CMPG_FLOAT://((short)0x2e, "cmpg-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CMPL_DOUBLE://((short)0x2f, "cmpl-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CMPG_DOUBLE://((short)0x30, "cmpg-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CMP_LONG:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), 
        				"(ite (= v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
                		" v" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ") "+ Utils.hexDec64(0, size) + " (ite (bvugt v" +
                		Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
                		" v" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ") " + Utils.hexDec64(1, size) +
                		' ' + Utils.hexDec64(-1, size) +"))");
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), 
        				"(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        	
        		break;//((short)0x31, "cmp-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case IF_EQ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not (= " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + "))"
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (= " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ")"
        				+ ")");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		
        		break;//((short)0x32, "if-eq", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),
        	case IF_NE:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (= " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')'
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not (= " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + "))"
        				+ ")");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		
        		break;//((short)0x33, "if-ne", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),
        	case IF_LT:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not (bvult " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + "))"
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (bvult " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ")"
        				+ ")");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		
        		break;//((short)0x34, "if-lt", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),
        	case IF_GE:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not (bvuge " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + "))"
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (bvuge " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ")"
        				+ ")");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		
        		break;//((short)0x35, "if-ge", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),
        	case IF_GT:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not (bvugt " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + "))"
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (bvugt " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ")"
        				+ ")");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		
        		break;//((short)0x36, "if-gt", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),
        	case IF_LE:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not (bvule " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + "))"
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (bvule " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           'v' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ")"
        				+ ")");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		
        		break;//((short)0x37, "if-le", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),
        	case IF_EQZ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not (= " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           Utils.hexDec64(0, size) + "))"
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (= " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				          Utils.hexDec64(0, size) + ")"
        				+ ")");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		
        		break;//((short)0x38, "if-eqz", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),
        	case IF_NEZ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (= " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				          Utils.hexDec64(0, size) + ')'
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not (= " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           Utils.hexDec64(0, size) + "))"
        				+ ")");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		
        		break;//((short)0x39, "if-nez", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),
        	case IF_LTZ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not (bvult " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           Utils.hexDec64(0, size) + "))"
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (bvult " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           Utils.hexDec64(0, size) + ")"
        				+ ")");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		
        		break;//((short)0x3a, "if-ltz", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),
        	case IF_GEZ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not (bvuge " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				          Utils.hexDec64(0, size) + "))"
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (bvuge " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				          Utils.hexDec64(0, size) + ")"
        				+ ")");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		
        		break;//((short)0x3b, "if-gez", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),
        	case IF_GTZ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not (bvugt " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           Utils.hexDec64(0, size) + "))"
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (bvugt " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           Utils.hexDec64(0, size) + ")"
        				+ ")");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		
        		break;//((short)0x3c, "if-gtz", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),
        	case IF_LEZ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (not (bvule " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				           Utils.hexDec64(0, size) + "))"
        				+ ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ " (bvule " + 'v' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ' ' + 
        				          Utils.hexDec64(0, size) + ")"
        				+ ")");
        		cl3.appendBody(refClassElement.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl3);
        		
        		break;//((short)0x3d, "if-lez", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),
        	case AGET://((short)0x44, "aget", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case AGET_WIDE://((short)0x45, "aget-wide", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case AGET_OBJECT://((short)0x46, "aget-object", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case AGET_BOOLEAN://((short)0x47, "aget-boolean", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case AGET_BYTE://((short)0x48, "aget-byte", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case AGET_CHAR://((short)0x49, "aget-char", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case AGET_SHORT:
        		if (options.arrays){
            			Clause cl6 = new Clause();
        				cl6.appendHead("(and " + 
            			refClassElement.hPred("cn", "v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()), 
            					"v" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()), "val", "lval", "bval") +
        						' ' + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) +
        						")");
        				regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "val");
        				regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "lval");
        				regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "bval");
                		cl6.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        				gen.addClause(cl6);
        		}
        		else{
        		Clause cl6 = new Clause();
				cl6.appendHead("(and " + 
    			refClassElement.hPred("cn", "v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()), 
    					Utils.hexDec64(0, size), "val", "lval", "bval") +
						' ' + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) +
						")");
				regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "val");
				regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "lval");
				regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "bval");
        		cl6.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
				gen.addClause(cl6);
        		}
        		break;//((short)0x4a, "aget-short", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case APUT://((short)0x4b, "aput", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case APUT_WIDE://((short)0x4c, "aput-wide", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case APUT_OBJECT://((short)0x4d, "aput-object", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case APUT_BOOLEAN://((short)0x4e, "aput-boolean", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case APUT_BYTE://((short)0x4f, "aput-byte", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case APUT_CHAR://((short)0x50, "aput-char", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case APUT_SHORT:
        		if (options.arrays){
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdateL.put(((TwoRegisterInstruction)instruction).getRegisterB(), "(or " + 'l' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB())
        				+ ' ' +  'l' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ")");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		regUpdateL.clear();
        		cl2.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ ' ' + refClassElement.hPred("cn", "v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()), Utils.hexDec64(0, size), Utils.hexDec64(0, size), "lf", "bf") +')');
        		cl2.appendBody(refClassElement.hPred("cn", "v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()), 
        				"v" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()), 
        				'v'+ Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()), 'l'+Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()),
        				'b'+Integer.toString(((OneRegisterInstruction)instruction).getRegisterA())));
        		gen.addClause(cl2);
        		}
        		else{
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdateL.put(((TwoRegisterInstruction)instruction).getRegisterB(), "(or " + 'l' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB())
        				+ ' ' +  'l' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ")");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		regUpdateL.clear();
        		cl2.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ ' ' + refClassElement.hPred("cn", "v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()), Utils.hexDec64(0, size), Utils.hexDec64(0, size), "lf", "bf") +')');
        		cl2.appendBody(refClassElement.hPred("cn", "v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()), 
        				Utils.hexDec64(0, size), 
        				'v'+ Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()), 'l'+Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()),
        				'b'+Integer.toString(((OneRegisterInstruction)instruction).getRegisterA())));
        		gen.addClause(cl2);
        		}
        		break;
        		//((short)0x51, "aput-short", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IGET://((short)0x52, "iget", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case IGET_WIDE://((short)0x53, "iget-wide", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case IGET_OBJECT://((short)0x54, "iget-object", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case IGET_BOOLEAN://((short)0x55, "iget-boolean", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case IGET_BYTE://((short)0x56, "iget-byte", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case IGET_CHAR://((short)0x57, "iget-char", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case IGET_SHORT:
        		Clause cl7 = new Clause();
				cl7.appendHead("(and " + 
    			refClassElement.hPred("cn", "v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()), 
    					Utils.hexDec64(referenceIntIndex, size), "val", "lval", "bval") +
						' ' + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) +
						")");
				regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "val");
				regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "lval");
				regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "bval");
        		cl7.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
				gen.addClause(cl7);
        		
        		break;//((short)0x58, "iget-short", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case IPUT://((short)0x59, "iput", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_WIDE://((short)0x5a, "iput-wide", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_OBJECT://((short)0x5b, "iput-object", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_BOOLEAN://((short)0x5c, "iput-boolean", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_BYTE://((short)0x5d, "iput-byte", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_CHAR://((short)0x5e, "iput-char", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_SHORT:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdateL.put(((TwoRegisterInstruction)instruction).getRegisterB(), "(or " + 'l' + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB())
        				+ ' ' +  'l' + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ")");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		regUpdateL.clear();
        		cl2.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
        				+ ' ' + refClassElement.hPred("cn", "v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()), "f", Utils.hexDec64(0, size), "lf", "bf") +')');
        		cl2.appendBody(refClassElement.hPred("cn", "v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()), 
        				Utils.hexDec64(referenceIntIndex, size), 
        				'v'+ Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()), 'l'+Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()),
        				'b'+Integer.toString(((OneRegisterInstruction)instruction).getRegisterA())));
        		gen.addClause(cl2);
        		
        		break;//((short)0x5f, "iput-short", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case SGET://((short)0x60, "sget", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SGET_WIDE://((short)0x61, "sget-wide", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case SGET_OBJECT://((short)0x62, "sget-object", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SGET_BOOLEAN://((short)0x63, "sget-boolean", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SGET_BYTE://((short)0x64, "sget-byte", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SGET_CHAR://((short)0x65, "sget-char", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SGET_SHORT:
        		cl.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) + 
        				' ' + "(S " + Integer.toString(refClassElement.staticFieldLookup(classDefs, indStr, referenceClassIndex, referenceIntIndex)) + ' ' + Integer.toString(referenceIntIndex) + " f lf bf))");
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "f");
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "lf");
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "bf");
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl2.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) 
        				);
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), Utils.hexDec64(0, size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "false");
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), "bf");
        		cl2.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl2);
        		
        		break;//((short)0x66, "sget-short", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SPUT://((short)0x67, "sput", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case SPUT_WIDE://((short)0x68, "sput-wide", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case SPUT_OBJECT://((short)0x69, "sput-object", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case SPUT_BOOLEAN://((short)0x6a, "sput-boolean", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case SPUT_BYTE://((short)0x6b, "sput-byte", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case SPUT_CHAR://((short)0x6c, "sput-char", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case SPUT_SHORT:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		cl3.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		cl3.appendBody("(S " + Integer.toString(refClassElement.staticFieldLookup(classDefs, indStr, referenceClassIndex, referenceIntIndex)) + ' ' + Integer.toString(referenceIntIndex) + " v" + 
        				Integer.toString(((OneRegisterInstruction)instruction).getRegisterA())
        				+ " l" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) +  " b" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ')');
        		gen.addClause(cl3);
        		break;//((short)0x6d, "sput-short", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case INVOKE_VIRTUAL:
        	case INVOKE_SUPER:
        	case INVOKE_INTERFACE: 
        		
        		if ((referenceIntIndex == indStr.get("execute(Ljava/lang/Runnable;)V", 'm')) && (referenceClassIndex == indStr.get("Ljava/util/concurrent/ExecutorService;", 'c'))){
        			implementations = refClassElement.getImplementations(indStr.get("Ljava/lang/Runnable;", 'c'), indStr.get("run()V", 'm'), classDefs, indStr, gen);
        			isDefined = !implementations.isEmpty();
            		FiveRegisterInstruction instr = (FiveRegisterInstruction)this.instruction;	
            		if (isDefined){
            			for (Map.Entry<Integer, Integer> entry : implementations.entrySet()){
            				numRegCall = numLoc.get(entry.getValue(), indStr.get("run()V", 'm'));
            				Clause cl10  = new Clause();
                			Clause cl12 = new Clause();
                			cl10.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) + 
                					" (= v" + Integer.toString(instr.getRegisterD()) + ' ' + 
                					Utils.hexDec64(entry.getKey(), size) + "))");
                			
                			numArgCall = numLoc.getp(entry.getValue(), indStr.get("run()V", 'm'));
                			
                			regUpdate = updateReg(numRegCall, numArgCall, 'v', false);
                			regUpdateL = updateReg(numRegCall, numArgCall, 'l', false);
                			regUpdateB = updateReg(numRegCall, numArgCall, 'b', false);
                			
                			
                			cl10.appendBody(refClassElement.rInvokePred(Integer.toString(entry.getValue()), Integer.toString(indStr.get("run()V", 'm')), 0,  
                    				regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, gen, size));
                			gen.addClause(cl10);
                			regUpdate.clear();
                    		regUpdateL.clear();
                    		regUpdateB.clear();
                			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                			cl12.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                			gen.addClause(cl12);
            			}
            		}
            		else{
            			Clause cl12 = new Clause();
            			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
            			cl12.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
            			gen.addClause(cl12);
            		}
        			break;
        		}
        		
        		if (referenceIntIndex == indStr.get("start()V", 'm')){
        			implementations = refClassElement.getImplementations(referenceClassIndex, indStr.get("run()V", 'm'), classDefs, indStr, gen);
        		}
        		else{
        			if (referenceIntIndex == indStr.get("execute([Ljava/lang/Object;)Landroid/os/AsyncTask;", 'm')){
        				implementations = refClassElement.getImplementations(referenceClassIndex, indStr.get("doInBackground([Ljava/lang/Object;)Ljava/lang/Object;", 'm'), classDefs, indStr, gen);
        			}
        			else{
        				implementations = refClassElement.getImplementations(referenceClassIndex, referenceIntIndex, classDefs, indStr, gen);
        			}
        		}
        		isDefined = !implementations.isEmpty();
        		FiveRegisterInstruction instr = (FiveRegisterInstruction)this.instruction;	
        		if (isDefined){
        			for (Map.Entry<Integer, Integer> entry : implementations.entrySet()){
            			if ((Utils.isThread(classDefs, entry.getValue(), indStr)) && (referenceIntIndex == indStr.get("start()V", 'm')))

            				numRegCall = numLoc.get(entry.getValue(), indStr.get("run()V", 'm'));
            			else{
            				if ((Utils.isThread(classDefs, entry.getValue(), indStr)) && (referenceIntIndex == indStr.get("execute([Ljava/lang/Object;)Landroid/os/AsyncTask;", 'm'))){
            					numRegCall = numLoc.get(entry.getValue(), indStr.get("doInBackground([Ljava/lang/Object;)Ljava/lang/Object;", 'm'));
            				}
            				else{
            					numRegCall = numLoc.get(entry.getValue(), referenceIntIndex);
            				}
            			}
        				//numArgCall = instr.getRegisterCount();
        				if (numRegCall == 0)
                			numRegCallp = instr.getRegisterCount();
                		else numRegCallp = numRegCall;
                		if (gen.isSink(entry.getValue(), referenceIntIndex))
                			addQuery(gen, refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen), className, methodName, Integer.toString(codeAddress), referenceString, options);
                		
        				//int referenceReg = numRegCall - instr.getRegisterCount();
        				referenceReg = instr.getRegisterC();//range	instruction.getStartRegister()
            			Clause cl10  = new Clause();
            			Clause cl12 = new Clause();
            			regUpdate.clear();
                		regUpdateL.clear();
                		regUpdateB.clear();
                		
            			cl10.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) + 
            					" (= v" + Integer.toString(referenceReg) + ' ' + 
            					Utils.hexDec64(entry.getKey(), size) + "))");
            			
            			if ((Utils.isThread(classDefs, entry.getValue(), indStr)) && (referenceIntIndex == indStr.get("start()V", 'm')))
            				numArgCall = numLoc.getp(entry.getValue(), indStr.get("run()V", 'm'));
            			else{
            				if ((Utils.isThread(classDefs, entry.getValue(), indStr)) && (referenceIntIndex == indStr.get("execute([Ljava/lang/Object;)Landroid/os/AsyncTask;", 'm'))){
            					numArgCall = numLoc.getp(entry.getValue(), indStr.get("doInBackground([Ljava/lang/Object;)Ljava/lang/Object;", 'm'));
            				}
            				else{
            					numArgCall = numLoc.getp(entry.getValue(), referenceIntIndex);
            				}
            			}
            			regUpdate = updateReg(numRegCall, numArgCall, 'v', false);
            			regUpdateL = updateReg(numRegCall, numArgCall, 'l', false);
            			regUpdateB = updateReg(numRegCall, numArgCall, 'b', false);
            			
            			if ((Utils.isThread(classDefs, entry.getValue(), indStr)) && (referenceIntIndex == indStr.get("start()V", 'm'))){
            				cl10.appendBody(refClassElement.rInvokePred(Integer.toString(entry.getValue()), Integer.toString(indStr.get("run()V", 'm')), 0,  
                    				regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, gen, size));
            			}
            			else{
            				if ((Utils.isThread(classDefs, entry.getValue(), indStr)) && (referenceIntIndex == indStr.get("execute([Ljava/lang/Object;)Landroid/os/AsyncTask;", 'm'))){
                				cl10.appendBody(refClassElement.rInvokePred(Integer.toString(entry.getValue()), Integer.toString(indStr.get("doInBackground([Ljava/lang/Object;)Ljava/lang/Object;", 'm')), 0,  
                        				regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, gen, size));
            				}
                			else{
            				cl10.appendBody(refClassElement.rInvokePred(Integer.toString(entry.getValue()), Integer.toString(referenceIntIndex), 0,  
                				regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, gen, size));
                			}
            			}
                		regUpdate.clear();
                		regUpdateL.clear();
                		regUpdateB.clear();
                		gen.addClause(cl10);
            			
                		
                		if (callReturns){
                			head = "(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen);
                			regUpdate = updateRes(numRegCall, numArgCall, 'v', false);
                			regUpdateL = updateRes(numRegCall, numArgCall, 'l', false);
                			regUpdateB = updateRes(numRegCall, numArgCall, 'b', false);
                			regUpdate.put(numArgCall, "rez");
                			regUpdateL.put(numArgCall, "lrez");
                			regUpdateB.put(numArgCall, "brez");
                			head = head + ' ' + refClassElement.resPred(Integer.toString(entry.getValue()), referenceIndex, regUpdate, regUpdateL, regUpdateB, numArgCall, gen) +
                					" (= v" + Integer.toString(referenceReg) + ' ' + 
                					Utils.hexDec64(entry.getKey(), size) + "))";
                		}
                		else{
                			head = refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen);
                		}
            			cl12.appendHead(head);
            			regUpdate.clear();
                		regUpdateL.clear();
                		regUpdateB.clear();
            			if (gen.isSource(entry.getValue(), referenceIntIndex)) returnLabel = "true"; else returnLabel = "lrez";
            			if (callReturns) {
            				regUpdate.put(numRegLoc, "rez");
            				regUpdateL.put(numRegLoc, returnLabel);
            			}
            			cl12.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
            			gen.addClause(cl12);
            			regUpdate.clear();
                		regUpdateL.clear();
                		regUpdateB.clear();
            		}
        		}
        		else{
        			if (processIntent(ci, mi, numParLoc, numRegLoc, nextCode, referenceClassIndex, referenceIntIndex, gen, referenceString, classDefs, indStr, refClassElement, size))
        				break;
        			numRegCall = numLoc.get(referenceClassIndex, referenceIntIndex);
    				if (numRegCall == 0)
            			numRegCallp = instr.getRegisterCount();
            		else numRegCallp = numRegCall;
            		if (gen.isSink(referenceClassIndex, referenceIntIndex))
            			addQuery(gen, refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen), className, methodName, Integer.toString(codeAddress), referenceString, options);
            		
        			head = refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen);
        			cl.appendHead(head);
        			if (gen.isSource(referenceClassIndex, referenceIntIndex)) returnLabel = "true"; else returnLabel = getLabels();
        			
        			
        			
        			if (returnType.equals((String)"Ljava/lang/String;")){
        				regUpdate.put(numRegLoc, "f");
						regUpdateL.put(numRegLoc, returnLabel);
						regUpdateB.put(numRegLoc, "true");
        			}
        			else{
        			if ((returnType.charAt(0) != '[') && (returnType.charAt(returnType.length() -1) == ';' )){
        				instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
                		
					    fields = refClassElement.getClassFields(classDefs, indStr, returnType, instanceNum);
					    
					    if (fields != null)
                		for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                			Clause cl12 = new Clause();
                			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(returnTypeInt, size), "fpp", Utils.hexDec64(fieldN.getKey(), size), "vfp", returnLabel, 
                					Boolean.toString(fieldN.getValue())));
                			gen.addClause(cl12);
                		}
					    else{
					    	Clause cl12 = new Clause();
                			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(returnTypeInt, size), "fpp", "f", "vfp", returnLabel, 
                					"bf"));
                			gen.addClause(cl12);
					    }
                		regUpdate.put(numRegLoc, "fpp");
            			regUpdateL.put(numRegLoc, returnLabel);
            			regUpdateB.put(numRegLoc, "true");
        			}
        			else{
        				switch (returnType){
        				case "V": break;
        					case "Z": case "B": case "S": case "C": case "I": case "J": case "F": case "D":
        						regUpdate.put(numRegLoc, "f");
        						regUpdateL.put(numRegLoc, returnLabel);
        						regUpdateB.put(numRegLoc, "false");
        						break;
        					default: //array
        						instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
        						Clause cl12 = new Clause();
                    			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                    			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(returnTypeInt, size), Utils.hexDec64(instanceNum, size), "f", "buf", returnLabel, "bf"));
                    			gen.addClause(cl12);
                        		regUpdate.put(numRegLoc, Utils.hexDec64(instanceNum, size));
                    			regUpdateL.put(numRegLoc, returnLabel);
                    			regUpdateB.put(numRegLoc, "true");

        				}
        			}
        			}
        			regUpdateL = highReg(false, regUpdateL);
        			cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        			gen.addClause(cl);
        			
        		}
        		break;
        	case INVOKE_DIRECT:
        	case INVOKE_STATIC:
        		//we do a resolution on thread init, not on thread start, as at thread start the class information is lost 
        		//(it is stored somewhere in the thread class by the operating system, we can also simulate that storing class name somewhere). 
        		//on the other hand, if one initializes the thread and never spawns it? rare
        		//JavaThread2 for the reference
        		if ((referenceIntIndex == indStr.get("<init>(Ljava/lang/Runnable;)V", 'm')) && (referenceClassIndex == indStr.get("Ljava/lang/Thread;", 'c'))){
        			implementations = refClassElement.getImplementations(indStr.get("Ljava/lang/Runnable;", 'c'), indStr.get("run()V", 'm'), classDefs, indStr, gen);
        			isDefined = !implementations.isEmpty();
            		FiveRegisterInstruction instr2 = (FiveRegisterInstruction)this.instruction;	
            		if (isDefined){
            			for (Map.Entry<Integer, Integer> entry : implementations.entrySet()){
            				numRegCall = numLoc.get(entry.getValue(), indStr.get("run()V", 'm'));
            				Clause cl10  = new Clause();
                			cl10.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) + 
                					" (= v" + Integer.toString(instr2.getRegisterD()) + ' ' + 
                					Utils.hexDec64(entry.getKey(), size) + "))");
                			
                			numArgCall = numLoc.getp(entry.getValue(), indStr.get("run()V", 'm'));
                			
                			regUpdate.put(numRegCall - numArgCall + 0, 'v' + Integer.toString(instr2.getRegisterD())); 
                        	regUpdate.put(numRegCall + 1 + 0, 'v' + Integer.toString(instr2.getRegisterD()));
                        	regUpdateL.put(numRegCall - numArgCall + 0, 'l' + Integer.toString(instr2.getRegisterD())); 
                        	regUpdateL.put(numRegCall + 1 + 0, 'l' + Integer.toString(instr2.getRegisterD()));
                        	regUpdateB.put(numRegCall - numArgCall + 0, 'b' + Integer.toString(instr2.getRegisterD())); 
                        	regUpdateB.put(numRegCall + 1 + 0, 'b' + Integer.toString(instr2.getRegisterD()));
                			
                			
                			cl10.appendBody(refClassElement.rInvokePred(Integer.toString(entry.getValue()), Integer.toString(indStr.get("run()V", 'm')), 0,  
                    				regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, gen, size));
                			gen.addClause(cl10);
                			
                			regUpdate.clear();
                			regUpdateL.clear();
                			regUpdateB.clear();
            			}
            		}
            		else{
            		}
        		}
        		
        		FiveRegisterInstruction instr2 = (FiveRegisterInstruction)this.instruction;
        		numRegCall = numLoc.get(referenceClassIndex, referenceIntIndex);
        		if (numRegCall == 0)
        			numRegCallp = instr2.getRegisterCount();
        		else numRegCallp = numRegCall;
        		//numArgCall = instr2.getRegisterCount();
				numArgCall = numLoc.getp(referenceClassIndex, referenceIntIndex);

        		if (gen.isSink(referenceClassIndex, referenceIntIndex))
        			addQuery(gen, refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen), className, methodName, Integer.toString(codeAddress), referenceString, options);
        			/*for (int i = 0; i < numRegCallp; i++){
        				gen.addQuery("(query (and " + "(P_" + referenceStringClassIndex + '_' + referenceIndex + '_' + 
        							Integer.toString(0) + getRegsDefs(referenceClassIndex, referenceIntIndex, 0, gen, regUpdate, regUpdateL, callReturns, numRegCall) 
        							+ " (= l" + Integer.toString(i) + " true)"
        							+ ")\n :unbound-compressor false \n)");
        			}*/
        		regUpdate.clear();
        		regUpdateL.clear();
        		regUpdateB.clear();
        		cl2.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));  
        		
        		regUpdate = updateReg(numRegCall, numArgCall, 'v', false);
    			regUpdateL = updateReg(numRegCall, numArgCall, 'l', false);
    			regUpdateB = updateReg(numRegCall, numArgCall, 'b', false);
        		cl2.appendBody(refClassElement.rInvokePred(referenceStringClassIndex, referenceIndex, 0, regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, gen, size));
        		regUpdate.clear();
        		regUpdateL.clear();
        		regUpdateB.clear();
        		gen.addClause(cl2);
        		if (gen.isDefined(referenceClassIndex, referenceIntIndex)){
            		
            		if (callReturns){
            			head = "(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen);
            			regUpdate = updateRes(numRegCall, numArgCall, 'v', false);
            			regUpdateL = updateRes(numRegCall, numArgCall, 'l', false);
            			regUpdateB = updateRes(numRegCall, numArgCall, 'b', false);
            			regUpdate.put(numArgCall, "rez");
            			regUpdateL.put(numArgCall, "lrez");
            			regUpdateB.put(numArgCall, "brez");
            			head = head + ' ' +  refClassElement.resPred(referenceStringClassIndex,
            					referenceIndex, regUpdate, regUpdateL, regUpdateB, numArgCall, gen) + ')';
            			
            		}
            		else{
            			head = refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen);
            		}
        			cl.appendHead(head);
        			regUpdate.clear();
            		regUpdateL.clear();
            		regUpdateB.clear();
        			if (gen.isSource(referenceClassIndex, referenceIntIndex)) returnLabel = "true"; else returnLabel = "lrez";
        			if (callReturns) {
        				regUpdate.put(numRegLoc, "rez");
        				regUpdateL.put(numRegLoc, returnLabel);
        			}
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		}
        		else{  
        			if (processIntent(ci, mi, numParLoc, numRegLoc, nextCode, referenceClassIndex, referenceIntIndex, gen, referenceString, classDefs, indStr, refClassElement, size))
        				break;
        			head = refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen);
        			cl.appendHead(head);
        			if (gen.isSource(referenceClassIndex, referenceIntIndex)) returnLabel = "true"; else returnLabel = getLabels();
        			
        			if (returnType.equals((String)"Ljava/lang/String;")){
        				regUpdate.put(numRegLoc, "f");
						regUpdateL.put(numRegLoc, returnLabel);
						regUpdateB.put(numRegLoc, "true");
        			}
        			else{
        			if ((returnType.charAt(0) != '[') && (returnType.charAt(returnType.length() -1) == ';' )){
        				instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
							fields = refClassElement.getClassFields(classDefs, indStr, returnType, instanceNum);
						if (fields != null)
                		for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                			Clause cl12 = new Clause();
                			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(returnTypeInt, size), "fpp", Utils.hexDec64(fieldN.getKey(), size), "vfp", returnLabel, Boolean.toString(fieldN.getValue())));
                			gen.addClause(cl12);
                			
                		}
						else{
							Clause cl12 = new Clause();
                			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(returnTypeInt, size), "fpp", "f", "vfp", returnLabel, "bf"));
                			gen.addClause(cl12);
						}
                		regUpdate.put(numRegLoc, "fpp");
            			regUpdateL.put(numRegLoc, returnLabel);
            			regUpdateB.put(numRegLoc, "true");
        			}
        			else{
        				switch (returnType){
        				case "V": break;
        					case "Z": case "B": case "S": case "C": case "I": case "J": case "F": case "D":
        						regUpdate.put(numRegLoc, "f");
        						regUpdateL.put(numRegLoc, returnLabel);
        						regUpdateB.put(numRegLoc, "false");
        						break;
        					default: //array
        						instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
                        		
                    			Clause cl12 = new Clause();
                    			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                    			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(returnTypeInt, size), Utils.hexDec64(instanceNum, size), "f", "buf", returnLabel, "bf"));
                    			gen.addClause(cl12);
                    			regUpdate.put(numRegLoc, Utils.hexDec64(instanceNum, size));
                    			regUpdateL.put(numRegLoc, returnLabel);
                    			regUpdateB.put(numRegLoc, "true");

        				}
        			}
        			}
        			regUpdateL = highReg(false, regUpdateL);
        			cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		}
        		gen.addClause(cl);
        		break;//((short)0x6e, "invoke-virtual", ReferenceType.METHOD, Format.Format35c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        	case INVOKE_VIRTUAL_RANGE:
        	case INVOKE_SUPER_RANGE:
        	case INVOKE_INTERFACE_RANGE:
        		implementations = refClassElement.getImplementations(referenceClassIndex, referenceIntIndex, classDefs, indStr, gen);
        		isDefined = !implementations.isEmpty();
        		RegisterRangeInstruction instr3 = (RegisterRangeInstruction)this.instruction;	
        		if (isDefined){
        			for (Map.Entry<Integer, Integer> entry : implementations.entrySet()){
        				numRegCall = numLoc.get(entry.getValue(), referenceIntIndex);
        				//numArgCall = instr.getRegisterCount();
        				if (numRegCall == 0)
                			numRegCallp = instr3.getRegisterCount();
                		else numRegCallp = numRegCall;
                		if (gen.isSink(entry.getValue(), referenceIntIndex))
                			addQueryRange(gen, refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen), className, methodName, Integer.toString(codeAddress), referenceString, options);
                		
        				//int referenceReg = numRegCall - instr.getRegisterCount();
        				referenceReg = instr3.getStartRegister();//range	instruction.getStartRegister()
            			Clause cl10  = new Clause();
            			Clause cl12 = new Clause();
            			regUpdate.clear();
                		regUpdateL.clear();
                		regUpdateB.clear();
            			cl10.appendHead("(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) + 
            					" (= v" + Integer.toString(referenceReg) + ' ' + 
            					Utils.hexDec64(entry.getKey(), size) + "))");  
        				numArgCall = numLoc.getp(entry.getValue(), referenceIntIndex);

            			regUpdate = updateReg(numRegCall, numArgCall, 'v', true);
            			regUpdateL = updateReg(numRegCall, numArgCall, 'l', true);
            			regUpdateB = updateReg(numRegCall, numArgCall, 'b', true);
                		cl10.appendBody(refClassElement.rInvokePred(Integer.toString(entry.getValue()), Integer.toString(referenceIntIndex), 0,  
                				regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, gen, size));
                		regUpdate.clear();
                		regUpdateL.clear();
                		regUpdateB.clear();
                		gen.addClause(cl10);
                		
                		
                		if (callReturns){
                			head = "(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen);
                			regUpdate = updateRes(numRegCall, numArgCall, 'v', true);
                			regUpdateL = updateRes(numRegCall, numArgCall, 'l', true);
                			regUpdateB = updateRes(numRegCall, numArgCall, 'b', true);
                			regUpdate.put(numArgCall, "rez");
                			regUpdateL.put(numArgCall, "lrez");
                			regUpdateB.put(numArgCall, "brez");
                			head = head + ' ' + refClassElement.resPred(Integer.toString(entry.getValue()), referenceIndex, regUpdate, regUpdateL, regUpdateB, numArgCall, gen) +
                					" (= v" + Integer.toString(referenceReg) + ' ' + 
                					Utils.hexDec64(entry.getKey(), size) + "))";
                		}
                		else{
                			head = refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen);
                		}
            			cl12.appendHead(head);
            			regUpdate.clear();
                		regUpdateL.clear();
                		regUpdateB.clear();
            			if (gen.isSource(entry.getValue(), referenceIntIndex)) returnLabel = "true"; else returnLabel = "lrez";
            			if (callReturns) {
            				regUpdate.put(numRegLoc, "rez");
            				regUpdateL.put(numRegLoc, returnLabel);
            			}
            			cl12.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
            			gen.addClause(cl12);
            			regUpdate.clear();
                		regUpdateL.clear();
                		regUpdateB.clear();
            		}
        		}
        		else{
        			numRegCall = numLoc.get(referenceClassIndex, referenceIntIndex);
    				if (numRegCall == 0)
            			numRegCallp = instr3.getRegisterCount();
            		else numRegCallp = numRegCall;
            		if (gen.isSink(referenceClassIndex, referenceIntIndex))
            			addQueryRange(gen, refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen), className, methodName, Integer.toString(codeAddress), referenceString, options);
            		
        			head = refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen);
        			cl.appendHead(head);
        			if (gen.isSource(referenceClassIndex, referenceIntIndex)) returnLabel = "true"; else returnLabel = getLabelsRange();
        			
        			if (returnType.equals((String)"Ljava/lang/String;")){
        				regUpdate.put(numRegLoc, "f");
						regUpdateL.put(numRegLoc, returnLabel);
						regUpdateB.put(numRegLoc, "true");
        			}
        			else{
        			if ((returnType.charAt(0) != '[') && (returnType.charAt(returnType.length() -1) == ';' )){
        				instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
                		
					    fields = refClassElement.getClassFields(classDefs, indStr, returnType, instanceNum);
					    if (fields != null)
                		for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                			Clause cl12 = new Clause();
                			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(returnTypeInt, size), "fpp", Utils.hexDec64(fieldN.getKey(), size), "vfp", returnLabel, 
                					Boolean.toString(fieldN.getValue())));
                			gen.addClause(cl12);
                		}
					    else{
					    	Clause cl12 = new Clause();
                			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(returnTypeInt, size), "fpp", "f", "vfp", returnLabel, 
                					"bf"));
                			gen.addClause(cl12);
					    }
                		regUpdate.put(numRegLoc, "fpp");
            			regUpdateL.put(numRegLoc, returnLabel);
            			regUpdateB.put(numRegLoc, "true");
        			}
        			else{
        				switch (returnType){
        				case "V": break;
        					case "Z": case "B": case "S": case "C": case "I": case "J": case "F": case "D":
        						regUpdate.put(numRegLoc, "f");
        						regUpdateL.put(numRegLoc, returnLabel);
        						regUpdateB.put(numRegLoc, "false");
        						break;
        					default: //array
        						instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
        						Clause cl12 = new Clause();
                    			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                    			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(returnTypeInt, size), Utils.hexDec64(instanceNum, size), "f", "buf", returnLabel, "bf"));
                    			gen.addClause(cl12);
                        		regUpdate.put(numRegLoc, Utils.hexDec64(instanceNum, size));
                    			regUpdateL.put(numRegLoc, returnLabel);
                    			regUpdateB.put(numRegLoc, "true");

        				}
        			}
        			}
        			regUpdateL = highReg(true, regUpdateL);
        			cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        			gen.addClause(cl);
        			
        		}
        		break;
        	case INVOKE_DIRECT_RANGE:
        	case INVOKE_STATIC_RANGE:
        		RegisterRangeInstruction instr4 = (RegisterRangeInstruction)this.instruction;
        		numRegCall = numLoc.get(referenceClassIndex, referenceIntIndex);
        		if (numRegCall == 0)
        			numRegCallp = instr4.getRegisterCount();
        		else numRegCallp = numRegCall;
        		//numArgCall = instr2.getRegisterCount();
				numArgCall = numLoc.getp(referenceClassIndex, referenceIntIndex);

        		if (gen.isSink(referenceClassIndex, referenceIntIndex))
        			addQueryRange(gen, refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen), className, methodName, Integer.toString(codeAddress), referenceString, options);
        			/*for (int i = 0; i < numRegCallp; i++){
        				gen.addQuery("(query (and " + "(P_" + referenceStringClassIndex + '_' + referenceIndex + '_' + 
        							Integer.toString(0) + getRegsDefs(referenceClassIndex, referenceIntIndex, 0, gen, regUpdate, regUpdateL, callReturns, numRegCall) 
        							+ " (= l" + Integer.toString(i) + " true)"
        							+ ")\n :unbound-compressor false \n)");
        			}*/
        		regUpdate.clear();
        		regUpdateL.clear();
        		regUpdateB.clear();
        		cl2.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));  
        		
        		regUpdate = updateReg(numRegCall, numArgCall, 'v', true);
    			regUpdateL = updateReg(numRegCall, numArgCall, 'l', true);
    			regUpdateB = updateReg(numRegCall, numArgCall, 'b', true);
        		cl2.appendBody(refClassElement.rInvokePred(referenceStringClassIndex, referenceIndex, 0, regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, gen, size));
        		regUpdate.clear();
        		regUpdateL.clear();
        		regUpdateB.clear();
        		gen.addClause(cl2);
        		if (gen.isDefined(referenceClassIndex, referenceIntIndex)){
            		
            		if (callReturns){
            			head = "(and " + refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen);
            			regUpdate = updateRes(numRegCall, numArgCall, 'v', true);
            			regUpdateL = updateRes(numRegCall, numArgCall, 'l', true);
            			regUpdateB = updateRes(numRegCall, numArgCall, 'b', true);
            			regUpdate.put(numArgCall, "rez");
            			regUpdateL.put(numArgCall, "lrez");
            			regUpdateB.put(numArgCall, "brez");
            			head = head + ' ' +  refClassElement.resPred(referenceStringClassIndex,
            					referenceIndex, regUpdate, regUpdateL, regUpdateB, numArgCall, gen) + ')';
            		
            		}
            		else{
            			head = refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen);
            		}
        			cl.appendHead(head);
        			regUpdate.clear();
            		regUpdateL.clear();
            		regUpdateB.clear();
        			if (gen.isSource(referenceClassIndex, referenceIntIndex)) returnLabel = "true"; else returnLabel = "lrez";
        			if (callReturns) {
        				regUpdate.put(numRegLoc, "rez");
        				regUpdateL.put(numRegLoc, returnLabel);
        			}
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		}
        		else{            		
        			head = refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen);
        			cl.appendHead(head);
        			if (gen.isSource(referenceClassIndex, referenceIntIndex)) returnLabel = "true"; else returnLabel = getLabelsRange();
        			
        			if (returnType.equals((String)"Ljava/lang/String;")){
        				regUpdate.put(numRegLoc, "f");
						regUpdateL.put(numRegLoc, returnLabel);
						regUpdateB.put(numRegLoc, "true");
        			}
        			else{
        			if ((returnType.charAt(0) != '[') && (returnType.charAt(returnType.length() -1) == ';' )){
        				instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
							fields = refClassElement.getClassFields(classDefs, indStr, returnType, instanceNum);
                		if (fields != null)
							for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                			Clause cl12 = new Clause();
                			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(returnTypeInt, size), "fpp", Utils.hexDec64(fieldN.getKey(), size), "vfp", returnLabel, Boolean.toString(fieldN.getValue())));
                			gen.addClause(cl12);
                			
                		}
                		else{
                			Clause cl12 = new Clause();
                			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(returnTypeInt, size), "fpp", "f", "vfp", returnLabel, "bf"));
                			gen.addClause(cl12);
                		}
                		regUpdate.put(numRegLoc, "fpp");
            			regUpdateL.put(numRegLoc, returnLabel);
            			regUpdateB.put(numRegLoc, "true");
        			}
        			else{
        				switch (returnType){
        				case "V": break;
        					case "Z": case "B": case "S": case "C": case "I": case "J": case "F": case "D":
        						regUpdate.put(numRegLoc, "f");
        						regUpdateL.put(numRegLoc, returnLabel);
        						regUpdateB.put(numRegLoc, "false");
        						break;
        					default: //array
        						instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
                        		
                    			Clause cl12 = new Clause();
                    			cl12.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
                    			cl12.appendBody(refClassElement.hPred(Utils.hexDec64(returnTypeInt, size), Utils.hexDec64(instanceNum, size), "f", "buf", returnLabel, "bf"));
                    			gen.addClause(cl12);
                    			regUpdate.put(numRegLoc, Utils.hexDec64(instanceNum, size));
                    			regUpdateL.put(numRegLoc, returnLabel);
                    			regUpdateB.put(numRegLoc, "true");

        				}
        			}
        			}
        			regUpdateL = highReg(true, regUpdateL);
        			cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		}
        		gen.addClause(cl);
        		break;//((short)0x74, "invoke-virtual/range", ReferenceType.METHOD, Format.Format3rc, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        	case NEG_INT://((short)0x7b, "neg-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case NEG_LONG://((short)0x7d, "neg-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case NEG_FLOAT://((short)0x7f, "neg-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case NEG_DOUBLE:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvneg v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0x80, "neg-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case NOT_INT://((short)0x7c, "not-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case NOT_LONG:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvnot v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0x7e, "not-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case INT_TO_LONG://((short)0x81, "int-to-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case INT_TO_FLOAT://((short)0x82, "int-to-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case INT_TO_DOUBLE://((short)0x83, "int-to-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case LONG_TO_INT://((short)0x84, "long-to-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case LONG_TO_FLOAT://((short)0x85, "long-to-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case LONG_TO_DOUBLE://((short)0x86, "long-to-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case FLOAT_TO_INT://((short)0x87, "float-to-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case FLOAT_TO_LONG://((short)0x88, "float-to-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case FLOAT_TO_DOUBLE://((short)0x89, "float-to-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case DOUBLE_TO_INT://((short)0x8a, "double-to-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case DOUBLE_TO_LONG://((short)0x8b, "double-to-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case DOUBLE_TO_FLOAT://((short)0x8c, "double-to-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case INT_TO_BYTE://((short)0x8d, "int-to-byte", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case INT_TO_CHAR://((short)0x8e, "int-to-char", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case INT_TO_SHORT:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0x8f, "int-to-short", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case ADD_INT://((short)0x90, "add-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case ADD_LONG://((short)0x9b, "add-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case ADD_FLOAT://((short)0xa6, "add-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case ADD_DOUBLE:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvadd v" + 
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + " v" +
        				Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), 
        				"(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0xab, "add-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case SUB_INT://((short)0x91, "sub-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SUB_LONG://((short)0x9c, "sub-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case SUB_FLOAT://((short)0xa7, "sub-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SUB_DOUBLE:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvsub v" + 
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + " v" +
        				Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
        				"(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		break;//((short)0xac, "sub-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case MUL_INT://((short)0x92, "mul-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MUL_LONG://((short)0x9d, "mul-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case MUL_FLOAT://((short)0xa8, "mul-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MUL_DOUBLE:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvmul v" + 
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + " v" +
        				Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xad, "mul-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case DIV_INT://((short)0x93, "div-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case DIV_LONG://((short)0x9e, "div-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case DIV_FLOAT://((short)0xa9, "div-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case DIV_DOUBLE:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvudiv v" + 
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + " v" +
        				Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xae, "div-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case REM_INT://((short)0x94, "rem-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case REM_LONG://((short)0x9f, "rem-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case REM_FLOAT://((short)0xaa, "rem-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case REM_DOUBLE:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvurem v" + 
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + " v" +
        				Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xaf, "rem-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case AND_INT://((short)0x95, "and-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case AND_LONG:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvand v" + 
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + " v" +
        				Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xa0, "and-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case OR_INT://((short)0x96, "or-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case OR_LONG:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvor v" + 
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + " v" +
        				Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xa1, "or-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case XOR_INT://((short)0x97, "xor-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case XOR_LONG:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvxor v" + 
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + " v" +
        				Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xa2, "xor-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case SHL_INT://((short)0x98, "shl-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SHL_LONG:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvshl v" + 
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + " v" +
        				Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xa3, "shl-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case SHR_LONG://((short)0xa4, "shr-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case SHR_INT:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvashr v" + 
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + " v" +
        				Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0x99, "shr-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	
        	case USHR_INT://((short)0x9a, "ushr-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case USHR_LONG:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvlshr v" + 
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + " v" +
        				Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((ThreeRegisterInstruction) instruction).getRegisterC()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xa5, "ushr-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case ADD_INT_2ADDR://((short)0xb0, "add-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case ADD_LONG_2ADDR://((short)0xc0, "and-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case ADD_FLOAT_2ADDR://((short)0xc6, "add-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case ADD_DOUBLE_2ADDR:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvadd v" + 
        				Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), 
        				"(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xcb, "add-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case SUB_INT_2ADDR://((short)0xb1, "sub-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SUB_LONG_2ADDR://((short)0xbc, "sub-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case SUB_FLOAT_2ADDR://((short)0xc7, "sub-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SUB_DOUBLE_2ADDR:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvsub v" + 
        				Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xcc, "sub-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case MUL_INT_2ADDR://((short)0xb2, "mul-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MUL_LONG_2ADDR://((short)0xbd, "mul-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case MUL_FLOAT_2ADDR://((short)0xc8, "mul-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MUL_DOUBLE_2ADDR:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvmul v" + 
        				Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xcd, "mul-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case DIV_INT_2ADDR://((short)0xb3, "div-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case DIV_LONG_2ADDR://((short)0xbe, "div-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case DIV_FLOAT_2ADDR://((short)0xc9, "div-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case DIV_DOUBLE_2ADDR:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvudiv v" + 
        				Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xce, "div-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case REM_INT_2ADDR://((short)0xb4, "rem-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case REM_LONG_2ADDR://((short)0xbf, "rem-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case REM_FLOAT_2ADDR://((short)0xca, "rem-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case REM_DOUBLE_2ADDR:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvurem v" + 
        				Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xcf, "rem-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case AND_INT_2ADDR://((short)0xb5, "and-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case AND_LONG_2ADDR:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvand v" + 
        				Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xbb, "add-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case OR_INT_2ADDR://((short)0xb6, "or-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case OR_LONG_2ADDR:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvor v" + 
        				Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xc1, "or-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case XOR_INT_2ADDR://((short)0xb7, "xor-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case XOR_LONG_2ADDR:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvxor v" + 
        				Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xc2, "xor-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case SHL_INT_2ADDR://((short)0xb8, "shl-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SHL_LONG_2ADDR:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvshl v" + 
        				Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xc3, "shl-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case SHR_INT_2ADDR://((short)0xb9, "shr-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SHR_LONG_2ADDR:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvashr v" + 
        				Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xc4, "shr-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case USHR_INT_2ADDR://((short)0xba, "ushr-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case USHR_LONG_2ADDR:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvlshr v" + 
        				Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + " v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "(or l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + 
        				" l" + Integer.toString(((OneRegisterInstruction)instruction).getRegisterA()) + ')');
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xc5, "ushr-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case ADD_INT_LIT16://((short)0xd0, "add-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case ADD_INT_LIT8:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvadd v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ' ' 
        				+ Utils.hexDec64(((WideLiteralInstruction)instruction).getWideLiteral(), size) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        	
        		break;//((short)0xd8, "add-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),

        	
        		
        		
        	case MUL_INT_LIT16://((short)0xd2, "mul-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MUL_INT_LIT8:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvmul v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ' ' 
        				+ Utils.hexDec64(((WideLiteralInstruction)instruction).getWideLiteral(), size) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xda, "mul-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case DIV_INT_LIT16://((short)0xd3, "div-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case DIV_INT_LIT8:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvudiv v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ' ' 
        				+ Utils.hexDec64(((WideLiteralInstruction)instruction).getWideLiteral(), size) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xdb, "div-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),

        	case REM_INT_LIT16://((short)0xd4, "rem-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case REM_INT_LIT8:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvurem v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ' ' 
        				+ Utils.hexDec64(((WideLiteralInstruction)instruction).getWideLiteral(), size) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xdc, "rem-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),

        	case AND_INT_LIT16://((short)0xd5, "and-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case AND_INT_LIT8:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvand v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ' ' 
        				+ Utils.hexDec64(((WideLiteralInstruction)instruction).getWideLiteral(), size) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xdd, "and-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),

        	case OR_INT_LIT16://((short)0xd6, "or-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case OR_INT_LIT8:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvor v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ' ' 
        				+ Utils.hexDec64(((WideLiteralInstruction)instruction).getWideLiteral(), size) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xde, "or-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),

        	case XOR_INT_LIT16://((short)0xd7, "xor-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case XOR_INT_LIT8:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvxor v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ' ' 
        				+ Utils.hexDec64(((WideLiteralInstruction)instruction).getWideLiteral(), size) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        	
        		break;//((short)0xdf, "xor-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case RSUB_INT://break;//((short)0xd1, "rsub-int", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case RSUB_INT_LIT8:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvsub " + 
        				Utils.hexDec64(((WideLiteralInstruction)instruction).getWideLiteral(), size) + " v" +
        				Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) 
        				 + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xd9, "rsub-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SHL_INT_LIT8:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvshl v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ' ' 
        				+ Utils.hexDec64(((WideLiteralInstruction)instruction).getWideLiteral(), size) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xe0, "shl-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SHR_INT_LIT8:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvashr v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ' ' 
        				+ Utils.hexDec64(((WideLiteralInstruction)instruction).getWideLiteral(), size) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xe1, "shr-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case USHR_INT_LIT8:
        		cl.appendHead(refClassElement.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), "(bvlshr v" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()) + ' ' 
        				+ Utils.hexDec64(((WideLiteralInstruction)instruction).getWideLiteral(), size) + ')');
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), "l" + Integer.toString(((TwoRegisterInstruction)instruction).getRegisterB()));
        		cl.appendBody(refClassElement.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
        		gen.addClause(cl);
        		
        		break;//((short)0xe2, "ushr-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),

        	case IGET_VOLATILE://((short)0xe3, "iget-volatile", minApi(9), ReferenceType.FIELD, Format.Format22c, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case IPUT_VOLATILE://((short)0xe4, "iput-volatile", minApi(9), ReferenceType.FIELD, Format.Format22c, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case SGET_VOLATILE://((short)0xe5, "sget-volatile", minApi(9), ReferenceType.FIELD, Format.Format21c, Opcode.ODEX_ONLY | Opcode.ODEXED_STATIC_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SPUT_VOLATILE://((short)0xe6, "sput-volatile", minApi(9), ReferenceType.FIELD, Format.Format21c, Opcode.ODEX_ONLY | Opcode.ODEXED_STATIC_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IGET_OBJECT_VOLATILE://((short)0xe7, "iget-object-volatile", minApi(9), ReferenceType.FIELD, Format.Format22c, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case IGET_WIDE_VOLATILE://((short)0xe8, "iget-wide-volatile", minApi(9), ReferenceType.FIELD, Format.Format22c, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case IPUT_WIDE_VOLATILE://((short)0xe9, "iput-wide-volatile", minApi(9), ReferenceType.FIELD, Format.Format22c, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case SGET_WIDE_VOLATILE://((short)0xea, "sget-wide-volatile", minApi(9), ReferenceType.FIELD, Format.Format21c, Opcode.ODEX_ONLY | Opcode.ODEXED_STATIC_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case SPUT_WIDE_VOLATILE://((short)0xeb, "sput-wide-volatile", minApi(9), ReferenceType.FIELD, Format.Format21c, Opcode.ODEX_ONLY | Opcode.ODEXED_STATIC_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        		
        	case THROW_VERIFICATION_ERROR://((short)0xed, "throw-verification-error", minApi(5), ReferenceType.NONE, Format.Format20bc, Opcode.ODEX_ONLY | Opcode.CAN_THROW),
        	case EXECUTE_INLINE://((short)0xee, "execute-inline", ReferenceType.NONE,  Format.Format35mi, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        	case EXECUTE_INLINE_RANGE://((short)0xef, "execute-inline/range", minApi(8), ReferenceType.NONE,  Format.Format3rmi,  Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        	case INVOKE_DIRECT_EMPTY://((short)0xf0, "invoke-direct-empty", maxApi(13), ReferenceType.METHOD,  Format.Format35c, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT | Opcode.CAN_INITIALIZE_REFERENCE),
        	case INVOKE_OBJECT_INIT_RANGE://((short)0xf0, "invoke-object-init/range", minApi(14), ReferenceType.METHOD,  Format.Format3rc, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT | Opcode.CAN_INITIALIZE_REFERENCE),
        	case RETURN_VOID_BARRIER://((short)0xf1, "return-void-barrier", minApi(11), ReferenceType.NONE, Format.Format10x, Opcode.ODEX_ONLY),
        	case IGET_QUICK://((short)0xf2, "iget-quick", ReferenceType.NONE,  Format.Format22cs, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_QUICK | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case IGET_WIDE_QUICK://((short)0xf3, "iget-wide-quick", ReferenceType.NONE,  Format.Format22cs, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_QUICK | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case IGET_OBJECT_QUICK://((short)0xf4, "iget-object-quick", ReferenceType.NONE,  Format.Format22cs, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_QUICK | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case IPUT_QUICK://((short)0xf5, "iput-quick", ReferenceType.NONE,  Format.Format22cs, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_QUICK | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_WIDE_QUICK://((short)0xf6, "iput-wide-quick", ReferenceType.NONE,  Format.Format22cs, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_QUICK | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_OBJECT_QUICK://((short)0xf7, "iput-object-quick", ReferenceType.NONE,  Format.Format22cs, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_QUICK | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case INVOKE_VIRTUAL_QUICK://((short)0xf8, "invoke-virtual-quick", ReferenceType.NONE,  Format.Format35ms, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        	case INVOKE_VIRTUAL_QUICK_RANGE://((short)0xf9, "invoke-virtual-quick/range", ReferenceType.NONE,  Format.Format3rms, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        	case INVOKE_SUPER_QUICK://((short)0xfa, "invoke-super-quick", ReferenceType.NONE,  Format.Format35ms, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        	case INVOKE_SUPER_QUICK_RANGE://((short)0xfb, "invoke-super-quick/range", ReferenceType.NONE,  Format.Format3rms, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),

        	case IPUT_OBJECT_VOLATILE://((short)0xfc, "iput-object-volatile", minApi(9), ReferenceType.FIELD, Format.Format22c, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case SGET_OBJECT_VOLATILE://((short)0xfd, "sget-object-volatile", minApi(9), ReferenceType.FIELD, Format.Format21c, Opcode.ODEX_ONLY | Opcode.ODEXED_STATIC_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SPUT_OBJECT_VOLATILE:
        		break;//((short)0xfe, "sput-object-volatile", minApi(9), ReferenceType.FIELD, Format.Format21c, Opcode.ODEX_ONLY | Opcode.ODEXED_STATIC_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),

        	case PACKED_SWITCH_PAYLOAD:
        		break;//((short)0x100, "packed-switch-payload", ReferenceType.NONE, Format.PackedSwitchPayload, 0),
        	case SPARSE_SWITCH_PAYLOAD:
        		break;//((short)0x200, "sparse-switch-payload", ReferenceType.NONE, Format.SparseSwitchPayload, 0),
        	case ARRAY_PAYLOAD:
        		break;//((short)0x300, "array-payload", ReferenceType.NONE, Format.ArrayPayload, 0);
        }	
	}
	
	private String getLabels(){
    	FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
        final int regCount = instruction.getRegisterCount();
        switch (regCount) {
            case 1:
            	return "(or false " + 'l' + Integer.toString(instruction.getRegisterC()) + ")";      	
            case 2:
            	return "(or false " + 'l' + Integer.toString(instruction.getRegisterC()) + ' '
            						+ 'l' + Integer.toString(instruction.getRegisterD()) + ")";
            case 3:
            	return "(or false " + 'l' + Integer.toString(instruction.getRegisterC()) + ' '
						+ 'l' + Integer.toString(instruction.getRegisterD()) +  ' '
            			+ 'l' + Integer.toString(instruction.getRegisterE()) + ")";
            case 4:
            	return "(or false " + 'l' + Integer.toString(instruction.getRegisterC()) + ' '
						+ 'l' + Integer.toString(instruction.getRegisterD()) + ' '
						+ 'l' + Integer.toString(instruction.getRegisterE()) + ' '
            			+ 'l' + Integer.toString(instruction.getRegisterF()) + ")";
            case 5:
            	return "(or false " + 'l' + Integer.toString(instruction.getRegisterC()) + ' '
						+ 'l' + Integer.toString(instruction.getRegisterD()) + ' '
						+ 'l' + Integer.toString(instruction.getRegisterE()) + ' '
						+ 'l' + Integer.toString(instruction.getRegisterF()) + ' '
            			+ 'l' + Integer.toString(instruction.getRegisterG()) + ")"; 
            default:
            	return "false";
        }
    }
    
    private String getLabelsRange(){
    	RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
        int regCount = instruction.getRegisterCount();
    	int startRegister = instruction.getStartRegister();
    	int endRegister   =   startRegister+regCount-1;
    	int count = 0;
    	String label = "(or false ";
        for (int reg = startRegister; reg <= endRegister; reg++ ){
        	label = label + 'l' + Integer.toString(reg) + ' ';
        }
        return label + ')';
    }
    
    private void addQueryRange(final Gen gen, String p, String className, String methodName, String pc, String sinkName, final options options){
    	RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
        int regCount = instruction.getRegisterCount();
    	int startRegister = instruction.getStartRegister();
    	int endRegister   =   startRegister+regCount-1;
    	String verbose = "";
    	if (options.verboseResults){
    		verbose = ":print_answer true \n ";
    	};
        for (int reg = startRegister; reg <= endRegister; reg++ ){
        	gen.addQuery("(query (and " + p + ' ' +
        			"(= " + 'l' + Integer.toString(reg) +  " true))\n " + verbose + ":unbound-compressor false \n)");
        	gen.addQueryV("Test if register " + Integer.toString(reg) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
        }
    }
    
    private void addQuery(final Gen gen, String p, String className, String methodName, String pc, String sinkName, final options options){
    	FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
        final int regCount = instruction.getRegisterCount();
        String qb = "(query (and " + p + ' ';
        String verbose = "";
    	if (options.verboseResults){
    		verbose = ":print_answer true \n ";
    	};
        String qe = ")\n " + verbose + " :unbound-compressor false \n)";
        switch (regCount) {
            case 1:
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterC()) + " true)" + qe); 
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterC()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	break;
            case 2:
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterC()) + " true)" + qe);
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterC()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterD()) + " true)" + qe); 
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterD()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	break;
            case 3:
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterC()) + " true)" + qe);
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterC()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterD()) + " true)" + qe);
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterD()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterE()) + " true)" + qe); 
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterE()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	break;
            case 4:
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterC()) + " true)" + qe);
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterC()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterD()) + " true)" + qe);
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterD()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterE()) + " true)" + qe);
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterE()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterF()) + " true)" + qe); 
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterF()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	break;
            case 5:
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterC()) + " true)" + qe);
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterC()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterD()) + " true)" + qe);
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterD()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterE()) + " true)" + qe);
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterE()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterF()) + " true)" + qe);
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterF()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	gen.addQuery(qb + "(= " + 'l' + Integer.toString(instruction.getRegisterG()) + " true)" + qe);
            	gen.addQueryV("Test if register " + Integer.toString(instruction.getRegisterG()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName);
            	break;
        }
    }
    
    private Map<Integer, String> highReg(final boolean range, Map<Integer, String> regUpdate){
    	
    	
    	if (! range){
    		FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    		final int regCount = instruction.getRegisterCount();
    		switch (regCount) {
    		case 1:
            	regUpdate.put(instruction.getRegisterC(), "l" + Integer.toString(instruction.getRegisterC()));
            	break;
            case 2:
            	regUpdate.put(instruction.getRegisterC(), "(or l" + Integer.toString(instruction.getRegisterC()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterC()) + " l" + Integer.toString(instruction.getRegisterD()) + "))");
            	regUpdate.put(instruction.getRegisterD(), "(or l" + Integer.toString(instruction.getRegisterD()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterD()) + " l" + Integer.toString(instruction.getRegisterC()) + "))");
            	break;
            case 3:
            	regUpdate.put(instruction.getRegisterC(), "(or l" + Integer.toString(instruction.getRegisterC()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterC()) + ' ' 
            			+ "(or l" + Integer.toString(instruction.getRegisterD()) + " l" + Integer.toString(instruction.getRegisterE()) + ")))");
            	regUpdate.put(instruction.getRegisterD(), "(or l" + Integer.toString(instruction.getRegisterD()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterD()) + ' ' 
            			+ "(or l" + Integer.toString(instruction.getRegisterC()) + " l" + Integer.toString(instruction.getRegisterE()) + ")))");
            	regUpdate.put(instruction.getRegisterE(), "(or l" + Integer.toString(instruction.getRegisterE()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterE()) + ' ' 
            			+ "(or l" + Integer.toString(instruction.getRegisterC()) + " l" + Integer.toString(instruction.getRegisterD()) + ")))");
            	break;
            case 4:
            	regUpdate.put(instruction.getRegisterC(), "(or l" + Integer.toString(instruction.getRegisterC()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterC()) + ' ' 
            			+ "(or l" + Integer.toString(instruction.getRegisterD()) + " l" + Integer.toString(instruction.getRegisterE()) + " l" +
            			Integer.toString(instruction.getRegisterF()) + ")))");
            	regUpdate.put(instruction.getRegisterD(), "(or l" + Integer.toString(instruction.getRegisterD()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterD()) + ' ' 
            			+ "(or l" + Integer.toString(instruction.getRegisterC()) + " l" + Integer.toString(instruction.getRegisterE()) + " l" + 
            			Integer.toString(instruction.getRegisterF()) + ")))");
            	regUpdate.put(instruction.getRegisterE(), "(or l" + Integer.toString(instruction.getRegisterE()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterE()) + ' ' 
            			+ "(or l" + Integer.toString(instruction.getRegisterD()) + " l" + Integer.toString(instruction.getRegisterC()) + " l" + 
            			Integer.toString(instruction.getRegisterF()) + ")))");
            	regUpdate.put(instruction.getRegisterF(), "(or l" + Integer.toString(instruction.getRegisterF()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterF()) + ' ' 
            			+ "(or l" + Integer.toString(instruction.getRegisterD()) + " l" + Integer.toString(instruction.getRegisterE()) + " l"
            			+ Integer.toString(instruction.getRegisterC()) + ")))");
            	break;
            case 5:
            	regUpdate.put(instruction.getRegisterC(), "(or l" + Integer.toString(instruction.getRegisterC()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterC()) + ' ' 
            			+ "(or l" + Integer.toString(instruction.getRegisterD()) + " l" + Integer.toString(instruction.getRegisterE()) + " l" 
            			+ Integer.toString(instruction.getRegisterF()) + " l" 
            			+ Integer.toString(instruction.getRegisterG()) + ")))");
            	regUpdate.put(instruction.getRegisterD(), "(or l" + Integer.toString(instruction.getRegisterD()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterD()) + ' ' 
            			+ "(or l" + Integer.toString(instruction.getRegisterC()) + " l" + Integer.toString(instruction.getRegisterE()) 
            			+ " l" + Integer.toString(instruction.getRegisterF()) 
            			+ " l" + Integer.toString(instruction.getRegisterG()) + ")))");
            	regUpdate.put(instruction.getRegisterE(), "(or l" + Integer.toString(instruction.getRegisterE()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterE()) + ' ' 
            			+ "(or l" + Integer.toString(instruction.getRegisterD()) + " l" + Integer.toString(instruction.getRegisterC())
            			+ " l" + Integer.toString(instruction.getRegisterF())
            			+ " l" + Integer.toString(instruction.getRegisterG()) + ")))");
            	regUpdate.put(instruction.getRegisterF(), "(or l" + Integer.toString(instruction.getRegisterF()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterF()) + ' ' 
            			+ "(or l" + Integer.toString(instruction.getRegisterD()) + " l" + Integer.toString(instruction.getRegisterE())
            			+ " l" + Integer.toString(instruction.getRegisterC())
            			+ " l"  + Integer.toString(instruction.getRegisterG()) + ")))");
            	regUpdate.put(instruction.getRegisterG(), "(or l" + Integer.toString(instruction.getRegisterG()) + ' ' + 
            			"(and b" + Integer.toString(instruction.getRegisterG()) + ' ' 
            			+ "(or l" + Integer.toString(instruction.getRegisterD()) + " l" + Integer.toString(instruction.getRegisterE()) 
            			+ " l" + Integer.toString(instruction.getRegisterF())
            			+ " l" + Integer.toString(instruction.getRegisterC()) + ")))");
            	break;
    	}
    	}
    	else{
    		RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
            int regCount = instruction.getRegisterCount();
        	int startRegister = instruction.getStartRegister();
        	int endRegister   =   startRegister+regCount-1;
        	String orLabels = null;
        	switch (regCount){
        	case 0: return regUpdate;
        	case 1: return regUpdate;
        	default:
            for (int reg = startRegister; reg <= endRegister; reg++ ){
            	orLabels = "";
            	for (int reg2 = startRegister; reg2 <= endRegister; reg2++ ){
            		if (reg2 == reg){continue;}
            		if (orLabels == null) orLabels = 'l' + Integer.toString(reg);
            		else orLabels = orLabels + ' ' + 'l' + Integer.toString(reg);
            	}
            	regUpdate.put(reg, "(or l" + Integer.toString(reg) + ' ' + "(and b" + Integer.toString(reg) + ' ' + "(or "+ orLabels + ")))");
            }
        	}
    	}
    	return regUpdate;
    }
    
    private Map<Integer, String> updateReg(final int numReg, final int numArg, final char label, final boolean range){
    	Map<Integer, String> regUpdate = new HashMap<Integer, String>();
    	if (! range){
        	FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    			switch (numArg) {
                case 1:
                	regUpdate.put(numReg - numArg + 0, label + Integer.toString(instruction.getRegisterC())); 
                	regUpdate.put(numReg + 1 + 0, label + Integer.toString(instruction.getRegisterC()));
                	break;
                case 2:
                	regUpdate.put(numReg - numArg + 0, label + Integer.toString(instruction.getRegisterC()));
                	regUpdate.put(numReg - numArg + 1, label + Integer.toString(instruction.getRegisterD())); 
                	regUpdate.put(numReg + 1 + 0, label + Integer.toString(instruction.getRegisterC()));
                	regUpdate.put(numReg + 1 + 1, label + Integer.toString(instruction.getRegisterD()));
                	break;
                case 3:
                	regUpdate.put(numReg - numArg + 0, label + Integer.toString(instruction.getRegisterC()));
                	regUpdate.put(numReg - numArg + 1, label + Integer.toString(instruction.getRegisterD()));
                	regUpdate.put(numReg - numArg + 2, label + Integer.toString(instruction.getRegisterE())); 
                	regUpdate.put(numReg + 1 + 0, label + Integer.toString(instruction.getRegisterC()));
                	regUpdate.put(numReg + 1 + 1, label + Integer.toString(instruction.getRegisterD()));
                	regUpdate.put(numReg + 1 + 2, label + Integer.toString(instruction.getRegisterE())); 
                	break;
                case 4:
                	regUpdate.put(numReg - numArg + 0, label + Integer.toString(instruction.getRegisterC()));
                	regUpdate.put(numReg - numArg + 1, label + Integer.toString(instruction.getRegisterD()));
                	regUpdate.put(numReg - numArg + 2, label + Integer.toString(instruction.getRegisterE()));
                	regUpdate.put(numReg - numArg + 3, label + Integer.toString(instruction.getRegisterF()));
                	regUpdate.put(numReg + 1 + 0, label + Integer.toString(instruction.getRegisterC()));
                	regUpdate.put(numReg + 1 + 1, label + Integer.toString(instruction.getRegisterD()));
                	regUpdate.put(numReg + 1 + 2, label + Integer.toString(instruction.getRegisterE()));
                	regUpdate.put(numReg + 1 + 3, label + Integer.toString(instruction.getRegisterF())); 
                	break;
                case 5:
                	regUpdate.put(numReg - numArg + 0, label + Integer.toString(instruction.getRegisterC()));
                	regUpdate.put(numReg - numArg + 1, label + Integer.toString(instruction.getRegisterD()));
                	regUpdate.put(numReg - numArg + 2, label + Integer.toString(instruction.getRegisterE()));
                	regUpdate.put(numReg - numArg + 3, label + Integer.toString(instruction.getRegisterF()));
                	regUpdate.put(numReg - numArg + 4, label + Integer.toString(instruction.getRegisterG())); 
                	regUpdate.put(numReg + 1 +  0, label + Integer.toString(instruction.getRegisterC()));
                	regUpdate.put(numReg + 1 +  1, label + Integer.toString(instruction.getRegisterD()));
                	regUpdate.put(numReg + 1 +  2, label + Integer.toString(instruction.getRegisterE()));
                	regUpdate.put(numReg + 1 +  3, label + Integer.toString(instruction.getRegisterF()));
                	regUpdate.put(numReg + 1 +  4, label + Integer.toString(instruction.getRegisterG()));
                	break;
    			}
    		}
    		else{
    	        RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
    			int startRegister = instruction.getStartRegister();
            	int endRegister   =   startRegister+numReg-1;
            	int count = 0;
                for (int reg = startRegister; reg <= endRegister; reg++ )
                {
                	regUpdate.put(reg, label + Integer.toString(count));
                	regUpdate.put(numReg + 1 + count, label + Integer.toString(count));
                    count ++;
                }
    		}
    	
    	return regUpdate;
    }
    
    private Map<Integer, String> updateRes(final int numReg, final int numArg, final char label, final boolean range){
    	Map<Integer, String> regUpdate = new HashMap<Integer, String>();
    	if (! range){
        	FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    			switch (numArg) {
                case 1:
                	regUpdate.put(0, label + Integer.toString(instruction.getRegisterC())); 
                	break;
                case 2:
                	regUpdate.put(0, label + Integer.toString(instruction.getRegisterC()));
                	regUpdate.put(1, label + Integer.toString(instruction.getRegisterD())); 
                	break;
                case 3:
                	regUpdate.put(0, label + Integer.toString(instruction.getRegisterC()));
                	regUpdate.put(1, label + Integer.toString(instruction.getRegisterD()));
                	regUpdate.put(2, label + Integer.toString(instruction.getRegisterE())); 
                	break;
                case 4:
                	regUpdate.put(0, label + Integer.toString(instruction.getRegisterC()));
                	regUpdate.put(1, label + Integer.toString(instruction.getRegisterD()));
                	regUpdate.put(2, label + Integer.toString(instruction.getRegisterE()));
                	regUpdate.put(3, label + Integer.toString(instruction.getRegisterF()));
                	break;
                case 5:
                	regUpdate.put(0, label + Integer.toString(instruction.getRegisterC()));
                	regUpdate.put(1, label + Integer.toString(instruction.getRegisterD()));
                	regUpdate.put(2, label + Integer.toString(instruction.getRegisterE()));
                	regUpdate.put(3, label + Integer.toString(instruction.getRegisterF()));
                	regUpdate.put(4, label + Integer.toString(instruction.getRegisterG())); 
                	break;
    			}
    		}
    		else{
    	        RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
    			int startRegister = instruction.getStartRegister();
            	int endRegister   =   startRegister+numReg-1;
            	int count = 0;
                for (int reg = startRegister; reg <= endRegister; reg++ )
                {
                	regUpdate.put(count, label + Integer.toString(count));
                    count ++;
                }
    		}
    	
    	return regUpdate;
    }
    
    private boolean processIntent(final int ci, final int mi, final int numParLoc, final int numRegLoc, final int nextCode, final int c, final int m, final Gen gen, final String shortMethodName, final List<? extends ClassDef> classDefs,
    		final IndStr indStr, final RefClassElement refClassElement, final int size){
		Clause cl = new Clause();
		Clause cl2 = new Clause();
		Clause cl6 = new Clause();
	    Map<Integer, String> regUpdate = new HashMap<Integer, String>();
	    Map<Integer, String> regUpdateL = new HashMap<Integer, String>();
	    Map<Integer, String> regUpdateB = new HashMap<Integer, String>();
        Map<Integer, Boolean> fields = Collections.synchronizedMap(new HashMap <Integer, Boolean>());
        
        ////////////////////////////////////
        if  (c == (indStr.get("Landroid/os/Parcel;", 'c')) && 
    			(indStr.get("writeValue(Ljava/lang/Object;)V", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    		cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
    		cl2.appendBody(refClassElement.hPred(Utils.hexDec64(indStr.get("Landroid/os/Parcel;", 'c'), size), 
    				'v' + Integer.toString(instruction.getRegisterC()), Utils.hexDec64(0, size), 
    				'v' + Integer.toString(instruction.getRegisterD()), 'l' + Integer.toString(instruction.getRegisterD()), 'b' + Integer.toString(instruction.getRegisterD())));
    		gen.addClause(cl2);
			cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
        }
        if  (c == (indStr.get("Landroid/os/Parcel;", 'c')) && 
    			(indStr.get("marshall()[B", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    		cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
    		regUpdate.put(numRegLoc, "v" + Integer.toString(instruction.getRegisterC()));
			regUpdateL.put(numRegLoc, "l" + Integer.toString(instruction.getRegisterC()));
			regUpdateB.put(numRegLoc, "b" + Integer.toString(instruction.getRegisterC()));
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
        }
        if  (c == (indStr.get("Landroid/os/Parcel;", 'c')) && 
    			(indStr.get("unmarshall([BII)V", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    		cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
    		regUpdate.put(instruction.getRegisterC(), "v" + Integer.toString(instruction.getRegisterD()));
			regUpdateL.put(instruction.getRegisterC(), "l" + Integer.toString(instruction.getRegisterD()));
			regUpdateB.put(instruction.getRegisterC(), "b" + Integer.toString(instruction.getRegisterD()));
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
        }
        if  (c == (indStr.get("Landroid/os/Parcel;", 'c')) && 
    			(indStr.get("readValue(Ljava/lang/ClassLoader;)Ljava/lang/Object;", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    		cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
    				+ ' ' +
    		refClassElement.hPred(Utils.hexDec64(indStr.get("Landroid/os/Parcel;", 'c'), size), 
    				'v' + Integer.toString(instruction.getRegisterC()), Utils.hexDec64(0, size), 
    				"f", "lf", "bf") + ')');
    		regUpdate.put(numRegLoc, "f");
			regUpdateL.put(numRegLoc, "lf");
			regUpdateB.put(numRegLoc, "bf");
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
        }
        if  (c == (indStr.get("Ljava/lang/RuntimeException;", 'c')) && 
    			(indStr.get("<init>(Ljava/lang/String;)V", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    		cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
    		cl2.appendBody(refClassElement.hPred(Utils.hexDec64(indStr.get("Ljava/lang/RuntimeException;", 'c'), size), 
    				'v' + Integer.toString(instruction.getRegisterC()), Utils.hexDec64(indStr.get("message", 'f'), size), 
    				'v' + Integer.toString(instruction.getRegisterD()), 'l' + Integer.toString(instruction.getRegisterD()), 'b' + Integer.toString(instruction.getRegisterD())));
    		gen.addClause(cl2);
			cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
        }
        if  (c == (indStr.get("Ljava/lang/RuntimeException;", 'c')) && 
    			(indStr.get("getMessage()Ljava/lang/String;", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    		cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
    				+ ' ' +
    		refClassElement.hPred(Utils.hexDec64(indStr.get("Ljava/lang/RuntimeException;", 'c'), size), 
    				'v' + Integer.toString(instruction.getRegisterC()), Utils.hexDec64(indStr.get("message", 'f'), size), 
    				"f", "lf", "bf") + ')');
    		regUpdate.put(numRegLoc, "f");
			regUpdateL.put(numRegLoc, "lf");
			regUpdateB.put(numRegLoc, "bf");
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
        }
        if  (c == (indStr.get("Landroid/telephony/SmsManager;", 'c')) && 
    			(indStr.get("getDefault()Landroid/telephony/SmsManager;", 'm') == m)){
			final int instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
    		cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
    		cl2.appendBody(refClassElement.hPred(Utils.hexDec64(indStr.get("Landroid/telephony/SmsManager;", 'c'), size), 
    				Utils.hexDec64(instanceNum, size), "f", "vfp", "false", "bf"));
    		gen.addClause(cl2);
			cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
    		regUpdate.put(numRegLoc, Utils.hexDec64(instanceNum, size));
			regUpdateL.put(numRegLoc, "false");
			regUpdateB.put(numRegLoc, "true");
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
        }
        if  (c == (indStr.get("Landroid/graphics/PointF;", 'c')) && 
    			(indStr.get("<init>(FF)V", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    		cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
    		cl2.appendBody(refClassElement.hPred(Utils.hexDec64(indStr.get("Landroid/graphics/PointF;", 'c'), size), 
    				'v' + Integer.toString(instruction.getRegisterC()), Utils.hexDec64(indStr.get("x:F", 'f'), size), 
    				'v' + Integer.toString(instruction.getRegisterD()), 'l' + Integer.toString(instruction.getRegisterD()), 'b' + Integer.toString(instruction.getRegisterD())));
    		gen.addClause(cl2);
    		cl6.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
    		cl6.appendBody(refClassElement.hPred(Utils.hexDec64(indStr.get("Landroid/graphics/PointF;", 'c'), size), 
    				'v' + Integer.toString(instruction.getRegisterC()), Utils.hexDec64(indStr.get("y:F", 'f'), size), 
    				'v' + Integer.toString(instruction.getRegisterE()), 'l' + Integer.toString(instruction.getRegisterE()), 'b' + Integer.toString(instruction.getRegisterE())));
    		gen.addClause(cl6);
			cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
        }
        if  (c == (indStr.get("Ljava/util/Map;", 'c')) && 
    			(indStr.get("put(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    		cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
    		cl2.appendBody(refClassElement.hPred(Utils.hexDec64(indStr.get("Ljava/util/Map;", 'c'), size), 
    				'v' + Integer.toString(instruction.getRegisterC()), 'v' + Integer.toString(instruction.getRegisterD()), 
    				'v' + Integer.toString(instruction.getRegisterE()), 'l' + Integer.toString(instruction.getRegisterE()), 'b' + Integer.toString(instruction.getRegisterE())));
    		gen.addClause(cl2);
			cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
        }
        if  (c == (indStr.get("Ljava/util/Map;", 'c')) && 
    			(indStr.get("get(Ljava/lang/Object;)Ljava/lang/Object;", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    		cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
    				+ ' ' +
    		refClassElement.hPred(Utils.hexDec64(indStr.get("Ljava/util/Map;", 'c'), size), 
    				'v' + Integer.toString(instruction.getRegisterC()), 'v' + Integer.toString(instruction.getRegisterD()), 
    				"f", "lf", "bf") + ')');
    		regUpdate.put(numRegLoc, "f");
			regUpdateL.put(numRegLoc, "lf");
			regUpdateB.put(numRegLoc, "bf");
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
        }
        if  (c == (indStr.get("Ljava/lang/String;", 'c')) && 
    			(indStr.get("getChars(II[CI)V", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, 
					regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) + ' ' + refClassElement.hPred(
							Utils.hexDec64(indStr.get("[C", 'c'), size), 'v' + Integer.toString(instruction.getRegisterF()),
							Utils.hexDec64(0, size), "f", "lf", "bf") + ')');
			cl.appendBody(refClassElement.hPred(
					Utils.hexDec64(indStr.get("[C", 'c'), size), 'v' + Integer.toString(instruction.getRegisterF()),
					Utils.hexDec64(0, size), "fpp", 'l' + Integer.toString(instruction.getRegisterC()), 'b' + Integer.toString(instruction.getRegisterC())));
			gen.addClause(cl);
			cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl2.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl2);
			return true;
        }
        if  (c == (indStr.get("Ljava/util/Formatter;", 'c')) && 
    			(indStr.get("<init>(Ljava/lang/Appendable;)V", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl.appendBody(refClassElement.hPred(
					Utils.hexDec64(indStr.get("Ljava/lang/StringBuffer;", 'c'), size), 'v' + Utils.Dec(instruction.getRegisterD()),
					Utils.hexDec64(0, size), 'v' + Utils.Dec(instruction.getRegisterC()), "false", "true"));
			gen.addClause(cl);
			cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl2.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl2);
			return true;
        }
        if  (c == (indStr.get("Ljava/util/Formatter;", 'c')) && 
    			(indStr.get("format(Ljava/lang/String;[Ljava/lang/Object;)Ljava/util/Formatter;", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, 
					regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) + refClassElement.hPred(
							Utils.hexDec64(indStr.get("Ljava/lang/StringBuffer;", 'c'), size), "f",
							Utils.hexDec64(0, size), 'v' + Utils.Dec(instruction.getRegisterC()), "false", "true") + ')');
			cl.appendBody(refClassElement.hPred(
					Utils.hexDec64(indStr.get("Ljava/lang/StringBuffer;", 'c'), size), "f",
					Utils.hexDec64(0, size), 'v' + Utils.Dec(instruction.getRegisterC()), "(or l" + Utils.Dec(instruction.getRegisterD()) + " l" + Utils.Dec(instruction.getRegisterE()) + ')', "true"));
			gen.addClause(cl);
			cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl2.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl2);
			return true;
        }
        if  (c == (indStr.get("Ljava/lang/StringBuffer;", 'c')) && 
    			(indStr.get("toString()Ljava/lang/String;", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, 
					regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen) + refClassElement.hPred(
							Utils.hexDec64(indStr.get("Ljava/lang/StringBuffer;", 'c'), size), 'v' + Utils.Dec(instruction.getRegisterC()),
							Utils.hexDec64(0, size), "f", "lf", "bf") + ')');
			regUpdate.put(numRegLoc, "fpp");
			regUpdateL.put(numRegLoc, "lf");
			regUpdateB.put(numRegLoc, "bf");
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
        }
        if  (c == (indStr.get("Ljava/lang/System;", 'c')) && 
    			(indStr.get("arraycopy(Ljava/lang/Object;ILjava/lang/Object;II)V", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
					+ ' ' + refClassElement.hPred(
							"cn", 'v' + Utils.Dec(instruction.getRegisterC()),
							Utils.hexDec64(0, size), "val", "lf", "bf") + ')');
			cl.appendBody(refClassElement.hPred(
					"cn", 'v' + Utils.Dec(instruction.getRegisterE()),
					Utils.hexDec64(0, size), "val", "lf", "bf"));
			gen.addClause(cl);
			cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl2.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl2);
			return true;
        }
        if  (c == (indStr.get("Landroid/widget/Button;", 'c')) && 
    			(indStr.get("getHint()Ljava/lang/CharSequence;", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
					+ ' ' + refClassElement.hPred(
							Utils.hexDec64(indStr.get("Landroid/widget/Button;", 'c'), size), 'v' + Utils.Dec(instruction.getRegisterC()),
							Utils.hexDec64(indStr.get("hint", 'f'), size), "val", "lf", "bf") + ')');
			regUpdate.put(numRegLoc, "val");
			regUpdateL.put(numRegLoc, "lf");
			regUpdateB.put(numRegLoc, "bf");
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			regUpdate.clear();
			regUpdateL.clear();
			regUpdateB.clear();
			cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			regUpdate.put(numRegLoc, Utils.hexDec64(0, size));
			regUpdateL.put(numRegLoc, "false");
			regUpdateB.put(numRegLoc, "true");
			cl2.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl2);
			return true;
        }
        if  (c == (indStr.get("Landroid/widget/Button;", 'c')) && 
    			(indStr.get("setHint(Ljava/lang/CharSequence;)V", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
					);
			cl.appendBody(refClassElement.hPred(
					Utils.hexDec64(indStr.get("Landroid/widget/Button;", 'c'), size), 'v' + Utils.Dec(instruction.getRegisterC()),
					Utils.hexDec64(indStr.get("hint", 'f'), size), 'v' + Integer.toString(instruction.getRegisterD()), 'l' + Integer.toString(instruction.getRegisterD())
					, 'b' + Integer.toString(instruction.getRegisterD())));
			gen.addClause(cl);
			cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl2.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl2);
			return true;
        }
        if  (indStr.get("getSystemService(Ljava/lang/String;)Ljava/lang/Object;", 'm') == m){
			final int instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
    		cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
    		cl2.appendBody(refClassElement.hPred(Utils.hexDec64(indStr.get("Ljava/lang/Object;", 'c'), size), 
    				Utils.hexDec64(instanceNum, size), "f", "vfp", "false", "bf"));
    		gen.addClause(cl2);
			cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
    		regUpdate.put(numRegLoc, Utils.hexDec64(instanceNum, size));
			regUpdateL.put(numRegLoc, "false");
			regUpdateB.put(numRegLoc, "true");
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
        }
        ////////////////////////////////////
        
        
        if  (c == (indStr.get("Landroid/content/Intent;", 'c')) && 
    			(indStr.get("setComponent(Landroid/content/ComponentName;)Landroid/content/Intent;", 'm') == m)){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl2.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
					+ ' ' + refClassElement.hiPred(
							"cn", 'v' + Utils.Dec(instruction.getRegisterC()), "val", "lf", "bf") + ')');
			cl2.appendBody(refClassElement.hiPred(
					'v' + Integer.toString(instruction.getRegisterD()), 'v' + Integer.toString(instruction.getRegisterC()), "val", "lf", "bf"));
			gen.addClause(cl2);
			cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			regUpdate.put(instruction.getRegisterC(), 'v' + Integer.toString(instruction.getRegisterC()));
			regUpdateL.put(instruction.getRegisterC(), 'l' + Integer.toString(instruction.getRegisterC()));
			regUpdateB.put(instruction.getRegisterC(), 'b' + Integer.toString(instruction.getRegisterC()));
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
        	return true;
        }
        
		if  (c == (indStr.get("Landroid/content/Intent;", 'c')) && 
			(indStr.get("<init>(Landroid/content/Context;Ljava/lang/Class;)V", 'm') == m)){
			final int instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			
			cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl2.appendBody(refClassElement.hiPred(
					'v' + Integer.toString(instruction.getRegisterE()), Utils.hexDec64(instanceNum, size), Utils.hexDec64(0, size), "false", "false"));
			gen.addClause(cl2);
			cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			regUpdate.put(instruction.getRegisterC(), Utils.hexDec64(instanceNum, size));
			regUpdateL.put(instruction.getRegisterC(), "false");
			regUpdateB.put(instruction.getRegisterC(), "true");
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			
			regUpdate.clear();
			regUpdateL.clear();
			regUpdateB.clear();
			fields = refClassElement.getClassFields(classDefs, indStr, "Landroid/content/Intent;", instanceNum);
			if (fields != null)
    		for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
    			Clause cl12 = new Clause();
    			cl12.appendHead(refClassElement.rPred(Utils.Dec(ci), Utils.Dec(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
    			cl12.appendBody(refClassElement.hPred(
    					Utils.hexDec64(indStr.get("Landroid/content/Intent;", 'c'), size), Utils.hexDec64(instanceNum, size), Utils.hexDec64(fieldN.getKey(), size), Utils.hexDec64(0, size), "false", Boolean.toString(fieldN.getValue())));
    			gen.addClause(cl12);
    		}
			
			return true;
		}
		if  (c == (indStr.get("Landroid/content/Intent;", 'c')) && 
				(indStr.get("<init>(Ljava/lang/String;)V", 'm') == m)){
				final int instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
				FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
				
				cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
				cl2.appendBody(refClassElement.hiPred(
						'v' + Integer.toString(instruction.getRegisterE()), Utils.hexDec64(instanceNum, size), Utils.hexDec64(0, size), "false", "false"));
				gen.addClause(cl2);
				cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
				regUpdate.put(instruction.getRegisterC(), Utils.hexDec64(instanceNum, size));
				regUpdateL.put(instruction.getRegisterC(), "false");
				regUpdateB.put(instruction.getRegisterC(), "true");
				cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
				gen.addClause(cl);
				
				regUpdate.clear();
				regUpdateL.clear();
				regUpdateB.clear();
				fields = refClassElement.getClassFields(classDefs, indStr, "Landroid/content/Intent;", instanceNum);
				if (fields != null)
	    		for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
	    			Clause cl12 = new Clause();
	    			cl12.appendHead(refClassElement.rPred(Utils.Dec(ci), Utils.Dec(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
	    			cl12.appendBody(refClassElement.hPred(
	    					Utils.hexDec64(indStr.get("Landroid/content/Intent;", 'c'), size), Utils.hexDec64(instanceNum, size), Utils.hexDec64(fieldN.getKey(), size), Utils.hexDec64(0, size), "false", Boolean.toString(fieldN.getValue())));
	    			gen.addClause(cl12);
	    		}
				
				return true;
			}
		if  (c == (indStr.get("Landroid/content/Intent;", 'c')) && 
				(indStr.get("<init>()V", 'm') == m)){
				final int instanceNum = refClassElement.getInstNum(ci, mi, codeAddress);
				FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
				
				cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
				cl2.appendBody(refClassElement.hiPred(
						"f", Utils.hexDec64(instanceNum, size), Utils.hexDec64(0, size), "false", "false"));
				gen.addClause(cl2);
				cl.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
				regUpdate.put(instruction.getRegisterC(), Utils.hexDec64(instanceNum, size));
				regUpdateL.put(instruction.getRegisterC(), "false");
				regUpdateB.put(instruction.getRegisterC(), "true");
				cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
				gen.addClause(cl);
				
				regUpdate.clear();
				regUpdateL.clear();
				regUpdateB.clear();
				fields = refClassElement.getClassFields(classDefs, indStr, "Landroid/content/Intent;", instanceNum);
				if (fields != null)
	    		for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
	    			Clause cl12 = new Clause();
	    			cl12.appendHead(refClassElement.rPred(Utils.Dec(ci), Utils.Dec(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
	    			cl12.appendBody(refClassElement.hPred(
	    					Utils.hexDec64(indStr.get("Landroid/content/Intent;", 'c'), size), Utils.hexDec64(instanceNum, size), Utils.hexDec64(fieldN.getKey(), size), Utils.hexDec64(0, size), "false", Boolean.toString(fieldN.getValue())));
	    			gen.addClause(cl12);
	    		}
				return true;
		}
		if ((indStr.get("startActivity(Landroid/content/Intent;)V", 'm') == m) || shortMethodName.contains("startActivityForResult")){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
					+ ' ' + refClassElement.hiPred(
							"cn", 'v' + Utils.Dec(instruction.getRegisterD()), "val", "lf", "bf") + ')');
			cl.appendBody(refClassElement.iPred(
							"cn", Utils.hexDec64(c, size), "val", "lf", "bf"));
			gen.addClause(cl);
			cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl2.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl2);
			
			Clause cl3 = new Clause();
			cl3.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
					+ ' ' + refClassElement.hiPred(
							"cn", 'v' + Utils.Dec(instruction.getRegisterD()), "val", "lf", "bf") + ')');
			final String inC = Utils.hexDec64(indStr.get(Utils.Dec(instruction.getRegisterD()) + Utils.Dec(c), 'c'), size); // in(c) = _ + _)
			cl3.appendBody(refClassElement.hiPred(
					"cn", inC , "val", "lf", "bf")); 
			gen.addClause(cl3);
			
			Clause cl4 = new Clause();
			cl4.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
					+ ' ' + refClassElement.hiPred(
							"cn", 'v' + Utils.Dec(instruction.getRegisterD()), "val", "lf", "bf") + ')');
			cl4.appendBody(refClassElement.hPred(
					"cn", "cn" , Utils.hexDec64(indStr.get("parent", 'f'), size), Utils.hexDec64(c, size), "false", "true")); 
			gen.addClause(cl4);
			
			Clause cl5 = new Clause();
			cl5.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
					+ ' ' + refClassElement.hiPred(
							"cn", 'v' + Utils.Dec(instruction.getRegisterD()), "val", "lf", "bf") + ')');
			cl5.appendBody(refClassElement.hPred(
					"cn", "cn" , Utils.hexDec64(indStr.get("intent", 'f'), size), inC, "false", "true")); 
			gen.addClause(cl5);
			
			return true;
		}
		if (shortMethodName.contains((String) "putExtra") && c == (indStr.get("Landroid/content/Intent;", 'c'))){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
					+ ' ' + refClassElement.hiPred(
							"cn", 'v' + Utils.Dec(instruction.getRegisterC()), "val", "lf", "bf") + ')');
			cl.appendBody(refClassElement.hiPred(
							"cn", 'v' + Utils.Dec(instruction.getRegisterC()),
							'v' + Integer.toString(instruction.getRegisterE()), 'l' + Integer.toString(instruction.getRegisterE()), 'b' + Integer.toString(instruction.getRegisterE())));
			gen.addClause(cl);
			cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			regUpdateL.put(instruction.getRegisterC(), "(or l" + Utils.Dec(instruction.getRegisterC()) + ' ' + 'l' + Utils.Dec(instruction.getRegisterE()) + ')');
			cl2.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl2);
			return true;
		}
		if (shortMethodName.contains((String) "get") && c == (indStr.get("Landroid/content/Intent;", 'c'))){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
					+ ' ' + refClassElement.hiPred(
							"cn", 'v' + Utils.Dec(instruction.getRegisterC()), "val", "lf", "bf") + ')');
			regUpdate.put(numRegLoc, "val");
			regUpdateL.put(numRegLoc, "lf");
			regUpdateB.put(numRegLoc, "bf");
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
		}
		if (m ==  indStr.get("setResult(ILandroid/content/Intent;)V", 'm')){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
					+ ' ' + refClassElement.hiPred(
							"cn", 'v' + Utils.Dec(instruction.getRegisterE()), "val", "lf", "bf") + ')');
			cl.appendBody(refClassElement.hPred(
							Utils.hexDec64(c, size), Utils.hexDec64(c, size), Utils.hexDec64(indStr.get("result", 'f'), size), 
							'v' + Utils.Dec(instruction.getRegisterE()), 'l' + Utils.Dec(instruction.getRegisterE()), 'b' + Utils.Dec(instruction.getRegisterE())));
			gen.addClause(cl);
			cl2.appendHead(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			cl2.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl2);
			return true;
		}
		if (m ==  indStr.get("getIntent()Landroid/content/Intent;", 'm')){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			cl.appendHead("(and " + refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen)
					+ ' ' + refClassElement.hPred(
							Utils.hexDec64(c, size), Utils.hexDec64(c, size), Utils.hexDec64(indStr.get("intent", 'f'), size), "val", "lf", "bf") + ')');
			regUpdate.put(numRegLoc, "val");
			regUpdateL.put(numRegLoc, "lf");
			regUpdateB.put(numRegLoc, "bf");
			cl.appendBody(refClassElement.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc, gen));
			gen.addClause(cl);
			return true;
		}
		return false;
	}
	
}
