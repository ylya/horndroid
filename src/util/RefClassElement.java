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

import gen.Gen;
import gen.CallRef;
import util.iface.IndStr;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.annotation.Nonnull;

import org.apache.commons.lang3.builder.EqualsBuilder;
import org.apache.commons.lang3.builder.HashCodeBuilder;
import org.jf.baksmali.Adaptors.FieldDefinition;
import org.jf.dexlib2.dexbacked.DexBackedClassDef;
import org.jf.dexlib2.iface.ClassDef;
import org.jf.dexlib2.iface.Field;
import org.jf.dexlib2.iface.Method;
import org.jf.dexlib2.util.ReferenceUtil;
import org.jf.util.StringUtils;

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
	@Nonnull private final Map<Integer, Integer> implementations;
	private String heapDef;
	public RefClassElement(){
		this.synConcurRange = 0;
		this.refClassField = Collections.synchronizedSet(new HashSet <Pair>());
		this.refClassMethod = Collections.synchronizedSet(new HashSet <Pair>());
		this.classDefSet = Collections.synchronizedSet(new HashSet <ClassDefGen>());
		this.callRefs = Collections.synchronizedSet(new HashSet <CallRef>());
		this.instanceMapping = Collections.synchronizedMap(new HashMap <Integer, Instance>());
		this.instanceConcurMapping = Collections.synchronizedMap(new HashMap <Integer, ConcurInstance>());
		this.implementations = Collections.synchronizedMap(new HashMap <Integer, Integer>());
	}
	private void addImplementationsFromSuperClass(final int c, final int m, final List<? extends ClassDef> classDefs, final IndStr indStr, 
			final int iNum, final int cSuper, final int iType, final Gen gen){
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
				addImplementationsFromSuperClass(c, m, classDefs, indStr, iNum, superClassInd, iType, gen);
		}
	}
	private void addImplementationsFromInterface(final int c, final int m, final List<? extends ClassDef> classDefs, final IndStr indStr, 
			final int iNum, final int iType, final Gen gen){
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
	private void addChild(int superClass, final List<? extends ClassDef> classDefs, final IndStr indStr, final int c){
		for (final ClassDef classDef: classDefs) {
			if (indStr.get(classDef.getSuperclass(), 'c') == superClass){
				for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet()){	
					if (entry.getValue().getType() == indStr.get(classDef.getType(), 'c'))
							implementations.put(entry.getKey(), c);
				}
				addChild(indStr.get(classDef.getType(), 'c'), classDefs, indStr, c);
			}
		}
	}

	public final Map<Integer, Integer> getImplementations(final int c, final int m, final List<? extends ClassDef> classDefs, final IndStr indStr, final Gen gen){
		implementations.clear();
		for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet()){	
			if (entry.getValue().getType() == c)
				if (gen.isDefined(c, m)){
					implementations.put(entry.getKey(), c);
					addChild(c, classDefs, indStr, c);
				}
			addImplementationsFromSuperClass(c, m, classDefs, indStr, entry.getKey(), entry.getValue().getType(), entry.getValue().getType(), gen);
			addImplementationsFromInterface(c, m, classDefs, indStr, entry.getKey(), entry.getValue().getType(), gen);
		}
		return implementations;
	}
	public void addCallRef(final int calleeC, final int calleeM, final int callerC, final int callerM, final int callerNextLine){
		callRefs.add(new CallRef(calleeC, calleeM, callerC, callerM, callerNextLine));
	}

	private void addHeapDef(final int c, final int m, final int line, final Gen gen){
    	gen.addDef("(declare-rel H_" + Integer.toString(c) + '_' + Integer.toString(m) + '_' + Integer.toString(line) + ' ' + getHeapDef() + ')');
    }
	private void addHeapVar (String var, final Gen gen){
		if (var.equals((String) "true") || var.equals((String) "false")) return;
		char firstLetter = var.charAt(0);
		switch (firstLetter){
			case 't': gen.addVar("(declare-var " + var + " Int)"); break;
			case 'l': gen.addVar("(declare-var " + var + " Bool)"); break;
			case 'f': gen.addVar("(declare-var " + var + " bv64)"); break;
		}		
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
	public String addHeapPredMain(final int c, final int m, final int line, final Gen gen, final Map<Integer, String> fieldUpdate, final Map<Integer, String> fieldUpdateL){
    	String res = "(H_" + Integer.toString(c) + '_' + Integer.toString(m) + '_' + Integer.toString(line) + ' ';
    	String var = "";
    	int prev = 0;
    	int i = 0;
    	boolean found;
    	if (getHeapDef() != null){
    		addHeapDef(c, m, line, gen);
    		for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet()){	
    			found = false;
				var = 't' + Integer.toString(entry.getKey());
				addHeapVar(var, gen);
				res += var + ' ';
				if (entry.getValue().isObj()){
					for (ClassDefGen cldef : classDefSet)
						if (cldef.getType() == entry.getValue().getType()){
							for (i = prev; i < cldef.getNumberOfFields() + prev; i++){
								var = 'f' + Integer.toString(i);
								addHeapVar(var, gen);
								res += var + ' ';
								var = fieldUpdateL.get(i);
								if (var != null)
									addHeapVar(var, gen);
								else{
									var = "lf" + Integer.toString(i);
									addHeapVar(var, gen);
								}
								res += var + ' ';
							}
							found = true;
							break;
						}
					if (!found){
						for (i = prev; i < refClassField.size() + prev; i++){
							var = 'f' + Integer.toString(i);
							addHeapVar(var, gen);
							res += var + ' ';
							var = fieldUpdateL.get(i);
							if (var != null)
								addHeapVar(var, gen);
							else{
								var = "lf" + Integer.toString(i);
								addHeapVar(var, gen);
							}
							res += var + ' ';
						}
					}
				}
				else
					for (i=prev; i < gen.verRange + prev; i++){
						var = 'f' + Integer.toString(i);
						addHeapVar(var, gen);
						res += var + ' ';
						var = fieldUpdateL.get(i);
						if (var != null)
							addHeapVar(var, gen);
						else{
							var = "lf" + Integer.toString(i);
							addHeapVar(var, gen);
						}
						res += var + ' ';
					}
			prev = prev + i;	
			}
    	}
    	return res + ')';
    }		
    public String addHeapPred(final int c, final int m, final int line, final Gen gen, final Map<Integer, String> fieldUpdate, final Map<Integer, String> fieldUpdateL, final int iNum){
    	String res = "(H_" + Integer.toString(c) + '_' + Integer.toString(m) + '_' + Integer.toString(line) + ' ';
    	String var = "";
    	int prev = 0;
    	int i = 0;
    	boolean found;
    	if (getHeapDef() != null){
    		addHeapDef(c, m, line, gen);
    		for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet()){	
    			found = false;
				var = 't' + Integer.toString(entry.getKey());
				addHeapVar(var, gen);
				res += var + ' ';
				if (entry.getValue().isObj()){
					for (ClassDefGen cldef : classDefSet)
						if (cldef.getType() == entry.getValue().getType()){
							for (i = prev; i < cldef.getNumberOfFields() + prev; i++){
								var = fieldUpdate.get(i);
								if ((var != null) && (entry.getKey() == iNum))
									addHeapVar(var, gen);
								else{
									var = 'f' + Integer.toString(i);
									addHeapVar(var, gen);
								}
								res += var + ' ';
								var = fieldUpdateL.get(i);
								if ((var != null) && (entry.getKey() == iNum))
									addHeapVar(var, gen);
								else{
									var = "lf" + Integer.toString(i);
									addHeapVar(var, gen);
								}
								res += var + ' ';
							}
							found = true;
							break;
						}
					if (!found){
						for (i = prev; i < refClassField.size() + prev; i++){
							var = 'f' + Integer.toString(i);
							addHeapVar(var, gen);
							res += var + ' ';
							var = fieldUpdateL.get(i);
							if (var != null)
								addHeapVar(var, gen);
							else{
								var = "lf" + Integer.toString(i);
								addHeapVar(var, gen);
							}
							res += var + ' ';
						}
					}
				}
				else
					for (i=prev; i < gen.verRange + prev; i++){
						var = fieldUpdate.get(i);
						if ((var != null) && (entry.getKey() == iNum))
							addHeapVar(var, gen);
						else{
							var = 'f' + Integer.toString(i);
							addHeapVar(var, gen);
						}
						res += var + ' ';
						var = fieldUpdateL.get(i);
						if ((var != null) && (entry.getKey() == iNum))
							addHeapVar(var, gen);
						else{
							var = "lf" + Integer.toString(i);
							addHeapVar(var, gen);
						}
						res += var + ' ';
					}
			prev = prev + i;	
			}
    	}
    	return res + ')';
    }
    private void addHeapDefR(final int c, final int m, final Gen gen, boolean forReturn){
    	gen.addDef("(declare-rel H_" + Integer.toString(c) + '_' + Integer.toString(m) + "_r " + getHeapDef() + ')');
    }
    public String addHeapPredRBody(final int c, final int m, final int line, final Gen gen){
    	String res = "(H_" + Integer.toString(c) + '_' + Integer.toString(m) + '_' + Integer.toString(line) + ' ';
    	String var = "";
    	int prev = 0;
    	boolean found;
    	int i = 0;
    		if (getHeapDef() != null){
    				for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet()){	
    					found = false;
    					var = 't' + Integer.toString(entry.getKey()) + 'p';
    					addHeapVar(var, gen);
    					res += var + ' ';
    					if (entry.getValue().isObj()){
    						for (ClassDefGen cldef : classDefSet)
    							if (cldef.getType() == entry.getValue().getType()){
    								for (i=prev; i < cldef.getNumberOfFields() + prev; i++){
    									var = 'f' + Integer.toString(i) + 'p';
    									addHeapVar(var, gen);
    									res += var + ' ';
    									var = "lf" + Integer.toString(i) + 'p';
    									addHeapVar(var, gen);
    									res += var + ' ';
    								}
    								found = true;
    								break;
    							}
    						if (!found){
    							for (i=prev; i < refClassField.size() + prev; i++){
									var = 'f' + Integer.toString(i) + 'p';
									addHeapVar(var, gen);
									res += var + ' ';
									var = "lf" + Integer.toString(i) + 'p';
									addHeapVar(var, gen);
									res += var + ' ';
								}
    						}
    					}
    					else
    						for (i=prev; i < gen.verRange+prev; i++){
								var = 'f' + Integer.toString(i) + 'p';
								addHeapVar(var, gen);
								res += var + ' ';
								var = "lf" + Integer.toString(i) + 'p';
								addHeapVar(var, gen);
								res += var + ' ';
							}
    					prev = prev + i;	
    			} 		
    		}
    	return res + ')';
    }
    public String addHeapPredR(final int c, final int m, final Gen gen, boolean forReturn){
    	String res = "(H_" + Integer.toString(c) + '_' + Integer.toString(m) + "_r ";
    	String var = "";
    	int prev = 0;
    	boolean found;
    	int i = 0;
    	if (forReturn){
    		if (getHeapDef() != null){
    			addHeapDefR(c, m, gen, forReturn);
    				for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet()){	
    					found = false;
    					var = 't' + Integer.toString(entry.getKey());
    					addHeapVar(var, gen);
    					res += var + ' ';
    					if (entry.getValue().isObj()){
    						for (ClassDefGen cldef : classDefSet)
    							if (cldef.getType() == entry.getValue().getType()){
    								for (i=prev; i < cldef.getNumberOfFields() + prev; i++){
    									var = 'f' + Integer.toString(i);
    									addHeapVar(var, gen);
    									res += var + ' ';
    									var = "lf" + Integer.toString(i);
    									addHeapVar(var, gen);
    									res += var + ' ';
    								}
    								found = true;
    								break;
    							}
    					
    						if (!found){
    							for (i=prev; i < refClassField.size() + prev; i++){
									var = 'f' + Integer.toString(i);
									addHeapVar(var, gen);
									res += var + ' ';
									var = "lf" + Integer.toString(i);
									addHeapVar(var, gen);
									res += var + ' ';
								}
    						}
    					}
    					else
    						for (i=prev; i < gen.verRange + prev; i++){
								var = 'f' + Integer.toString(i);
								addHeapVar(var, gen);
								res += var + ' ';
								var = "lf" + Integer.toString(i);
								addHeapVar(var, gen);
								res += var + ' ';
							}
    			prev = prev + i;
    			} 		
    		}
    	}
    	else{
    		if (getHeapDef() != null){
    			addHeapDefR(c, m, gen, forReturn);
    				for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet()){	
    					found = false;
    					var = 't' + Integer.toString(entry.getKey()) + 'p';
    					addHeapVar(var, gen);
    					res += var + ' ';
    					if (entry.getValue().isObj()){
    						for (ClassDefGen cldef : classDefSet)
    							if (cldef.getType() == entry.getValue().getType()){
    								for (i=prev; i < cldef.getNumberOfFields() + prev; i++){
    									var = 'f' + Integer.toString(i) + 'p';
    									addHeapVar(var, gen);
    									res += var + ' ';
    									var = "lf" + Integer.toString(i) + 'p';
    									addHeapVar(var, gen);
    									res += var + ' ';
    								}
    								found = true;
    								break;
    							}
    						if (!found){
    							for (i=prev; i < refClassField.size() + prev; i++){
									var = 'f' + Integer.toString(i) + 'p';
									addHeapVar(var, gen);
									res += var + ' ';
									var = "lf" + Integer.toString(i) + 'p';
									addHeapVar(var, gen);
									res += var + ' ';
    							}
    						}
    					}
    					else
    						for (i=prev; i < gen.verRange + prev; i++){
								var = 'f' + Integer.toString(i) + 'p';
								addHeapVar(var, gen);
								res += var + ' ';
								var = "lf" + Integer.toString(i) + 'p';
								addHeapVar(var, gen);
								res += var + ' ';
							}
    						
    					prev = prev + i;			
    			} 		
    		}
    		
    	}
    	return res + ')';
    }
	public String getHeapDef(){
		return heapDef;
	}
	public void formHeapDef(final Gen gen){
		if (instanceMapping.isEmpty()) {heapDef = null; return;}
		boolean fieldsPresent = false;
		boolean found;
		heapDef = "(";
		for (Map.Entry<Integer, Instance> entry : instanceMapping.entrySet()){	
			heapDef += " Int ";
			found = false;
			if (entry.getValue().isObj())
			{
				for (ClassDefGen cldef : classDefSet)
					if (cldef.getType() == entry.getValue().getType()){
						for (int i=0; i < cldef.getNumberOfFields(); i++){
							heapDef += " bv64 Bool ";
							fieldsPresent = true;
						}
						found = true;
						break;
					}
				if (!found){
					for (int i=0; i < refClassField.size(); i++){
						heapDef += " bv64 Bool ";
						fieldsPresent = true;
					}
				}
			}
			else
				for (int i=0; i < gen.verRange; i++){
					heapDef += " bv64 Bool ";
					fieldsPresent = true;
				}
				
		}	
		if (fieldsPresent)
			heapDef += ")";
		else 
			heapDef = null;
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

    
    private static boolean lookInStaticFields(ClassDef classDef, String fieldName){
    	Iterable<? extends Field> staticFields;
        if (classDef instanceof DexBackedClassDef) {
            staticFields = ((DexBackedClassDef)classDef).getStaticFields(false);
        } else {
            staticFields = classDef.getStaticFields();
        }
        for (Field field: staticFields) {
        	if (fieldName.equals(Utils.getShortReferenceString(field))) {
        		return true;
        	}
        }
        return false;
    }
    
    private static boolean lookInDynamicFields(ClassDef classDef, String fieldName){
    	Iterable<? extends Field> instanceFields;
        if (classDef instanceof DexBackedClassDef) {
            instanceFields = ((DexBackedClassDef)classDef).getInstanceFields(false);
        } else {
            instanceFields = classDef.getInstanceFields();
        }
        for (Field field: instanceFields) {
        	if (fieldName.equals(Utils.getShortReferenceString(field))) {
        		return true;
        	}
        }
        return false;
    }
    
    private static void writeMissedItem (String className, String item, boolean mode) throws IOException{
    	String fileName = "";
    	if (mode) fileName = "missField.txt"; else fileName = "missMethod.txt";
    	File missFile = new File(fileName);
    	try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(missFile, true)))) {
    		out.println(className + ' ' + item);
    	}catch (IOException e) {
    	}
    }
    
   /* private static void writeFoundItem(String className, String item, boolean mode) throws IOException{
    	String fileName = "";
    	if (mode) fileName = "missField.txt"; else fileName = "missMethod.txt";
    	File missFile = new File(fileName);
    	try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(missFile, true)))) {
    		out.println("founded! " + className + ' ' + item);
    	}catch (IOException e) {
    	}
    }*/
    
    
    /*public static void writeSourceSink(String className, String methodName, IndStr indStr, String outputDirectory, Set<SourceSinkMethod> sourcesSinks) throws IOException {
    	//check if the method is source/sink, and write it to the file in case is is the source/sink
    	File sourcesSinksFile = new File(outputDirectory+"/sourcesSinks.txt");
		boolean isSource = false;
		String classIndex = Integer.toString(indStr.get(className, 'c'));
		String methodIndex = Integer.toString(indStr.get(methodName, 'm'));
    	for (SourceSinkMethod sourceSink: sourcesSinks){
    		String classNameFormat = className.substring(1, className.length()-1);
    		String methodNameFormat = methodName.substring(0, methodName.indexOf('('));
    		
    		if (classNameFormat.equals(sourceSink.className)){
    			if (methodNameFormat.equals(sourceSink.name)){
    				if (!sourceSink.source){
        				isSource = true;
    					try
    					(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(sourcesSinksFile, true)))) {
    						out.println(Utils.factIt("source " + classIndex + ' ' + methodIndex)
    								+ "\n;" + Utils.factIt("source " + sourceSink.className + ' ' + sourceSink.name));
    					}catch (IOException e) {
    					}
    				}
    				else
    					try
						(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(sourcesSinksFile, true)))) {
    						out.println(Utils.factIt("sink " + classIndex + ' ' + methodIndex)
    								+ "\n;" + Utils.factIt("sink " + sourceSink.className + ' ' + sourceSink.name));
    					}catch (IOException e) {
    					}
    				break;
    			}
    		}	
    	}
    	if (!isSource){
    		try
			(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(sourcesSinksFile, true)))) {
				out.println(Utils.factIt("non-source " + classIndex + ' ' + methodIndex));
			}catch (IOException e) {
			}
    	}
    }*/
    
    private static String getReturnTypeIndex(String methodName, IndStr indStr){
    	if (methodName.charAt(methodName.length()-1) == ';')
    		return Integer.toString(indStr.get(methodName.substring(methodName.lastIndexOf(')') + 1), 'c'));
    	else return null;
    }
    
    private static void addFacts(String className, String methodName, IndStr indStr, String outputDirectory){
    	
    	File addFactsFile = new File (outputDirectory + "/additionalFacts.txt");
    	String classIndex = Integer.toString(indStr.get(className, 'c'));
    	String methodIndex = Integer.toString(indStr.get(methodName, 'm'));
    	String returnTypeIndex = getReturnTypeIndex(methodName, indStr);
    	if (methodName.charAt(methodName.length()-1) == 'V')
    		try
			(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(addFactsFile, true)))) {
    			out.println("(rule (absent-void " + classIndex + ' ' + methodIndex + "))");
    		}catch (IOException e) {
    		}
    	else
    		if ((methodName.charAt(methodName.length()-1) != ';') && (!methodName.contains("[")))
    			try
				(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(addFactsFile, true)))) {
    				out.println("(rule (absent-r " + classIndex + ' ' + methodIndex + "))");
    			}catch (IOException e) {
    			}
    		else
    			try
				(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(addFactsFile, true)))) {
    				out.println("(rule (absent-r " + classIndex + ' ' + methodIndex  + "))");
    			}catch (IOException e) {
    			}
    }
    
private static void addFactsFound(String className, String methodName, IndStr indStr, String outputDirectory){
    	File addFactsFile = new File (outputDirectory + "/additionalFacts.txt");
    	String classIndex = Integer.toString(indStr.get(className, 'c'));
    	String methodIndex = Integer.toString(indStr.get(methodName, 'm'));
    	try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(addFactsFile, true)))) {
			out.println("(rule (present " + classIndex + ' ' + methodIndex + "))");
		}catch (IOException e) {
		}
    }
    
    
   /* public void findMissedReferences(List<? extends ClassDef> classDefs, IndStr indStr, String outputDirectory, Set<SourceSinkMethod> sourcesSinks) throws IOException{
    
        Iterator<Pair> it = this.refClassField.iterator();
        String className, fieldName, methodName;
        boolean found;
    	while (it.hasNext()){
    		found = false;
    		Pair p = it.next();
    		className = p.className;
    		fieldName = p.item;
    		for (final ClassDef classDef: classDefs) {
    			if (className.equals(classDef.getType())) {
    				//look in static fields
    				found = lookInStaticFields(classDef, fieldName);
    		        if (!found) {
    		        	//look in dynamic fields
    		        	found = lookInDynamicFields(classDef, fieldName);
    		        }
    			}		
    		}
    	    if (!found) 
    	    	writeMissedItem(className, fieldName, true);
    	    //else 
    	    //	writeFoundItem(className, fieldName, true);
    	}
    	
    	it = this.refClassMethod.iterator();
    	while (it.hasNext()){
    		found = false;
    		Pair p = it.next();
    		className = p.className;
    		methodName = p.item;
    		writeSourceSink(className, methodName, indStr, outputDirectory, sourcesSinks);
      		for (final ClassDef classDef: classDefs) {
    		  if (found) break;
    		  	if (className.equals(classDef.getType())) {
    		  		found = lookInDirectMethods(classDef, methodName);
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
    		if (!found) {
    			writeMissedItem(className, methodName, false);
    			addFacts(className, methodName, indStr, outputDirectory);
    		}
    		else 
    			addFactsFound(className, methodName, indStr, outputDirectory);
    	}
    }*/
    
    public int getNumArg(final int c, final int m, final List<? extends ClassDef> classDefs, final IndStr indStr){
    	int numArg = 0;
    	int superClassInd;
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
    
    /*public Set<Integer> getClassFields(final List<? extends ClassDef> classDefs, final IndStr indStr, final String className, final int instanceNum){
    	Set<Integer> result = Collections.synchronizedSet(new HashSet <Integer>());
    	boolean found = false;
    	for (final ClassDef classDef: classDefs) {
    		if (classDef.getType().equals(className)){
    			found = true;
    			Iterable<? extends Field> instanceFields;
    	        if (classDef instanceof DexBackedClassDef) 
    	            instanceFields = ((DexBackedClassDef)classDef).getInstanceFields(false);
    	        else 
    	            instanceFields = classDef.getInstanceFields();
    	        for (Field field: instanceFields) {
        			result.add(indStr.get(Utils.getShortReferenceString(field), 'f'));
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
    					result.add(indStr.get(className + "->" + f.getName() + ':' + Utils.toDalvikType(f.getType().toString()), 'f'));
    				}
    		}
    		catch (ClassNotFoundException e) {
				e.printStackTrace();
			}
    	}
    	return result;
    }
    */
    
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
    
    public String rInvokePred(final String c, final String m, final int pc, final Map<Integer, String> rUp, final Map<Integer, String> rUpL, final Map<Integer, String> rUpB, final int numArg, final int numReg, final Gen gen){
    	rPredDef(c, m , pc, numArg + numReg, gen);
    	String ret = "(R" + '_' + c + '_' + m + '_' + Integer.toString(pc) + ' ';
    	String v = "", l = "", b = "", var;
    	for (int i = 0; i <= (numArg + numReg); i++){
    		var = rUp.get(i);
			if (var == null) var = "(_ bv0 64)";	
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
    
    public static void addSourceSink(String className, String methodName, IndStr indStr, String outputDirectory, Set<SourceSinkMethod> sourcesSinks, Gen gen) throws IOException {
		int classIndex = indStr.get(className, 'c');
		int methodIndex = indStr.get(methodName, 'm');
		String classNameFormat = className.substring(1, className.length()-1);
		String methodNameFormat = methodName.substring(0, methodName.indexOf('('));
    	for (SourceSinkMethod sourceSink: sourcesSinks){
    		
    		if (classNameFormat.equals(sourceSink.className)){
    			
    			if (methodNameFormat.equals(sourceSink.name)){
    				if (sourceSink.source)
    					gen.putSource(classIndex, methodIndex);
    				else
    					gen.putSink(classIndex, methodIndex);
    				break;
    			}
    		}	
    	}
    	gen.putSink(indStr.get("Ljava/lang/ProcessBuilder;", 'c'), indStr.get("command([Ljava/lang/String;)Ljava/lang/ProcessBuilder;", 'm'));
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
    		addSourceSink(className, methodName, indStr, outputDirectory, sourcesSinks, gen);
      		for (final ClassDef classDef: classDefs) {
    		  if (found) break;
    		  	if (className.equals(classDef.getType())) {
    		  		found = lookInDirectMethods(classDef, methodName);
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
