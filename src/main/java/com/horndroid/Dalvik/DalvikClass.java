/*
 * MIT License
 *
 * Copyright (c) 2017 TU Wien
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

package com.horndroid.Dalvik;

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
	
	/*
	 * Return the fields of the class, always in the same order.
	 */
	public Set<DalvikField> getFields(){
        if (fields == null) return new HashSet<DalvikField>();
        TreeSet<DalvikField> f = new TreeSet<DalvikField>(fields);
        if (this.superClass instanceof DalvikClass){
            f.addAll(((DalvikClass) this.superClass).getFields());
        }
        return f;
    }
	public Set<DalvikField> getExactFields(){
        if (fields == null) return new HashSet<DalvikField>();
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