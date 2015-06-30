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

import org.jf.dexlib2.iface.reference.FieldReference;
import org.jf.dexlib2.iface.reference.MethodReference;
import org.jf.dexlib2.iface.reference.Reference;
import org.jf.dexlib2.iface.reference.StringReference;
import org.jf.dexlib2.iface.reference.TypeReference;
import org.jf.dexlib2.util.ReferenceUtil;
import org.jf.util.StringUtils;

public class Utils {
    
    public static String factIt(String it)
    {
    	return "(rule (" + it + "))";
    }
    
    public static String factItc(String it)
    {
    	return ";(rule (" + it + "))";
    }
    
    public static String hexDec64It(String it, int size)
    {
    	return "(_ bv" + it + " " + Integer.toString(size) + ')';
    }
    
    public static String hexDec64NegIt(String it, int size)
    {
    	return "(bvneg (_ bv" + it + " " + Integer.toString(size) + "))";
    }
    
    public static String hexDec64(long i, int size)
    {
    	if (Long.toString(i).charAt(0) == '-')
    		return hexDec64NegIt(Long.toString(i).replace("-", ""), size);

    	else
    		return hexDec64It(Long.toString(i), size);
    }
    
    public static String Dec(int i)
    {
    	return Integer.toString(i);
    }
    
    public static String toStandardJavaClassName(String name){
    	String result = name.substring(1, name.length() - 1);
    	
    	return result.replace('/', '.');
    }
    
    public static String toStandardDalvikClassName(String name){
    	return 'L' + name.replace('.', '/') + ';';
    }
    
    public static String toDalvikType(String type){
    	String arr = "";
    	final int size = type.length() - type.replace("[", "").length();
    	for (int i = 0; i< size; i++){
    		arr = arr + '[';
    	}
		final String name  = type.split("\\[")[0];
    	switch (name){
    	case "void":
    		return "V";
    	case "boolean":
    		return arr + "Z";
    	case "byte":
    		return arr + "B";
    	case "short":
    		return arr + "S";
    	case "char":
    		return arr + "C";
    	case "int":
    		return arr + "I";
    	case "long":
    		return arr + "J";
    	case "float":
    		return arr + "F";
    	case "double":
    		return arr + "D";
		default:
			return arr + 'L' + name.replace('.', '/') + ';';
    	}
    }
    public static String getShortMethodDescriptor(MethodReference methodReference) {
        StringBuilder sb = new StringBuilder();
        sb.append(methodReference.getName());
        sb.append('(');
        for (CharSequence paramType: methodReference.getParameterTypes()) {
            sb.append(paramType);
        }
        sb.append(')');
        sb.append(methodReference.getReturnType());
        return sb.toString();
    }
    
    public static String getShortReferenceString(Reference reference) {
        if (reference instanceof StringReference) {
            return String.format("\"%s\"", StringUtils.escapeString(((StringReference)reference).getString()));
        }
        if (reference instanceof TypeReference) {
            return ((TypeReference)reference).getType();
        }
        if (reference instanceof FieldReference) {
            return ReferenceUtil.getShortFieldDescriptor((FieldReference)reference);
        }
        if (reference instanceof MethodReference) {
            return getShortMethodDescriptor((MethodReference)reference);
        }
        return null;
    }
}
