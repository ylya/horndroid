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

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import javax.annotation.Nonnull;
import util.iface.IndStr;


public class IndStrDef implements IndStr {
	private final int def = 1; //reserving 0 for the artificial 'main' class
	@Nonnull public final Map<String, Integer> classMap;
	@Nonnull private int classInd;
	@Nonnull public final Map<String, Integer> fieldMap;
	@Nonnull private int fieldInd;
	@Nonnull public final Map<String, Integer> methodMap;
	@Nonnull private int methodInd;
	@Nonnull public final Map<String, Integer> stringMap;
	@Nonnull private int stringInd;
	public IndStrDef() {
		this.classMap = Collections.synchronizedMap(new HashMap <String, Integer>());
		this.fieldMap =  Collections.synchronizedMap(new HashMap <String, Integer>());
		this.methodMap =  Collections.synchronizedMap(new HashMap <String, Integer>());
		this.stringMap =  Collections.synchronizedMap(new HashMap <String, Integer>());
		}
	@Override
	public int biggestC(){
		int max = 0;
		for (Map.Entry<String, Integer> entry : classMap.entrySet())
	    	if (entry.getValue() > max) 
	    		max = entry.getValue();
		return max;
	}
	@Override
	public int biggestM(){
		int max = 0;
		for (Map.Entry<String, Integer> entry : methodMap.entrySet())
	    	if (entry.getValue() > max) 
	    		max = entry.getValue();
		return max;
	}
	
	@Override
	public int get(String str, char c) {
		int ind = -1;
		try{
			switch (c)
			{
				case 'c' : ind = classMap.get(str); break;
				case 'f' : ind = fieldMap.get(str); break;
				case 'm' : ind = methodMap.get(str); break;
				case 's' : ind = stringMap.get(str); break;
				
			}
			return ind;
		}
		catch(NullPointerException e)
		{
			return put(str, c);
		}
	}

	@Override
	public int put(String str, char c) {
		switch (c){
		case 'c' :
			if (!str.equals((String) "LdummyMainClass;")){
				if (classMap.isEmpty()) classInd = def; 
				else classInd++; 
				classMap.put(str , Integer.valueOf(classInd)); 
				return classInd;
			}
			else return 0;
		case 'f' : 
			if (fieldMap.isEmpty()) {fieldInd = def;} else fieldInd++; fieldMap.put(str , Integer.valueOf(fieldInd)); return fieldInd;
		case 'm' : 
			if (!str.equals((String) "dummyMainMethod()V")){
				if (methodMap.isEmpty()) methodInd = def;
				else methodInd++; 
				methodMap.put(str , Integer.valueOf(methodInd)); 
				return methodInd;
			}
			else return 0;
		case 's' : 
			if (stringMap.isEmpty()) {stringInd = def;} else stringInd++; stringMap.put(str , Integer.valueOf(stringInd)); return stringInd;
		}
		return -1;
	}
	
	public void printMethodIndex() throws FileNotFoundException, UnsupportedEncodingException{
		PrintWriter writer = new PrintWriter("methodIndex.txt", "UTF-8");
		for (String str: methodMap.keySet()){
			String ind = Integer.toString(methodMap.get(str));
            writer.println(ind + " " + str);  
		}
		writer.close();
	}
	
	public void printClassIndex() throws FileNotFoundException, UnsupportedEncodingException{
		PrintWriter writer = new PrintWriter("classIndex.txt", "UTF-8");
		for (String str: classMap.keySet()){
			String ind = Integer.toString(classMap.get(str));
            writer.println(ind + " " + str);  
		}
		writer.close();
	}

}
