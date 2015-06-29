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
