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
    
    public static String hexDec64It(String it)
    {
    	return "(_ bv" + it + " 64)";
    }
    
    public static String hexDec64NegIt(String it)
    {
    	return "(bvneg (_ bv" + it + " 64))";
    }
    
    public static String hexDec64(long i)
    {
    	if (Long.toString(i).charAt(0) == '-')
    		return hexDec64NegIt(Long.toString(i).replace("-", ""));

    	else
    		return hexDec64It(Long.toString(i));
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
