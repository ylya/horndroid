
package util;

import gen.Gen;

import java.util.Map;

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
    
    
    
	/*private static void addVar(String var, final Gen gen, final String c){
		if (var.equals((String) "true") || var.equals((String) "false")) return;
		char firstLetter = var.charAt(0);
		switch (firstLetter){
			case 'l': case 'b': gen.addVar("(declare-var " + var + " Bool)", Integer.parseInt(c)); break;
			case 'v': gen.addVar("(declare-var " + var + " bv64)", Integer.parseInt(c)); break;
		}		
	}*/
	
	 private static void rPredDef(final String c, final String m, final int pc, final int size, final Gen gen){
	    	String v = "", l = "", b = "";
	    	for (int i = 0; i <= size; i++){
	    		if (!v.isEmpty()) v = v + ' ' + "bv64";
	    		else v = "bv64";
	    		if (!l.isEmpty()) l = l + ' ' + "Bool";
	    		else l = "Bool";
	    		if (!b.isEmpty()) b = b + ' ' + "Bool";
	    		else b = "Bool";
	    	}
	    	gen.addDef("(declare-rel R_" + c + '_' + m + '_' + Integer.toString(pc) + '(' + v + ' ' + l + ' ' + b + ") interval_relation bound_relation)", Integer.parseInt(c));
	    }
	    
	    public static String rPred(final String c, final String m, final int pc, final Map<Integer, String> rUp, final Map<Integer, String> rUpL, final Map<Integer, String> rUpB, final int numArg, final int numReg, final Gen gen){
	    	rPredDef(c, m , pc, numArg + numReg, gen);
	    	String ret = "(R" + '_' + c + '_' + m + '_' + Integer.toString(pc) + ' ';
	    	String v = "", l = "", b = "", var;
	    	for (int i = 0; i <= (numArg + numReg); i++){
	    		//boolean contains = gen.containsVar(i); 
	    		gen.updateBiggestRegister(i);
	    		var = rUp.get(i);
				if (var == null) {var = 'v' + Integer.toString(i);}
				if (!v.isEmpty()) {v = v + ' ' + var;}
				else {v = var;}	
				//if (!contains){
				//addVar(var, gen, c);
				//gen.putVar(i);
				//}
				var = rUpL.get(i);
				if (var == null) var = 'l' + Integer.toString(i);	
				if (!l.isEmpty()) l = l + ' ' + var;
				else l = var;
				//if (!contains){
				//addVar(var, gen, c);
				//}
				var = rUpB.get(i);
				if (var == null) var = 'b' + Integer.toString(i);	
				if (!l.isEmpty()) b = b + ' ' + var;
				else b = var;
				//if (!contains){
				//addVar(var, gen, c);
				//}
				}	
	    	return ret + v + ' ' + l + ' ' + b + ')';
	    }
	    
	    public static String rInvokePred(final String c, final String m, final int pc, final Map<Integer, String> rUp, final Map<Integer, String> rUpL, final Map<Integer, String> rUpB, final int numArg, final int numReg, final Gen gen,
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
	    
	    private static void resPredDef(final String c, final String m, final int size, final Gen gen){
	    	String v = "", l = "", b = "";
	    	for (int i = 0; i <= size; i++){
	    		if (!v.isEmpty()) v = v + ' ' + "bv64";
	    		else v = "bv64";
	    		if (!l.isEmpty()) l = l + ' ' + "Bool";
	    		else l = "Bool";
	    		if (!b.isEmpty()) b = b + ' ' + "Bool";
	    		else b = "Bool";
	    	}
	    	gen.addDef("(declare-rel RES_" + c + '_' + m + ' ' + '(' + v + ' ' + l + ' ' + b + ") interval_relation bound_relation)", Integer.parseInt(c));
	    }
	    
	    public static String resPred(final String c, final String m, final Map<Integer, String> rUp, final Map<Integer, String> rUpL, final Map<Integer, String> rUpB, final int numArg, final Gen gen){
	    	resPredDef(c, m , numArg, gen);
	    	String ret = "(RES" + '_' + c + '_' + m + ' ';
	    	String v = "", l = "", b = "", var;
	    	for (int i = 0; i <= numArg; i++){
	    		//boolean contains = gen.containsVar(i);
	    		var = rUp.get(i);
				if (var == null) var = 'v' + Integer.toString(i);	
				if (!v.isEmpty()) v = v + ' ' + var;
				else v = var;
				//if (!contains){
				//addVar(var, gen, c);
				//gen.putVar(i);
				//}
				var = rUpL.get(i);
				if (var == null) var = 'l' + Integer.toString(i);	
				if (!l.isEmpty()) l = l + ' ' + var;
				else l = var;
				//if (!contains){
				//addVar(var, gen, c);
				//}
				var = rUpB.get(i);
				if (var == null) var = 'b' + Integer.toString(i);	
				if (!b.isEmpty()) b = b + ' ' + var;
				else b = var;
				//if (!contains){
				//addVar(var, gen, c);
				//}
				}
	    	return ret + v + ' ' + l + ' ' + b + ')';
	    }
	    
	    public static String hPred(final String cname, final String inst, final String element, final String value, final String label, final String block){
	    	return ("(H " + cname + ' ' + inst + ' ' + element + ' ' + value + ' ' + label + ' ' + block + ')');
	    }
	    
	    public static String hiPred(final String cname, final String inst, final String value, final String label, final String block){
	    	return ("(HI " + cname + ' ' + inst +  ' ' + value + ' ' + label + ' ' + block + ')');
	    }
	    
	    public static String iPred(final String cname, final String inst, final String value, final String label, final String block){
	    	return ("(I " + cname + ' ' + inst + ' ' + value + ' ' + label + ' ' + block + ')');
	    }
}
