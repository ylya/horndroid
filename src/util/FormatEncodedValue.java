package util;

import util.iface.IndStr;

import java.io.IOException;

import org.jf.dexlib2.ValueType;
import org.jf.dexlib2.iface.value.BooleanEncodedValue;
import org.jf.dexlib2.iface.value.ByteEncodedValue;
import org.jf.dexlib2.iface.value.CharEncodedValue;
import org.jf.dexlib2.iface.value.DoubleEncodedValue;
import org.jf.dexlib2.iface.value.EncodedValue;
import org.jf.dexlib2.iface.value.EnumEncodedValue;
import org.jf.dexlib2.iface.value.FieldEncodedValue;
import org.jf.dexlib2.iface.value.FloatEncodedValue;
import org.jf.dexlib2.iface.value.IntEncodedValue;
import org.jf.dexlib2.iface.value.LongEncodedValue;
import org.jf.dexlib2.iface.value.ShortEncodedValue;
import org.jf.dexlib2.iface.value.StringEncodedValue;
import org.jf.dexlib2.util.ReferenceUtil;

public class FormatEncodedValue {
	
	 public static String toString(EncodedValue encodedValue, IndStr indStr) throws IOException {
		 	long lVal;
	        switch (encodedValue.getValueType()) {
	            case ValueType.ANNOTATION:
	            	return "";
	            case ValueType.ARRAY:
	            	return "";
	            case ValueType.BOOLEAN:
	            	if (((BooleanEncodedValue)encodedValue).getValue()) {
	                    return Utils.hexDec64(1);
	                } else {
	                	return Utils.hexDec64(0);
	                }
	            case ValueType.BYTE:
	            	lVal = (long) ((ByteEncodedValue)encodedValue).getValue();
	             	return Utils.hexDec64(lVal);
	            case ValueType.CHAR:
	            	lVal = (long) ((CharEncodedValue)encodedValue).getValue();
	             	return Utils.hexDec64(lVal);
	            case ValueType.DOUBLE:
	            	lVal = Double.doubleToRawLongBits(((DoubleEncodedValue)encodedValue).getValue());
	            	return Utils.hexDec64(lVal);
	            case ValueType.ENUM:
	            	return Utils.hexDec64(indStr.get(ReferenceUtil.getShortFieldDescriptor(((EnumEncodedValue)encodedValue).getValue()),'f'));
	            case ValueType.FIELD:
	            	return Utils.hexDec64(indStr.get(ReferenceUtil.getShortFieldDescriptor(((FieldEncodedValue)encodedValue).getValue()),'f'));
	            case ValueType.FLOAT:
	            	lVal = (long) Float.floatToRawIntBits(((FloatEncodedValue)encodedValue).getValue());
	            	return Utils.hexDec64(lVal);
	            case ValueType.INT:
	            	return Utils.hexDec64((long)((IntEncodedValue)encodedValue).getValue());
	            case ValueType.LONG:
	            	return Utils.hexDec64(((LongEncodedValue)encodedValue).getValue());
	            case ValueType.METHOD:
	            	return "";
	            case ValueType.NULL:
	            	return Utils.hexDec64((long) 0);
	            case ValueType.SHORT:
	            	return Utils.hexDec64((long) ((ShortEncodedValue)encodedValue).getValue());
	            case ValueType.STRING:
	            	return Utils.hexDec64(indStr.get(((StringEncodedValue)encodedValue).getValue(),'s'));
	            case ValueType.TYPE:
	            	return "";
	        }
	        return "";
	    }

}