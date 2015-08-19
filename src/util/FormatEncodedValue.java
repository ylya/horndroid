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
	
	 public static String toString(EncodedValue encodedValue, int size)  {
		 	long lVal;
	        switch (encodedValue.getValueType()) {
	            case ValueType.ANNOTATION:
	            	return "";
	            case ValueType.ARRAY:
	            	return "";
	            case ValueType.BOOLEAN:
	            	if (((BooleanEncodedValue)encodedValue).getValue()) {
	                    return Utils.hexDec64(1, size);
	                } else {
	                	return Utils.hexDec64(0, size);
	                }
	            case ValueType.BYTE:
	            	lVal = (long) ((ByteEncodedValue)encodedValue).getValue();
	             	return Utils.hexDec64(lVal, size);
	            case ValueType.CHAR:
	            	lVal = (long) ((CharEncodedValue)encodedValue).getValue();
	             	return Utils.hexDec64(lVal, size);
	            case ValueType.DOUBLE:
	            	lVal = Double.doubleToRawLongBits(((DoubleEncodedValue)encodedValue).getValue());
	            	return Utils.hexDec64(lVal, size);
	            case ValueType.ENUM:
	            	return Utils.hexDec64(ReferenceUtil.getShortFieldDescriptor(((EnumEncodedValue)encodedValue).getValue()).hashCode(), size);
	            case ValueType.FIELD:
	            	return Utils.hexDec64(ReferenceUtil.getShortFieldDescriptor(((FieldEncodedValue)encodedValue).getValue()).hashCode(), size);
	            case ValueType.FLOAT:
	            	lVal = (long) Float.floatToRawIntBits(((FloatEncodedValue)encodedValue).getValue());
	            	return Utils.hexDec64(lVal, size);
	            case ValueType.INT:
	            	return Utils.hexDec64((long)((IntEncodedValue)encodedValue).getValue(), size);
	            case ValueType.LONG:
	            	return Utils.hexDec64(((LongEncodedValue)encodedValue).getValue(), size);
	            case ValueType.METHOD:
	            	return "";
	            case ValueType.NULL:
	            	return Utils.hexDec64((long) 0, size);
	            case ValueType.SHORT:
	            	return Utils.hexDec64((long) ((ShortEncodedValue)encodedValue).getValue(), size);
	            case ValueType.STRING:
	            	return Utils.hexDec64(((StringEncodedValue)encodedValue).getValue().hashCode(), size);
	            case ValueType.TYPE:
	            	return "";
	        }
	        return "";
	    }

}