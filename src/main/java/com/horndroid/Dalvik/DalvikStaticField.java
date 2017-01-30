package com.horndroid.Dalvik;

import org.jf.dexlib2.iface.value.EncodedValue;


public class DalvikStaticField extends DalvikField {
	final private EncodedValue defaultValue;
	
	public DalvikStaticField(final String name, final EncodedValue defaultValue){
		super(name);
		this.defaultValue = defaultValue;
	}
	public EncodedValue getDefaultValue(){
		return defaultValue;
	}
}
