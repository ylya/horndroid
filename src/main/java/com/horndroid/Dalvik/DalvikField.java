package com.horndroid.Dalvik;

public class DalvikField implements Comparable<DalvikField>{
	final private String name;
	
	public DalvikField(final String name){
		this.name = name;
	}
	public String getName(){
		return name;
	}
    @Override
    public int compareTo(DalvikField o) {
        if (this.name.equals(o.name))
            return 0;
        if (this.name.hashCode() < o.name.hashCode())
            return -1;
        return 1;                    
    }
}
