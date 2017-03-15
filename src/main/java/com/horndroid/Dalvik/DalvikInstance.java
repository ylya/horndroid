package com.horndroid.Dalvik;

public class DalvikInstance {
	final private int c, m, pc;
	private GeneralClass type;
	final boolean isObj;
	final boolean isNewInstance; // instances can be created also as a result of method invocation (when we don;t know the implementation,
								 // they are never local. Flag isNewInstacne = true shows that the inctance was created inside the code,
								 // hence, maybe be local.
	
	public DalvikInstance(final int c, final int m , final int pc, final GeneralClass type, final boolean isObj,
						  final boolean isNewInstance){
		this.c = c;
		this.m = m;
		this.pc = pc;
		this.type = type;
		this.isObj = isObj;
		this.isNewInstance = isNewInstance;
	}
	public int getC(){
		return c;
	}
	public int getM(){
		return m;
	}
	public int getPC(){
		return pc;
	}
	public GeneralClass getType(){
		return type;
	}
	public boolean isObj(){
		return isObj;
	}
	public boolean isNewInstance(){
		return isNewInstance;
	}
	/*
	 * Need to be careful and to change the mapping if the DalvikInstances is stored in the Analysis.instances map
	 */
	public void changeType(final GeneralClass type){
		this.type = type;
	}
	
	/*
	 * Return the an hashcode, which depends only on c,m and pc
	 */
    @Override
	public int hashCode(){
        return (c + "_" + m + "_" + pc).hashCode();
    }
    
    static public int hashCode(int c, int m, int pc){
        return (c + "_" + m + "_" + pc).hashCode();
    }
}
