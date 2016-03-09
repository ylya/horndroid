package Dalvik;

public class DalvikInstance {
	final private int c, m, pc;
	private GeneralClass type;
	final boolean isObj;
	
	public DalvikInstance(final int c, final int m , final int pc, final GeneralClass type, final boolean isObj){
		this.c = c;
		this.m = m;
		this.pc = pc;
		this.type = type;
		this.isObj = isObj;
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
