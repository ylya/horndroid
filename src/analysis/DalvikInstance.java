package analysis;

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
	public void changeType(final GeneralClass type){
		this.type = type;
	}
}
