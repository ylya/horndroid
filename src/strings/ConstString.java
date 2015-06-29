package strings;

public class ConstString {
	private final int c;
	private final int m;
	private int pc;
	private int v;
	private int val;
	public ConstString(final int c, final int m, final int pc, final int v, final int val){
		this.c = c;
		this.m = m;
		this.pc = pc;
		this.v = v;
		this.val = val;
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
	public int getV(){
		return v;
	}
	public int getVAL(){
		return val;
	}
	public void putPC(int pc){
		this.pc = pc;
	}
	public void putV(int v){
		this.v = v;
	}
}
