package payload;

import java.util.List;

public class PackedSwitch {
	final private int c, m, codeAddress;
	final private List<Number> targets;
	final private int firstKey;
	public PackedSwitch(final int c, final int m, final int codeAddress, final List<Number> targets, final int firstKey){
		this.c = c;
		this.m = m;
		this.codeAddress = codeAddress;
		this.targets = targets;
		this.firstKey = firstKey;
	}
	public List<Number> getTargets(final int c, final int m, final int codeAddress){
		if ((this.getC() == c) && (this.m == m) && (this.codeAddress == codeAddress)){
			return targets;
		}
		return null;
	}
	public int getFirstKey(final int c, final int m, final int codeAddress){
		if ((this.getC() == c) && (this.m == m) && (this.codeAddress == codeAddress)){
			return firstKey;
		}else{
			throw new RuntimeException( "No first key found");
		}
	}
    public int getC() {
        return c;
    }
    public int getM(){
        return m;
    }
}
