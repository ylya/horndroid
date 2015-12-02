package payload;

import java.util.Map;

import javax.annotation.Nonnull;

public class SparseSwitch {
	final private int c, m, codeAddress;
	@Nonnull private final Map<Integer, Integer> targets;
	public SparseSwitch(final int c, final int m, final int codeAddress, final Map<Integer, Integer> targets){
		this.c = c;
		this.m = m;
		this.codeAddress = codeAddress;
		this.targets = targets;
	}
	public Map<Integer, Integer> getTargets(final int c, final int m, final int codeAddress){
		if ((this.getC() == c) && (this.m == m) && (this.codeAddress == codeAddress)){
			return targets;
		}
		return null;
	}
    public int getC() {
        return c;
    }
}
