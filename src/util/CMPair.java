package util;

import org.apache.commons.lang3.builder.EqualsBuilder;
import org.apache.commons.lang3.builder.HashCodeBuilder;

public class CMPair {
	final int c;
	final int m;
	public CMPair (int c, int m){
		this.c = c;
		this.m = m;
	}
	@Override
	public int hashCode() {
        return new HashCodeBuilder(17, 31). // two randomly chosen prime numbers
            // if deriving: appendSuper(super.hashCode()).
            append(c).
            append(m).
            toHashCode();
    }
	@Override
    public boolean equals(Object obj) {
       if (!(obj instanceof CMPair))
            return false;
        if (obj == this)
            return true;

        CMPair p = (CMPair) obj;
        return new EqualsBuilder().
            // if deriving: appendSuper(super.equals(obj)).
            append(c, p.c).
            append(m, p.m).
            isEquals();
    }
}
