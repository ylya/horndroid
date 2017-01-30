
package com.horndroid.util;

import org.apache.commons.lang3.builder.EqualsBuilder;
import org.apache.commons.lang3.builder.HashCodeBuilder;

public class CMPair {
	final private int c;
	final private int m;
	public CMPair (int c, int m){
		this.c = c;
		this.m = m;
	}
	public int getC(){
		return c;
	}
	public int getM(){
		return m;
	}
	@Override
	public int hashCode() {
        return new HashCodeBuilder(17, 31).
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
            append(c, p.c).
            append(m, p.m).
            isEquals();
    }
}
