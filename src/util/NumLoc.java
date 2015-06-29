package util;

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import javax.annotation.Nonnull;

import org.apache.commons.lang3.builder.EqualsBuilder;
import org.apache.commons.lang3.builder.HashCodeBuilder;

final class LocInf{
	final int c;
	final int m;
	final int loc;
	public LocInf (int c, int m, int loc){
		this.c = c;
		this.m = m;
		this. loc = loc;
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
       if (!(obj instanceof LocInf))
            return false;
        if (obj == this)
            return true;

        LocInf p = (LocInf) obj;
        return new EqualsBuilder().
            // if deriving: appendSuper(super.equals(obj)).
            append(c, p.c).
            append(m, p.m).
            isEquals();
    }
}

public class NumLoc {
	@Nonnull private final Set<LocInf> locInfSet;
	@Nonnull private final Set<LocInf> parInfSet;
	
	public NumLoc(){
		this.locInfSet = Collections.synchronizedSet(new HashSet <LocInf>());
		this.parInfSet = Collections.synchronizedSet(new HashSet <LocInf>());
	}
	
	public void put(int c, int m , int loc){
		this.locInfSet.add(new LocInf(c, m, loc));
	}
	public int get(int c, int m){
		Iterator<LocInf> it = this.locInfSet.iterator();
		while (it.hasNext()){
			LocInf l = it.next();
			if ((l.c == c) && (l.m == m)) return l.loc;
		}
		return 0;
	}
	
	public void putp(int c, int m , int loc){
		this.parInfSet.add(new LocInf(c, m, loc));
	}
	public int getp(int c, int m){
		Iterator<LocInf> it = this.parInfSet.iterator();
		while (it.hasNext()){
			LocInf l = it.next();
			if ((l.c == c) && (l.m == m)) return l.loc;
		}
		return 0;
	}
}
