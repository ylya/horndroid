/*
 * [The "BSD licence"]
 * Copyright (c) 2015 Ilya Grishchenko
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

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
