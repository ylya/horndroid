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

package gen;

import org.apache.commons.lang3.builder.EqualsBuilder;
import org.apache.commons.lang3.builder.HashCodeBuilder;

public class CallRef {
	public final int calleeC;
	public final int calleeM;
	public final int callerC;
	public final int callerM;
	public final int callerNextLine;
	public CallRef (int calleeC, int calleeM, int callerC, int callerM, int callerNextLine){
		this.calleeC = calleeC;
		this.calleeM = calleeM;
		this.callerC = callerC;
		this.callerM = callerM;
		this.callerNextLine = callerNextLine;
	}
	@Override
	public int hashCode() {
        return new HashCodeBuilder(17, 31). // two randomly chosen prime numbers
            // if deriving: appendSuper(super.hashCode()).
            append(calleeC).
            append(calleeM).
            append(callerC).
            append(callerM).
            append(callerNextLine).
            toHashCode();
    }
	@Override
    public boolean equals(Object obj) {
       if (!(obj instanceof CallRef))
            return false;
        if (obj == this)
            return true;

        CallRef p = (CallRef) obj;
        return new EqualsBuilder().
            // if deriving: appendSuper(super.equals(obj)).
            append(calleeC, p.calleeC).
            append(calleeM, p.calleeM).
            append(callerC, p.callerC).
            append(callerM, p.callerM).
            append(callerNextLine, p.callerNextLine).
            isEquals();
    }
}
