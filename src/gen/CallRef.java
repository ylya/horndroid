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
