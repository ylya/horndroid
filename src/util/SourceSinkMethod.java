
package util;

import javax.annotation.Nonnull;

import org.apache.commons.lang3.builder.EqualsBuilder;
import org.apache.commons.lang3.builder.HashCodeBuilder;

public class SourceSinkMethod {
	@Nonnull public final String name;
	@Nonnull public final String className;
	@Nonnull public final boolean source;
	
	public SourceSinkMethod (String name, String className, boolean source){
		this.name = name;
		this.className = className;
		this.source = source;
	}
	@Override
	public int hashCode() {
        return new HashCodeBuilder(17, 31). // two randomly chosen prime numbers
            // if deriving: appendSuper(super.hashCode()).
            append(name).
            append(className).
            toHashCode();
    }
	@Override
    public boolean equals(Object obj) {
       if (!(obj instanceof SourceSinkMethod))
            return false;
        if (obj == this)
            return true;

        SourceSinkMethod p = (SourceSinkMethod) obj;
        return new EqualsBuilder().
            // if deriving: appendSuper(super.equals(obj)).
            append(name, p.name).
            append(className, p.className).
            isEquals();
    }
}
