
package com.horndroid.gen;

import org.apache.commons.lang3.builder.EqualsBuilder;
import org.apache.commons.lang3.builder.HashCodeBuilder;

public class Clause {
	private String head;
	private String body;
	public Clause(){
		this.head = "";
		this.body = "";
	}
	public void appendHead(String a){
		head = head + ' ' + a;
	}
	public void appendBody(String a){
		body =  body + ' ' +a;
	}
	public String toString(){
		return 
				"(rule (=> \n"
				+ head  + " \n" + body 
				+ "))";
	}
	@Override
	public int hashCode() {
        return new HashCodeBuilder(17, 31). // two randomly chosen prime numbers
            // if deriving: appendSuper(super.hashCode()).
            append(head.replaceAll("\\s","")).
            append(body.replaceAll("\\s","")).
            toHashCode();
    }
	@Override
    public boolean equals(Object obj) {
       if (!(obj instanceof Clause))
            return false;
        if (obj == this)
            return true;

        Clause c = (Clause) obj;
        return new EqualsBuilder().
            // if deriving: appendSuper(super.equals(obj)).
            append(head.replaceAll("\\s",""), c.head.replaceAll("\\s","")).
            append(body.replaceAll("\\s",""), c.body.replaceAll("\\s","")).
            isEquals();
    }
}