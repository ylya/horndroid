
/*
 * MIT License
 *
 * Copyright (c) 2017 TU Wien
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

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