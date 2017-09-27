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

package com.horndroid.payload;

import java.util.List;

public class PackedSwitch {
	final private int c, m, codeAddress;
	final private List<Number> targets;
	final private int firstKey;
	public PackedSwitch(final int c, final int m, final int codeAddress, final List<Number> targets, final int firstKey){
		this.c = c;
		this.m = m;
		this.codeAddress = codeAddress;
		this.targets = targets;
		this.firstKey = firstKey;
	}
	public List<Number> getTargets(final int c, final int m, final int codeAddress){
		if ((this.getC() == c) && (this.m == m) && (this.codeAddress == codeAddress)){
			return targets;
		}
		return null;
	}
	public int getFirstKey(final int c, final int m, final int codeAddress){
		if ((this.getC() == c) && (this.m == m) && (this.codeAddress == codeAddress)){
			return firstKey;
		}else{
			throw new RuntimeException( "No first key found");
		}
	}
    public int getC() {
        return c;
    }
    public int getM(){
        return m;
    }
}
