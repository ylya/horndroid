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

package com.horndroid.Dalvik;

//import java.util.Collections;
//import java.util.HashSet;
//import java.util.Set;

/*
 * A implementation of a method c,m
 */
public class DalvikImplementation extends Implementation{
	final private DalvikClass dc;
	final private DalvikMethod dm;
	//final private Set<DalvikInstance> di;
	
	public DalvikImplementation(final DalvikClass dc, final DalvikMethod dm){
		this.dc = dc;
		this.dm = dm;
		//this.di = Collections.synchronizedSet(new HashSet<DalvikInstance>());
	}
	public DalvikClass getDalvikClass(){
		return dc;
	}
	public DalvikMethod getMethod(){
		return dm;
	}
	/*public void putInstance(final DalvikInstance di){
		this.di.add(di);
	}
	public Set<DalvikInstance> getInstances(){
		return di;
	}*/
}
