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

public class DalvikInstance {
	final private int c, m, pc;
	private GeneralClass type;
	final boolean isObj;
	final boolean isNewInstance; // instances can be created also as a result of method invocation (when we don;t know the implementation,
								 // they are never local. Flag isNewInstacne = true shows that the inctance was created inside the code,
								 // hence, maybe be local.
	
	public DalvikInstance(final int c, final int m , final int pc, final GeneralClass type, final boolean isObj,
						  final boolean isNewInstance){
		this.c = c;
		this.m = m;
		this.pc = pc;
		this.type = type;
		this.isObj = isObj;
		this.isNewInstance = isNewInstance;
	}
	public int getC(){
		return c;
	}
	public int getM(){
		return m;
	}
	public int getPC(){
		return pc;
	}
	public GeneralClass getType(){
		return type;
	}
	public boolean isObj(){
		return isObj;
	}
	public boolean isNewInstance(){
		return isNewInstance;
	}
	/*
	 * Need to be careful and to change the mapping if the DalvikInstances is stored in the Analysis.instances map
	 */
	public void changeType(final GeneralClass type){
		this.type = type;
	}
	
	/*
	 * Return the an hashcode, which depends only on c,m and pc
	 */
    @Override
	public int hashCode(){
        return (c + "_" + m + "_" + pc).hashCode();
    }
    
    static public int hashCode(int c, int m, int pc){
        return (c + "_" + m + "_" + pc).hashCode();
    }
}
