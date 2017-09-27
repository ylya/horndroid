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

package com.horndroid.strings;

public class ConstString {
	private final int c;
	private final int m;
	private int pc;
	private int v;
	private int val;
	private String dalvikName;
	public ConstString(final int c, final int m, final int pc, final int v, final int val, final String dalvikName){
		this.c = c;
		this.m = m;
		this.pc = pc;
		this.v = v;
		this.val = val;
		this.dalvikName = dalvikName;
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
	public int getV(){
		return v;
	}
	public int getVAL(){
		return val;
	}
	public String getDalvikName(){
		return dalvikName;
	}
	public void putPC(int pc){
		this.pc = pc;
	}
	public void putV(int v){
		this.v = v;
	}
	public void putDalvikName(String dalvikName){
		this.dalvikName = dalvikName;
	}
}
