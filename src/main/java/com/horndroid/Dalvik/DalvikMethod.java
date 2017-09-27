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

import org.jf.dexlib2.iface.instruction.Instruction;

import com.google.common.collect.ImmutableList;

public class DalvikMethod {
	final private String name;
	final private int numArg;
	final private int numReg;
	final private String returnType;
	final private boolean isVoid;
	final private ImmutableList<Instruction> instructions;
	
	public DalvikMethod(final String name, final int numArg, final int numReg, final String returnType, final boolean isVoid, final ImmutableList<Instruction> instructions){
		this.name = name;
		this.numArg = numArg;
		this.numReg = numReg;
		this.returnType = returnType;
		this.isVoid = isVoid;
		this.instructions = instructions;
	}
	public String getName(){
		return name;
	}
	public int getNumArg(){
		return numArg;
	}
	public int getNumReg(){
		return numReg;
	}
	public String getReturnType(){
		return returnType;
	}
	public boolean isVoid(){
		return isVoid;
	}
	public ImmutableList<Instruction> getInstructions(){
		return instructions;
	}
}
