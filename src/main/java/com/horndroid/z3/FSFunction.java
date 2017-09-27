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

package com.horndroid.z3;


import com.microsoft.z3.BitVecSort;
import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Context;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Z3Exception;

public class FSFunction {

    // Function
    private final FuncDecl h, hi, i, s, ta, ra, j;
    private FuncDecl reachLH, cFilter;


    public FSFunction(Context ctx, int bvSize) throws Z3Exception {
        BitVecSort bv64 = ctx.mkBitVecSort(bvSize);
        BoolSort bool = ctx.mkBoolSort();
        IntSort integer = ctx.mkIntSort();

        //class name, allocation point, field, value, taint, pointer
        this.h = ctx.mkFuncDecl("H", new Sort[]{bv64, bv64, bv64, bv64, bool, bool}, bool);
        this.hi = ctx.mkFuncDecl("HI", new Sort[]{bv64, bv64, bv64, bool, bool}, bool);
        this.i = ctx.mkFuncDecl("I", new Sort[]{bv64, bv64, bv64, bool, bool}, bool);
        this.s = ctx.mkFuncDecl("S", new Sort[]{integer, integer, bv64, bool, bool}, bool);
        
        this.ta = ctx.mkFuncDecl("TA", new Sort[]{bv64, bool}, bool); //used for computing taint on the connected component on the heap
        this.ra = ctx.mkFuncDecl("RA", new Sort[]{bv64, bv64}, bool); //used for computing the connected component of the heap element
        this.j = ctx.mkFuncDecl("J", new Sort[]{bv64, bool}, bool); //used for computing the join taint of heap elements
    }

    public FuncDecl getH() {
        return h;
    }

    public FuncDecl getHi() {
        return hi;
    }

    public FuncDecl getI() {
        return i;
    }

    public FuncDecl getS() {
        return s;
    }
    
    public FuncDecl getTaint(){
        return ta;
    }
    public FuncDecl getReachLH(){
    	return reachLH;
    }
    public void setReachLH(FuncDecl f){
    	this.reachLH = f;
    }
    public FuncDecl getCFilter(){
    	return cFilter;
    }
    public void setCFilter(FuncDecl f){
    	this.cFilter = f;
    }
    /*public FuncDecl getLiftLH(){
    	return liftLH;
    }
    public void setLiftLH(FuncDecl f){
    	this.liftLH = f;
    }*/
    public FuncDecl getReach(){
        return ra;
    }
    public FuncDecl getJoin(){
        return j;
    }
}
