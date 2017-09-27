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

import java.util.Map;
import java.util.Map.Entry;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;

public class LHUpdate {
    private Map<Integer,BitVecExpr> bv;
    private Map<Integer,BoolExpr> h;
    private Map<Integer,BoolExpr> l;
    private Map<Integer,BoolExpr> g;
    
    public LHUpdate(Map<Integer,BitVecExpr> bv, Map<Integer,BoolExpr> h, Map<Integer,BoolExpr> l, Map<Integer,BoolExpr> g){
        this.bv = bv;
        this.h= h;
        this.l = l;
        this.g = g;
    }
    
    public void apply(Map<Integer, BitVecExpr> regUpLHV,Map<Integer, BoolExpr> regUpLHH,Map<Integer, BoolExpr> regUpLHL,Map<Integer, BoolExpr> regUpLHG){
        for (Entry<Integer,BitVecExpr> entry : bv.entrySet()){
        	regUpLHV.put(entry.getKey(), entry.getValue());
        }
        for (Entry<Integer,BoolExpr> entry : h.entrySet()){
        	regUpLHH.put(entry.getKey(), entry.getValue());
        }
        for (Entry<Integer,BoolExpr> entry : l.entrySet()){
        	regUpLHL.put(entry.getKey(), entry.getValue());
        }
        for (Entry<Integer,BoolExpr> entry : g.entrySet()){
        	regUpLHG.put(entry.getKey(), entry.getValue());
        }
    }
}
