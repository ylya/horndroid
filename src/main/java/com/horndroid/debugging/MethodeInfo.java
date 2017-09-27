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

package com.horndroid.debugging;

import com.horndroid.analysis.Analysis;

import java.util.HashMap;
import java.util.Set;
import java.util.TreeSet;


public class MethodeInfo {
    public String c;
    public String m;
    public int numReg;
    public RegInfo[] regInfo;
    private HashMap<Integer,HashMap<Integer, LHInfo>> lhMap;
    private Analysis analysis;

    public MethodeInfo(Analysis analysis, String c, String m, int numReg){
        this.c = c;
        this.m = m;
        this.numReg = numReg;
        this.analysis = analysis;
        
        regInfo = new RegInfo[numReg];
        for (int i = 0; i < regInfo.length; i++){
            regInfo[i] = new RegInfo();
        }
        
        lhMap = new HashMap<Integer,HashMap<Integer, LHInfo>>();

}
    
    private void addLHElem(int instanceNum, int field, final LHInfo lhinfo){
        if (!lhMap.containsKey(instanceNum)){
            HashMap<Integer, LHInfo> hmap = new HashMap<Integer, LHInfo>();
            lhMap.put(instanceNum, hmap);
        }
        lhMap.get(instanceNum).put(field, lhinfo);
    }
    
    public Set<LHKey> getLHKeySet(){
        TreeSet<LHKey> keySet = new TreeSet<LHKey>();
        for (int instanceNum : lhMap.keySet()){
            for (int field : lhMap.get(instanceNum).keySet()){
                keySet.add(new LHKey(instanceNum, field));
            }
        }
        return keySet;
    }
    
    public final LHInfo getLHInfo(int instanceNum, int field){
        if (lhMap.containsKey(instanceNum)){
            if (lhMap.get(instanceNum).containsKey(field))
                return lhMap.get(instanceNum).get(field);
        }
        
        final LHInfo lhinfo = LHInfo.lhInfoFromInstanceNum(analysis,instanceNum, field);
        addLHElem(instanceNum, field, lhinfo);
        return lhinfo;
    }
}
