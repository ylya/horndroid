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

import java.util.Set;
import java.util.TreeMap;

public class RegInfo {
    private TreeMap<Integer,Boolean> high;
    private TreeMap<Integer,Boolean> local;
    private TreeMap<Integer,Boolean> global;

    
    public RegInfo(){
        high = new TreeMap<Integer,Boolean>();
        local = new TreeMap<Integer,Boolean>();
        global = new TreeMap<Integer,Boolean>();
    }
    
    public boolean highGet(int num){
        return high.get(num);
    }
    
    public boolean localGet(int num){
        return local.get(num);
    }
    
    public boolean globalGet(int num){
        return global.get(num);
    }
    
    public void highPut(int num, boolean bool){
        high.put(num,bool);
    }
    
    public void localPut(int num, boolean bool){
        local.put(num,bool);
        
    }    public void globalPut(int num, boolean bool){
        global.put(num,bool);
    }
    
    public Set<Integer> keySet(){
        return high.keySet();
    }
    
}