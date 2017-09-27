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

public class LHInfo {
        private RegInfo regInfo;
        public String allocatedClass;
        public int field;
        public String c;
        public String m;
        public int pc;
        
        public LHInfo(String ac, int f, String c, String m, int pc){
            this.regInfo = new RegInfo();
            
            allocatedClass = ac;
            field = f;
            this.c = c;
            this.m = m;
            this.pc = pc;
        }
        
        public static LHInfo lhInfoFromInstanceNum(Analysis analysis, int instanceNum, int field){
            return new LHInfo(analysis.getAllocationPointClass(instanceNum), field, analysis.getAllocationPointClassDebug(instanceNum), analysis.getAllocationPointMethod(instanceNum), analysis.getAllocationPointPC(instanceNum));
        }

        public RegInfo getRegInfo() {
            return regInfo;
        }

}

