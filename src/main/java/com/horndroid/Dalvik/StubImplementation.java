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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import com.horndroid.executors.HorndroidExecutor;
import com.horndroid.util.CMPair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/*
 * A stub implementation of a method c,m
 * replaceMethods and replaceMethodsDependent are the methods used to replace c,m
 * Moreover the methods in replaceMethodDependent should take as input the output of a certain method in replaceMethod
 */
public class StubImplementation extends Implementation {
    private int c;
    private int m;
    private Set<CMPair> replaceMethods;
    private Map<CMPair,CMPair> replaceMethodsDependent;
    private Map<Integer,DalvikImplementation> implementation;
    private int numberCM;
    private int numberDI;
    private static final Logger LOGGER = LogManager.getLogger(StubImplementation.class);
    
    public StubImplementation(int c, int m){
        this.c = c;
        this.m = m;
        this.replaceMethods = new HashSet<CMPair>();
        this.replaceMethodsDependent = new HashMap<CMPair,CMPair>();
        this.implementation = new HashMap<Integer,DalvikImplementation>();
    }

    public void addMethod(CMPair cmPair) {
        numberCM++;
        replaceMethods.add(cmPair);
    }

    /*
     * Add the two CMPair 'from' and 'to'
     * The result of invocation 'from' should be used has input by 'to'
     */
    public void addDependentMethod(CMPair from, CMPair to) {
        numberCM++;
        replaceMethods.add(from);
        replaceMethods.add(to);
        replaceMethodsDependent.put(to,from);
    }
    
    public Set<CMPair> getStubsCM(){
        return replaceMethods;
    }
    
    public boolean hasStub(){
        return !replaceMethods.isEmpty();
    }
    
    public void addDalvikImp(DalvikImplementation di){
        numberDI++;
        CMPair cmp = new CMPair(di.getDalvikClass().getType().hashCode(),di.getMethod().getName().hashCode());
        implementation.put(cmp.hashCode(),di);
    }
    
    public final Map<CMPair,CMPair> getDependentInvokation(){
        return this.replaceMethodsDependent;
    }
    
    public Collection<DalvikImplementation> getDalvikImp(){
        if (numberCM != numberDI){
            LOGGER.info("StubImplementation: some methods have no implementation (or there are too many implementations). There are "+numberCM + " stubs but only " + numberDI + " DalvikImplementation found for " + c + " " + m);
        }
        if (numberDI == 0){
            LOGGER.info("This stub contains no Dalvik implementation :" + c + " " + m);
        }
        return implementation.values();
    }
    
    public DalvikImplementation getDalvikImpByID(int id){
        return implementation.get(id);
    }
}
