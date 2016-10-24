package Dalvik;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import util.CMPair;

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
            System.out.println("StubImplementation: some methods have no implementation (or there are too many implementations). There are "+numberCM + " stubs but only " + numberDI + " DalvikImplementation found for " + c + " " + m);
        }
        if (numberDI == 0){
            System.out.println("This stub contains no Dalvik implementation :" + c + " " + m);
        }
        return implementation.values();
    }
    
    public DalvikImplementation getDalvikImpByID(int id){
        return implementation.get(id);
    }
}
