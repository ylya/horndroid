package Dalvik;

import java.util.HashSet;
import java.util.Set;

import util.CMPair;
import util.ECMPair;

/*
 * A stub implementation of a method c,m
 * replaceMethods and replaceMethodsDependent are the methods used to replace c,m
 * Moreover the methods in replaceMethodDependent should take as input the output of a certain method in replaceMethod
 */
public class StubImplementation extends Implementation {
    private int c;
    private int m;
    private Set<CMPair> replaceMethods;
    private Set<ECMPair> replaceMethodsDependent;
    private Set<DalvikImplementation> implementation;
    private int numberCM;
    private int numberDI;
    
    public StubImplementation(int c, int m){
        this.c = c;
        this.m = m;
        this.replaceMethods = new HashSet<CMPair>();
        this.replaceMethodsDependent = new HashSet<ECMPair>();
        this.implementation = new HashSet<DalvikImplementation>();
    }

    public void addMethod(CMPair cmPair) {
        numberCM++;
        replaceMethods.add(cmPair);
    }

    public void addDependentMethod(ECMPair ecmPair) {
        numberCM++;
        replaceMethodsDependent.add(ecmPair);
    }
    
    public Set<CMPair> getStubsCM(){
        HashSet<CMPair> hs = new HashSet<CMPair>(replaceMethods);
        for (ECMPair ecm : replaceMethodsDependent){
            hs.add(ecm);
        }
        return hs;
    }
    
    public boolean hasStub(){
        return (!replaceMethods.isEmpty()) || (!replaceMethodsDependent.isEmpty());
    }
    
    public void addDalvikImp(DalvikImplementation di){
        numberDI++;
        implementation.add(di);
    }
    
    public Set<DalvikImplementation> getDalvikImp(){
        if (numberCM != numberDI){
            System.out.println("StubImplementation: some methods have no implementation (or there are too many implementations). There are "+numberCM + " stubs but only " + numberDI + " DalvikImplementation found for " + c + " " + m);
        }
        if (numberDI == 0){
            System.out.println("This stub contains no Dalvik implementation :" + c + " " + m);
        }
        return implementation;
    }
}
