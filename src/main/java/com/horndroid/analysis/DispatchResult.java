package com.horndroid.analysis;

import com.horndroid.Dalvik.DalvikImplementation;
import com.horndroid.Dalvik.DalvikInstance;

import java.util.HashSet;



public class DispatchResult {
    final private HashSet<DalvikInstance> instances;
    final private HashSet<DalvikImplementation> implementations;
    DispatchResult(HashSet<DalvikInstance> instances, HashSet<DalvikImplementation> implementations){
        this.instances = instances;
        this.implementations = implementations;
    }
    
    public HashSet<DalvikInstance>  getInstances(){
        return instances;
    }
    public HashSet<DalvikImplementation> getImplementations(){
        return implementations;
    }
    public void mergeResults(final DispatchResult dr){
        this.instances.addAll(dr.getInstances());
        this.implementations.addAll(dr.getImplementations());
    }
}
