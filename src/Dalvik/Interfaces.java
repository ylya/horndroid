package Dalvik;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/*
 * Class used to store the Analysis Dalvikinterfaces
 * The interfaces are indexed by the hashcode of the type's name string for efficiency reasons
 */
public class Interfaces {
    final private Map<Integer,HashSet<DalvikClass>> interfaces;
    final private Map<Integer,HashSet<Integer>> interfaceImp;
    
    public Interfaces(){
        interfaces = new ConcurrentHashMap<Integer,HashSet<DalvikClass>>();
        interfaceImp = new ConcurrentHashMap<Integer,HashSet<Integer>>();
    }
    
    /*
     * Add the element to the set of interfaces
     */
    public void add(int c, DalvikClass di){
        if (!interfaces.containsKey(c)){
            interfaces.put(c,new HashSet<DalvikClass>());
        }
        interfaces.get(c).add(di);
        if (!interfaceImp.containsKey(di.getType().hashCode())){
            interfaceImp.put(di.getType().hashCode(),new HashSet<Integer>());
        }
        interfaceImp.get(di.getType().hashCode()).add(c);
    }
    
    public HashSet<DalvikClass> getByInterfaceType(final int c){
        return interfaces.get(c);
    }
    
    public HashSet<Integer> getByClassType(final int c){
        return interfaceImp.get(c);
    }
    
//    public Map<Integer,HashSet<DalvikInstance>> get(){
//        return (Map<Integer,HashSet<DalvikInstance>>) interfaces;
//    }
//  
    /*
     * Give a Set view of all interfaces. This operation may be a bit costly, and should be avoided as much as possible
     */
    public Set<DalvikClass> getAllOnce(){
        HashSet<DalvikClass> hset = new HashSet<DalvikClass>();
        for (int hc : interfaces.keySet()){
            hset.addAll(interfaces.get(hc));
        }
        return hset;
    }

    /*
     * Return the number of interfaces stored
     */
    public int size() {
        int size = 0;
        for (int key : interfaces.keySet()){
            size += interfaces.get(key).size();
        }
        return size;
        
    }
}
