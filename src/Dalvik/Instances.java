package Dalvik;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/*
 * Class used to store the Analysis DalvikInstances
 * The instances are indexed by the hashcode of the type's name string for efficiency reasons
 */
public class Instances {
    final private Map<Integer,HashSet<DalvikInstance>> instances;
    
    public Instances(){
        instances = new ConcurrentHashMap<Integer,HashSet<DalvikInstance>>();
    }
    
    /*
     * Add the element to the set of instances
     */
    public void add(DalvikInstance di){
        int key = di.getType().getType().hashCode();
        if (!instances.containsKey(key)){
            instances.put(key,new HashSet<DalvikInstance>());
        }
        instances.get(key).add(di);
    }

    /*
     * Return all instances whose type name string hashcode is typeHash
     * If there is no instance mathching, then return an empty set
     */
    public Set<DalvikInstance> getByType(int typeHash){
        Set<DalvikInstance> set = instances.get(typeHash);
        if (set == null){
            return new HashSet<DalvikInstance>();
        }else{
            return set;
        }
    }
    
    /*
     * Give a Set view of all instances. This operation may be a bit costly, and should be avoided as much as possible
     */
    public Set<DalvikInstance> getAll(){
        HashSet<DalvikInstance> hset = new HashSet<DalvikInstance>();
        for (int hc : instances.keySet()){
            hset.addAll(instances.get(hc));
        }
        return hset;
    }

    /*
     * Change the instance type to cd for all instances whose type name string is the same as the name string of cd.
     */
    public void changeType(DalvikClass cd) {
        int key = cd.getType().hashCode();
        if (instances.containsKey(key)){
            for (DalvikInstance di: instances.get(key)){
                di.changeType(cd);
            }
        }
    }

    /*
     * Return the number of instances stored
     */
    public int size() {
        int size = 0;
        for (int key : instances.keySet()){
            size += instances.get(key).size();
        }
        return size;
        
    }
}
