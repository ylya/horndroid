package util;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import Dalvik.DalvikClass;
import Dalvik.GeneralClass;

/*
 * A lazy union of two Map.
 * Very few methods are implemented so be careful.
 */
public class LazyUnion implements Map<Integer,GeneralClass> {
    private Map<Integer,GeneralClass> map1;
    private Map<Integer,GeneralClass> map2;

    public LazyUnion(Map<Integer,GeneralClass> map1, Map<Integer,GeneralClass> map2){
        this.map1 = map1;
        this.map2 = map2;
    }
    @Override
    public int size() {
        return map1.size() + map2.size();
    }

    @Override
    public boolean isEmpty() {
        return map1.isEmpty() && map2.isEmpty();
    }

    @Override
    public boolean containsKey(Object key) {
        if (map1.containsKey(key)){
            return ((map1.get(key) instanceof DalvikClass)||(map2.containsKey(key)));
        }
        return ((map1.containsKey(key))||(map2.containsKey(key)));
    }

    @Override
    public boolean containsValue(Object value) {
        return ((map1.containsValue(value))||(map2.containsValue(value)));

    }
    @Override
    public GeneralClass get(Object key) {
        if (map1.containsKey(key)){
            GeneralClass ret = map1.get(key);
            if (ret instanceof DalvikClass){
                return ret;
            }
        }
        return map2.get(key);
    }
    
    @Override
    public GeneralClass put(Integer key, GeneralClass value) {
        throw new RuntimeException("LazyUnion");
    }
    @Override
    public GeneralClass remove(Object key) {
        throw new RuntimeException("LazyUnion");
    }
    @Override
    public void putAll(Map<? extends Integer, ? extends GeneralClass> m) {
        throw new RuntimeException("LazyUnion");       
    }
    @Override
    public void clear() {
        throw new RuntimeException("LazyUnion");   
    }
    @Override
    public Set<Integer> keySet() {
        throw new RuntimeException("LazyUnion");
    }
    @Override
    public Collection<GeneralClass> values() {
        throw new RuntimeException("LazyUnion");
    }
    @Override
    public Set<java.util.Map.Entry<Integer, GeneralClass>> entrySet() {
        throw new RuntimeException("LazyUnion");
    }

}
