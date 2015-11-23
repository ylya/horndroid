package debugging;

import java.util.Set;
import java.util.TreeMap;

public class RegInfo {
    private TreeMap<Integer,Boolean> high;
    private TreeMap<Integer,Boolean> local;
    private TreeMap<Integer,Boolean> global;


    public int size(){
        return high.size() + local.size() + global.size();
    }
    
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
        //System.out.println("high" + this.size());
        high.put(num,bool);
    }
    
    public void localPut(int num, boolean bool){
        //System.out.println("local" + this.size());
        local.put(num,bool);
        
    }    public void globalPut(int num, boolean bool){
        //System.out.println("global" + this.size());
        global.put(num,bool);
    }
    
    public Set<Integer> highKeySet(){
        return high.keySet();
    }
    
    public Set<Integer> localKeySet(){
        return local.keySet();
    }
    
    public Set<Integer> globalKeySet(){
        return global.keySet();
    }
    
}