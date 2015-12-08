package util;

import java.util.HashMap;
import java.util.Map;

public class SourcesSinks {
    private Map<String,Map<String,Boolean>> map;
    
    public SourcesSinks(){
        map = new HashMap<String,Map<String,Boolean>>();
    }
    
    public void put(String c, String m, boolean bool){
        if (!map.containsKey(c)){
            map.put(c, new HashMap<String,Boolean>());
        }
        map.get(c).put(m, bool);
    }
    
    public Boolean isSourceSink(String c, String m){
        if (!map.containsKey(c)){
            return null;
        }else{
            if(map.get(c).containsKey(m)){
                return map.get(c).get(m);
            }else{
                return null;
            }
        }
    }    
}
