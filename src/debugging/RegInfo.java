package debugging;

import java.util.HashMap;
import java.util.TreeMap;

public class RegInfo {
    public TreeMap<Integer,Boolean> high;
    public TreeMap<Integer,Boolean> local;
    public TreeMap<Integer,Boolean> global;


    public RegInfo(){
        high = new TreeMap<Integer,Boolean>();
        local = new TreeMap<Integer,Boolean>();
        global = new TreeMap<Integer,Boolean>();

    }
}