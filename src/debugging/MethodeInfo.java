package debugging;

import java.util.HashMap;
import java.util.Set;
import java.util.TreeSet;

import analysis.Analysis;

public class MethodeInfo {
    public String c;
    public String m;
    public int numReg;
    public int numPc;
    public RegInfo[] regInfo;
    private HashMap<Integer,HashMap<Integer, LHInfo>> lhMap;
    private Analysis analysis;

    public MethodeInfo(Analysis analysis, String c, String m, int numReg, int numPc){
        this.c = c;
        this.m = m;
        this.numReg = numReg;
        this.numPc = numPc;
        this.analysis = analysis;
        
        regInfo = new RegInfo[numReg];
        for (int i = 0; i < regInfo.length; i++){
            regInfo[i] = new RegInfo();
        }
        
        lhMap = new HashMap<Integer,HashMap<Integer, LHInfo>>();
        /*
         for (int instanceNum : analysis.getAllocationPoints()){
            final String referenceString = analysis.getAllocationPointClass(instanceNum);
            final Map<Integer, Boolean> fieldsMap = analysis.getClassFields(referenceString, instanceNum);
            Set<Integer> fields = null;
            if (fieldsMap != null)
                fields = fieldsMap.keySet();
            else{
                fields = new HashSet<Integer>();
                fields.add(0);
            }
            for (int field : fields){
                LHInfo lhinfo = LHInfo.lhInfoFromInstanceNum(analysis,instanceNum, field);
                addLHElem(instanceNum, field ,lhinfo);
            }
    }
    */
}
    
    private void addLHElem(int instanceNum, int field, final LHInfo lhinfo){
        if (!lhMap.containsKey(instanceNum)){
            HashMap<Integer, LHInfo> hmap = new HashMap<Integer, LHInfo>();
            lhMap.put(instanceNum, hmap);
        }
        lhMap.get(instanceNum).put(field, lhinfo);
    }
    
    public Set<LHKey> getLHKeySet(){
        TreeSet<LHKey> keySet = new TreeSet<LHKey>();
        for (int instanceNum : lhMap.keySet()){
            for (int field : lhMap.get(instanceNum).keySet()){
                keySet.add(new LHKey(instanceNum, field));
            }
        }
        return keySet;
    }
    
    public final LHInfo getLHInfo(int instanceNum, int field){
        if (lhMap.containsKey(instanceNum)){
            if (lhMap.get(instanceNum).containsKey(field))
                return lhMap.get(instanceNum).get(field);
        }
        
        //final String referenceString = analysis.getAllocationPointClass(instanceNum);
        final LHInfo lhinfo = LHInfo.lhInfoFromInstanceNum(analysis,instanceNum, field);
        addLHElem(instanceNum, field, lhinfo);
        return lhinfo;
    }
}
