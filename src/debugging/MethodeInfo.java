package debugging;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import analysis.Analysis;
import analysis.DalvikInstance;

public class MethodeInfo {
    public String c;
    public String m;
    public int numReg;
    public int numPc;
    public RegInfo[] regInfo;
    private HashMap<LHKey,LHInfo> lhMap;
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
        
        lhMap = new HashMap<LHKey,LHInfo>();
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
            for (int f : fields){
                LHKey lhkey = new LHKey(instanceNum,f); 
                LHInfo lhinfo = LHInfo.lhInfoFromInstanceNum(analysis,lhkey);
                lhMap.put(lhkey,lhinfo);
            }
        }
    }
    
    public Set<LHKey> getLHKeySet(){
        return lhMap.keySet();
    }
    
    public LHInfo getLHInfo(LHKey lhkey){
        if (lhMap.containsKey(lhkey))
            return lhMap.get(lhkey);

        int instanceNum = lhkey.instanceNum;
        int f = lhkey.field;
        final String referenceString = analysis.getAllocationPointClass(instanceNum);
        LHInfo lhinfo = LHInfo.lhInfoFromInstanceNum(analysis,lhkey);
        lhMap.put(lhkey,lhinfo);
        return lhinfo;
    }
}
