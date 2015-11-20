package debugging;

import analysis.Analysis;

public class LHInfo {
        public RegInfo regInfo;
        public String allocatedClass;
        public int field;
        public String c;
        public String m;
        public int pc;



        public LHInfo(String ac, int f, String c, String m, int pc){
            regInfo = new RegInfo();
            
            allocatedClass = ac;
            field = f;
            this.c = c;
            this.m = m;
            this.pc = pc;
        }
        
        public static LHInfo lhInfoFromInstanceNum(Analysis analysis, LHKey lhKey){
            int instanceNum = lhKey.instanceNum;
            int f = lhKey.field;
            return new LHInfo(analysis.getAllocationPointClass(instanceNum), f, analysis.getAllocationPointClassDebug(instanceNum), analysis.getAllocationPointMethod(instanceNum), analysis.getAllocationPointPC(instanceNum));
        }
}

