package debugging;

import analysis.Analysis;

public class LHInfo {
        private RegInfo regInfo;
        public String allocatedClass;
        public int field;
        public String c;
        public String m;
        public int pc;


        static int dcounter = 0;
        
        public LHInfo(String ac, int f, String c, String m, int pc){
            this.regInfo = new RegInfo();
            
            allocatedClass = ac;
            field = f;
            this.c = c;
            this.m = m;
            this.pc = pc;
        }
        
        public static LHInfo lhInfoFromInstanceNum(Analysis analysis, int instanceNum, int field){
            dcounter++;
            System.out.println("" + dcounter);
            return new LHInfo(analysis.getAllocationPointClass(instanceNum), field, analysis.getAllocationPointClassDebug(instanceNum), analysis.getAllocationPointMethod(instanceNum), analysis.getAllocationPointPC(instanceNum));
        }

        public RegInfo getRegInfo() {
            return regInfo;
        }

}

