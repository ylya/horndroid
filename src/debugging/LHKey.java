package debugging;

public class LHKey implements Comparable<LHKey> {
    int instanceNum;
    int field;
    
    public LHKey(int instanceNum,int field){
        this.instanceNum = instanceNum;
        this.field = field;
    }

    @Override
    public int compareTo(LHKey o) {
        if ((this.instanceNum == o.instanceNum) && (this.field == o.field))
            return 0;
        if ((this.instanceNum < o.instanceNum))
            return 1;
        if ((this.instanceNum == o.instanceNum) && (this.field < o.field))
            return 1;
        return -1;        
    }
    
    
    
}
