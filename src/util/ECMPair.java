package util;

public class ECMPair extends CMPair {
    private CMPair linkedCM;
    
    public ECMPair(int ci, int mi, CMPair linkedCM){
        super(ci,mi);
        this.linkedCM = linkedCM;
    }
    
    public CMPair getLink(){
        return this.linkedCM;
    }
}
