package com.horndroid.util;

public class StringPair {
    public final String st1;
    public final String st2;
    
    public StringPair(String st1, String st2){
        this.st1 = st1;
        this.st2 = st2;
    }
    
    @Override
    public int hashCode(){
        // Very quick simple hashCode
        return 17 * st1.hashCode() + 37 * st2.hashCode();
    }
    
    @Override
    public boolean equals(Object obj){
        if (obj instanceof StringPair){
            StringPair objSP = (StringPair) obj;
            return (objSP.st1.equals(this.st1)) && (objSP.st2.equals(this.st2));
        }else{
            return false;
        }
    }
}
