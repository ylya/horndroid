package z3;

import java.util.Map;
import java.util.Map.Entry;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;

public class LHUpdate {
    private Map<Integer,BitVecExpr> bv;
    private Map<Integer,BoolExpr> h;
    private Map<Integer,BoolExpr> l;
    private Map<Integer,BoolExpr> g;
    
    public LHUpdate(Map<Integer,BitVecExpr> bv, Map<Integer,BoolExpr> h, Map<Integer,BoolExpr> l, Map<Integer,BoolExpr> g){
        this.bv = bv;
        this.h= h;
        this.l = l;
        this.g = g;
    }
    
    public void apply(Map<Integer, BitVecExpr> regUpLHV,Map<Integer, BoolExpr> regUpLHH,Map<Integer, BoolExpr> regUpLHL,Map<Integer, BoolExpr> regUpLHG){
        for (Entry<Integer,BitVecExpr> entry : bv.entrySet()){
        	regUpLHV.put(entry.getKey(), entry.getValue());
        }
        for (Entry<Integer,BoolExpr> entry : h.entrySet()){
        	regUpLHH.put(entry.getKey(), entry.getValue());
        }
        for (Entry<Integer,BoolExpr> entry : l.entrySet()){
        	regUpLHL.put(entry.getKey(), entry.getValue());
        }
        for (Entry<Integer,BoolExpr> entry : g.entrySet()){
        	regUpLHG.put(entry.getKey(), entry.getValue());
        }
    }
}
