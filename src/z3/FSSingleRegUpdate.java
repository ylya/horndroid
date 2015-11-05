package z3;

import java.util.Map;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;

public class FSSingleRegUpdate {
    private int regNumber;
    private BitVecExpr bv;
    private BoolExpr h;
    private BoolExpr l;
    private BoolExpr g;
    
    public FSSingleRegUpdate(int regNumber, BitVecExpr bv, BoolExpr h, BoolExpr l, BoolExpr g){
        this.bv = bv;
        this.h= h;
        this.l = l;
        this.g = g;
    }
    
    public void apply(Map<Integer, BitVecExpr> regUpV,Map<Integer, BoolExpr> regUpH,Map<Integer, BoolExpr> regUpL,Map<Integer, BoolExpr> regUpG){
        regUpV.put(regNumber, bv);
        regUpH.put(regNumber, h);
        regUpL.put(regNumber, l);
        regUpG.put(regNumber, g);
    }
}
