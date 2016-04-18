package z3;

import com.microsoft.z3.*;

/**
 * Created by rtongchenchitt on 10/15/2015.
 */
public class Z3Function {

    // Function
    private final FuncDecl h, hi, i, s, ta;

    public Z3Function(Context ctx, int bvSize) throws Z3Exception {
//        out.println("(declare-rel H (bv64 bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
//        out.println("(declare-rel HI (bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
//        out.println("(declare-rel I (bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
//        out.println("(declare-rel S (Int Int bv64 Bool Bool) interval_relation bound_relation)");
        BitVecSort bv64 = ctx.mkBitVecSort(bvSize);
        BoolSort bool = ctx.mkBoolSort();
        IntSort integer = ctx.mkIntSort();

        this.h = ctx.mkFuncDecl("H", new Sort[]{bv64, bv64, bv64, bv64, bool, bool}, bool);
        this.hi = ctx.mkFuncDecl("HI", new Sort[]{bv64, bv64, bv64, bool, bool}, bool);
        this.i = ctx.mkFuncDecl("I", new Sort[]{bv64, bv64, bv64, bool, bool}, bool);
        this.s = ctx.mkFuncDecl("S", new Sort[]{integer, integer, bv64, bool, bool}, bool);
        
        this.ta = ctx.mkFuncDecl("TA", new Sort[]{bv64, bool}, bool); //used for computing taint on the connected component on the heap
    }

    public FuncDecl getH() {
        return h;
    }

    public FuncDecl getHi() {
        return hi;
    }

    public FuncDecl getI() {
        return i;
    }

    public FuncDecl getS() {
        return s;
    }
    
    public FuncDecl getTaint(){
        return ta;
    }
}
