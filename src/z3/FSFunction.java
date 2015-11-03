package z3;

import com.microsoft.z3.BitVecSort;
import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Context;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Z3Exception;

public class FSFunction {

    // Function
    private final FuncDecl h, hi, i, s;

    public FSFunction(Context ctx, int bvSize) throws Z3Exception {
//        out.println("(declare-rel H (bv64 bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
//        out.println("(declare-rel HI (bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
//        out.println("(declare-rel I (bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
//        out.println("(declare-rel S (Int Int bv64 Bool Bool) interval_relation bound_relation)");
        BitVecSort bv64 = ctx.mkBitVecSort(bvSize);
        BoolSort bool = ctx.mkBoolSort();
        IntSort integer = ctx.mkIntSort();

        //class name, allocation point, field, value, taint, pointer
        this.h = ctx.mkFuncDecl("H", new Sort[]{bv64, bv64, bv64, bv64, bool, bool}, bool);
        this.hi = ctx.mkFuncDecl("HI", new Sort[]{bv64, bv64, bv64, bool, bool}, bool);
        this.i = ctx.mkFuncDecl("I", new Sort[]{bv64, bv64, bv64, bool, bool}, bool);
        this.s = ctx.mkFuncDecl("S", new Sort[]{integer, integer, bv64, bool, bool}, bool);
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
}
