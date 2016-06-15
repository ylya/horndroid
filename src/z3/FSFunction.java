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
    private final FuncDecl h, hi, i, s, ta, ra;
    private FuncDecl reachLH, cFilter, liftLH;


    public FSFunction(Context ctx, int bvSize) throws Z3Exception {
        BitVecSort bv64 = ctx.mkBitVecSort(bvSize);
        BoolSort bool = ctx.mkBoolSort();
        IntSort integer = ctx.mkIntSort();

        //class name, allocation point, field, value, taint, pointer
        this.h = ctx.mkFuncDecl("H", new Sort[]{bv64, bv64, bv64, bv64, bool, bool}, bool);
        this.hi = ctx.mkFuncDecl("HI", new Sort[]{bv64, bv64, bv64, bool, bool}, bool);
        this.i = ctx.mkFuncDecl("I", new Sort[]{bv64, bv64, bv64, bool, bool}, bool);
        this.s = ctx.mkFuncDecl("S", new Sort[]{integer, integer, bv64, bool, bool}, bool);
        
        this.ta = ctx.mkFuncDecl("TA", new Sort[]{bv64, bool}, bool); //used for computing taint on the connected component on the heap
        this.ra = ctx.mkFuncDecl("RA", new Sort[]{bv64, bv64}, bool); //used for computing the connected component of the heap element
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
    public FuncDecl getReachLH(){
    	return reachLH;
    }
    public void setReachLH(FuncDecl f){
    	this.reachLH = f;
    }
    public FuncDecl getCFilter(){
    	return cFilter;
    }
    public void setCFilter(FuncDecl f){
    	this.cFilter = f;
    }
    /*public FuncDecl getLiftLH(){
    	return liftLH;
    }
    public void setLiftLH(FuncDecl f){
    	this.liftLH = f;
    }*/
    public FuncDecl getReach(){
        return ra;
    }
}
