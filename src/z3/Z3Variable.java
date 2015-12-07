package z3;

import com.microsoft.z3.*;

/**
 * Created by rtongchenchitt on 10/15/2015.
 */
public class Z3Variable {

    private final int GUARD = 100;

    private final Context ctx;
    private final BoolSort bool;
    private final BitVecSort bv64;

    private final BitVecExpr rez, rezp, buf, bufp, f, fpp, vfp, cn, val;
    private final BoolExpr lrez, brez, lrezp, lbuf, lbufp, lfp, bfp, lf, bf, lval, bval;
    private final IntExpr fnum, cnum;

    public Z3Variable(Context ctx, int bvSize) throws Z3Exception {
        this.ctx = ctx;

        this.bool = ctx.mkBoolSort();
        this.bv64 = ctx.mkBitVecSort(bvSize);
        IntSort integer = ctx.mkIntSort();

        this.rez = (BitVecExpr) ctx.mkBound(0, bv64);
        this.rezp = (BitVecExpr) ctx.mkBound(1, bv64);
        this.buf = (BitVecExpr) ctx.mkBound(2, bv64);
        this.bufp = (BitVecExpr) ctx.mkBound(3, bv64);
        this.lrez = (BoolExpr) ctx.mkBound(4, bool);
        this.brez = (BoolExpr) ctx.mkBound(5, bool);
        this.lrezp = (BoolExpr) ctx.mkBound(6, bool);
        this.lbuf = (BoolExpr) ctx.mkBound(7, bool);
        this.lbufp = (BoolExpr) ctx.mkBound(8, bool);
        this.fnum = (IntExpr) ctx.mkBound(9, integer);
        this.f = (BitVecExpr) ctx.mkBound(10, bv64);
        this.fpp = (BitVecExpr) ctx.mkBound(11, bv64);
        this.vfp = (BitVecExpr) ctx.mkBound(12, bv64);
        this.lfp = (BoolExpr) ctx.mkBound(13, bool);
        this.bfp = (BoolExpr) ctx.mkBound(14, bool);
        this.cn = (BitVecExpr) ctx.mkBound(15, bv64);
        this.lf = (BoolExpr) ctx.mkBound(16, bool);
        this.bf = (BoolExpr) ctx.mkBound(17, bool);
        this.val = (BitVecExpr) ctx.mkBound(18, bv64);
        this.lval = (BoolExpr) ctx.mkBound(19, bool);
        this.bval = (BoolExpr) ctx.mkBound(20, bool);
        this.cnum = (IntExpr) ctx.mkBound(21, integer);

    }

    public BitVecExpr getRez() {
        return rez;
    }

    public BitVecExpr getRezp() {
        return rezp;
    }

    public BitVecExpr getBuf() {
        return buf;
    }

    public BitVecExpr getBufp() {
        return bufp;
    }

    public BitVecExpr getF() {
        return f;
    }

    public BitVecExpr getFpp() {
        return fpp;
    }

    public BitVecExpr getVfp() {
        return vfp;
    }

    public BitVecExpr getCn() {
        return cn;
    }

    public BitVecExpr getVal() {
        return val;
    }

    public BoolExpr getLrez() {
        return lrez;
    }

    public BoolExpr getBrez() {
        return brez;
    }

    public BoolExpr getLrezp() {
        return lrezp;
    }

    public BoolExpr getLbuf() {
        return lbuf;
    }

    public BoolExpr getLbufp() {
        return lbufp;
    }

    public BoolExpr getLfp() {
        return lfp;
    }

    public BoolExpr getBfp() {
        return bfp;
    }

    public BoolExpr getLf() {
        return lf;
    }

    public BoolExpr getBf() {
        return bf;
    }

    public BoolExpr getLval() {
        return lval;
    }

    public BoolExpr getBval() {
        return bval;
    }

    public IntExpr getFnum() {
        return fnum;
    }

    public IntExpr getCnum() {
        return cnum;
    }


    public BitVecExpr getV(int i){
        try {
            return (BitVecExpr) ctx.mkBound(GUARD + 3*i + 0, bv64);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getV");
        }
    }

    public VariableInject getInjectV(final Z3Variable var){
        return new VariableInject() {
            @Override
            public BitVecExpr get(int i) {
                return var.getV(i);
            }
        };
    }

    public BoolExpr getL(int i){
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 3*i + 1, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getL");
        }
    }

    public VariableInject getInjectL(final Z3Variable var){
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getL(i);
            }
        };
    }

    public BoolExpr getB(int i){
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 3*i + 2, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getB");
        }
    }

    public VariableInject getInjectB(final Z3Variable var){
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getB(i);
            }
        };
    }
}