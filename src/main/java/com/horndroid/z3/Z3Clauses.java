package com.horndroid.z3;


import com.horndroid.analysis.Analysis;
import com.horndroid.model.Report;
import com.microsoft.z3.*;
import java.util.ArrayList;

public abstract class Z3Clauses {
    final protected boolean QUERY_IS_COMPACT = false;

    protected Context mContext;
    protected ArrayList<BoolExpr> mRules;
    protected ArrayList<FuncDecl> mFuncs;

    protected ArrayList<Z3Query> mQueries;
    protected Z3Query mCurrentQuery;

    protected int bvSize;
   
    /*
     * Abstract methods
     */
    abstract void addQuery(Z3Query query);
    
    abstract void addQueryDebug(Z3Query query);

    abstract Report executeAllQueries(Analysis analysis, String tag);
    
    
    /*
     * Methods
     */
    public void declareRel(FuncDecl funcDecl) {
        try {
            mFuncs.add(funcDecl);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: declareRel");
        }
    }

    public void declareRel(String name, Sort[] domain, Sort range) {
        try {
            FuncDecl f = mContext.mkFuncDecl(name, domain, range);
            this.declareRel(f);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: declareRel");
        }
    }
    
    public Context getContext(){ return mContext; }
    
    public void addRule(BoolExpr rule, String symbol){
        try {
            mRules.add(rule);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: addRule");
        }
    }


    public BoolExpr mkTrue() {
        try {
            return mContext.mkBool(true);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: true");
        }
    }

    public BoolExpr mkFalse() {
        try {
            return mContext.mkBool(false);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: false");
        }
    }

    public BoolExpr mkBool(boolean b) {
        try {
            return mContext.mkBool(b);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: mkBool");
        }
    }

    public BitVecExpr mkBitVector(String data, int len) {
        try {
            return mContext.mkBV(data, len);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: mkBitVector String");
        }
    }

    public BitVecExpr mkBitVector(int data, int len) {
        try {
            return mContext.mkBV(data, len);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: mkBitVector int");
        }
    }

    public BitVecExpr mkBitVector(long data, int len) {
        try {
            return mContext.mkBV(data, len);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: mkBitVector long");
        }
    }

    public IntExpr mkInt(String data) {
        try {
            return mContext.mkInt(data);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: mkInt");
        }
    }

    public IntExpr mkInt(int data) {
        try {
            return mContext.mkInt(data);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: mkInt");
        }
    }

    public BoolExpr and(BoolExpr... b) {
        try {
            return mContext.mkAnd(b);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: and");
        }
    }

    public BoolExpr or(BoolExpr... b) {
        try {
            return mContext.mkOr(b);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: or");
        }
    }

    public BoolExpr not(BoolExpr b) {
        try {
            return mContext.mkNot(b);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: not");
        }
    }

    public BoolExpr eq(BoolExpr b1, BoolExpr b2) {
        try {
            return mContext.mkEq(b1, b2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: eq");
        }
    }

    public BoolExpr eq(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkEq(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: eq");
        }
    }

    public Expr ite(BoolExpr b, Expr e1, Expr e2) {
        try {
            return mContext.mkITE(b, e1, e2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: ite");
        }
    }


    public BitVecExpr bvneg(BitVecExpr bv, Type type) {
        try {
            switch(type){
            case FLOAT:
                return floatToIEEEBV(mContext.mkFPNeg(toFloat(bv)));
            case DOUBLE:
                return doubleToIEEEBV(mContext.mkFPNeg(toDouble(bv)));
            case INT:
                return toLong(mContext.mkBVNeg(toInt(bv)));
            case LONG:
                return mContext.mkBVNeg(bv);
            }
            return mContext.mkBVNeg(bv);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvneg");
        }
    }

    public BitVecExpr bvnot(BitVecExpr bv, Type type) {
        try {
            switch(type){
            case INT:
                return toLong(mContext.mkBVNot(toInt(bv)));
            case LONG:
                return mContext.mkBVNot(bv);
            default:
                throw new RuntimeException("BVNOT on wrong type");                    
            }
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvnot");
        }
    }

    private FPRMExpr rM(){
        return mContext.mkFPRoundNearestTiesToEven();
    }
    
    public BitVecExpr bvadd(BitVecExpr bv1, BitVecExpr bv2, Type type) {
        try {
            switch(type){
            case FLOAT:
                return floatToIEEEBV(mContext.mkFPAdd(rM(),toFloat(bv1), toFloat(bv2)));
            case DOUBLE:
                return doubleToIEEEBV(mContext.mkFPAdd(rM(),toDouble(bv1), toDouble(bv2)));
            case INT:
                return toLong(mContext.mkBVAdd(toInt(bv1),toInt(bv2)));
            case LONG:
                return mContext.mkBVAdd(bv1, bv2);
            }
            return mContext.mkBVAdd(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvadd");
        }
    }

    public BitVecExpr bvmul(BitVecExpr bv1, BitVecExpr bv2, Type type) {
        try {
            switch(type){
            case FLOAT:
                return floatToIEEEBV(mContext.mkFPMul(rM(),toFloat(bv1), toFloat(bv2)));
            case DOUBLE:
                return doubleToIEEEBV(mContext.mkFPMul(rM(),toDouble(bv1), toDouble(bv2)));
            case INT:
                return toLong(mContext.mkBVMul(toInt(bv1),toInt(bv2)));
            case LONG:
                return mContext.mkBVMul(bv1, bv2);
            }
            return mContext.mkBVMul(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvmul");
        }
    }

    public BitVecExpr bvdiv(BitVecExpr bv1, BitVecExpr bv2, Type type) {
        try {
            switch(type){
            case FLOAT:
                return floatToIEEEBV(mContext.mkFPDiv(rM(),toFloat(bv1), toFloat(bv2)));
            case DOUBLE:
                return doubleToIEEEBV(mContext.mkFPDiv(rM(),toDouble(bv1), toDouble(bv2)));
            case INT:
                return toLong(mContext.mkBVSDiv(toInt(bv1),toInt(bv2)));
            case LONG:
                return mContext.mkBVSDiv(bv1, bv2);
            }
            return mContext.mkBVSDiv(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvudiv");
        }
    }

    public BitVecExpr bvrem(BitVecExpr bv1, BitVecExpr bv2, Type type) {
        try {
            switch(type){
            //TODO: I think that mkFPRem follows the IEEE754 standard, whereas Dalvik reminder is a bit different
            case FLOAT:
                return floatToIEEEBV(mContext.mkFPRem(toFloat(bv1), toFloat(bv2)));
            case DOUBLE:
                return doubleToIEEEBV(mContext.mkFPRem(toDouble(bv1), toDouble(bv2)));
            case INT:
                return toLong(mContext.mkBVSRem(toInt(bv1),toInt(bv2)));
            case LONG:
                return mContext.mkBVSRem(bv1, bv2);
            }
            return mContext.mkBVSRem(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvurem");
        }
    }

    public BoolExpr bvugt(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVUGT(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvugt");
        }
    }

    public BoolExpr bvuge(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVUGE(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvuge");
        }
    }

    public BoolExpr bvule(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVULE(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvule");
        }
    }

    public BoolExpr bvult(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVULE(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvult");
        }
    }


    public BitVecExpr bvlshr(BitVecExpr bv1, BitVecExpr bv2, Type type) {
        try {
            switch(type){
            case INT:
                return toLong(mContext.mkBVLSHR(toInt(bv1), toInt(bv2)));
            case LONG:
                return mContext.mkBVLSHR(bv1, bv2);
            default:
                    throw new RuntimeException("Z3Clause: wrong type in LSHR");
            }
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvlshr");
        }
    }

    public BitVecExpr bvashr(BitVecExpr bv1, BitVecExpr bv2, Type type) {
        try {
            switch(type){
            case INT:
                return toLong(mContext.mkBVASHR(toInt(bv1), toInt(bv2)));
            case LONG:
                return mContext.mkBVASHR(bv1, bv2);
            default:
                    throw new RuntimeException("Z3Clause: wrong type in ASHR");
            }
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvashr");
        }
    }
    

    public BitVecExpr bvshl(BitVecExpr bv1, BitVecExpr bv2, Type type) {
        try {
            switch(type){
            case INT:
                return toLong(mContext.mkBVSHL(toInt(bv1), toInt(bv2)));
            case LONG:
                return mContext.mkBVSHL(bv1, bv2);
            default:
                    throw new RuntimeException("Z3Clause: wrong type in SHL");
            }
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvshl");
        }
    }

    public BitVecExpr bvsub(BitVecExpr bv1, BitVecExpr bv2, Type type) {
        try {
            switch(type){
            case FLOAT:
                return floatToIEEEBV(mContext.mkFPSub(rM(),toFloat(bv1), toFloat(bv2)));
            case DOUBLE:
                return doubleToIEEEBV(mContext.mkFPSub(rM(),toDouble(bv1), toDouble(bv2)));
            case INT:
                return toLong(mContext.mkBVSub(toInt(bv1),toInt(bv2)));
            case LONG:
                return mContext.mkBVSub(bv1, bv2);
            }
            return mContext.mkBVSub(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvsub");
        }
    }

    public BitVecExpr bvxor(BitVecExpr bv1, BitVecExpr bv2, Type type) {
        try {
            switch(type){
            case INT:
                return toLong(mContext.mkBVXOR(toInt(bv1),toInt(bv2)));
            case LONG:
                return mContext.mkBVXOR(bv1,bv2);
            default:
                throw new RuntimeException("BVXOR on wrong type");                    
            }
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvxor");
        }
    }

    public BitVecExpr bvor(BitVecExpr bv1, BitVecExpr bv2, Type type) {
        try {
            switch(type){
            case INT:
                return toLong(mContext.mkBVOR(toInt(bv1),toInt(bv2)));
            case LONG:
                return mContext.mkBVOR(bv1,bv2);
            default:
                throw new RuntimeException("BVOR on wrong type");                    
            }
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvor");
        }
    }

    public BitVecExpr bvand(BitVecExpr bv1, BitVecExpr bv2, Type type) {
        try {
            switch(type){
            case INT:
                return toLong(mContext.mkBVAND(toInt(bv1),toInt(bv2)));
            case LONG:
                return mContext.mkBVAND(bv1,bv2);
            default:
                throw new RuntimeException("BVAND on wrong type");                    
            }
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: bvand");
        }
    }
    
    public BitVecExpr toInt(BitVecExpr longBV){
        return mContext.mkExtract(31, 0, longBV);
    }

    public BitVecExpr toLong(BitVecExpr longBV){
        return mContext.mkConcat(mkBitVector(0, 32),longBV);
    }

    public FPExpr toFloat(BitVecExpr longBV){
        return mContext.mkFPToFP(toInt(longBV), mContext.mkFPSort32());
    }
    
    public FPExpr toDouble(BitVecExpr longBV){
        return mContext.mkFPToFP(longBV, mContext.mkFPSort64());
    }
    
    public BitVecExpr floatToIEEEBV(FPExpr floatExpr){
        return toLong(mContext.mkFPToIEEEBV(floatExpr));        
    }
    
    public BitVecExpr doubleToIEEEBV(FPExpr doubleExpr){
        return mContext.mkFPToIEEEBV(doubleExpr);
    }
    
    public BitVecExpr uOpIntToFloat(BitVecExpr bv){
        return(floatToIEEEBV(mContext.mkFPToFP(rM(),bv,mContext.mkFPSort32(),true)));
    }
    
    
    public BitVecExpr uOpIntToDouble(BitVecExpr bv){
        return(doubleToIEEEBV(mContext.mkFPToFP(rM(),bv,mContext.mkFPSort64(),true)));
    }
    
    public BitVecExpr uOpLongToFloat(BitVecExpr bv){
        return(floatToIEEEBV(mContext.mkFPToFP(rM(),bv,mContext.mkFPSort32(),true)));
    }
    
    
    public BitVecExpr uOpLongToDouble(BitVecExpr bv){
        return(doubleToIEEEBV(mContext.mkFPToFP(rM(),bv,mContext.mkFPSort64(),true)));
    }

    public BitVecExpr floatRoundToInt(BitVecExpr bv){
        return toLong(mContext.mkFPToBV(rM(),toFloat(bv),32, true));
    }

    public BitVecExpr floatRoundToLong(BitVecExpr bv){
        return mContext.mkFPToBV(rM(),toFloat(bv),64, true);
    }
    
    public BitVecExpr doubleRoundToInt(BitVecExpr bv){
        return toLong(mContext.mkFPToBV(rM(),toDouble(bv),32, true));
    }

    public BitVecExpr doubleRoundToLong(BitVecExpr bv){
        return mContext.mkFPToBV(rM(),toDouble(bv),64, true);
    }
    
    public BitVecExpr floatToDouble(BitVecExpr bv){
        return doubleToIEEEBV(mContext.mkFPToFP(rM(),toFloat(bv),mContext.mkFPSort64()));
    }
    
    public BitVecExpr doubleToFloat(BitVecExpr bv){
        return floatToIEEEBV(mContext.mkFPToFP(rM(),toDouble(bv),mContext.mkFPSort32()));
    }
    
    public BitVecExpr intToShort(BitVecExpr bv){
        return bvashr(bvshl(bv, mkBitVector(16, 64), Type.INT),mkBitVector(16, 64), Type.INT);
    }
    
    public BitVecExpr intToByte(BitVecExpr bv){
        return bvashr(bvshl(bv, mkBitVector(24, 64), Type.INT),mkBitVector(24, 64), Type.INT);
    }
    
    public BitVecExpr intToChar(BitVecExpr bv){
        return this.bvand(bv, mkBitVector(65535,64), Type.INT);
    }

    public BoolExpr implies(BoolExpr b1, BoolExpr b2){
        try {
            return mContext.mkImplies(b1, b2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Clause Failed: implies");
        }
    }
}
