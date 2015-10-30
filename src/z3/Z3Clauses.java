package z3;

import com.microsoft.z3.*;

import java.util.Map;

/**
 * Created by rtongchenchitt on 10/15/2015.
 */
public interface Z3Clauses {

    /*
     *  Expression from Context
     */
    public BoolExpr mkTrue();
    public BoolExpr mkFalse();
    public BoolExpr mkBool(boolean b);
    public BitVecExpr mkBitVector(String data, int len);
    public BitVecExpr mkBitVector(int data, int len);
    public BitVecExpr mkBitVector(long data, int len);
    public IntExpr mkInt(String data);
    public IntExpr mkInt(int data);

    public BoolExpr and(BoolExpr... b);
    public BoolExpr or(BoolExpr... b);
    public BoolExpr not(BoolExpr b);
    public BoolExpr eq(BoolExpr b1, BoolExpr b2);
    public BoolExpr eq(BitVecExpr bv1, BitVecExpr bv2);
    public Expr ite(BoolExpr b, Expr e1, Expr e2);
    public BoolExpr implies(BoolExpr b1, BoolExpr b2);
    public BoolExpr bvugt(BitVecExpr bv1, BitVecExpr bv2);
    public BoolExpr bvuge(BitVecExpr bv1, BitVecExpr bv2);
    public BoolExpr bvule(BitVecExpr bv1, BitVecExpr bv2);
    public BoolExpr bvult(BitVecExpr bv1, BitVecExpr bv2);
    public BitVecExpr bvneg(BitVecExpr bv);
    public BitVecExpr bvnot(BitVecExpr bv);
    public BitVecExpr bvadd(BitVecExpr bv1, BitVecExpr bv2);
    public BitVecExpr bvmul(BitVecExpr bv1, BitVecExpr bv2);
    public BitVecExpr bvudiv(BitVecExpr bv1, BitVecExpr bv2);
    public BitVecExpr bvurem(BitVecExpr bv1, BitVecExpr bv2);
    public BitVecExpr bvshl(BitVecExpr bv1, BitVecExpr bv2);
    public BitVecExpr bvlshr(BitVecExpr bv1, BitVecExpr bv2);
    public BitVecExpr bvashr(BitVecExpr bv1, BitVecExpr bv2);
    public BitVecExpr bvsub(BitVecExpr bv1, BitVecExpr bv2);
    public BitVecExpr bvxor(BitVecExpr bv1, BitVecExpr bv2);
    public BitVecExpr bvor(BitVecExpr bv1, BitVecExpr bv2);
    public BitVecExpr bvand(BitVecExpr bv1, BitVecExpr bv2);


    /*
     *  Custom Predicate
     */
    public BoolExpr rPred(String c, String m, int pc, Map<Integer, BitVecExpr> rUp, Map<Integer, BoolExpr> rUpL, Map<Integer, BoolExpr> rUpB, int numArg, int numReg);
    public BoolExpr rInvokePred(String c, String m, int pc, Map<Integer, BitVecExpr> rUp, Map<Integer, BoolExpr> rUpL, Map<Integer, BoolExpr> rUpB, int numArg, int numReg, int size);
    //    public void rPredDef(String c, String m, int pc, int size);

    public BoolExpr resPred(String c, String m, Map<Integer, BitVecExpr> rUp, Map<Integer, BoolExpr> rUpL, Map<Integer, BoolExpr> rUpB, int numArg);
    //    public void resPredDef(String c, String m, int size);

    public BoolExpr hPred(BitVecExpr cname, BitVecExpr inst, BitVecExpr element, BitVecExpr value, BoolExpr label, BoolExpr block);
    public BoolExpr hiPred(BitVecExpr cname, BitVecExpr inst, BitVecExpr value, BoolExpr label, BoolExpr block);
    public BoolExpr iPred(BitVecExpr cname, BitVecExpr inst, BitVecExpr value, BoolExpr label, BoolExpr block);
    public BoolExpr sPred(IntExpr v1, IntExpr v2, BitVecExpr v3, BoolExpr v4, BoolExpr v5);

    /*
     *  Fixed-point
     */
    public void declareRel(FuncDecl function);
    public void declareRel(String name, Sort[] domain, Sort range);
    public void declareVar(Sort type);




}
