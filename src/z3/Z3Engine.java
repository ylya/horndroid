package z3;

import com.microsoft.z3.*;
import com.sun.org.apache.xpath.internal.operations.Bool;

import horndroid.options;

import org.apache.commons.lang3.RandomStringUtils;

import util.CMPair;

import javax.annotation.Nonnull;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

public class Z3Engine implements Z3Clauses {

    private Context mContext;
    private Fixedpoint mFixedPoint;

    private ArrayList<Z3Query> mQueries;

    private int bvSize;
    private Z3Variable var;
    private Z3Function func;

    //legacy
    private int biggestRegisterNumber;
    public void updateBiggestRegister(final int i){
        if (i > this.biggestRegisterNumber) biggestRegisterNumber = i;
    }

    @Nonnull private final Set<CMPair> methodIsEntryPoint;
    @Nonnull private final Set<Integer> staticConstructor;

    public Z3Engine(options options){
        try {
            bvSize = options.bitvectorSize;
            mQueries = new ArrayList<>();

            //legacy
            this.methodIsEntryPoint = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<CMPair, Boolean>()));
            this.staticConstructor = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<Integer, Boolean>()));


            Global.setParameter("fixedpoint.engine", "pdr");
            Global.setParameter("fixedpoint.unbound_compressor", "false");
            Global.setParameter("pp.bv-literals", "false");

            HashMap<String, String> cfg = new HashMap<String, String>();
            mContext = new Context(cfg); //Context ctx = mContext;
            mFixedPoint = mContext.mkFixedpoint(); //Fixedpoint fp = mFixedPoint;

            // add vars
            var = new Z3Variable(mContext, bvSize);

            // add func
            func = new Z3Function(mContext, bvSize);
            mFixedPoint.registerRelation(func.getH());
            mFixedPoint.registerRelation(func.getHi());
            mFixedPoint.registerRelation(func.getI());
            mFixedPoint.registerRelation(func.getS());
            Symbol[] symbols = new Symbol[]{mContext.mkSymbol("interval_relation"),
                                            mContext.mkSymbol("bound_relation")};
            mFixedPoint.setPredicateRepresentation(func.getH(), symbols);
            mFixedPoint.setPredicateRepresentation(func.getHi(), symbols);
            mFixedPoint.setPredicateRepresentation(func.getI(), symbols);
            mFixedPoint.setPredicateRepresentation(func.getS(), symbols);

            // add main
            BoolExpr b1 = hPred( var.getCn(), var.getCn(),
                                 mContext.mkBV("parent".hashCode(), bvSize),
                                 var.getF(), var.getLf(), var.getBf());
            BoolExpr b2 = hPred( var.getCn(), var.getCn(),
                                 mContext.mkBV("result".hashCode(), bvSize),
                                 var.getVal(), var.getLval(), var.getBval());
            BoolExpr b3 = hPred( var.getF(), var.getF(), var.getFpp(),
                                 var.getVfp(), var.getLfp(), var.getBfp());
            BoolExpr b1b2b3 = mContext.mkAnd(b1, b2, b3);
            BoolExpr b4 = hPred( var.getF(), var.getF(),
                                 mContext.mkBV("result".hashCode(), bvSize),
                                 var.getVal(), var.getLval(), var.getBval());
            BoolExpr b1b2b3_b4 = mContext.mkImplies(b1b2b3, b4);

            this.addRule(b1b2b3_b4, "zz");
        } catch (Z3Exception e){
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed");
        }
    }

    //legacy
    public void putEntryPoint(int c, int m){ methodIsEntryPoint.add(new CMPair (c, m));}
    public boolean isEntryPoint(int c, int m){
        return methodIsEntryPoint.contains(new CMPair(c, m));
    }
    public boolean hasStaticConstructor(int c){
        return staticConstructor.contains(c);
    }
    public void putStaticConstructor(int c){
        staticConstructor.add(c);
    }


    public Context getContext(){ return mContext; }

    public Z3Variable getVars(){ return var; }

    public Z3Function getFunc(){ return func; }

    public void addRule(BoolExpr rule, String symbol){
        try {
            mFixedPoint.addRule(rule, mContext.mkSymbol(RandomStringUtils.random(16,true,true)));
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: addRule");
        }
    }

//    public void addRule(BoolExpr rule, int symbol){
//        mFixedPoint.addRule(rule, mContext.mkSymbol(symbol));
//    }


    @Override
    public BoolExpr mkTrue() {
        try {
            return mContext.mkBool(true);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: true");
        }
    }

    @Override
    public BoolExpr mkFalse() {
        try {
            return mContext.mkBool(false);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: false");
        }
    }

    @Override
    public BoolExpr mkBool(boolean b) {
        try {
            return mContext.mkBool(b);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: mkBool");
        }
    }

    @Override
    public BitVecExpr mkBitVector(String data, int len) {
        try {
            return mContext.mkBV(data, len);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: mkBitVector String");
        }
    }

    @Override
    public BitVecExpr mkBitVector(int data, int len) {
        try {
            return mContext.mkBV(data, len);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: mkBitVector int");
        }
    }

    @Override
    public BitVecExpr mkBitVector(long data, int len) {
        try {
            return mContext.mkBV(data, len);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: mkBitVector long");
        }
    }

    @Override
    public IntExpr mkInt(String data) {
        try {
            return mContext.mkInt(data);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: mkInt");
        }
    }

    @Override
    public IntExpr mkInt(int data) {
        try {
            return mContext.mkInt(data);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: mkInt");
        }
    }

    @Override
    public BoolExpr and(BoolExpr... b) {
        try {
            return mContext.mkAnd(b);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: and");
        }
    }

    @Override
    public BoolExpr or(BoolExpr... b) {
        try {
            return mContext.mkOr(b);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: or");
        }
    }

    @Override
    public BoolExpr not(BoolExpr b) {
        try {
            return mContext.mkNot(b);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: not");
        }
    }

    @Override
    public BoolExpr eq(BoolExpr b1, BoolExpr b2) {
        try {
            return mContext.mkEq(b1, b2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: eq");
        }
    }

    @Override
    public BoolExpr eq(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkEq(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: eq");
        }
    }

    @Override
    public Expr ite(BoolExpr b, Expr e1, Expr e2) {
        try {
            return mContext.mkITE(b, e1, e2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: ite");
        }
    }

    @Override
    public BitVecExpr bvneg(BitVecExpr bv) {
        try {
            return mContext.mkBVNeg(bv);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvneg");
        }
    }

    @Override
    public BitVecExpr bvnot(BitVecExpr bv) {
        try {
            return mContext.mkBVNot(bv);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvnot");
        }
    }


    @Override
    public BitVecExpr bvadd(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVAdd(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvadd");
        }
    }


    @Override
    public BitVecExpr bvmul(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVMul(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvmul");
        }
    }


    @Override
    public BitVecExpr bvudiv(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVUDiv(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvudiv");
        }
    }


    @Override
    public BitVecExpr bvurem(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVURem(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvurem");
        }
    }


    @Override
    public BoolExpr bvugt(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVUGT(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvugt");
        }
    }

    @Override
    public BoolExpr bvuge(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVUGE(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvuge");
        }
    }

    @Override
    public BoolExpr bvule(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVULE(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvule");
        }
    }

    @Override
    public BoolExpr bvult(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVULE(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvult");
        }
    }

    @Override
    public BitVecExpr bvshl(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVSHL(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvshl");
        }
    }

    @Override
     public BitVecExpr bvlshr(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVLSHR(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvlshr");
        }
    }

    @Override
     public BitVecExpr bvashr(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVASHR(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvashr");
        }
    }

    @Override
    public BitVecExpr bvsub(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVASHR(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvsub");
        }
    }

    @Override
    public BitVecExpr bvxor(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVXOR(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvxor");
        }
    }

    @Override
    public BitVecExpr bvor(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVOR(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvor");
        }
    }

    @Override
    public BitVecExpr bvand(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVAND(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: bvand");
        }
    }

    @Override
    public BoolExpr implies(BoolExpr b1, BoolExpr b2){
        try {
            return mContext.mkImplies(b1, b2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: implies");
        }
    }

    public void addQuery(Z3Query query){
        mQueries.add(query);
    }

    public void executeAllQueries(){

    	//System.out.println(mFixedPoint);
        for (int i = 0; i < mQueries.size(); i++){
            Z3Query q = mQueries.get(i);
            System.out.print((i+1) + ": ");
         // if(q.isVerbose())
        //       System.out.println(q.getDescription());
            try{
                Status result = mFixedPoint.query(q.getQuery());
//                System.out.println(q.getQuery());
                System.out.println(result);
//                if(q.isVerbose())
//                    System.out.println(mFixedPoint.getAnswer());
            } catch (Z3Exception e) {
                throw new RuntimeException("Fail executing query: " + q.getDescription());
            }
        }
    }


    public void declareRel(FuncDecl funcDecl){
        try {
            mFixedPoint.registerRelation(funcDecl);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: declareRel");
        }
    }

    public void declareRel(String name, Sort[] domain, Sort range){
        try {
            FuncDecl f = mContext.mkFuncDecl(name, domain, range);
            this.declareRel(f);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: declareRel");
        }
    }

    public void declareVar(Sort type){
        try {
            Expr var = mContext.mkBound(0, type);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: declareVar");
        }
    }

//    private void rPredDef(final String c, final String m, final int pc, final int size, final Z3Engine z3engine){
//        String v = "", l = "", b = "";
//        for (int i = 0; i <= size; i++){
//            if (!v.isEmpty()) v = v + ' ' + "bv64";
//            else v = "bv64";
//            if (!l.isEmpty()) l = l + ' ' + "Bool";
//            else l = "Bool";
//            if (!b.isEmpty()) b = b + ' ' + "Bool";
//            else b = "Bool";
//        }
//        gen.addDef("(declare-rel R_" + c + '_' + m + '_' + Integer.toString(pc) + '(' + v + ' ' + l + ' ' + b + ") interval_relation bound_relation)", Integer.parseInt(c));
//    }

    private FuncDecl rPredDef(String c, String m, int pc, int size) {
        try {
            BitVecSort bv64 = mContext.mkBitVecSort(bvSize);
            BoolSort bool = mContext.mkBoolSort();

            String funcName = "R_" + c + '_' + m + '_' + Integer.toString(pc);
            Sort[] domains = new Sort[3 * size];
            Arrays.fill(domains, 0, size, bv64);
            Arrays.fill(domains, size, 3 * size, bool);
            FuncDecl f = mContext.mkFuncDecl(funcName, domains, mContext.mkBoolSort());
            this.declareRel(f);
            Symbol[] symbols = new Symbol[]{mContext.mkSymbol("interval_relation"),
                                            mContext.mkSymbol("bound_relation")};
            mFixedPoint.setPredicateRepresentation(f, symbols);
            return f;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: rPredDef");
        }
    }

//    public BoolExpr rPred(final String c, final String m, final int pc, final Map<Integer, String> rUp, final Map<Integer, String> rUpL, final Map<Integer, String> rUpB, final int numArg, final int numReg, final Z3Engine z3engine){
////        rPredDef(c, m , pc, numArg + numReg);
////        String ret = "(R" + '_' + c + '_' + m + '_' + Integer.toString(pc) + ' ';
//        String v = "", l = "", b = "", var;
//        for (int i = 0; i <= (numArg + numReg); i++){
////            gen.updateBiggestRegister(i);
//            //TODO: ASK
//            z3engine.updateBiggestRegister(i);
//            var = rUp.get(i);
//            if (var == null) {var = 'v' + Integer.toString(i);}
//            if (!v.isEmpty()) {v = v + ' ' + var;}
//            else {v = var;}
//            var = rUpL.get(i);
//            if (var == null) var = 'l' + Integer.toString(i);
//            if (!l.isEmpty()) l = l + ' ' + var;
//            else l = var;
//            var = rUpB.get(i);
//            if (var == null) var = 'b' + Integer.toString(i);
//            if (!l.isEmpty()) b = b + ' ' + var;
//            else b = var;
//        }
//        return null;
////        return ret + v + ' ' + l + ' ' + b + ')';
//    }


    @Override
    public BoolExpr rPred(final String c, final String m, final int pc, final Map<Integer, BitVecExpr> rUp, final Map<Integer, BoolExpr> rUpL, final Map<Integer, BoolExpr> rUpB, final int numArg, final int numReg) {
        try {
            int size = numArg + numReg + 1; // include return register
            FuncDecl r = this.rPredDef(c, m, pc, size);

            Expr[] e = new Expr[3 * size];
            for(int i = 0, j = size, k = 2*size; i < size; i++, j++, k++){
                e[i] = rUp.get(i); if (e[i] == null) e[i] = var.getV(i);
                e[j] = rUpL.get(i); if (e[j] == null) e[j] = var.getL(i);
                e[k] = rUpB.get(i); if (e[k] == null) e[k] = var.getB(i);
            }
            BoolExpr b = this.and(
            		(BoolExpr) r.apply(e),
            		this.eq(this.getVars().getL(0), this.mkFalse())
    		);
            
            Z3Query q = new Z3Query(b, c + ' ' + m + ' ' + Integer.toString(pc) + " test register 0", true);
            //this.addQuery(q);
            return (BoolExpr) r.apply(e);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: rPred");
        }
    }

//    public BoolExpr rInvokePred(final String c, final String m, final int pc, final Map<Integer, String> rUp, final Map<Integer, String> rUpL, final Map<Integer, String> rUpB, final int numArg, final int numReg, final int size){
//        rPredDef(c, m , pc, numArg + numReg);
//        String ret = "(R" + '_' + c + '_' + m + '_' + Integer.toString(pc) + ' ';
//        String v = "", l = "", b = "", var;
//        for (int i = 0; i <= (numArg + numReg); i++){
//            var = rUp.get(i);
//            if (var == null) var = "(_ bv0 "+ Integer.toString(size) + ")";
//            if (!v.isEmpty()) v = v + ' ' + var;
//            else v = var;
//            var = rUpL.get(i);
//            if (var == null) var = "false";
//            if (!l.isEmpty()) l = l + ' ' + var;
//            else l = var;
//            var = rUpB.get(i);
//            if (var == null) var = "false";
//            if (!l.isEmpty()) b = b + ' ' + var;
//            else b = var;
//        }
//        return null;
//        return ret + v + ' ' + l + ' ' + b + ')';
//    }

    @Override
    public BoolExpr rInvokePred(final String c, final String m, final int pc, final Map<Integer, BitVecExpr> rUp, final Map<Integer, BoolExpr> rUpL, final Map<Integer, BoolExpr> rUpB, final int numArg, final int numReg, final int size) {
        try {
            int arraySize = numArg + numReg + 1;
            FuncDecl f = this.rPredDef(c, m, pc, arraySize);
    //        String name = "R" + '_' + c + '_' + m + '_' + Integer.toString(pc);

            Expr[] e = new Expr[3 * arraySize];
            for(int i = 0, j = arraySize, k = 2*arraySize; i < arraySize; i++, j++, k++){
                e[i] = rUp.get(i); if (e[i] == null) e[i] = this.mkBitVector(0, size);
                e[j] = rUpL.get(i); if (e[j] == null) e[j] = this.mkFalse();
                e[k] = rUpB.get(i); if (e[k] == null) e[k] = this.mkFalse();
            }

            return (BoolExpr) f.apply(e);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: rInvokePred");
        }
    }

//    private void resPredDef(final String c, final String m, final int size, final Z3Engine z3engine){
//        String v = "", l = "", b = "";
//        for (int i = 0; i <= size; i++){
//            if (!v.isEmpty()) v = v + ' ' + "bv64";
//            else v = "bv64";
//            if (!l.isEmpty()) l = l + ' ' + "Bool";
//            else l = "Bool";
//            if (!b.isEmpty()) b = b + ' ' + "Bool";
//            else b = "Bool";
//        }
//        gen.addDef("(declare-rel RES_" + c + '_' + m + ' ' + '(' + v + ' ' + l + ' ' + b + ") interval_relation bound_relation)", Integer.parseInt(c));
//    }

    private FuncDecl resPredDef(String c, String m, int size) {
        try {
            BitVecSort bv64 = mContext.mkBitVecSort(bvSize);
            BoolSort bool = mContext.mkBoolSort();

            String funcName = "RES_" + c + '_' + m;
            Sort[] domains = new Sort[3 * size];
            Arrays.fill(domains, 0, size, bv64);
            Arrays.fill(domains, size, 3 * size, bool);
            FuncDecl f = mContext.mkFuncDecl(funcName, domains, bool);

            this.declareRel(f);
            Symbol[] symbols = new Symbol[]{mContext.mkSymbol("interval_relation"),
                                            mContext.mkSymbol("bound_relation")};
            mFixedPoint.setPredicateRepresentation(f, symbols);
            return f;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: resPredDef");
        }
    }

//    public BoolExpr resPred(final String c, final String m, final Map<Integer, String> rUp, final Map<Integer, String> rUpL, final Map<Integer, String> rUpB, final int numArg, final Z3Engine z3engine){
//        resPredDef(c, m , numArg);
//        String ret = "(RES" + '_' + c + '_' + m + ' ';
//        String v = "", l = "", b = "", var;
//        for (int i = 0; i <= numArg; i++){
//            var = rUp.get(i);
//            if (var == null) var = 'v' + Integer.toString(i);
//            if (!v.isEmpty()) v = v + ' ' + var;
//            else v = var;
//            var = rUpL.get(i);
//            if (var == null) var = 'l' + Integer.toString(i);
//            if (!l.isEmpty()) l = l + ' ' + var;
//            else l = var;
//            var = rUpB.get(i);
//            if (var == null) var = 'b' + Integer.toString(i);
//            if (!b.isEmpty()) b = b + ' ' + var;
//            else b = var;
//        }
//        return null;
////        return ret + v + ' ' + l + ' ' + b + ')';
//    }

    @Override
    public BoolExpr resPred(final String c, final String m, final Map<Integer, BitVecExpr> rUp, final Map<Integer, BoolExpr> rUpL, final Map<Integer, BoolExpr> rUpB, final int numArg) {
        try {
            int size = numArg + 1; // include return register
            FuncDecl res = this.resPredDef(c, m, size);

            Expr[] e = new Expr[3 * size];
            for(int i = 0, j = size, k = 2*size; i < size; i++, j++, k++) {
                e[i] = rUp.get(i);
                if (e[i] == null) e[i] = var.getV(i);
                e[j] = rUpL.get(i);
                if (e[j] == null) e[j] = var.getL(i);
                e[k] = rUpB.get(i);
                if (e[k] == null) e[k] = var.getB(i);
            }

            return (BoolExpr) res.apply(e);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: resPred");
        }
    }

    @Override
    public BoolExpr hPred(BitVecExpr cname, BitVecExpr inst, BitVecExpr element, BitVecExpr value, BoolExpr label, BoolExpr block) {
        try {
            return (BoolExpr) func.getH().apply(cname, inst, element, value, label, block);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: hPred");
        }
    }

    @Override
    public BoolExpr hiPred(BitVecExpr cname, BitVecExpr inst, BitVecExpr value, BoolExpr label, BoolExpr block) {
        try {
            return (BoolExpr) func.getHi().apply(cname, inst, value, label, block);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: hiPred");
        }
    }

    @Override
    public BoolExpr iPred(BitVecExpr cname, BitVecExpr inst, BitVecExpr value, BoolExpr label, BoolExpr block) {
        try {
            return (BoolExpr) func.getI().apply(cname, inst, value, label, block);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: iPred");
        }
    }

    @Override
    public BoolExpr sPred(IntExpr v1, IntExpr v2, BitVecExpr v3, BoolExpr v4, BoolExpr v5) {
        try {
            return (BoolExpr) func.getS().apply(v1, v2, v3, v4, v5);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: sPred");
        }
    }

}