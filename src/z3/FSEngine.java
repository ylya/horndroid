package z3;

import com.microsoft.z3.*;

import analysis.Analysis;
import debugging.Debug;
import debugging.LHInfo;
import debugging.LHKey;
import debugging.MethodeInfo;
import debugging.RegInfo;
import horndroid.options;

import java.io.IOException;
import java.util.*;
import java.util.concurrent.*;

public class FSEngine {

    final private boolean QUERY_IS_COMPACT = false;

    private Context mContext;
    private Boolean initialized = false;
    // private Fixedpoint mFixedPoint;
    private ArrayList<BoolExpr> mRules;
    private ArrayList<FuncDecl> mFuncs;

    private ArrayList<Z3Query> mQueries;
    //private ArrayList<Z3Query> mQueriesDebug;
    private Z3Query mCurrentQuery;

    private int bvSize;
    private FSVariable var;
    private FSFunction func;

    private Integer localHeapNumberEntries;
    private Integer localHeapSize;

    private Map<Integer, Integer> allocationPointOffset;
    // legacy
    // private int biggestRegisterNumber;
    // public void updateBiggestRegister(final int i){
    // if (i > this.biggestRegisterNumber) biggestRegisterNumber = i;
    // }

    private Map<Integer, Integer> allocationPointSize;

    public FSEngine(options options) {
        try {
            bvSize = options.bitvectorSize;
            mQueries = new ArrayList<>();
            //mQueriesDebug = new ArrayList<>();

            Global.setParameter("fixedpoint.engine", "pdr");
            // Global.setParameter("fixedpoint.unbound_compressor", "false");
            Global.setParameter("pp.bv-literals", "false");

            HashMap<String, String> cfg = new HashMap<String, String>();
            mContext = new Context(cfg); // Context ctx = mContext;
            // mFixedPoint = mContext.mkFixedpoint(); //Fixedpoint fp =
            // mFixedPoint;
            mFuncs = new ArrayList<>();
            mRules = new ArrayList<>();

            // add vars
            var = new FSVariable(mContext, bvSize);

            // add func
            func = new FSFunction(mContext, bvSize);
            this.declareRel(func.getH());
            this.declareRel(func.getHi());
            this.declareRel(func.getI());
            this.declareRel(func.getS());

            // add main
            BoolExpr b1 = hPred(var.getCn(), var.getCn(), mContext.mkBV("parent".hashCode(), bvSize), var.getF(),
                    var.getLf(), var.getBf());
            BoolExpr b2 = hPred(var.getCn(), var.getCn(), mContext.mkBV("result".hashCode(), bvSize), var.getVal(),
                    var.getLval(), var.getBval());
            BoolExpr b3 = hPred(var.getF(), var.getF(), var.getFpp(), var.getVfp(), var.getLfp(), var.getBfp());
            BoolExpr b1b2b3 = mContext.mkAnd(b1, b2, b3);
            BoolExpr b4 = hPred(var.getF(), var.getF(), mContext.mkBV("result".hashCode(), bvSize), var.getVal(),
                    var.getLval(), var.getBval());
            BoolExpr b1b2b3_b4 = mContext.mkImplies(b1b2b3, b4);

            this.addRule(b1b2b3_b4, null);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed");
        }
    }

    public void initialize(Integer localHeapNumberEntries, Integer localHeapSize, Map<Integer,Integer> allocationPointOffset, Map<Integer,Integer> allocationPointSize) {
        if (this.initialized)
            throw new RuntimeException("FSEngine Failed: initialized twice");
        this.localHeapNumberEntries = localHeapNumberEntries;
        this.localHeapSize = localHeapSize;
        this.allocationPointOffset = allocationPointOffset;
        this.allocationPointSize = allocationPointSize;
        this.var.initialize(localHeapSize);
        this.initialized = true;
    }

    public Boolean isInitialized() {
        return initialized;
    }

    public Integer getOffset(int instanceNumber){
        return allocationPointOffset.get(instanceNumber);
    }
    public Integer getSize(int instanceNumber){
        return allocationPointSize.get(instanceNumber);
    }
    public Context getContext() {
        return mContext;
    }

    public FSVariable getVars() {
        return var;
    }

    public FSFunction getFunc() {
        return func;
    }

    public void addRule(BoolExpr rule, String symbol) {
        try {
            // mFixedPoint.addRule(rule, null);
            mRules.add(rule);
            // mContext.mkSymbol(RandomStringUtils.random(16,true,true)));
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: addRule");
        }
    }

    public BoolExpr mkTrue() {
        try {
            return mContext.mkBool(true);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: true");
        }
    }

    public BoolExpr mkFalse() {
        try {
            return mContext.mkBool(false);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: false");
        }
    }

    public BoolExpr mkBool(boolean b) {
        try {
            return mContext.mkBool(b);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: mkBool");
        }
    }

    public BitVecExpr mkBitVector(String data, int len) {
        try {
            return mContext.mkBV(data, len);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: mkBitVector String");
        }
    }

    public BitVecExpr mkBitVector(int data, int len) {
        try {
            return mContext.mkBV(data, len);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: mkBitVector int");
        }
    }

    public BitVecExpr mkBitVector(long data, int len) {
        try {
            return mContext.mkBV(data, len);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: mkBitVector long");
        }
    }

    public IntExpr mkInt(String data) {
        try {
            return mContext.mkInt(data);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: mkInt");
        }
    }

    public IntExpr mkInt(int data) {
        try {
            return mContext.mkInt(data);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: mkInt");
        }
    }

    public BoolExpr and(BoolExpr... b) {
        try {
            return mContext.mkAnd(b);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: and");
        }
    }

    public BoolExpr or(BoolExpr... b) {
        try {
            return mContext.mkOr(b);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: or");
        }
    }

    public BoolExpr not(BoolExpr b) {
        try {
            return mContext.mkNot(b);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: not");
        }
    }

    public BoolExpr eq(BoolExpr b1, BoolExpr b2) {
        try {
            return mContext.mkEq(b1, b2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: eq");
        }
    }

    public BoolExpr eq(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkEq(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: eq");
        }
    }

    public BoolExpr neq(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkNot(mContext.mkEq(bv1, bv2));
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: eq");
        }
    }
    
    public Expr ite(BoolExpr b, Expr e1, Expr e2) {
        try {
            return mContext.mkITE(b, e1, e2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: ite");
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
            throw new RuntimeException("FSEngine Failed: bvneg");
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
            throw new RuntimeException("FSEngine Failed: bvnot");
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
            throw new RuntimeException("FSEngine Failed: bvadd");
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
            throw new RuntimeException("FSEngine Failed: bvmul");
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
            throw new RuntimeException("FSEngine Failed: bvudiv");
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
            throw new RuntimeException("FSEngine Failed: bvurem");
        }
    }

    public BoolExpr bvugt(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVUGT(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: bvugt");
        }
    }

    public BoolExpr bvuge(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVUGE(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: bvuge");
        }
    }

    public BoolExpr bvule(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVULE(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: bvule");
        }
    }

    public BoolExpr bvult(BitVecExpr bv1, BitVecExpr bv2) {
        try {
            return mContext.mkBVULE(bv1, bv2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: bvult");
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
                    throw new RuntimeException("FSEngine: wrong type in LSHR");
            }
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: bvlshr");
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
                    throw new RuntimeException("FSEngine: wrong type in ASHR");
            }
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: bvashr");
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
                    throw new RuntimeException("FSEngine: wrong type in SHL");
            }
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: bvshl");
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
            throw new RuntimeException("FSEngine Failed: bvsub");
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
            throw new RuntimeException("FSEngine Failed: bvxor");
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
            throw new RuntimeException("FSEngine Failed: bvor");
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
            throw new RuntimeException("FSEngine Failed: bvand");
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
    
    
    public BoolExpr implies(BoolExpr b1, BoolExpr b2) {
        try {
            return mContext.mkImplies(b1, b2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: implies");
        }
    }

    public void addQuery(Z3Query query) {
        boolean sameAsCurrentQuery = QUERY_IS_COMPACT && mCurrentQuery != null
                && mCurrentQuery.getClassName().equals(query.getClassName())
                && mCurrentQuery.getMethodName().equals(query.getMethodName())
                && mCurrentQuery.getPc().equals(query.getPc())
                && mCurrentQuery.getSinkName().equals(query.getSinkName());

        if (sameAsCurrentQuery) {
            // merge by or-ing queries
            mCurrentQuery.setQuery(this.or(mCurrentQuery.getQuery(), query.getQuery()));
        } else {
            // start new query
            if (mCurrentQuery != null)
                mQueries.add(mCurrentQuery);
            mCurrentQuery = query;
        }
    }
    
    public void addQueryDebug(Z3Query query) {
        if (!query.debugging)
            //throw new RuntimeException("debug queries only");
        mQueries.add(query);
    }

    public void executeAllQueries(Analysis analysis) {    
        
        // ensure that the cached query is added
        if (mCurrentQuery != null)
            mQueries.add(mCurrentQuery);

        int threshold = 10;
        int timeout = 30; // 30 minutes

        // ExecutorService executor = Executors.newFixedThreadPool(threshold);
        ExecutorService executor = Executors.newSingleThreadExecutor();
        
       
        
        System.out.println("Number of queries: " + Integer.toString(mQueries.size()));

        //Used for debugging
        final Debug debug = new Debug(analysis);
        //Counter of the number of queries
        int counter = 0;
        for (int i = 0; i < mQueries.size(); i++) {

            final Z3Query q = mQueries.get(i);
            if(!q.debugging){
                System.out.println((i + 1) + ": ");
                if (q.isVerbose())
                    System.out.println(q.getDescription());
            }

            final Fixedpoint temp = mContext.mkFixedpoint();
            for (BoolExpr rule : mRules) {
                temp.addRule(rule, null);
            }
            for (FuncDecl func : mFuncs) {
                temp.registerRelation(func);
                Symbol[] symbols = new Symbol[] { mContext.mkSymbol("interval_relation"),
                        mContext.mkSymbol("bound_relation") };
                temp.setPredicateRepresentation(func, symbols);
            }

         
            
            Future<String> future = null;
            future = executor.submit(new Callable() {


                public String call() throws Exception {

                    Status result = temp.query(q.getQuery());
                    if(!q.debugging)
                        System.out.println(result);

                    /*if(q.isLocalHeap && result.equals("SATISFIABLE"))
                        System.out.println("" + q.field);*/
                    
                    return result.toString();
                }
            });
            
            /*
             * Apparently the Z3 wrapper is not handling the memory correctly, need to GC manually. See:
             * http://stackoverflow.com/questions/24188626/performance-issues-about-z3-for-java#comment37349014_24190067
             */
            if (counter % 50 == 0)
                System.gc();
            counter++;
            
            try{
                if (q.debugging && q.isReg){
                    final MethodeInfo minfo = debug.get(q.getClassName(), q.getMethodName());
                    boolean res = future.get(timeout, TimeUnit.MINUTES).equals("SATISFIABLE");
                    switch(q.queryType){
                    case HIGH:
                        minfo.regInfo[q.regNum].highPut(Integer.parseInt(q.getPc()),res);
                        break;
                    case LOCAL:
                        minfo.regInfo[q.regNum].localPut(Integer.parseInt(q.getPc()),res);
                        break;
                    case GLOBAL:
                        minfo.regInfo[q.regNum].globalPut(Integer.parseInt(q.getPc()),res);
                        break;
                    }
                }
                if (q.debugging && q.isLocalHeap){
                    final MethodeInfo minfo = debug.get(q.getClassName(), q.getMethodName());
                    boolean res = future.get(timeout, TimeUnit.MINUTES).equals("SATISFIABLE");
                    //LHKey lhkey = new LHKey(q.instanceNum,q.field);
                    final LHInfo lhinf = minfo.getLHInfo(q.instanceNum,q.field);
                    final RegInfo regInf = lhinf.getRegInfo();
                    Integer k = Integer.parseInt(q.getPc());
                    switch(q.queryType){
                    case HIGH:
                        regInf.highPut(k,res);
                        break;
                    case LOCAL:
                        regInf.localPut(k,res);
                        break;
                    case GLOBAL:
                        regInf.globalPut(k,res);
                        break;
                    }
                }


                if(!q.debugging)
                    future.get(timeout, TimeUnit.MINUTES);
            } catch (TimeoutException e) {
                future.cancel(true);
            } catch (InterruptedException e) {
                future.cancel(true);
            } catch (ExecutionException e) {
                future.cancel(true);
            }
        }
        
        debug.printToLatex();
        try {
            new ProcessBuilder(new String[]{ "pdflatex", "wrapper.tex"}).start();
        } catch (IOException e) {
            e.printStackTrace();
        }

        executor.shutdownNow();
    }

    public void declareRel(FuncDecl funcDecl) {
        try {
            // mFixedPoint.registerRelation(funcDecl);
            mFuncs.add(funcDecl);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: declareRel");
        }
    }

    public void declareRel(String name, Sort[] domain, Sort range) {
        try {
            FuncDecl f = mContext.mkFuncDecl(name, domain, range);
            this.declareRel(f);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: declareRel");
        }
    }

    public void declareVar(Sort type) {
        try {
            Expr var = mContext.mkBound(0, type);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: declareVar");
        }
    }

    private FuncDecl rPredDef(String c, String m, int pc, int size) {
        try {
            // rPredDef
            BitVecSort bv64 = mContext.mkBitVecSort(bvSize);
            BoolSort bool = mContext.mkBoolSort();

            String funcName = "R_" + c + '_' + m + '_' + Integer.toString(pc);
            Sort[] domains = new Sort[4 * size + 5 * localHeapSize];
            // argument + register + result register
            Arrays.fill(domains, 0, size, bv64); 
            // high value and local object label and global object label
            Arrays.fill(domains, size, 4 * size, bool);             
            // local heap entries
            Arrays.fill(domains, 4 * size, 4 * size + localHeapSize, bv64); 
            // high value and local object label and global object label and abstract filter
            Arrays.fill(domains, 4 * size + localHeapSize, 4 * size + 5 * localHeapSize, bool); 
            FuncDecl f = mContext.mkFuncDecl(funcName, domains, mContext.mkBoolSort());
            this.declareRel(f);
            return f;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: rPredDef");
        }
    }

    public BoolExpr rPred(final String c, final String m, final int pc, final Map<Integer, BitVecExpr> rUp,
            final Map<Integer, BoolExpr> rUpHigh, final Map<Integer, BoolExpr> rUpLocal,
            final Map<Integer, BoolExpr> rUpGlobal, final Map<Integer, BitVecExpr> lHValues,
            final Map<Integer, BoolExpr> lHHigh, final Map<Integer, BoolExpr> lHLocal,
            final Map<Integer, BoolExpr> lHGlobal, final Map<Integer, BoolExpr> lHFilter, final int numArg,
            final int numReg) {
        try {
            int size = numArg + numReg + 1; // include return register
            FuncDecl r = this.rPredDef(c, m, pc, size);

            Expr[] e = new Expr[4 * size + 5 * this.localHeapSize];
            for (int i = 0, j = size, k = 2 * size, l = 3 * size; i < size; i++, j++, k++, l++) {
                e[i] = rUp.get(i);
                if (e[i] == null) {
                    e[i] = var.getV(i);
                }
                e[j] = rUpHigh.get(i);
                if (e[j] == null) {
                    e[j] = var.getH(i);
                }
                e[k] = rUpLocal.get(i);
                if (e[k] == null) {
                    e[k] = var.getL(i);
                }
                e[l] = rUpGlobal.get(i);
                if (e[l] == null) {
                    e[l] = var.getG(i);
                }
            }
            ;
            for (int loop = 0,  i = 4 * size, j = 4 * size + this.localHeapSize, k = 4 * size
                    + 2 * this.localHeapSize, l = 4 * size + 3 * this.localHeapSize, n = 4 * size
                            + 4 * this.localHeapSize; loop < this.localHeapSize; loop++, i++, j++, k++, l++, n++) {
                e[i] = lHValues.get(loop);
                if (e[i] == null) {
                    e[i] = var.getLHV(loop);
                }
                e[j] = lHHigh.get(loop);
                if (e[j] == null) {
                    e[j] = var.getLHH(loop);
                }
                e[k] = lHLocal.get(loop);
                if (e[k] == null) {
                    e[k] = var.getLHL(loop);
                }
                e[l] = lHGlobal.get(loop);
                if (e[l] == null) {
                    e[l] = var.getLHG(loop);
                }
                e[n] = lHFilter.get(loop);
                if (e[n] == null) {
                    e[n] = var.getLHF(loop);
                }
            }
            ;
            BoolExpr rez = (BoolExpr) r.apply(e); 
            
            return rez;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: rPred");
        }
    }

    public BoolExpr rPredInvok(final String c, final String m, final int pc, final Map<Integer, BitVecExpr> rUp,
            final Map<Integer, BoolExpr> rUpHigh, final Map<Integer, BoolExpr> rUpLocal,
            final Map<Integer, BoolExpr> rUpGlobal, final Map<Integer, BitVecExpr> lHValues,
            final Map<Integer, BoolExpr> lHHigh, final Map<Integer, BoolExpr> lHLocal,
            final Map<Integer, BoolExpr> lHGlobal, final Map<Integer, BoolExpr> lHFilter, final int numArg,
            final int numReg, final int size) {
        try {
            int rsize = numArg + numReg + 1; // include return register
            FuncDecl r = this.rPredDef(c, m, pc, rsize);

            Expr[] e = new Expr[4 * rsize + 5 * this.localHeapSize];
            for (int i = 0, j = rsize, k = 2 * rsize, l = 3 * rsize; i < rsize; i++, j++, k++, l++) {
                e[i] = rUp.get(i);
                if (e[i] == null) {
                    e[i] = this.mkBitVector(0, size);
                }
                e[j] = rUpHigh.get(i);
                if (e[j] == null) {
                    e[j] = this.mkFalse();
                }
                e[k] = rUpLocal.get(i);
                if (e[k] == null) {
                    e[k] = this.mkFalse();
                }
                e[l] = rUpGlobal.get(i);
                if (e[l] == null) {
                    e[l] = this.mkFalse();
                }
            }
            ;
            for (int loop = 0, i = 4 * rsize, j = 4 * rsize + this.localHeapSize, k = 4 * rsize
                    + 2 * this.localHeapSize, l = 4 * rsize + 3 * this.localHeapSize, n = 4 * rsize
                            + 4 * this.localHeapSize; loop < this.localHeapSize; loop++, i++, j++, k++, l++, n++) {
                e[i] = lHValues.get(loop);
                if (e[i] == null) {
                    e[i] = var.getLHV(loop);
                }
                e[j] = lHHigh.get(loop);
                if (e[j] == null) {
                    e[j] = var.getLHH(loop);
                }
                e[k] = lHLocal.get(loop);
                if (e[k] == null) {
                    e[k] = var.getLHL(loop);
                }
                e[l] = lHGlobal.get(loop);
                if (e[l] == null) {
                    e[l] = var.getLHG(loop);
                }
                e[n] = this.mkFalse();
             
            }
            ;

            return (BoolExpr) r.apply(e);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: rPredInvok");
        }
    }

    private FuncDecl resPredDef(String c, String m, int size) {
        try {
            BitVecSort bv64 = mContext.mkBitVecSort(bvSize);
            BoolSort bool = mContext.mkBoolSort();

            String funcName = "RES_" + c + '_' + m;
            Sort[] domains = new Sort[4 * size + 5 * localHeapSize];
            Arrays.fill(domains, 0, size, bv64); // argument + register + result register
            Arrays.fill(domains, size, 4 * size, bool); // high value + local object label + global object label
            Arrays.fill(domains, 4 * size, 4 * size + localHeapSize, bv64);
            // local + heap + entries
            Arrays.fill(domains, 4 * size + localHeapSize, 4 * size + 5 * localHeapSize, bool);
            // high value and local object label and global object label and abstract filter

            FuncDecl f = mContext.mkFuncDecl(funcName, domains, bool);

            this.declareRel(f);
            return f;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: resPredDef");
        }
    }

    public BoolExpr resPred(final String c, final String m, final Map<Integer, BitVecExpr> rUp,
            final Map<Integer, BoolExpr> rUpHigh, final Map<Integer, BoolExpr> rUpLocal,
            final Map<Integer, BoolExpr> rUpGlobal, final Map<Integer, BitVecExpr> lHValues,
            final Map<Integer, BoolExpr> lHHigh, final Map<Integer, BoolExpr> lHLocal,
            final Map<Integer, BoolExpr> lHGlobal, final Map<Integer, BoolExpr> lHFilter, final int numArg) {
        try {
            int size = numArg + 1; // include return register
            FuncDecl res = this.resPredDef(c, m, size);

            Expr[] e = new Expr[4 * size + 5 * this.localHeapSize];
            for (int i = 0, j = size, k = 2 * size, l = 3 * size; i < size; i++, j++, k++, l++) {
                e[i] = rUp.get(i);
                if (e[i] == null) {
                    e[i] = var.getV(i);
                }
                e[j] = rUpHigh.get(i);
                if (e[j] == null) {
                    e[j] = var.getH(i);
                } 
                e[k] = rUpLocal.get(i);
                if (e[k] == null) {
                    e[k] = var.getL(i);
                } 
                e[l] = rUpGlobal.get(i);
                if (e[l] == null) {
                    e[l] = var.getG(i);
                }
            }
            ;

            for (int loop = 0, i = 4 * size, j = 4 * size + this.localHeapSize, k = 4 * size
                    + 2 * this.localHeapSize, l = 4 * size + 3 * this.localHeapSize, n = 4 * size
                            + 4 * this.localHeapSize; loop < this.localHeapSize; loop++, i++, j++, k++, l++, n++) {
                e[i] = lHValues.get(loop);
                if (e[i] == null) {
                    e[i] = var.getLHV(loop);
                } 
                e[j] = lHHigh.get(loop);
                if (e[j] == null) {
                    e[j] = var.getLHH(loop);
                } 
                e[k] = lHLocal.get(loop);
                if (e[k] == null) {
                    e[k] = var.getLHL(loop);
                } 
                e[l] = lHGlobal.get(loop);
                if (e[l] == null) {
                    e[l] = var.getLHG(loop);
                } 
                e[n] = lHFilter.get(loop);
                if (e[n] == null) {
                    e[n] = var.getLHF(loop);
                } 
            }
            ;
            //this.addQuery(new Z3Query((BoolExpr) res.apply(e), c + ' ' + m , true, c, m, "rez", ""));

            return (BoolExpr) res.apply(e);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: resPred");
        }
    }

    public BoolExpr hPred(BitVecExpr cname, BitVecExpr inst, BitVecExpr element, BitVecExpr value, BoolExpr label,
            BoolExpr block) {
        try {
            return (BoolExpr) func.getH().apply(cname, inst, element, value, label, block);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: hPred");
        }
    }

    public BoolExpr hiPred(BitVecExpr cname, BitVecExpr inst, BitVecExpr value, BoolExpr label, BoolExpr block) {
        try {
            return (BoolExpr) func.getHi().apply(cname, inst, value, label, block);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: hiPred");
        }
    }

    public BoolExpr iPred(BitVecExpr cname, BitVecExpr inst, BitVecExpr value, BoolExpr label, BoolExpr block) {
        try {
            return (BoolExpr) func.getI().apply(cname, inst, value, label, block);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: iPred");
        }
    }

    public BoolExpr sPred(IntExpr v1, IntExpr v2, BitVecExpr v3, BoolExpr v4, BoolExpr v5) {
        try {
            return (BoolExpr) func.getS().apply(v1, v2, v3, v4, v5);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: sPred");
        }
    }

}
