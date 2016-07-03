package z3;

import com.microsoft.z3.*;

import analysis.Analysis;
import debugging.Debug;
import debugging.MethodeInfo;
import horndroid.options;

import java.util.*;
import java.util.concurrent.*;

public class Z3Engine extends Z3Clauses{

    private Z3Variable var;
    private Z3Function func;


    public Z3Engine(options options){
        try {
            bvSize = options.bitvectorSize;
            mQueries = new ArrayList<>();

            Global.setParameter("fixedpoint.engine", "pdr");
            Global.setParameter("pp.bv-literals", "false");

            HashMap<String, String> cfg = new HashMap<String, String>();
            mContext = new Context(cfg);
            mFuncs = new ArrayList<>();
            mRules = new ArrayList<>();

            // add vars
            var = new Z3Variable(mContext, bvSize);

            // add func
            func = new Z3Function(mContext, bvSize);
            this.declareRel(func.getH());
            this.declareRel(func.getHi());
            this.declareRel(func.getI());
            this.declareRel(func.getS());
            
            this.declareRel(func.getTaint());
            this.declareRel(func.getReach());
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

            this.addRule(b1b2b3_b4, null);
            
            // adding rules for the connected component taint
            // base
            BoolExpr hh1 = hPred(var.getCn(), var.getVfp(),
                    var.getF(),
                    var.getVal(), var.getLf(), var.getBf());
            BoolExpr bb1 = taintPred(var.getVfp(), var.getLf());
            BoolExpr hh1_bb1 = mContext.mkImplies(hh1, bb1);
            this.addRule(hh1_bb1, null);
            // step
            BoolExpr hh2 = mContext.mkAnd(
                    hPred(var.getCn(), var.getVfp(),
                            var.getF(),
                            var.getVal(), var.getLf(), var.getBf()),
                    this.eq(var.getBf(), mContext.mkTrue()),
                    taintPred(var.getVal(), var.getLfp())
                    );
            BoolExpr bb2 = taintPred(var.getVfp(), var.getLfp());
            BoolExpr hh2_bb2 = mContext.mkImplies(hh2, bb2);
            this.addRule(hh2_bb2, null);
            
            // adding rules for the connected component reach
            // base
            BoolExpr hh3 = mContext.mkAnd(
                    hPred(var.getCn(), var.getVfp(),
                            var.getF(),
                            var.getVal(), var.getLf(), var.getBf()),
                    this.eq(var.getBf(), mContext.mkTrue())
                    );
            BoolExpr bb3 = reachPred(var.getVfp(), var.getVal());
            BoolExpr hh3_bb3 = mContext.mkImplies(hh3, bb3);
            this.addRule(hh3_bb3, null);
            // step
            BoolExpr hh4 = mContext.mkAnd(
                    hPred(var.getCn(), var.getVfp(),
                            var.getF(),
                            var.getVal(), var.getLf(), var.getBf()),
                    this.eq(var.getBf(), mContext.mkTrue()),
                    reachPred(var.getVal(), var.getRez())
                    );
            BoolExpr bb4 = reachPred(var.getVfp(), var.getRez());
            BoolExpr hh4_bb4 = mContext.mkImplies(hh4, bb4);
            this.addRule(hh4_bb4, null);
            
        } catch (Z3Exception e){
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed");
        }
    }



    public Z3Variable getVars(){ return var; }

    public Z3Function getFunc(){ return func; }



    @SuppressWarnings("unused")
    public void addQuery(Z3Query query){


        boolean sameAsCurrentQuery =
                QUERY_IS_COMPACT
                && mCurrentQuery != null
                && mCurrentQuery.getClassName().equals(query.getClassName())
                && mCurrentQuery.getMethodName().equals(query.getMethodName())
                && mCurrentQuery.getPc().equals(query.getPc())
                && mCurrentQuery.getSinkName().equals(query.getSinkName());

        if( sameAsCurrentQuery ){
            // merge by or-ing queries
            mCurrentQuery.setQuery(
                    this.or(
                            mCurrentQuery.getQuery(),
                            query.getQuery()
                            )
                    );
        } else {
            // start new query
            if(mCurrentQuery != null){
                mQueries.add(mCurrentQuery);
            }
            mCurrentQuery = query;
        }
    }

    
    public void addQueryDebug(Z3Query query){
                mQueries.add(query);
    }

    
    
    public void executeAllQueries(Analysis analysis){
        Debug debug = new Debug(analysis);
        
        // ensure that the cached query is added
        if(mCurrentQuery != null) mQueries.add(mCurrentQuery);

        int timeout = 30; // 30 minutes

        //		ExecutorService executor = Executors.newFixedThreadPool(threshold);
        ExecutorService executor = Executors.newSingleThreadExecutor();
        System.out.println("Number of queries: " + Integer.toString(mQueries.size()));
        int counter = 0;
        int currentPrint = 0;
        int percentage = 0;
        int mQueriesLength = mQueries.size();

        
        for (int i = 0; i < mQueries.size(); i++) {

            final Z3Query q = mQueries.get(i);
            if(!q.debugging){
                System.out.println((i + 1) + ": ");
                if (q.isVerbose()){
                    System.out.println(q.getDescription());
                }
            }
            
            final Fixedpoint temp = mContext.mkFixedpoint();
            for(BoolExpr rule : mRules){
                temp.addRule(rule, null);
            }
            for(FuncDecl func : mFuncs){
                temp.registerRelation(func);
                Symbol[] symbols = new Symbol[]{mContext.mkSymbol("interval_relation"),
                        mContext.mkSymbol("bound_relation")};
                temp.setPredicateRepresentation(func, symbols);
            }

            final Future<String> future = executor.submit(new Callable<String>() {
                @Override
                public String call() throws Exception {

                    Status result = temp.query(q.getQuery());
                    if(!q.debugging){
                        System.out.println(result);
                    }
                    
                    return result.toString();
                }
            });
            
            /*
             * Apparently the Z3 wrapper is not handling the memory correctly, need to GC manually. See:
             * http://stackoverflow.com/questions/24188626/performance-issues-about-z3-for-java#comment37349014_24190067
             */
            if (counter % 50 == 0){
                System.gc();
            }

            if ((counter >= currentPrint + (mQueriesLength/10)) && (mQueriesLength > 10)){
                currentPrint = counter;
                percentage+= 10;
                System.out.println(percentage + "% of queries handled");
            }
            
            counter++;


            try {
                if (q.debugging && q.isReg){
                    final MethodeInfo minfo = debug.get(q.getClassName(), q.getMethodName());
                    boolean res = future.get(timeout, TimeUnit.MINUTES).equals("SATISFIABLE");
                    /*
                     * The queries are not stored in an obvious way inside the debug object.
                     */
                    switch(q.queryType){
                    case STANDARD_REACH:
                        minfo.regInfo[q.regNum].highPut(Integer.parseInt(q.getPc()),res);
                        break;
                    case STANDARD_HIGH:
                        minfo.regInfo[q.regNum].localPut(Integer.parseInt(q.getPc()),res);
                        break;
                    case STANDARD_BLOCK:
                        minfo.regInfo[q.regNum].globalPut(Integer.parseInt(q.getPc()),res);
                        break;
                    default:
                        throw new RuntimeException("In standard mode received a flow sensitive query: " + q.queryType.toString());
                    }
                }

                if(!q.debugging){
                    future.get(timeout, TimeUnit.MINUTES);
                }
                
            } catch (TimeoutException e) {
                future.cancel(true);
            } catch (InterruptedException e) {
                future.cancel(true);
            } catch (ExecutionException e) {
                future.cancel(true);
            }
        }
        
        debug.printToLatex();

        executor.shutdownNow();
    }


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
            return f;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: rPredDef");
        }
    }

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

            return (BoolExpr) r.apply(e);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: rPred");
        }
    }


    public BoolExpr rInvokePred(final String c, final String m, final int pc, final Map<Integer, BitVecExpr> rUp, final Map<Integer, BoolExpr> rUpL, final Map<Integer, BoolExpr> rUpB, final int numArg, final int numReg, final int size) {
        try {
            int arraySize = numArg + numReg + 1;
            FuncDecl f = this.rPredDef(c, m, pc, arraySize);

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
            return f;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: resPredDef");
        }
    }

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

    public BoolExpr hPred(BitVecExpr cname, BitVecExpr inst, BitVecExpr element, BitVecExpr value, BoolExpr label, BoolExpr block) {
        try {
            return (BoolExpr) func.getH().apply(cname, inst, element, value, label, block);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: hPred");
        }
    }

    public BoolExpr hiPred(BitVecExpr cname, BitVecExpr inst, BitVecExpr value, BoolExpr label, BoolExpr block) {
        try {
            return (BoolExpr) func.getHi().apply(cname, inst, value, label, block);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: hiPred");
        }
    }

    public BoolExpr iPred(BitVecExpr cname, BitVecExpr inst, BitVecExpr value, BoolExpr label, BoolExpr block) {
        try {
            return (BoolExpr) func.getI().apply(cname, inst, value, label, block);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: iPred");
        }
    }

    public BoolExpr sPred(IntExpr v1, IntExpr v2, BitVecExpr v3, BoolExpr v4, BoolExpr v5) {
        try {
            return (BoolExpr) func.getS().apply(v1, v2, v3, v4, v5);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: sPred");
        }
    }
    
    public BoolExpr taintPred(BitVecExpr value, BoolExpr label) {
        try {
            return (BoolExpr) func.getTaint().apply(value, label);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: taintPred");
        }
    }
    public BoolExpr reachPred(BitVecExpr value, BitVecExpr value2) {
        try {
            return (BoolExpr) func.getReach().apply(value, value2);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: reachPred");
        }
    }
}
