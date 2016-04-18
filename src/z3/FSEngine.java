package z3;

import com.microsoft.z3.*;

import analysis.Analysis;
import debugging.Debug;
import debugging.LHInfo;
import debugging.MethodeInfo;
import debugging.RegInfo;
import horndroid.options;

import java.util.*;
import java.util.concurrent.*;

public class FSEngine extends Z3Clauses{

    
    boolean initialized = false;
    private FSVariable var;
    private FSFunction func;

    private Integer localHeapSize;

    private Map<Integer, Integer> allocationPointOffset;

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
            
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed");
        }
    }

    public void initialize( Integer localHeapSize, Map<Integer,Integer> allocationPointOffset, Map<Integer,Integer> allocationPointSize) {
        if (this.initialized){
            throw new RuntimeException("FSEngine Failed: initialized twice");
        }
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

    public FSVariable getVars() {
        return var;
    }

    public FSFunction getFunc() {
        return func;
    }

    @SuppressWarnings("unused")
    public void addQuery(Z3Query query) {
        boolean sameAsCurrentQuery = QUERY_IS_COMPACT && (mCurrentQuery != null)
                && mCurrentQuery.getClassName().equals(query.getClassName())
                && mCurrentQuery.getMethodName().equals(query.getMethodName())
                && mCurrentQuery.getPc().equals(query.getPc())
                && mCurrentQuery.getSinkName().equals(query.getSinkName());

        if (sameAsCurrentQuery) {
            // merge by or-ing queries
            mCurrentQuery.setQuery(this.or(mCurrentQuery.getQuery(), query.getQuery()));
        } else {
            // start new query
            if (mCurrentQuery != null){
                mQueries.add(mCurrentQuery);
            }
            mCurrentQuery = query;
        }
    }
    
    public void addQueryDebug(Z3Query query) {
        mQueries.add(query);
    }

    public void executeAllQueries(Analysis analysis) {    
        
        // ensure that the cached query is added
        if (mCurrentQuery != null){
            mQueries.add(mCurrentQuery);
        }

        int timeout = 30; // 30 minutes

        // ExecutorService executor = Executors.newFixedThreadPool(threshold);
        ExecutorService executor = Executors.newSingleThreadExecutor();
        
       
        
        System.out.println("Number of queries: " + Integer.toString(mQueries.size()));

        //Used for debugging
        final Debug debug = new Debug(analysis);
        //Counter of the number of queries
        int counter = 0;
        int currentPrint = 0;
        int percentage = 0;
        
        int mQueriesLength = mQueries.size();
        
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
            future = executor.submit(new Callable<String>() {


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
                    default:
                        throw new RuntimeException("In flow sensitiv mode received a flow sensitive query: " + q.queryType.toString());
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
                    default:
                        throw new RuntimeException("In flow sensitive mode received a standard query: " + q.queryType.toString());
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
    
    public BoolExpr taintPred(BitVecExpr value, BoolExpr label) {
        try {
            return (BoolExpr) func.getTaint().apply(value, label);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: taintPred");
        }
    }
    
    /*private FuncDecl taintPredDef(String c, String m, int pc, int size) {
        try {
            // taintPredDef
            BitVecSort bv64 = mContext.mkBitVecSort(bvSize);
            BoolSort bool = mContext.mkBoolSort();

            String funcName = "TA_" + c + '_' + m + '_' + Integer.toString(pc);
            FuncDecl f = mContext.mkFuncDecl(funcName, new Sort[]{bv64, bool, bool}, bool);
            this.declareRel(f);
            return f;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("FSEngine Failed: rPredDef");
        }
    }
    
    public BoolExpr taintPred(final String c, final String m, final int pc, BitVecExpr value, BoolExpr global, BoolExpr label, int size) {
        try {
            FuncDecl taint = this.taintPredDef(c, m, pc, size);
            BoolExpr rez = (BoolExpr) taint.apply(value, global, label);
            return rez;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: taintPred");
        }
    }*/
}
