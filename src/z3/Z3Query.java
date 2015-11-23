package z3;

import com.microsoft.z3.BoolExpr;

import debugging.QUERY_TYPE;

import java.util.ArrayList;

/**
 * Created by rtongchenchitt on 10/19/2015.
 */
public class Z3Query {

    private BoolExpr query;
    private String description;
    private boolean isVerbose;
    public boolean debugging;
    public boolean isReg;
    public boolean isLocalHeap;
    
    public String allocationClassName;
    public String allocationMethodeName;
    public int field = 0;
    public int allocationPC;
    public int regNum = 0;
    public QUERY_TYPE queryType;
    public int instanceNum;

    
    private String className;
    private String methodName;
    private String pc;
    private String sinkName;

    public Z3Query(BoolExpr query, String desc, boolean verbose,
                   String className, String methodName, String pc, String sinkName){
        this.query = query;
        this.description = desc;
        this.isVerbose = verbose;
        this.debugging = false;
        this.isReg = false;
        this.isLocalHeap = false;
        
        this.field = 99999;
        this.allocationClassName = "Error Z3QUery3";
        this.allocationMethodeName = "Error Z3QUery4";
        
        this.className = className;
        this.methodName = methodName;
        this.pc = pc;
        this.sinkName = sinkName;
    }

    /*
     * Debug queries for registers
     */
    public Z3Query(BoolExpr query, int regNum, QUERY_TYPE queryType,
            String className, String methodName, String pc){
        this.query = query;
        this.description = null;
        this.isVerbose = false;
        this.debugging = true;
        this.isReg = true;
        this.isLocalHeap = false;
        
        this.regNum = regNum;
        this.queryType = queryType;
        
        this.field = 99999;
        this.allocationClassName = "Error Z3QUery";
        this.allocationMethodeName = "Error Z3QUery2";
        
        this.className = className;
        this.methodName = methodName;
        this.pc = pc;
        this.sinkName = null;
    }
    
    /*
     * Debuq queries for local heap values
     */
    public Z3Query(BoolExpr query, String acn, String amn, int apc, int af, int instanceNum, QUERY_TYPE queryType,
            String className, String methodName, String pc){
        this.query = query;
        this.description = null;
        this.isVerbose = false;
        this.debugging = true;
        this.isReg = false;
        this.isLocalHeap = true;
        
        this.allocationClassName = acn;
        this.allocationMethodeName = amn;
        this.allocationPC = apc;
        this.field = af;
        this.queryType = queryType;
        this.instanceNum = instanceNum;

        this.className = className;
        this.methodName = methodName;
        this.pc = pc;
        this.sinkName = null;
    }
    

    public BoolExpr getQuery() {
        return query;
    }

    public void setQuery(BoolExpr query) {
        this.query = query;
    }

    public String getDescription() {
        return description;
    }

    public boolean isVerbose() {
        return isVerbose;
    }

    public String getClassName() {
        return className;
    }

    public String getMethodName() {
        return methodName;
    }

    public String getPc() {
        return pc;
    }

    public String getSinkName() {
        return sinkName;
    }

}
