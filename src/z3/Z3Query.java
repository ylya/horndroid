package z3;

import com.microsoft.z3.BoolExpr;

import java.util.ArrayList;

/**
 * Created by rtongchenchitt on 10/19/2015.
 */
public class Z3Query {

    private BoolExpr query;
    private String description;
    private boolean isVerbose;

    private String className;
    private String methodName;
    private String pc;
    private String sinkName;

    public Z3Query(BoolExpr query, String desc, boolean verbose,
                   String className, String methodName, String pc, String sinkName){
        this.query = query;
        this.description = desc;
        this.isVerbose = verbose;

        this.className = className;
        this.methodName = methodName;
        this.pc = pc;
        this.sinkName = sinkName;
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
