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

    public Z3Query(BoolExpr query, String desc, boolean verbose){
        this.query = query;
        this.description = desc;
        this.isVerbose = verbose;
    }

    public BoolExpr getQuery() {
        return query;
    }

    public String getDescription() {
        return description;
    }

    public boolean isVerbose() {
        return isVerbose;
    }
}
