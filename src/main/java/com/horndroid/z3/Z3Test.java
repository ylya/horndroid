package com.horndroid.z3;

import com.microsoft.z3.*;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashMap;

public class Z3Test {

    private static final Logger LOGGER = LogManager.getLogger(Z3Test.class);

    public static void main(String[] args) throws Z3Exception {
        Global.setParameter("fixedpoint.engine", "pdr");
        HashMap<String, String> cfg = new HashMap<String, String>();
        Context ctx = new Context(cfg);
        Fixedpoint fp = ctx.mkFixedpoint();

        FuncDecl a = ctx.mkConstDecl("a", ctx.mkBoolSort());
        fp.registerRelation(a);
        ctx.mkConst("x", ctx.mkBoolSort());
        FuncDecl b = ctx.mkConstDecl("b", ctx.mkBoolSort());
        fp.registerRelation(b);
        FuncDecl c = ctx.mkConstDecl("c", ctx.mkBoolSort());
        fp.registerRelation(c);

        fp.addRule(
                ctx.mkImplies(
                        (BoolExpr) b.apply(),
                        (BoolExpr) a.apply()
                ),
                null
        );

        fp.addRule(
                ctx.mkImplies(
                        (BoolExpr) c.apply(),
                        (BoolExpr) b.apply()
                ),
                null
        );

        LOGGER.info(fp);

        Status ans = fp.query((BoolExpr) a.apply());
        LOGGER.info(ans);
//
//    System.out.println("====================");
//
//    fp.addRule((BoolExpr) c.apply(), null);
//    System.out.println(fp);
//
//
//    ans = fp.query((BoolExpr) a.apply());
//    System.out.println(ans);


//    BoolSort b = ctx.getBoolSort();
//    BoolExpr v = (BoolExpr) ctx.mkBound(1, b);
////    BoolExpr v2 = (BoolExpr) ctx.mkBound(1, b);
//    FuncDecl p = ctx.mkFuncDecl("p", new Sort[]{b, b}, b);
//    FuncDecl p2 = ctx.mkFuncDecl("p2", new Sort[]{b, b}, b);
//    Fixedpoint fp = ctx.mkFixedpoint();
//    fp.setPredicateRepresentation(p, new Symbol[] {ctx.mkSymbol("interval_relation")});
//    fp.registerRelation(p);
//    fp.registerRelation(p2);
//    fp.addRule(ctx.mkImplies((BoolExpr) p.apply(v, v), (BoolExpr) p2.apply(v, v)), null);
//    int[] array = new int[2];
//    array[0] = 1;
//    array[1] = 0;
//    fp.addFact(p, array);
//    System.out.println(fp);

//    Status a = fp.query((BoolExpr) p2.apply(ctx.mkBool(true), ctx.mkBool(true)));
//    System.out.println(a);
//    System.out.println(fp.getAnswer());
    }
}
