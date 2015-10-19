package z3;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;

/**
 * Created by rtongchenchitt on 10/19/2015.
 */
public interface VariableInject {
    public BitVecExpr getBV(int i);
    public BoolExpr getB(int i);
}
