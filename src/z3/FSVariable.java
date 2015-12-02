package z3;

import com.microsoft.z3.*;


/**
 * Created by rtongchenchitt on 10/15/2015.
 */
public class FSVariable {

    private final int GUARD = 100;
    public final int MAX_REGISTER = 68;
    public int MAX_LOCALHEAP = 0;

    //private int localHeapNumberEntries = 0;
    //private int localHeapSize = 0;

    private final Context ctx;
    private final BoolSort bool;
    private final BitVecSort bv64;

    //TODO: Those variables are not the correct one for the FS analysis!
    private final BitVecExpr rez, rezp, buf, bufp, f, fpp, vfp, cn, val;
    private final BoolExpr lrez, hrez, grez, lrezp, lbuf, lbufp, lfp, bfp, lf, bf, lval, bval;
    private final IntExpr fnum, cnum;

    public FSVariable(Context ctx, int bvSize) throws Z3Exception {
        this.ctx = ctx;

        this.bool = ctx.mkBoolSort();
        this.bv64 = ctx.mkBitVecSort(bvSize);
        IntSort integer = ctx.mkIntSort();

        this.rez = (BitVecExpr) ctx.mkBound(0, bv64);
        this.rezp = (BitVecExpr) ctx.mkBound(1, bv64);
        this.buf = (BitVecExpr) ctx.mkBound(2, bv64);
        this.bufp = (BitVecExpr) ctx.mkBound(3, bv64);
        this.hrez = (BoolExpr) ctx.mkBound(4, bool);
        this.lrez = (BoolExpr) ctx.mkBound(5, bool);
        this.grez = (BoolExpr) ctx.mkBound(25, bool);
        this.lrezp = (BoolExpr) ctx.mkBound(6, bool);
        this.lbuf = (BoolExpr) ctx.mkBound(7, bool);
        this.lbufp = (BoolExpr) ctx.mkBound(8, bool);
        this.fnum = (IntExpr) ctx.mkBound(9, integer);
        this.f = (BitVecExpr) ctx.mkBound(10, bv64);
        this.fpp = (BitVecExpr) ctx.mkBound(11, bv64);
        this.vfp = (BitVecExpr) ctx.mkBound(12, bv64);
        this.lfp = (BoolExpr) ctx.mkBound(13, bool);
        this.bfp = (BoolExpr) ctx.mkBound(14, bool);
        this.cn = (BitVecExpr) ctx.mkBound(15, bv64);
        this.lf = (BoolExpr) ctx.mkBound(16, bool);
        this.bf = (BoolExpr) ctx.mkBound(17, bool);
        this.val = (BitVecExpr) ctx.mkBound(18, bv64);
        this.lval = (BoolExpr) ctx.mkBound(19, bool);
        this.bval = (BoolExpr) ctx.mkBound(20, bool);
        this.cnum = (IntExpr) ctx.mkBound(21, integer);

    }

    
    public void initialize( Integer localHeapSize) { 
        this.MAX_LOCALHEAP = localHeapSize;
    }
    

    public BitVecExpr getRez() {
        return rez;
    }

    public BitVecExpr getRezp() {
        return rezp;
    }

    public BitVecExpr getBuf() {
        return buf;
    }

    public BitVecExpr getBufp() {
        return bufp;
    }

    public BitVecExpr getF() {
        return f;
    }

    public BitVecExpr getFpp() {
        return fpp;
    }

    public BitVecExpr getVfp() {
        return vfp;
    }

    public BitVecExpr getCn() {
        return cn;
    }

    public BitVecExpr getVal() {
        return val;
    }

    public BoolExpr getLrez() {
        return lrez;
    }

    public BoolExpr getHrez() {
        return hrez;
    }

    public BoolExpr getGrez() {
        return grez;
    }

    public BoolExpr getLrezp() {
        return lrezp;
    }

    public BoolExpr getLbuf() {
        return lbuf;
    }

    public BoolExpr getLbufp() {
        return lbufp;
    }

    public BoolExpr getLfp() {
        return lfp;
    }

    public BoolExpr getBfp() {
        return bfp;
    }

    public BoolExpr getLf() {
        return lf;
    }

    public BoolExpr getBf() {
        return bf;
    }

    public BoolExpr getLval() {
        return lval;
    }

    public BoolExpr getBval() {
        return bval;
    }

    public IntExpr getFnum() {
        return fnum;
    }

    public IntExpr getCnum() {
        return cnum;
    }

    // TODO:
    // cache vs remake
    public BitVecExpr getV(int i) {
        try {
            // if (i < 0) return ctx.mkBV(-1*i, bv64);
            return (BitVecExpr) ctx.mkBound(GUARD + 4 * i + 0, bv64);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getV");
        }
    }

    public VariableInject getInjectV(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BitVecExpr get(int i) {
                return var.getV(i);
            }
        };
    }

    public BoolExpr getH(int i) {
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 4 * i + 1, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getH");
        }
    }

    public VariableInject getInjectH(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getH(i);
            }
        };
    }

    public BoolExpr getL(int i) {
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 4 * i + 2, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getL");
        }
    }

    public VariableInject getInjectL(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getL(i);
            }
        };
    }

    public BoolExpr getG(int i) {
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 4 * i + 3, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getG");
        }
    }

    public VariableInject getInjectG(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getG(i);
            }
        };
    }

    // Local Heap variables
    public BitVecExpr getLHV(int i) {
        try {
            // if (i < 0) return ctx.mkBV(-1*i, bv64);
            return (BitVecExpr) ctx.mkBound(GUARD + 4 * MAX_REGISTER + 5 * i + 0, bv64);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getLHV");
        }
    }

    public VariableInject GetInjectLHV(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BitVecExpr get(int i) {
                return var.getLHV(i);
            }
        };
    }

    public BoolExpr getLHH(int i) {
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 4 * MAX_REGISTER + 5 * i + 1, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getLHH");
        }
    }

    public VariableInject GetInjectLHH(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getLHH(i);
            }
        };
    }

    public BoolExpr getLHL(int i) {
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 4 * MAX_REGISTER + 5 * i + 2, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getLHL");
        }
    }

    public VariableInject GetInjectLHL(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getLHL(i);
            }
        };
    }

    public BoolExpr getLHG(int i) {
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 4 * MAX_REGISTER + 5 * i + 3, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getLHG");
        }
    }

    public VariableInject GetInjectLHG(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getLHG(i);
            }
        };
    }

    public BoolExpr getLHF(int i) {
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 4 * MAX_REGISTER + 5 * i + 4, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getLHF");
        }
    }

    public VariableInject GetInjectLHF(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getLHF(i);
            }
        };
    }
    
    // Copie of local heap variables
    public BitVecExpr getLHCV(int i) {
        try {
            // if (i < 0) return ctx.mkBV(-1*i, bv64);
            return (BitVecExpr) ctx.mkBound(GUARD + 4 * MAX_REGISTER + 5 * MAX_LOCALHEAP + 5 * i + 0, bv64);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getLHCV");
        }
    }

    public VariableInject GetInjectLHCV(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BitVecExpr get(int i) {
                return var.getLHCV(i);
            }
        };
    }

    public BoolExpr getLHCH(int i) {
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 4 * MAX_REGISTER + 5 * MAX_LOCALHEAP + 5 * i + 1, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getLHCH");
        }
    }

    public VariableInject GetInjectLHCH(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getLHCH(i);
            }
        };
    }

    public BoolExpr getLHCL(int i) {
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 4 * MAX_REGISTER + 5 * MAX_LOCALHEAP + 5 * i + 2, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getLHCL");
        }
    }

    public VariableInject GetInjectLHCL(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getLHCL(i);
            }
        };
    }

    public BoolExpr getLHCG(int i) {
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 4 * MAX_REGISTER + 5 * MAX_LOCALHEAP + 5 * i + 3, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getLHCG");
        }
    }

    public VariableInject GetInjectLHCG(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getLHCG(i);
            }
        };
    }

    public BoolExpr getLHCF(int i) {
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 4 * MAX_REGISTER + 5 * MAX_LOCALHEAP +  5 * i + 4, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getLHCF");
        }
    }

    public VariableInject GetInjectLHCF(final FSVariable var) {
        return new VariableInject() {
            @Override
            public BoolExpr get(int i) {
                return var.getLHCF(i);
            }
        };
    }

}
