package analysis;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
//import gen.Clause;
//import gen.Gen;

import debugging.QUERY_TYPE;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.iface.instruction.FiveRegisterInstruction;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.OffsetInstruction;
import org.jf.dexlib2.iface.instruction.OneRegisterInstruction;
import org.jf.dexlib2.iface.instruction.ReferenceInstruction;
import org.jf.dexlib2.iface.instruction.RegisterRangeInstruction;
import org.jf.dexlib2.iface.instruction.ThreeRegisterInstruction;
import org.jf.dexlib2.iface.instruction.TwoRegisterInstruction;
import org.jf.dexlib2.iface.instruction.WideLiteralInstruction;
import org.jf.dexlib2.iface.instruction.formats.Instruction31t;
import org.jf.dexlib2.iface.reference.FieldReference;
import org.jf.dexlib2.iface.reference.MethodReference;
import org.jf.dexlib2.iface.reference.Reference;

import payload.ArrayData;
import payload.PackedSwitch;
import payload.SparseSwitch;
import util.Utils;
import z3.*;

public class FSInstructionAnalysis{
    final private Analysis analysis;
    final private FSEngine fsengine;
    final private Instruction instruction;
    final private DalvikClass dc;
    final private DalvikMethod dm;
    private final int c;
    private final int m;
    final private int codeAddress;
    
    private String methodIndex;
    private String classIndex;
    
    private String methodName;
    private String className;
    
    private String referenceString;
    private int referenceIntIndex;
    
    private Boolean callReturns;
    
    private int numRegLoc;
    private int numParLoc;
    int instanceNum;
    int nextCode;
    
    private String referenceStringClass;
    private String referenceStringClassIndex;
    
    private String referenceIndex;
    private String returnType;
    private int returnTypeInt;
    
    private FSVariable fsvar;
    
    private int referenceClassIndex;
        
    private Map<Integer, BitVecExpr> regUpV ;
    private Map<Integer, BoolExpr> regUpH ;
    private Map<Integer, BoolExpr> regUpL ;
    private Map<Integer, BoolExpr> regUpG ;
    private Map<Integer, BitVecExpr> regUpLHV ;
    private Map<Integer, BoolExpr> regUpLHH ;
    private Map<Integer, BoolExpr> regUpLHL ;
    private Map<Integer, BoolExpr> regUpLHG ;
    private Map<Integer, BoolExpr> regUpLHF ;
    
    private Map<Integer, BitVecExpr> regUpLHCV ;
    private Map<Integer, BoolExpr> regUpLHCH ;
    private Map<Integer, BoolExpr> regUpLHCL ;
    private Map<Integer, BoolExpr> regUpLHCG ;
    private Map<Integer, BoolExpr> regUpLHCF ;
    
    private Set<DalvikImplementation> implementations;

    public FSInstructionAnalysis(final Analysis analysis, final Instruction instruction, final DalvikClass dc, final DalvikMethod dm, final int codeAddress){
        this.analysis = analysis;
        this.fsengine = analysis.getFSEngine();
        this.fsvar = fsengine.getVars();
        this.instruction = instruction;
        this.dc = dc;
        this.c = dc.getType().hashCode();
        this.dm = dm;
        this.m = dm.getName().hashCode();
        this.codeAddress = codeAddress;

    
        this.regUpV = new HashMap<>();
        this.regUpH = new HashMap<>();
        this.regUpL = new HashMap<>();
        this.regUpG = new HashMap<>();
        this.regUpLHV = new HashMap<>();
        this.regUpLHH = new HashMap<>();
        this.regUpLHL = new HashMap<>();
        this.regUpLHG = new HashMap<>();
        this.regUpLHF = new HashMap<>();
        
        this.regUpLHCV = new HashMap<>();
        this.regUpLHCH = new HashMap<>();
        this.regUpLHCL = new HashMap<>();
        this.regUpLHCG = new HashMap<>();
        this.regUpLHCF = new HashMap<>();
        

    }

    private void initializeLHC(){
        regUpLHCV.clear();
        regUpLHCH.clear();
        regUpLHCL.clear();
        regUpLHCG.clear();
        regUpLHCF.clear();
        
        for (int i = 0; i < analysis.getLocalHeapSize(); i++){
            regUpLHCV.put(i, fsvar.getLHCV(i));
            regUpLHCH.put(i, fsvar.getLHCH(i));
            regUpLHCL.put(i, fsvar.getLHCL(i));
            regUpLHCG.put(i, fsvar.getLHCG(i));
            regUpLHCF.put(i, fsvar.getLHCF(i));
        }
    }
    
    public void CreateHornClauses(){
        boolean superBool = false;
        Integer staticFieldClassName;
        Map<DalvikClass, DalvikMethod> staticDefinitions = new ConcurrentHashMap<DalvikClass, DalvikMethod>();
        DalvikMethod dmc;
        final int size = analysis.getSize();
        fsvar = fsengine.getVars();
        BoolExpr negationString = null;
        int jump = 0;
        int referenceReg;
        boolean isDefined;
        callReturns = false;
        int numRegCall;
        int numArgCall;
        referenceStringClass = null;
        referenceStringClassIndex = null;
        returnType = null;
        returnTypeInt = 0;
        referenceClassIndex = -1;
        referenceIntIndex = -1;
        Opcode opcode = instruction.getOpcode();
        referenceString = null;
        referenceIndex = null;
        nextCode = codeAddress + instruction.getCodeUnits();


        if (instruction instanceof ReferenceInstruction) {
            ReferenceInstruction referenceInstruction = (ReferenceInstruction)instruction;
            Reference reference = referenceInstruction.getReference();
            referenceString = Utils.getShortReferenceString(reference);
            if (reference instanceof FieldReference) {
                referenceStringClass = ((FieldReference) reference).getDefiningClass();
                referenceClassIndex = referenceStringClass.hashCode();
                referenceStringClassIndex = Utils.Dec(referenceClassIndex);
            }
            else
                if (reference instanceof MethodReference){
                    referenceStringClass = ((MethodReference) reference).getDefiningClass();
                    referenceClassIndex = referenceStringClass.hashCode();
                    referenceStringClassIndex = Utils.Dec(referenceClassIndex);
                    returnType = ((MethodReference) reference).getReturnType();
                    returnTypeInt = returnType.hashCode();
                    if (returnType.equals((String) "V")) callReturns = false;
                    else callReturns = true;
                }
            referenceIntIndex = referenceString.hashCode();
            referenceIndex = Utils.Dec(referenceIntIndex);
        }
        methodName = dm.getName();
        className = dc.getType();
        int mi = m;
        methodIndex = Utils.Dec(mi);
        int ci = c;
        classIndex = Utils.Dec(ci);
        numRegLoc = dm.getNumReg();
        numParLoc = dm.getNumArg();
        BoolExpr returnLabel;

        

        boolean debug = true;
        if (debug){
           BoolExpr h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
           for (int i = 0; i < this.numRegLoc; i++){
               BoolExpr h1 = fsengine.and(fsvar.getH(i),h);
               BoolExpr h2 = fsengine.and(fsvar.getL(i),h);
               BoolExpr h3 = fsengine.and(fsvar.getG(i),h);
               Z3Query q1 = new Z3Query(h1,i,QUERY_TYPE.HIGH,className,methodName,Integer.toString(codeAddress));
               Z3Query q2 = new Z3Query(h2,i,QUERY_TYPE.LOCAL,className,methodName,Integer.toString(codeAddress));
               Z3Query q3 = new Z3Query(h3,i,QUERY_TYPE.GLOBAL,className,methodName,Integer.toString(codeAddress));
               fsengine.addQueryDebug(q1);
               fsengine.addQueryDebug(q2);
               fsengine.addQueryDebug(q3);
               }
            for (int i = 0; i < analysis.getLocalHeapNumberEntries(); i++){
                int instanceNumber = analysis.getInstanceNumFromReverse(i);
                int lhoffset = fsengine.getOffset(instanceNumber);
                int lhsize = fsengine.getSize(instanceNumber);
                String ac = analysis.getAllocationPointClassDebug(instanceNumber);
                String am = analysis.getAllocationPointMethod(instanceNumber);
                int apc = analysis.getAllocationPointPC(instanceNumber);
                
                for (int j = 0; j <= lhsize; j++){
                    BoolExpr h1 = fsengine.and(fsvar.getLHH(lhoffset + j),h);
                    BoolExpr h2 = fsengine.and(fsvar.getLHL(lhoffset + j),h);
                    BoolExpr h3 = fsengine.and(fsvar.getLHG(lhoffset + j),h);
                    Z3Query q1 = new Z3Query(h1,ac,am,apc,j,instanceNumber,QUERY_TYPE.HIGH,className,methodName,Integer.toString(codeAddress));
                    Z3Query q2 = new Z3Query(h2,ac,am,apc,j,instanceNumber,QUERY_TYPE.LOCAL,className,methodName,Integer.toString(codeAddress));
                    Z3Query q3 = new Z3Query(h3,ac,am,apc,j,instanceNumber,QUERY_TYPE.GLOBAL,className,methodName,Integer.toString(codeAddress));
                    fsengine.addQueryDebug(q1);
                    fsengine.addQueryDebug(q2);
                    fsengine.addQueryDebug(q3);
                }
            }
        }

        
        BoolExpr h, b, htob;
        switch (opcode){
        case NOP:
        case MONITOR_ENTER://((short)0x1d, "monitor-enter", ReferenceType.NONE, Format.Format11x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case MONITOR_EXIT://((short)0x1e, "monitor-exit", ReferenceType.NONE, Format.Format11x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
            break;//((short)0x00, "nop", ReferenceType.NONE, Format.Format10x, Opcode.CAN_CONTINUE),


        case MOVE://((short)0x01, "move", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MOVE_FROM16://((short)0x02, "move/from16", ReferenceType.NONE, Format.Format22x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MOVE_16://((short)0x03, "move/16", ReferenceType.NONE, Format.Format32x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MOVE_WIDE://((short)0x04, "move-wide", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case MOVE_WIDE_FROM16://((short)0x05, "move-wide/from16", ReferenceType.NONE, Format.Format22x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case MOVE_WIDE_16://((short)0x06, "move-wide/16", ReferenceType.NONE, Format.Format32x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case MOVE_OBJECT://((short)0x07, "move-object", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MOVE_OBJECT_FROM16://((short)0x08, "move-object/from16", ReferenceType.NONE, Format.Format22x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MOVE_OBJECT_16:
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getV(((TwoRegisterInstruction) instruction).getRegisterB()));
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getH(((TwoRegisterInstruction) instruction).getRegisterB()));
            regUpL.put(((OneRegisterInstruction) instruction).getRegisterA(), fsvar.getL(((TwoRegisterInstruction) instruction).getRegisterB()));
            regUpG.put(((OneRegisterInstruction) instruction).getRegisterA(), fsvar.getG(((TwoRegisterInstruction) instruction).getRegisterB()));
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
          
            break;//((short)0x09, "move-object/16", ReferenceType.NONE, Format.Format32x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case MOVE_RESULT://((short)0x0a, "move-result", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MOVE_RESULT_WIDE://((short)0x0b, "move-result-wide", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case MOVE_RESULT_OBJECT:
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getV(numRegLoc));
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getH(numRegLoc));
            regUpL.put(((OneRegisterInstruction) instruction).getRegisterA(), fsvar.getL(numRegLoc));
            regUpG.put(((OneRegisterInstruction) instruction).getRegisterA(), fsvar.getG(numRegLoc));
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
           
           
            break;//((short)0x0c, "move-result-object", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case MOVE_EXCEPTION:
            int previousCode = 0;
            for (final Instruction ins: dm.getInstructions()){
                if ((previousCode + ins.getCodeUnits()) == codeAddress){
                    h = fsengine.rPred(classIndex, methodIndex, previousCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                    b = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                    fsengine.addRule(fsengine.implies(h, b), null);
                }
                previousCode += ins.getCodeUnits();
            }
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);

            //System.out.println("Unsupported Intsruction! MOVE_EXCEPTION");
            break;//((short)0x0d, "move-exception", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case RETURN_VOID:
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
         
            int count1 = 0;
            for (int i = numRegLoc + 1; i <= numRegLoc + numParLoc; i++){
                regUpV.put(count1, fsvar.getV(i));
                regUpH.put(count1, fsvar.getH(i));
                regUpL.put(count1, fsvar.getL(i));
                regUpG.put(count1, fsvar.getG(i));
                count1++;
            }
            b = fsengine.resPred(classIndex, methodIndex,regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF,numParLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
            break;
            //((short)0x0e, "return-void", ReferenceType.NONE, Format.Format10x),


        case RETURN://((short)0x0f, "return", ReferenceType.NONE, Format.Format11x),
        case RETURN_WIDE://((short)0x10, "return-wide", ReferenceType.NONE, Format.Format11x),
        case RETURN_OBJECT:
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            regUpV.put(numParLoc, fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()));
            regUpH.put(numParLoc, fsvar.getH(((OneRegisterInstruction) instruction).getRegisterA()));
            regUpL.put(numParLoc, fsvar.getL(((OneRegisterInstruction) instruction).getRegisterA()));
            regUpG.put(numParLoc, fsvar.getG(((OneRegisterInstruction) instruction).getRegisterA()));
            int count = 0;
            for (int i = numRegLoc + 1; i <= numRegLoc + numParLoc; i++){
                regUpV.put(count, fsvar.getV(i));
                regUpH.put(count, fsvar.getH(i));
                regUpL.put(count, fsvar.getL(i));
                regUpG.put(count, fsvar.getG(i));
                count++;
            }
            b = fsengine.resPred(classIndex, methodIndex,regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF,numParLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
            break;//((short)0x11, "return-object", ReferenceType.NONE, Format.Format11x),


        case CONST_4://((short)0x12, "const/4", ReferenceType.NONE, Format.Format11n, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CONST_16://((short)0x13, "const/16", ReferenceType.NONE, Format.Format21s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CONST://((short)0x14, "const", ReferenceType.NONE, Format.Format31i, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CONST_HIGH16://((short)0x15, "const/high16", ReferenceType.NONE, Format.Format21ih, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CONST_WIDE_16://((short)0x16, "const-wide/16", ReferenceType.NONE, Format.Format21s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case CONST_WIDE_32://((short)0x17, "const-wide/32", ReferenceType.NONE, Format.Format31i, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case CONST_WIDE://((short)0x18, "const-wide", ReferenceType.NONE, Format.Format51l, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case CONST_WIDE_HIGH16:
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size));
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
            break;//((short)0x19, "const-wide/high16", ReferenceType.NONE, Format.Format21lh, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


        case CONST_STRING://((short)0x1a, "const-string", ReferenceType.STRING, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER, (short)0x1b),
        case CONST_STRING_JUMBO:
        case CONST_CLASS://((short)0x1c, "const-class", ReferenceType.TYPE, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkBitVector(referenceIntIndex, size));
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
            break;//((short)0x1b, "const-string/jumbo", ReferenceType.STRING, Format.Format31c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case CHECK_CAST:
            h = fsengine.and(
                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                    fsengine.eq(
                            fsvar.getG(((OneRegisterInstruction)instruction).getRegisterA()),
                            fsengine.mkTrue()
                            ),
                    fsengine.bvugt(
                            fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                            fsengine.mkBitVector(0, size)
                            )
                    );
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
            
            h = fsengine.and(
                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                    fsengine.eq(
                            fsvar.getL(((OneRegisterInstruction)instruction).getRegisterA()),
                            fsengine.mkTrue()
                            ),
                    fsengine.bvugt(
                            fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                            fsengine.mkBitVector(0, size)
                            )
                    );
            fsengine.addRule(fsengine.implies(h, b), null);
            break;//((short)0x1f, "check-cast", ReferenceType.TYPE, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case INSTANCE_OF:
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkBitVector(0, size));
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);

            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();

            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkBitVector(1, size));
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);            
            break;//((short)0x20, "instance-of", ReferenceType.TYPE, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case ARRAY_LENGTH:
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getF());
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getLf());
            regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            htob = fsengine.implies(h, b);
            fsengine.addRule(htob, null);
            break;//((short)0x21, "array-length", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case NEW_INSTANCE:
           
            if (referenceIntIndex == "Landroid/content/Intent;".hashCode()){
                h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                fsengine.addRule(fsengine.implies(h, b), null);
                break;
            }
            instanceNum = analysis.getInstNum(ci, mi, codeAddress);            
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            //lift all occurrence of instanceNum
            
            for (int i = 0; i <= numRegLoc  ; i++){
                regUpG.put(i,fsengine.or(fsvar.getG(i),fsengine.and(fsvar.getL(i),fsengine.eq(fsvar.getV(i), fsengine.mkBitVector(instanceNum, size)))));
                regUpL.put(i,fsengine.and(fsvar.getL(i),fsengine.neq(fsvar.getV(i), fsengine.mkBitVector(instanceNum, size))));
            }
            
            //update the register receiving the pointer to the newly created object
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkBitVector(instanceNum, size));
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkTrue());
            regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            
            //Initialize the object on the local heap
            int lhoffset = fsengine.getOffset(instanceNum);
            int lhsize = fsengine.getSize(instanceNum);
            for (int i = lhoffset; i < lhoffset + lhsize + 1; i++){
                regUpLHV.put(i, fsengine.mkBitVector(0, size));
                regUpLHH.put(i, fsengine.mkFalse());
                regUpLHL.put(i, fsengine.mkFalse());
                regUpLHG.put(i, fsengine.mkFalse());
                regUpLHF.put(i, fsengine.mkTrue());
            }

            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);

            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();
            regUpLHV.clear(); regUpLHH.clear(); regUpLHL.clear(); regUpLHG.clear(); regUpLHF.clear();
            
            //Lift old local heap object to the global heap
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            this.liftObject(h, instanceNum);

            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();
            regUpLHV.clear(); regUpLHH.clear(); regUpLHL.clear(); regUpLHG.clear(); regUpLHF.clear();
            
            //Lift the whole local heap if the old local heap object which was lifted contained a local heap pointer
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            //lift the registers to global heap pointers
            for (int i = 0; i <= numRegLoc  ; i++){
                regUpG.put(i,fsengine.or(fsvar.getG(i),fsvar.getL(i)));
                regUpL.put(i,fsengine.mkFalse());
            }
            //update the register receiving the pointer to the newly created object
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkBitVector(instanceNum, size));
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkTrue());
            regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());            
            //Reset the local heap
            for (int i = 0; i < analysis.getLocalHeapSize();i++) {
                regUpLHV.put(i,fsengine.mkBitVector(0, size));
                regUpLHH.put(i,fsengine.mkFalse());
                regUpLHL.put(i,fsengine.mkFalse());
                regUpLHG.put(i,fsengine.mkFalse());
                regUpLHF.put(i,fsengine.mkTrue());
            }
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            for (int i = lhoffset; i < lhoffset + lhsize + 1; i++){
                fsengine.addRule(fsengine.implies(fsengine.and(h,fsvar.getLHL(i)),b),null);
            }
                        
            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();
            regUpLHV.clear(); regUpLHH.clear(); regUpLHL.clear(); regUpLHG.clear(); regUpLHF.clear();
            
            //Lift the whole local heap if the old local heap object which was lifted contained a local heap pointer
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            for (int allocationPoint : analysis.getAllocationPoints()){
                for (int i = lhoffset; i < lhoffset + lhsize + 1; i++){
                    BoolExpr hh = fsengine.and(fsvar.getLHL(i),h);
                    this.liftObject(hh, allocationPoint);
                }
            }
            
            
            if (analysis.hasStaticConstructor(referenceIntIndex)){
                //h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                int staticConstNum = "<clinit>()V".hashCode();
                dmc = analysis.getExactMethod(referenceIntIndex, staticConstNum);

                for (int i = 0; i < dmc.getNumArg() + dmc.getNumReg() + 1; i++){
                    regUpV.put(i, fsengine.mkBitVector(0, size));
                    regUpLHH.put(i, fsengine.mkFalse());
                    regUpL.put(i, fsengine.mkFalse());
                    regUpG.put(i, fsengine.mkFalse());
                }
                
                for (int i = 0; i < analysis.getLocalHeapSize(); i++){                    
                    regUpLHV.put(i, fsengine.mkBitVector(0, size));
                    regUpLHH.put(i, fsengine.mkFalse());
                    regUpLHL.put(i, fsengine.mkFalse());
                    regUpLHG.put(i, fsengine.mkFalse());
                    regUpLHF.put(i, fsengine.mkFalse());
                }
                
                b = fsengine.rPred(Integer.toString(referenceIntIndex), Integer.toString(staticConstNum), 0, regUpV, regUpH, regUpL, regUpG,regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF,
                        dmc.getNumArg(), dmc.getNumReg());
                fsengine.addRule(b, null);
            }
            break;//((short)0x22, "new-instance", ReferenceType.TYPE, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case NEW_ARRAY:
            instanceNum = analysis.getInstNum(ci, mi, codeAddress);
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkBitVector(instanceNum, size));
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkTrue());
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);

            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();

            if (analysis.optionArrays()){
                h = fsengine.and(
                        fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                        fsengine.bvuge(
                                fsengine.mkBitVector(0, size),
                                fsvar.getF()
                                ),
                        fsengine.bvult(
                                fsvar.getF(),
                                fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                                )
                        );
                b = fsengine.hPred(
                        fsengine.mkBitVector(referenceIntIndex, size),
                        fsengine.mkBitVector(instanceNum, size),
                        fsvar.getF(), fsengine.mkBitVector(0, size),
                        fsengine.mkFalse(), fsengine.mkFalse()
                        );
            } else {
                h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                b = fsengine.hPred(
                        fsengine.mkBitVector(referenceIntIndex, size),
                        fsengine.mkBitVector(instanceNum, size),
                        fsengine.mkBitVector(0, size),//dummy field entry
                        fsengine.mkBitVector(0, size),
                        fsengine.mkFalse(), fsengine.mkFalse()
                        );
            }
            fsengine.addRule(fsengine.implies(h, b), null);
            break;//((short)0x23, "new-array", ReferenceType.TYPE, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case FILLED_NEW_ARRAY:
            FiveRegisterInstruction instructionA = (FiveRegisterInstruction)this.instruction;
            final int regCount = instructionA.getRegisterCount();
            instanceNum = analysis.getInstNum(ci, mi, codeAddress);
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            FSSingleRegUpdate u = new FSSingleRegUpdate(numRegLoc,
                    fsengine.mkBitVector(instanceNum, size),
                    fsengine.mkFalse(),
                    fsengine.mkFalse(),
                    fsengine.mkTrue());
            u.apply(regUpV, regUpH, regUpL, regUpG);

            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            htob = fsengine.implies(h, b);
            fsengine.addRule(htob, null);
            
            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();

            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            BoolExpr hh = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            if (analysis.optionArrays()){
                switch(regCount){
                case 5:
                    b = fsengine.hPred(fsengine.mkBitVector(referenceIntIndex, size),
                            fsengine.mkBitVector(instanceNum, size),
                            fsengine.mkBitVector(4, size),
                            fsvar.getV(instructionA.getRegisterG()),
                            fsvar.getH(instructionA.getRegisterG()),
                            fsengine.or(fsvar.getL(instructionA.getRegisterG()),fsvar.getG(instructionA.getRegisterG())));
                    htob = fsengine.implies(h, b);
                    fsengine.addRule(htob, null);
                    //if the register contains a local heap pointer, lift
                    hh = fsengine.and(h,fsvar.getL(instructionA.getRegisterG()));
                    this.liftIfLocal(hh,u);// classIndex, methodIndex, nextCode, numParLoc, numRegLoc, analysis, instanceNum, regUpV, regUpH, regUpLHL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF);
                case 4:
                    b = fsengine.hPred( fsengine.mkBitVector(referenceIntIndex, size),
                            fsengine.mkBitVector(instanceNum, size),
                            fsengine.mkBitVector(3, size),
                            fsvar.getV(instructionA.getRegisterF()),
                            fsvar.getH(instructionA.getRegisterF()),
                            fsengine.or(fsvar.getL(instructionA.getRegisterF()),fsvar.getG(instructionA.getRegisterF())));
                    htob = fsengine.implies(h, b);
                    fsengine.addRule(htob, null);
                    //if the register contains a local heap pointer, lift
                    hh = fsengine.and(h,fsvar.getL(instructionA.getRegisterF()));
                    this.liftIfLocal(hh,u);// classIndex, methodIndex, nextCode, numParLoc, numRegLoc, analysis, instanceNum, regUpV, regUpH, regUpLHL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF);
                case 3:
                    b = fsengine.hPred( fsengine.mkBitVector(referenceIntIndex, size),
                            fsengine.mkBitVector(instanceNum, size),
                            fsengine.mkBitVector(2, size),
                            fsvar.getV(instructionA.getRegisterE()),
                            fsvar.getH(instructionA.getRegisterE()),
                            fsengine.or(fsvar.getL(instructionA.getRegisterE()),fsvar.getG(instructionA.getRegisterE())));
                    htob = fsengine.implies(h, b);
                    fsengine.addRule(htob, null);
                    //if the register contains a local heap pointer, lift
                    hh = fsengine.and(h,fsvar.getL(instructionA.getRegisterE()));
                    this.liftIfLocal(hh,u);// classIndex, methodIndex, nextCode, numParLoc, numRegLoc, analysis, instanceNum, regUpV, regUpH, regUpLHL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF);
                case 2:
                    b = fsengine.hPred( fsengine.mkBitVector(referenceIntIndex, size),
                            fsengine.mkBitVector(instanceNum, size),
                            fsengine.mkBitVector(1, size),
                            fsvar.getV(instructionA.getRegisterD()),
                            fsvar.getH(instructionA.getRegisterD()),
                            fsengine.or(fsvar.getL(instructionA.getRegisterD()),fsvar.getG(instructionA.getRegisterD())));
                    htob = fsengine.implies(h, b);
                    fsengine.addRule(htob, null);
                    //if the register contains a local heap pointer, lift
                    hh = fsengine.and(h,fsvar.getL(instructionA.getRegisterD()));
                    this.liftIfLocal(hh,u);// classIndex, methodIndex, nextCode, numParLoc, numRegLoc, analysis, instanceNum, regUpV, regUpH, regUpLHL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF);
                case 1:
                    b = fsengine.hPred( fsengine.mkBitVector(referenceIntIndex, size),
                            fsengine.mkBitVector(instanceNum, size),
                            fsengine.mkBitVector(0, size),
                            fsvar.getV(instructionA.getRegisterC()),
                            fsvar.getH(instructionA.getRegisterC()),
                            fsengine.or(fsvar.getL(instructionA.getRegisterC()),fsvar.getG(instructionA.getRegisterC())));
                    htob = fsengine.implies(h, b);
                    fsengine.addRule(htob, null);
                    //if the register contains a local heap pointer, lift
                    hh = fsengine.and(h,fsvar.getL(instructionA.getRegisterC()));
                    this.liftIfLocal(hh,u);//, classIndex, methodIndex, nextCode, numParLoc, numRegLoc, analysis, instanceNum, regUpV, regUpH, regUpLHL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF);
                }
            } else {
                switch(regCount){
                case 5:
                    b = fsengine.hPred( fsengine.mkBitVector(referenceIntIndex, size),
                            fsengine.mkBitVector(instanceNum, size),
                            fsengine.mkBitVector(0, size),
                            fsvar.getV(instructionA.getRegisterG()),
                            fsvar.getH(instructionA.getRegisterG()),
                            fsengine.or(fsvar.getL(instructionA.getRegisterG()),fsvar.getG(instructionA.getRegisterG())));
                    htob = fsengine.implies(h, b);
                    fsengine.addRule(htob, null);
                    //if the register contains a local heap pointer, lift
                    hh = fsengine.and(h,fsvar.getL(instructionA.getRegisterG()));
                    this.liftIfLocal(hh,u);// classIndex, methodIndex, nextCode, numParLoc, numRegLoc, analysis, instanceNum, regUpV, regUpH, regUpLHL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF);
                case 4:
                    b = fsengine.hPred( fsengine.mkBitVector(referenceIntIndex, size),
                            fsengine.mkBitVector(instanceNum, size),
                            fsengine.mkBitVector(0, size),
                            fsvar.getV(instructionA.getRegisterF()),
                            fsvar.getH(instructionA.getRegisterF()),
                            fsengine.or(fsvar.getL(instructionA.getRegisterF()),fsvar.getG(instructionA.getRegisterF())));
                    htob = fsengine.implies(h, b);
                    fsengine.addRule(htob, null);
                    //if the register contains a local heap pointer, lift
                    hh = fsengine.and(h,fsvar.getL(instructionA.getRegisterF()));
                    this.liftIfLocal(hh,u);// classIndex, methodIndex, nextCode, numParLoc, numRegLoc, analysis, instanceNum, regUpV, regUpH, regUpLHL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF);
                case 3:
                    b = fsengine.hPred( fsengine.mkBitVector(referenceIntIndex, size),
                            fsengine.mkBitVector(instanceNum, size),
                            fsengine.mkBitVector(0, size),
                            fsvar.getV(instructionA.getRegisterE()),
                            fsvar.getH(instructionA.getRegisterE()),
                            fsengine.or(fsvar.getL(instructionA.getRegisterE()),fsvar.getG(instructionA.getRegisterE())));
                    htob = fsengine.implies(h, b);
                    fsengine.addRule(htob, null);
                    //if the register contains a local heap pointer, lift
                    hh = fsengine.and(h,fsvar.getL(instructionA.getRegisterE()));
                    this.liftIfLocal(hh,u);// classIndex, methodIndex, nextCode, numParLoc, numRegLoc, analysis, instanceNum, regUpV, regUpH, regUpLHL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF);
                case 2:
                    b = fsengine.hPred( fsengine.mkBitVector(referenceIntIndex, size),
                            fsengine.mkBitVector(instanceNum, size),
                            fsengine.mkBitVector(0, size),
                            fsvar.getV(instructionA.getRegisterD()),
                            fsvar.getH(instructionA.getRegisterD()),
                            fsengine.or(fsvar.getL(instructionA.getRegisterD()),fsvar.getG(instructionA.getRegisterD())));
                    htob = fsengine.implies(h, b);
                    fsengine.addRule(htob, null);
                    //if the register contains a local heap pointer, lift
                    hh = fsengine.and(h,fsvar.getL(instructionA.getRegisterD()));
                    this.liftIfLocal(hh,u);// classIndex, methodIndex, nextCode, numParLoc, numRegLoc, analysis, instanceNum, regUpV, regUpH, regUpLHL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF);
                case 1:
                    b = fsengine.hPred( fsengine.mkBitVector(referenceIntIndex, size),
                            fsengine.mkBitVector(instanceNum, size),
                            fsengine.mkBitVector(0, size),
                            fsvar.getV(instructionA.getRegisterC()),
                            fsvar.getH(instructionA.getRegisterC()),
                            fsengine.or(fsvar.getL(instructionA.getRegisterC()),fsvar.getG(instructionA.getRegisterC())));
                    htob = fsengine.implies(h, b);
                    fsengine.addRule(htob, null);
                    //if the register contains a local heap pointer, lift
                    hh = fsengine.and(h,fsvar.getL(instructionA.getRegisterC()));
                    this.liftIfLocal(hh,u);// classIndex, methodIndex, nextCode, numParLoc, numRegLoc, analysis, instanceNum, regUpV, regUpH, regUpLHL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF);
                }
            }
            break;//((short)0x24, "filled-new-array", ReferenceType.TYPE, Format.Format35c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),


        case FILLED_NEW_ARRAY_RANGE:
            instanceNum = analysis.getInstNum(ci, mi, codeAddress);
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            u = new FSSingleRegUpdate(numRegLoc,
                    fsengine.mkBitVector(instanceNum, size),
                    fsengine.mkFalse(),
                    fsengine.mkFalse(),
                    fsengine.mkTrue());
            u.apply(regUpV, regUpH, regUpL, regUpG);

            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            htob = fsengine.implies(h, b);
            fsengine.addRule(htob, null);
            
            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();

            RegisterRangeInstruction instructionAr = (RegisterRangeInstruction)this.instruction;
            int regCountr = instructionAr.getRegisterCount();
            int startRegister = instructionAr.getStartRegister();
            int endRegister   =   startRegister+regCountr-1;
            int cr = 0;

            for (int reg = startRegister; reg <= endRegister; reg++){
                h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                b = fsengine.hPred( fsengine.mkBitVector(referenceIntIndex, size),
                        fsengine.mkBitVector(instanceNum, size),
                        fsengine.mkBitVector(cr, size),
                        fsvar.getV(reg), fsvar.getH(reg), fsengine.or(fsvar.getL(reg),fsvar.getG(reg)));
                fsengine.addRule(fsengine.implies(h, b), null);
                //if the register contains a local heap pointer, lift
                hh = fsengine.and(h,fsvar.getL(reg));
                this.liftIfLocal(hh,u);// classIndex, methodIndex, nextCode, numParLoc, numRegLoc, analysis, instanceNum, regUpV, regUpH, regUpLHL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF);
                if (analysis.optionArrays()) cr++;
            }
            break;//((short)0x25, "filled-new-array/range", ReferenceType.TYPE, Format.Format3rc, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),


        case FILL_ARRAY_DATA:
            for (final ArrayData ad: analysis.getArrayData()){
                List<Number> elements = ad.getElements(c, m, codeAddress + ((Instruction31t)instruction).getCodeOffset());
                if (elements != null){
                    int elNum = 0;
                    BoolExpr mainh = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                    BoolExpr mainb = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                    fsengine.addRule(fsengine.implies(mainh, mainb), null);
                    for (final Number element: elements){
                        if (analysis.optionArrays()){
                            h = fsengine.and(
                                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                                    fsengine.hPred(fsvar.getCn(), fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                            fsengine.mkBitVector(0, size), fsengine.mkBitVector(0, size),
                                            fsvar.getLf(), fsvar.getBf())
                                    );
                            b = fsengine.hPred(fsvar.getCn(), fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                    fsengine.mkBitVector(elNum, size),
                                    fsengine.mkBitVector(element.intValue(), size),
                                    fsengine.mkFalse(),
                                    fsengine.mkFalse());
                            fsengine.addRule(fsengine.implies(h, b), null);
                        } else {
                            h = fsengine.and(
                                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                                    fsengine.hPred(fsvar.getCn(), fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                            fsengine.mkBitVector(0, size), fsengine.mkBitVector(0, size), fsvar.getLf(), fsvar.getBf())
                                    );
                            b = fsengine.hPred(fsvar.getCn(), fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                    fsengine.mkBitVector(0, size),
                                    fsengine.mkBitVector(element.intValue(), size),
                                    fsengine.mkFalse(),
                                    fsengine.mkFalse());
                            fsengine.addRule(fsengine.implies(h, b), null);
                        }
                        elNum++;
                    }
                    break;
                }
            }
            break;//((short)0x26, "fill-array-data", ReferenceType.NONE, Format.Format31t, Opcode.CAN_CONTINUE),


        case THROW:
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
            break;//((short)0x27, "throw", ReferenceType.NONE, Format.Format11x, Opcode.CAN_THROW),


        case GOTO://((short)0x28, "goto", ReferenceType.NONE, Format.Format10t),
        case GOTO_16://((short)0x29, "goto/16", ReferenceType.NONE, Format.Format20t),
        case GOTO_32:
            jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            b = fsengine.rPred(classIndex, methodIndex, jump, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
            break;//((short)0x2a, "goto/32", ReferenceType.NONE, Format.Format30t),


        case PACKED_SWITCH:
            negationString = fsengine.mkFalse();
            for (final PackedSwitch ps: analysis.getPackedSwitch()){
                List<Number> targets = ps.getTargets(c, m, codeAddress + ((Instruction31t)instruction).getCodeOffset());
                if (targets != null){
                    negationString = fsengine.mkTrue();
                    int t = 0;
                    final int payloadAddress = codeAddress + ((Instruction31t)instruction).getCodeOffset();
                    for (final Number target: targets){
                        try {
                            h = fsengine.and(
                                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                                    fsengine.eq(
                                            fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                            fsengine.mkBitVector(ps.getFirstKey(c, m, payloadAddress) + t, size)
                                            )
                                    );
                            b = fsengine.rPred(classIndex, methodIndex, target.intValue(), regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                            fsengine.addRule(fsengine.implies(h, b), null);
                        } catch (Exception e) {
                            e.printStackTrace();
                        }

                        try {
                            negationString = fsengine.and(
                                    negationString,
                                    fsengine.eq(
                                            fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                            fsengine.mkBitVector(ps.getFirstKey(c, m, payloadAddress) + t, size)
                                            )
                                    );
                        } catch (Exception e) {
                            e.printStackTrace();
                        }
                        t++;
                    }
                    break;
                }
            }
            h = fsengine.and(
                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                    fsengine.not(negationString)
                    );
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
            //System.out.println("Unsupported Intsruction! PACKED_SWITCH");
            break;//((short)0x2b, "packed-switch", ReferenceType.NONE, Format.Format31t, Opcode.CAN_CONTINUE),


        case SPARSE_SWITCH:
            negationString = fsengine.mkFalse();
            for (final SparseSwitch ss: analysis.getSparseSwitch()){
                Map<Integer, Integer> targets = ss.getTargets(c, m, codeAddress + ((Instruction31t)instruction).getCodeOffset());
                if (targets != null){
                    negationString = fsengine.mkTrue();
                    for (final Map.Entry<Integer, Integer> target: targets.entrySet()){
                        h = fsengine.and(
                                fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                                fsengine.eq(
                                        fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                        fsengine.mkBitVector(target.getKey(), size)
                                        )
                                );
                        b = fsengine.rPred(classIndex, methodIndex, target.getValue(), regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                        fsengine.addRule(fsengine.implies(h, b), null);

                        negationString = fsengine.and(
                                negationString,
                                fsengine.eq(
                                        fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                        fsengine.mkBitVector(target.getKey(), size)
                                        )
                                );
                    }
                    break;
                }
            }
            h = fsengine.and(
                    h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                    fsengine.not(negationString)
                    );
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
            break;//((short)0x2c, "sparse-switch", ReferenceType.NONE, Format.Format31t, Opcode.CAN_CONTINUE),


        case CMPL_FLOAT://((short)0x2d, "cmpl-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CMPG_FLOAT://((short)0x2e, "cmpg-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CMPL_DOUBLE://((short)0x2f, "cmpl-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CMPG_DOUBLE://((short)0x30, "cmpg-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CMP_LONG:
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(),
                    (BitVecExpr) fsengine.ite(
                            fsengine.eq(        //if
                                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                    fsvar.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                                    ),
                            fsengine.mkBitVector(0, size), //then
                            fsengine.ite( //else
                                    fsengine.bvugt(//sub-if
                                            fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                            fsvar.getV(((ThreeRegisterInstruction) instruction).getRegisterC())
                                            ),
                                    fsengine.mkBitVector(1, size), //sub-then
                                    fsengine.mkBitVector(-1, size) //sub-else
                                    )
                            )
                    );
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(),
                    fsengine.or(fsvar.getH(((TwoRegisterInstruction)instruction).getRegisterB()),
                            fsvar.getH(((ThreeRegisterInstruction) instruction).getRegisterC())));
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);

            break;//((short)0x31, "cmp-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case IF_EQ:
            BoolExpr boolexpr = fsengine.eq(
                    fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x32, "if-eq", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


        case IF_NE:
            boolexpr = fsengine.not(fsengine.eq(
                    fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                    ));
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x32, "if-eq", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),
            
        case IF_LT:
            boolexpr = fsengine.bvult(
                    fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x34, "if-lt", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


        case IF_GE:
            boolexpr = fsengine.bvuge(
                    fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x35, "if-ge", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


        case IF_GT:
            boolexpr = fsengine.bvugt(
                    fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                    );
            this.cmpInstruction(boolexpr, analysis);
             break;//((short)0x36, "if-gt", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


        case IF_LE:
            boolexpr = fsengine.bvule(
                    fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x37, "if-le", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


        case IF_EQZ:
            boolexpr = fsengine.eq(
                    fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    fsengine.mkBitVector(0, size)
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x38, "if-eqz", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


        case IF_NEZ:
            boolexpr = fsengine.not(fsengine.eq(
                    fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    fsengine.mkBitVector(0, size)
                    ));
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x39, "if-nez", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


        case IF_LTZ:
            boolexpr = fsengine.bvult(
                    fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    fsengine.mkBitVector(0, size)
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x3a, "if-ltz", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


        case IF_GEZ:
            boolexpr = fsengine.bvuge(
                    fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    fsengine.mkBitVector(0, size)
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x3b, "if-gez", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


        case IF_GTZ:
            boolexpr = fsengine.bvugt(
                    fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    fsengine.mkBitVector(0, size)
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x3c, "if-gtz", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


        case IF_LEZ:
            boolexpr = fsengine.bvule(
                    fsvar.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    fsengine.mkBitVector(0, size)
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x3d, "if-lez", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


        case AGET://((short)0x44, "aget", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case AGET_WIDE://((short)0x45, "aget-wide", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case AGET_OBJECT://((short)0x46, "aget-object", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case AGET_BOOLEAN://((short)0x47, "aget-boolean", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case AGET_BYTE://((short)0x48, "aget-byte", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case AGET_CHAR://((short)0x49, "aget-char", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case AGET_SHORT:
            if (analysis.optionArrays()){
                h = fsengine.and(
                        fsengine.hPred(fsvar.getCn(), fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                fsvar.getV(((ThreeRegisterInstruction) instruction).getRegisterC()),
                                fsvar.getVal(), fsvar.getLval(), fsvar.getBval()),
                        fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc)
                        );

                regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getVal());
                regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getLval());
                regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
                regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getBval());
                b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            } else {
                h = fsengine.and(
                        fsengine.hPred(fsvar.getCn(), fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                fsengine.mkBitVector(0, size),
                                fsvar.getVal(), fsvar.getLval(), fsvar.getBval()),
                        fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc)
                        );
                regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getVal());
                regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getLval());
                regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
                regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getBval());
                b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            }
            fsengine.addRule(fsengine.implies(h, b), null);
            break;//((short)0x4a, "aget-short", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case APUT://((short)0x4b, "aput", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case APUT_WIDE://((short)0x4c, "aput-wide", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case APUT_OBJECT://((short)0x4d, "aput-object", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case APUT_BOOLEAN://((short)0x4e, "aput-boolean", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case APUT_BYTE://((short)0x4f, "aput-byte", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case APUT_CHAR://((short)0x50, "aput-char", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case APUT_SHORT:
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            /*
            regUpH.put(((TwoRegisterInstruction)instruction).getRegisterB(),
                    fsengine.or(
                            fsvar.getH(((TwoRegisterInstruction)instruction).getRegisterB()),
                            fsvar.getH(((OneRegisterInstruction)instruction).getRegisterA())
                            )
                    );
             */
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);

            regUpH.clear();

            h = fsengine.and(
                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                    fsengine.hPred( fsvar.getCn(), fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                            fsengine.mkBitVector(0, size),
                            fsengine.mkBitVector(0, size),
                            fsvar.getLf(), fsvar.getBf())
                    );
            b = fsengine.hPred( fsvar.getCn(), fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    (analysis.optionArrays()
                            ? fsvar.getV(((ThreeRegisterInstruction) instruction).getRegisterC())
                                    : fsengine.mkBitVector(0, size)),
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getH(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsengine.or(
                            fsvar.getL(((OneRegisterInstruction)instruction).getRegisterA()),
                            fsvar.getG(((OneRegisterInstruction)instruction).getRegisterA())
                            )
                    );
            fsengine.addRule(fsengine.implies(h, b), null);
            
            //lift the local heap if the value moved was a local pointer
            h = fsengine.and(
                    fsengine.eq(fsvar.getL(((OneRegisterInstruction)instruction).getRegisterA()), fsengine.mkTrue()),
                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc)
                    );
            this.liftIfLocal(h, null);
            break;
            //((short)0x51, "aput-short", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),


        case IGET://((short)0x52, "iget", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IGET_WIDE://((short)0x53, "iget-wide", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case IGET_OBJECT://((short)0x54, "iget-object", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IGET_BOOLEAN://((short)0x55, "iget-boolean", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IGET_BYTE://((short)0x56, "iget-byte", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IGET_CHAR://((short)0x57, "iget-char", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IGET_SHORT:
            //Object on global heap
            h = fsengine.and(
                    fsengine.hPred(fsvar.getCn(), fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                            fsengine.mkBitVector(referenceIntIndex, size),
                            fsvar.getVal(), fsvar.getLval(), fsvar.getBval()),
                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc)
                    );
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getVal());
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getLval());
            regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(),fsengine.mkFalse());
            regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getBval());
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);

            regUpV.clear();regUpH.clear();regUpL.clear();regUpG.clear();
            
            //Object on local heap
            for (int allocationPoint : analysis.getAllocationPoints()){
                //we do not generate rules if class of the object allocated at 'allocationPoint' has no entry for the field allocated by the dalvik instruction
         
                if (analysis.getClassFields(analysis.getAllocationPointClass(allocationPoint),allocationPoint) != null)
                if (analysis.getClassFields(analysis.getAllocationPointClass(allocationPoint),allocationPoint).containsKey(referenceIntIndex)){
                    h = fsengine.and(
                            fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                            fsengine.eq(fsvar.getL(((TwoRegisterInstruction)instruction).getRegisterB()),fsengine.mkTrue()),
                            fsengine.eq(fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),fsengine.mkBitVector(allocationPoint,size))
                            );
                    int fieldPosition = fsengine.getOffset(allocationPoint) + analysis.getFieldOffset(allocationPoint, referenceIntIndex);
                    regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(),fsvar.getLHV(fieldPosition));
                    regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(),fsvar.getLHH(fieldPosition));
                    regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(),fsvar.getLHL(fieldPosition));
                    regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(),fsvar.getLHG(fieldPosition));
                    b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                    fsengine.addRule(fsengine.implies(h, b), null);
                    
                    regUpV.clear();regUpH.clear();regUpL.clear();regUpG.clear();
                    regUpLHV.clear();regUpLHH.clear();regUpLHL.clear();regUpLHG.clear();
                }
            }
            
            break;//((short)0x58, "iget-short", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case IPUT://((short)0x59, "iput", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_WIDE://((short)0x5a, "iput-wide", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_OBJECT://((short)0x5b, "iput-object", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_BOOLEAN://((short)0x5c, "iput-boolean", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_BYTE://((short)0x5d, "iput-byte", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_CHAR://((short)0x5e, "iput-char", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_SHORT:
            //object on the global heap: propagate R
            h = fsengine.and(
                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                    fsvar.getG(((TwoRegisterInstruction)instruction).getRegisterB()));
            /*
            regUpH.put(((TwoRegisterInstruction)instruction).getRegisterB(),
                    fsengine.or(
                            fsvar.getH(((TwoRegisterInstruction)instruction).getRegisterB()),
                            fsvar.getH(((OneRegisterInstruction)instruction).getRegisterA())
                            )
                    );
            */
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);

            regUpH.clear();

            //object on the global heap: update the global heap
            h = fsengine.and(
                    fsvar.getG(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                    fsengine.hPred(fsvar.getCn(), fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                            fsvar.getF(), fsengine.mkBitVector(0, size),
                            fsvar.getLf(), fsvar.getBf())
                    );
            b = fsengine.hPred(
                    fsvar.getCn(), fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsengine.mkBitVector(referenceIntIndex, size),
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getH(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsengine.or(
                            fsvar.getL(((OneRegisterInstruction)instruction).getRegisterA()),
                            fsvar.getG(((OneRegisterInstruction)instruction).getRegisterA())
                            )
                    );
            fsengine.addRule(fsengine.implies(h, b), null);

            //lift the local heap if the value moved was a local pointer and the object was on the global heap
            h = fsengine.and(
                    fsengine.eq(fsvar.getG(((TwoRegisterInstruction)instruction).getRegisterB()),fsengine.mkTrue()),
                    fsengine.eq(fsvar.getL(((OneRegisterInstruction)instruction).getRegisterA()),fsengine.mkTrue()),
                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc)
                    );
            this.liftIfLocal(h, null);
            
            //object is on the local heap: update the local heap
            for (int allocationPoint : analysis.getAllocationPoints()){
                //we do not generate rules if class of the object allocated at 'allocationPoint' has no entry for the field allocated by the dalvik instruction
                if (analysis.getClassFields(analysis.getAllocationPointClass(allocationPoint),allocationPoint) != null)
                if (analysis.getClassFields(analysis.getAllocationPointClass(allocationPoint),allocationPoint).containsKey(referenceIntIndex)){
                    h = fsengine.and(
                            fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                            fsengine.eq(fsvar.getL(((TwoRegisterInstruction)instruction).getRegisterB()),fsengine.mkTrue()),
                            fsengine.eq(fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),fsengine.mkBitVector(allocationPoint,size))
                            );
                    int fieldPosition = fsengine.getOffset(allocationPoint) + analysis.getFieldOffset(allocationPoint, referenceIntIndex);
                    regUpLHV.put(fieldPosition, fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()));
                    regUpLHH.put(fieldPosition, fsvar.getH(((OneRegisterInstruction)instruction).getRegisterA()));
                    regUpLHL.put(fieldPosition, fsvar.getL(((OneRegisterInstruction)instruction).getRegisterA()));
                    regUpLHG.put(fieldPosition, fsvar.getG(((OneRegisterInstruction)instruction).getRegisterA()));
                    b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                    fsengine.addRule(fsengine.implies(h, b), null);
                    
                    regUpV.clear();regUpH.clear();regUpL.clear();regUpG.clear();
                    regUpLHV.clear();regUpLHH.clear();regUpLHL.clear();regUpLHG.clear();
                }
            }
            break;//((short)0x5f, "iput-short", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),


        case SGET://((short)0x60, "sget", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SGET_WIDE://((short)0x61, "sget-wide", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case SGET_OBJECT://((short)0x62, "sget-object", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SGET_BOOLEAN://((short)0x63, "sget-boolean", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SGET_BYTE://((short)0x64, "sget-byte", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SGET_CHAR://((short)0x65, "sget-char", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SGET_SHORT:
            staticFieldClassName = analysis.staticFieldLookup(referenceClassIndex, referenceIntIndex, Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <Integer, Boolean>())));
            if (staticFieldClassName == null){
                staticFieldClassName = referenceClassIndex;
            }

            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkBitVector(0, size));
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getBf());
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
            
            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();

            h = fsengine.and(
                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                    fsengine.sPred(fsengine.mkInt(staticFieldClassName), fsengine.mkInt(referenceIntIndex),
                            fsvar.getF(), fsvar.getLf(), fsvar.getBf())
                    );
            regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getF());
            regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getLf());
            regUpL.put(((OneRegisterInstruction)instruction).getRegisterA(), fsengine.mkFalse());
            regUpG.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getBf());
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);
            break;//((short)0x66, "sget-short", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case SPUT://((short)0x67, "sput", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SPUT_WIDE://((short)0x68, "sput-wide", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SPUT_OBJECT://((short)0x69, "sput-object", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SPUT_BOOLEAN://((short)0x6a, "sput-boolean", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SPUT_BYTE://((short)0x6b, "sput-byte", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SPUT_CHAR://((short)0x6c, "sput-char", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SPUT_SHORT:
            staticFieldClassName = analysis.staticFieldLookup(referenceClassIndex, referenceIntIndex, Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <Integer, Boolean>())));
            if (staticFieldClassName == null){
                staticFieldClassName = referenceClassIndex;
            }
            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            fsengine.addRule(fsengine.implies(h, b), null);

            h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            b = fsengine.sPred(fsengine.mkInt(staticFieldClassName), fsengine.mkInt(referenceIntIndex),
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getH(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsengine.or(
                            fsvar.getL(((OneRegisterInstruction)instruction).getRegisterA()),
                            fsvar.getG(((OneRegisterInstruction)instruction).getRegisterA())
                            ));
            fsengine.addRule(fsengine.implies(h, b), null);
            
            // if the value moved to the static heap contains a local pointer then we lift
            h = fsengine.and(
                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                    fsengine.eq(fsvar.getL(((OneRegisterInstruction)instruction).getRegisterA()), fsengine.mkTrue()));
            this.liftIfLocal(h, null);
            break;//((short)0x6d, "sput-short", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),


        case INVOKE_SUPER:
            superBool = true;
        case INVOKE_VIRTUAL:
        case INVOKE_INTERFACE:
            if (referenceClassIndex == "Lde/ecspride/GeneralActivity;".hashCode() && referenceIntIndex == "onCreate(Landroid/os/Bundle;)V".hashCode()){
                int i =0;
                i = i +1;
            }
            this.getImplementationsSpecialCase(superBool);

            isDefined = (implementations != null);
            
            FiveRegisterInstruction instr = (FiveRegisterInstruction)this.instruction;
            referenceReg = instr.getRegisterC();

            if (isDefined){
                this.invokeImpKnown(referenceReg, implementations, false);
            }
            
            
            else {
                returnLabel = analysis.isSource(referenceClassIndex, referenceIntIndex) ? fsengine.mkTrue() : getLabels();
                
                this.invokeImpNotKnown(returnLabel, ci, mi, false);
            }
            break;


        case INVOKE_SUPER_RANGE:
            superBool = true;
        case INVOKE_VIRTUAL_RANGE:
        case INVOKE_INTERFACE_RANGE:

            this.getImplementationsSpecialCase(superBool);

            isDefined = (implementations != null);
            if (implementations != null)
                isDefined = true;
            RegisterRangeInstruction instr3 = (RegisterRangeInstruction)this.instruction;
            if (isDefined){
                referenceReg = instr3.getStartRegister();
                this.invokeImpKnown(referenceReg, implementations, true);
            }
            else{
                returnLabel = analysis.isSource(referenceClassIndex, referenceIntIndex) ? fsengine.mkTrue() : getLabelsRange();
                
                this.invokeImpNotKnown(returnLabel, ci, mi, true);
            }
            break;


            
            
        case INVOKE_DIRECT:
        case INVOKE_STATIC:
            //we do a resolution on thread init, not on thread start, as at thread start the class information is lost
            //(it is stored somewhere in the thread class by the operating system, we can also simulate that storing class name somewhere).
            //on the other hand, if one initializes the thread and never spawns it? rare
            //JavaThread2 for the reference
            if ((referenceIntIndex == "<init>(Ljava/lang/Runnable;)V".hashCode()) && (referenceClassIndex == "Ljava/lang/Thread;".hashCode())){
                implementations = analysis.getImplementations("Ljava/lang/Runnable;".hashCode(), "run()V".hashCode());
                isDefined = !implementations.isEmpty();
                FiveRegisterInstruction instr2 = (FiveRegisterInstruction)this.instruction;
                if (isDefined){
                    for (final DalvikImplementation di : implementations){
                        numRegCall = di.getMethod().getNumReg();
                        numArgCall = di.getMethod().getNumArg();

                        for (final DalvikInstance instance: di.getInstances()){
                            h = fsengine.and(
                                    fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                                    fsengine.eq(
                                            fsvar.getV(instr2.getRegisterD()),
                                            fsengine.mkBitVector(instance.hashCode(), size)
                                            )
                                    );

                            regUpV.put(numRegCall - numArgCall + 0, fsvar.getV(instr2.getRegisterD()));
                            regUpV.put(numRegCall + 1 + 0, fsvar.getV(instr2.getRegisterD()));
                            regUpH.put(numRegCall - numArgCall + 0, fsvar.getH(instr2.getRegisterD()));
                            regUpH.put(numRegCall + 1 + 0, fsvar.getH(instr2.getRegisterD()));
                            regUpL.put(numRegCall - numArgCall + 0, fsvar.getL(instr2.getRegisterD()));
                            regUpL.put(numRegCall + 1 + 0, fsvar.getL(instr2.getRegisterD()));
                            regUpG.put(numRegCall - numArgCall + 0, fsvar.getG(instr2.getRegisterD()));
                            regUpG.put(numRegCall + 1 + 0, fsvar.getG(instr2.getRegisterD()));
                            b = fsengine.rPredInvok(
                                    Integer.toString(di.getDalvikClass().getType().hashCode()),
                                    Integer.toString("run()V".hashCode()),
                                    0, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numArgCall, numRegCall, size);
                            fsengine.addRule(fsengine.implies(h, b), null);

                            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();
                        }

                        break;
                    }
                }
            }

            staticDefinitions = analysis.isDefined(referenceClassIndex, referenceIntIndex, Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <Integer, Boolean>())));
            isDefined = staticDefinitions != null;
            if (!isDefined) analysis.putNotDefined(referenceClassIndex, referenceIntIndex);
            else analysis.putDefined(referenceClassIndex, referenceIntIndex, staticDefinitions);
            if (isDefined){
                this.staticInvokeImpKnown(staticDefinitions, false);
            } else {
                returnLabel = analysis.isSource(referenceClassIndex, referenceIntIndex) ? fsengine.mkTrue() : getLabels();

                this.invokeImpNotKnown(returnLabel, ci, mi, false);    
            }
            break;
            //((short)0x6e, "invoke-virtual", ReferenceType.METHOD, Format.Format35c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),

        case INVOKE_DIRECT_RANGE:
        case INVOKE_STATIC_RANGE:
            staticDefinitions = analysis.isDefined(referenceClassIndex, referenceIntIndex, Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <Integer, Boolean>())));
            isDefined = staticDefinitions != null;
            if (!isDefined) analysis.putNotDefined(referenceClassIndex, referenceIntIndex);
            else analysis.putDefined(referenceClassIndex, referenceIntIndex, staticDefinitions);
            if (isDefined){
                this.staticInvokeImpKnown(staticDefinitions, true);
            } else {
                    returnLabel = analysis.isSource(referenceClassIndex, referenceIntIndex) ? fsengine.mkTrue() : getLabelsRange();
                    this.invokeImpNotKnown(returnLabel, ci, mi, true);
            }
            break;//((short)0x74, "invoke-virtual/range", ReferenceType.METHOD, Format.Format3rc, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),

        case NEG_INT://((short)0x7b, "neg-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case NEG_LONG://((short)0x7d, "neg-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case NEG_FLOAT://((short)0x7f, "neg-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case NEG_DOUBLE:
            BitVecExpr bv = fsengine.bvneg(fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()));
            this.unaryOp(bv);
            break;//((short)0x80, "neg-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


        case NOT_INT://((short)0x7c, "not-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case NOT_LONG:
            bv = fsengine.bvnot(fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()));
            this.unaryOp(bv);
            break;//((short)0x7e, "not-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


        case INT_TO_LONG://((short)0x81, "int-to-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case INT_TO_FLOAT://((short)0x82, "int-to-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case INT_TO_DOUBLE://((short)0x83, "int-to-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case LONG_TO_INT://((short)0x84, "long-to-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case LONG_TO_FLOAT://((short)0x85, "long-to-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case LONG_TO_DOUBLE://((short)0x86, "long-to-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case FLOAT_TO_INT://((short)0x87, "float-to-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case FLOAT_TO_LONG://((short)0x88, "float-to-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case FLOAT_TO_DOUBLE://((short)0x89, "float-to-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case DOUBLE_TO_INT://((short)0x8a, "double-to-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case DOUBLE_TO_LONG://((short)0x8b, "double-to-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case DOUBLE_TO_FLOAT://((short)0x8c, "double-to-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case INT_TO_BYTE://((short)0x8d, "int-to-byte", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case INT_TO_CHAR://((short)0x8e, "int-to-char", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case INT_TO_SHORT:
            this.propagate();
            break;//((short)0x8f, "int-to-short", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case ADD_INT://((short)0x90, "add-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case ADD_LONG://((short)0x9b, "add-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case ADD_FLOAT://((short)0xa6, "add-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case ADD_DOUBLE:
            bv = fsengine.bvadd(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsvar.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                    );
            this.binaryOpC(bv);
            break;//((short)0xab, "add-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case SUB_INT://((short)0x91, "sub-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SUB_LONG://((short)0x9c, "sub-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case SUB_FLOAT://((short)0xa7, "sub-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SUB_DOUBLE:
            bv = fsengine.bvsub(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsvar.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                    );
            this.binaryOpC(bv);
            break;//((short)0xac, "sub-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case MUL_INT://((short)0x92, "mul-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MUL_LONG://((short)0x9d, "mul-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case MUL_FLOAT://((short)0xa8, "mul-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MUL_DOUBLE:
            bv = fsengine.bvmul(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsvar.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                    );
            this.binaryOpC(bv);
            break;//((short)0xad, "mul-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case DIV_INT://((short)0x93, "div-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case DIV_LONG://((short)0x9e, "div-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case DIV_FLOAT://((short)0xa9, "div-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case DIV_DOUBLE:
            bv = fsengine.bvudiv(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsvar.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                    );
            this.binaryOpC(bv);
            break;//((short)0xae, "div-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case REM_INT://((short)0x94, "rem-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case REM_LONG://((short)0x9f, "rem-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case REM_FLOAT://((short)0xaa, "rem-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case REM_DOUBLE:
            bv = fsengine.bvudiv(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsvar.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                    );
            this.binaryOpC(bv);
            break;//((short)0xaf, "rem-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case AND_INT://((short)0x95, "and-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case AND_LONG:
            bv = fsengine.bvand(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsvar.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                    );
            this.binaryOpC(bv);
            break;//((short)0xa0, "and-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case OR_INT://((short)0x96, "or-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case OR_LONG:
            bv = fsengine.bvor(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsvar.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                    );
            this.binaryOpC(bv);
            break;//((short)0xa1, "or-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case XOR_INT://((short)0x97, "xor-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case XOR_LONG:
            bv = fsengine.bvxor(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsvar.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                    );
            this.binaryOpC(bv);
            break;//((short)0xa2, "xor-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case SHL_INT://((short)0x98, "shl-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SHL_LONG:
            bv = fsengine.bvxor(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsvar.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                    );
            this.binaryOpC(bv);
            break;//((short)0xa3, "shl-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


        case SHR_LONG://((short)0xa4, "shr-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case SHR_INT:
            bv = fsengine.bvashr(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsvar.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                    );
            this.binaryOpC(bv);
            break;//((short)0x99, "shr-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case USHR_INT://((short)0x9a, "ushr-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case USHR_LONG:
            bv = fsengine.bvlshr(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsvar.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                    );
            this.binaryOpC(bv);
            break;//((short)0xa5, "ushr-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


        case ADD_INT_2ADDR://((short)0xb0, "add-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case ADD_LONG_2ADDR://((short)0xc0, "and-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case ADD_FLOAT_2ADDR://((short)0xc6, "add-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case ADD_DOUBLE_2ADDR:
            bv = fsengine.bvadd(
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                    );
            this.binaryOp(bv);
            break;//((short)0xcb, "add-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


        case SUB_INT_2ADDR://((short)0xb1, "sub-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SUB_LONG_2ADDR://((short)0xbc, "sub-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case SUB_FLOAT_2ADDR://((short)0xc7, "sub-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SUB_DOUBLE_2ADDR:
            bv = fsengine.bvsub(
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                    );
            this.binaryOp(bv);
            break;//((short)0xcc, "sub-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case MUL_INT_2ADDR://((short)0xb2, "mul-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MUL_LONG_2ADDR://((short)0xbd, "mul-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case MUL_FLOAT_2ADDR://((short)0xc8, "mul-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MUL_DOUBLE_2ADDR:
            bv = fsengine.bvmul(
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                    );
            this.binaryOp(bv);
            break;//((short)0xcd, "mul-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case DIV_INT_2ADDR://((short)0xb3, "div-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case DIV_LONG_2ADDR://((short)0xbe, "div-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case DIV_FLOAT_2ADDR://((short)0xc9, "div-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case DIV_DOUBLE_2ADDR:
            bv = fsengine.bvudiv(
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                    );
            this.binaryOp(bv);
            break;//((short)0xce, "div-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case REM_INT_2ADDR://((short)0xb4, "rem-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case REM_LONG_2ADDR://((short)0xbf, "rem-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case REM_FLOAT_2ADDR://((short)0xca, "rem-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case REM_DOUBLE_2ADDR:
            bv = fsengine.bvurem(
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                    );
            this.binaryOp(bv);
            break;//((short)0xcf, "rem-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case AND_INT_2ADDR://((short)0xb5, "and-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case AND_LONG_2ADDR:
            bv = fsengine.bvand(
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                    );
            this.binaryOp(bv);
            break;//((short)0xbb, "add-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case OR_INT_2ADDR://((short)0xb6, "or-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case OR_LONG_2ADDR:
            bv = fsengine.bvor(
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                    );
            this.binaryOp(bv);
            break;//((short)0xc1, "or-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case XOR_INT_2ADDR://((short)0xb7, "xor-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case XOR_LONG_2ADDR:
            bv = fsengine.bvxor(
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                    );
            this.binaryOp(bv);
            break;//((short)0xc2, "xor-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case SHL_INT_2ADDR://((short)0xb8, "shl-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SHL_LONG_2ADDR:
            bv = fsengine.bvshl(
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                    );
            this.binaryOp(bv);

            break;//((short)0xc3, "shl-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        case SHR_INT_2ADDR://((short)0xb9, "shr-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SHR_LONG_2ADDR:
            bv = fsengine.bvashr(
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                    );
            this.binaryOp(bv);
            break;//((short)0xc4, "shr-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


        case USHR_INT_2ADDR://((short)0xba, "ushr-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case USHR_LONG_2ADDR:
            bv = fsengine.bvlshr(
                    fsvar.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                    );
            this.binaryOp(bv);
            break;//((short)0xc5, "ushr-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


        case ADD_INT_LIT16://((short)0xd0, "add-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case ADD_INT_LIT8:
            bv = fsengine.bvadd(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsengine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                    );
            this.unaryOp(bv);
            break;//((short)0xd8, "add-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case MUL_INT_LIT16://((short)0xd2, "mul-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MUL_INT_LIT8:
            bv = fsengine.bvmul(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsengine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                    );
            this.unaryOp(bv);
            break;//((short)0xda, "mul-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case DIV_INT_LIT16://((short)0xd3, "div-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case DIV_INT_LIT8:
            bv = fsengine.bvudiv(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsengine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                    );
            this.unaryOp(bv);
            break;//((short)0xdb, "div-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case REM_INT_LIT16://((short)0xd4, "rem-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case REM_INT_LIT8:
            bv = fsengine.bvurem(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsengine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                    );
            this.unaryOp(bv);
            break;//((short)0xdc, "rem-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case AND_INT_LIT16://((short)0xd5, "and-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case AND_INT_LIT8:
            bv = fsengine.bvand(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsengine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                    );
            this.unaryOp(bv);
            break;//((short)0xdd, "and-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case OR_INT_LIT16://((short)0xd6, "or-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case OR_INT_LIT8:
            bv = fsengine.bvor(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsengine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                    );
            this.unaryOp(bv);
            break;//((short)0xde, "or-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case XOR_INT_LIT16://((short)0xd7, "xor-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case XOR_INT_LIT8:
            bv = fsengine.bvxor(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsengine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                    );
            this.unaryOp(bv);
            break;//((short)0xdf, "xor-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case RSUB_INT://((short)0xd1, "rsub-int", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case RSUB_INT_LIT8:
            bv = fsengine.bvsub(
                    fsengine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                    );
            this.unaryOp(bv);
            break;//((short)0xd9, "rsub-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case SHL_INT_LIT8:
            bv = fsengine.bvshl(fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsengine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size));
            this.unaryOp(bv);
            break;//((short)0xe0, "shl-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case SHR_INT_LIT8:
            bv = fsengine.bvashr(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsengine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                    );
            this.unaryOp(bv);
            break;//((short)0xe1, "shr-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case USHR_INT_LIT8:
            bv = fsengine.bvlshr(
                    fsvar.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    fsengine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                    );
            this.unaryOp(bv);
            break;//((short)0xe2, "ushr-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),

        case IGET_VOLATILE://((short)0xe3, "iget-volatile", minApi(9), ReferenceType.FIELD, Format.Format22c, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IPUT_VOLATILE://((short)0xe4, "iput-volatile", minApi(9), ReferenceType.FIELD, Format.Format22c, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SGET_VOLATILE://((short)0xe5, "sget-volatile", minApi(9), ReferenceType.FIELD, Format.Format21c, Opcode.ODEX_ONLY | Opcode.ODEXED_STATIC_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SPUT_VOLATILE://((short)0xe6, "sput-volatile", minApi(9), ReferenceType.FIELD, Format.Format21c, Opcode.ODEX_ONLY | Opcode.ODEXED_STATIC_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IGET_OBJECT_VOLATILE://((short)0xe7, "iget-object-volatile", minApi(9), ReferenceType.FIELD, Format.Format22c, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IGET_WIDE_VOLATILE://((short)0xe8, "iget-wide-volatile", minApi(9), ReferenceType.FIELD, Format.Format22c, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case IPUT_WIDE_VOLATILE://((short)0xe9, "iput-wide-volatile", minApi(9), ReferenceType.FIELD, Format.Format22c, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SGET_WIDE_VOLATILE://((short)0xea, "sget-wide-volatile", minApi(9), ReferenceType.FIELD, Format.Format21c, Opcode.ODEX_ONLY | Opcode.ODEXED_STATIC_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case SPUT_WIDE_VOLATILE://((short)0xeb, "sput-wide-volatile", minApi(9), ReferenceType.FIELD, Format.Format21c, Opcode.ODEX_ONLY | Opcode.ODEXED_STATIC_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),

        case THROW_VERIFICATION_ERROR://((short)0xed, "throw-verification-error", minApi(5), ReferenceType.NONE, Format.Format20bc, Opcode.ODEX_ONLY | Opcode.CAN_THROW),
        case EXECUTE_INLINE://((short)0xee, "execute-inline", ReferenceType.NONE,  Format.Format35mi, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        case EXECUTE_INLINE_RANGE://((short)0xef, "execute-inline/range", minApi(8), ReferenceType.NONE,  Format.Format3rmi,  Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        case INVOKE_DIRECT_EMPTY://((short)0xf0, "invoke-direct-empty", maxApi(13), ReferenceType.METHOD,  Format.Format35c, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT | Opcode.CAN_INITIALIZE_REFERENCE),
        case INVOKE_OBJECT_INIT_RANGE://((short)0xf0, "invoke-object-init/range", minApi(14), ReferenceType.METHOD,  Format.Format3rc, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT | Opcode.CAN_INITIALIZE_REFERENCE),
        case RETURN_VOID_BARRIER://((short)0xf1, "return-void-barrier", minApi(11), ReferenceType.NONE, Format.Format10x, Opcode.ODEX_ONLY),
        case IGET_QUICK://((short)0xf2, "iget-quick", ReferenceType.NONE,  Format.Format22cs, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_QUICK | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IGET_WIDE_QUICK://((short)0xf3, "iget-wide-quick", ReferenceType.NONE,  Format.Format22cs, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_QUICK | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case IGET_OBJECT_QUICK://((short)0xf4, "iget-object-quick", ReferenceType.NONE,  Format.Format22cs, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_QUICK | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IPUT_QUICK://((short)0xf5, "iput-quick", ReferenceType.NONE,  Format.Format22cs, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_QUICK | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_WIDE_QUICK://((short)0xf6, "iput-wide-quick", ReferenceType.NONE,  Format.Format22cs, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_QUICK | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_OBJECT_QUICK://((short)0xf7, "iput-object-quick", ReferenceType.NONE,  Format.Format22cs, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_QUICK | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case INVOKE_VIRTUAL_QUICK://((short)0xf8, "invoke-virtual-quick", ReferenceType.NONE,  Format.Format35ms, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        case INVOKE_VIRTUAL_QUICK_RANGE://((short)0xf9, "invoke-virtual-quick/range", ReferenceType.NONE,  Format.Format3rms, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        case INVOKE_SUPER_QUICK://((short)0xfa, "invoke-super-quick", ReferenceType.NONE,  Format.Format35ms, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),
        case INVOKE_SUPER_QUICK_RANGE://((short)0xfb, "invoke-super-quick/range", ReferenceType.NONE,  Format.Format3rms, Opcode.ODEX_ONLY | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),

        case IPUT_OBJECT_VOLATILE://((short)0xfc, "iput-object-volatile", minApi(9), ReferenceType.FIELD, Format.Format22c, Opcode.ODEX_ONLY | Opcode.ODEXED_INSTANCE_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SGET_OBJECT_VOLATILE://((short)0xfd, "sget-object-volatile", minApi(9), ReferenceType.FIELD, Format.Format21c, Opcode.ODEX_ONLY | Opcode.ODEXED_STATIC_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SPUT_OBJECT_VOLATILE://((short)0xfe, "sput-object-volatile", minApi(9), ReferenceType.FIELD, Format.Format21c, Opcode.ODEX_ONLY | Opcode.ODEXED_STATIC_VOLATILE | Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case PACKED_SWITCH_PAYLOAD://((short)0x100, "packed-switch-payload", ReferenceType.NONE, Format.PackedSwitchPayload, 0),
        case SPARSE_SWITCH_PAYLOAD://((short)0x200, "sparse-switch-payload", ReferenceType.NONE, Format.SparseSwitchPayload, 0),
        case ARRAY_PAYLOAD://((short)0x300, "array-payload", ReferenceType.NONE, Format.ArrayPayload, 0);
        default:
            System.err.println("FSInstructionAnalysis: unsuported instruction" + opcode);
        }
    }

    private void propagate(){
        BoolExpr h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
        BoolExpr b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
        fsengine.addRule(fsengine.implies(h, b), null);
    }
    
    private void unaryOp(BitVecExpr bv){
        BoolExpr h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
        regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(),bv);
        regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(), fsvar.getH(((TwoRegisterInstruction)instruction).getRegisterB()));
        BoolExpr b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
        fsengine.addRule(fsengine.implies(h, b), null);
    }

    private void binaryOp(BitVecExpr bv){
        BoolExpr h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
        regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(),bv);
        regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(),
                fsengine.or(
                        fsvar.getH(((TwoRegisterInstruction)instruction).getRegisterA()),
                        fsvar.getH(((TwoRegisterInstruction)instruction).getRegisterB())));
        BoolExpr b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
        fsengine.addRule(fsengine.implies(h, b), null);
    }
    
    private void binaryOpC(BitVecExpr bv){
        BoolExpr h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
        regUpV.put(((OneRegisterInstruction)instruction).getRegisterA(),bv);
        regUpH.put(((OneRegisterInstruction)instruction).getRegisterA(),
                fsengine.or(
                        fsvar.getH(((ThreeRegisterInstruction)instruction).getRegisterB()),
                        fsvar.getH(((ThreeRegisterInstruction)instruction).getRegisterC())));
        BoolExpr b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
        fsengine.addRule(fsengine.implies(h, b), null);
    }
    
    
    
    private BoolExpr getLabels(){
        FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
        final int regCount = instruction.getRegisterCount();
        switch (regCount) {
        case 1:
            return fsengine.or(
                    fsvar.getH(instruction.getRegisterC()));
        case 2:
            return fsengine.or(
                    fsvar.getH(instruction.getRegisterC()),
                    fsvar.getH(instruction.getRegisterD()));
        case 3:
            return fsengine.or(
                    fsvar.getH(instruction.getRegisterC()),
                    fsvar.getH(instruction.getRegisterD()),
                    fsvar.getH(instruction.getRegisterE()));
        case 4:
            return fsengine.or(
                    fsvar.getH(instruction.getRegisterC()),
                    fsvar.getH(instruction.getRegisterD()),
                    fsvar.getH(instruction.getRegisterE()),
                    fsvar.getH(instruction.getRegisterF()));

        case 5:
            return fsengine.or(
                    fsvar.getH(instruction.getRegisterC()),
                    fsvar.getH(instruction.getRegisterD()),
                    fsvar.getH(instruction.getRegisterE()),
                    fsvar.getH(instruction.getRegisterF()),
                    fsvar.getH(instruction.getRegisterG()));
        default:
            return fsengine.mkFalse();
        }
    }

    private BoolExpr getLabelsRange(){
        RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
        int regCount = instruction.getRegisterCount();
        int startRegister = instruction.getStartRegister();
        int endRegister   =   startRegister+regCount-1;

        BoolExpr labels = fsengine.mkFalse();
        for(int reg = startRegister; reg <= endRegister; reg++){
            labels = fsengine.or(
                    labels, fsvar.getH(reg)
                    );
        }
        return fsengine.or(labels);
    }

    private void addQueryRange(BoolExpr p, String className, String methodName, String pc, String sinkName, final boolean verboseOption){
        RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
        int regCount = instruction.getRegisterCount();
        int startRegister = instruction.getStartRegister();
        int endRegister   =   startRegister+regCount-1;

        for (int reg = startRegister; reg <= endRegister; reg++ ){
            BoolExpr q = fsengine.and(
                    p,
                    fsengine.eq(fsvar.getH(reg), fsengine.mkTrue())
                    );
            String d = "Test if register " + Integer.toString(reg) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            fsengine.addQuery(new Z3Query(q, d, verboseOption, className, methodName, pc, sinkName));
        }
    }

    private void addQuery(BoolExpr p, String className, String methodName, String pc, String sinkName, final boolean verboseResults){
        FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
        final int regCount = instruction.getRegisterCount();

        switch (regCount) {
        case 5:
            BoolExpr q5 = fsengine.and(
                    p,
                    fsengine.eq(fsvar.getH(instruction.getRegisterG()), fsengine.mkTrue())
                    );
            String d5 = "Test if register " + Integer.toString(instruction.getRegisterG()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            fsengine.addQuery(new Z3Query(q5, d5, verboseResults, className, methodName, pc, sinkName));
        case 4:
            BoolExpr q4 = fsengine.and(
                    p,
                    fsengine.eq(fsvar.getH(instruction.getRegisterF()), fsengine.mkTrue())
                    );
            String d4 = "Test if register " + Integer.toString(instruction.getRegisterF()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            fsengine.addQuery(new Z3Query(q4, d4, verboseResults, className, methodName, pc, sinkName));
        case 3:
            BoolExpr q3 = fsengine.and(
                    p,
                    fsengine.eq(fsvar.getH(instruction.getRegisterE()), fsengine.mkTrue())
                    );
            String d3 = "Test if register " + Integer.toString(instruction.getRegisterE()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            fsengine.addQuery(new Z3Query(q3, d3, verboseResults, className, methodName, pc, sinkName));
        case 2:
            BoolExpr q2 = fsengine.and(
                    p,
                    fsengine.eq(fsvar.getH(instruction.getRegisterD()), fsengine.mkTrue())
                    );
            String d2 = "Test if register " + Integer.toString(instruction.getRegisterD()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            fsengine.addQuery(new Z3Query(q2, d2, verboseResults, className, methodName, pc, sinkName));
        case 1:
            BoolExpr q1 = fsengine.and(
                    p,
                    fsengine.eq(fsvar.getH(instruction.getRegisterC()), fsengine.mkTrue())
                    );
            String d1 = "Test if register " + Integer.toString(instruction.getRegisterC()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            fsengine.addQuery(new Z3Query(q1, d1, verboseResults, className, methodName, pc, sinkName));
        }
    }

    private Map<Integer, BoolExpr> highReg(final boolean range, Map<Integer, BoolExpr> regUpdate){
        if (! range){
            FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
            final int regCount = instruction.getRegisterCount();
            switch (regCount) {
            case 1:
                regUpdate.put(instruction.getRegisterC(), fsvar.getH(instruction.getRegisterC()));
                break;

            case 2:
                regUpdate.put(instruction.getRegisterC(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterC()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterC()),fsvar.getG(instruction.getRegisterC())),
                                        fsvar.getH(instruction.getRegisterD())
                                        )
                                )
                        );
                regUpdate.put(instruction.getRegisterD(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterD()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterD()),fsvar.getG(instruction.getRegisterD())),
                                        fsvar.getH(instruction.getRegisterC())
                                        )
                                )
                        );
                break;

            case 3:
                regUpdate.put(instruction.getRegisterC(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterC()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterC()),fsvar.getG(instruction.getRegisterC())),
                                        fsengine.or(
                                                fsvar.getH(instruction.getRegisterD()),
                                                fsvar.getH(instruction.getRegisterE())
                                                )
                                        )
                                )
                        );
                regUpdate.put(instruction.getRegisterD(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterD()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterD()),fsvar.getG(instruction.getRegisterD())),
                                        fsengine.or(
                                                fsvar.getH(instruction.getRegisterC()),
                                                fsvar.getH(instruction.getRegisterE())
                                                )
                                        )
                                )
                        );
                regUpdate.put(instruction.getRegisterE(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterE()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterE()),fsvar.getG(instruction.getRegisterE())),
                                        fsengine.or(
                                                fsvar.getH(instruction.getRegisterC()),
                                                fsvar.getH(instruction.getRegisterD())
                                                )
                                        )
                                )
                        );
                break;

            case 4:
                regUpdate.put(instruction.getRegisterC(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterC()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterC()),fsvar.getG(instruction.getRegisterC())),
                                        fsengine.or(
                                                fsvar.getH(instruction.getRegisterD()),
                                                fsvar.getH(instruction.getRegisterE()),
                                                fsvar.getH(instruction.getRegisterF())
                                                )
                                        )
                                )
                        );
                regUpdate.put(instruction.getRegisterD(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterD()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterD()),fsvar.getG(instruction.getRegisterD())),
                                        fsengine.or(
                                                fsvar.getH(instruction.getRegisterC()),
                                                fsvar.getH(instruction.getRegisterE()),
                                                fsvar.getH(instruction.getRegisterF())
                                                )
                                        )
                                )
                        );
                regUpdate.put(instruction.getRegisterE(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterE()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterE()),fsvar.getG(instruction.getRegisterE())),
                                        fsengine.or(
                                                fsvar.getH(instruction.getRegisterD()),
                                                fsvar.getH(instruction.getRegisterC()),
                                                fsvar.getH(instruction.getRegisterF())
                                                )
                                        )
                                )
                        );
                regUpdate.put(instruction.getRegisterF(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterF()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterF()),fsvar.getG(instruction.getRegisterF())),
                                        fsengine.or(
                                                fsvar.getH(instruction.getRegisterD()),
                                                fsvar.getH(instruction.getRegisterE()),
                                                fsvar.getH(instruction.getRegisterC())
                                                )
                                        )
                                )
                        );
                break;
            case 5:
                regUpdate.put(instruction.getRegisterC(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterC()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterC()),fsvar.getG(instruction.getRegisterC())),
                                        fsengine.or(
                                                fsvar.getH(instruction.getRegisterD()),
                                                fsvar.getH(instruction.getRegisterE()),
                                                fsvar.getH(instruction.getRegisterF()),
                                                fsvar.getH(instruction.getRegisterG())
                                                )
                                        )
                                )
                        );
                regUpdate.put(instruction.getRegisterD(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterD()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterD()),fsvar.getG(instruction.getRegisterD())),
                                        fsengine.or(
                                                fsvar.getH(instruction.getRegisterC()),
                                                fsvar.getH(instruction.getRegisterE()),
                                                fsvar.getH(instruction.getRegisterF()),
                                                fsvar.getH(instruction.getRegisterG())
                                                )
                                        )
                                )
                        );
                regUpdate.put(instruction.getRegisterE(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterE()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterE()),fsvar.getG(instruction.getRegisterE())),
                                        fsengine.or(
                                                fsvar.getH(instruction.getRegisterD()),
                                                fsvar.getH(instruction.getRegisterC()),
                                                fsvar.getH(instruction.getRegisterF()),
                                                fsvar.getH(instruction.getRegisterG())
                                                )
                                        )
                                )
                        );
                regUpdate.put(instruction.getRegisterF(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterF()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterF()),fsvar.getG(instruction.getRegisterF())),
                                        fsengine.or(
                                                fsvar.getH(instruction.getRegisterD()),
                                                fsvar.getH(instruction.getRegisterE()),
                                                fsvar.getH(instruction.getRegisterC()),
                                                fsvar.getH(instruction.getRegisterG())
                                                )
                                        )
                                )
                        );
                regUpdate.put(instruction.getRegisterG(),
                        fsengine.or(
                                fsvar.getH(instruction.getRegisterG()),
                                fsengine.and(
                                        fsengine.or(fsvar.getL(instruction.getRegisterG()),fsvar.getG(instruction.getRegisterG())),
                                        fsengine.or(
                                                fsvar.getH(instruction.getRegisterD()),
                                                fsvar.getH(instruction.getRegisterE()),
                                                fsvar.getH(instruction.getRegisterF()),
                                                fsvar.getH(instruction.getRegisterC())
                                                )
                                        )
                                )
                        );
                break;
            }
        } else {
            RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
            int regCount = instruction.getRegisterCount();
            int startRegister = instruction.getStartRegister();
            int endRegister   =   startRegister+regCount-1;
            BoolExpr orLabels = fsengine.mkFalse();
            switch (regCount){
            case 0: return regUpdate;
            case 1: return regUpdate;
            default:
                for (int reg = startRegister; reg <= endRegister; reg++ ){
                    orLabels = fsengine.mkFalse();
                    for (int reg2 = startRegister; reg2 <= endRegister; reg2++ ){
                        if (reg2 == reg){ continue; }
                        fsengine.or(orLabels, fsvar.getH(reg));
                    }
                    regUpdate.put(reg,
                            fsengine.or(
                                    fsvar.getH(reg),
                                    fsengine.and(
                                            fsengine.or(fsvar.getL(reg),fsvar.getL(reg)),
                                            orLabels
                                            )
                                    )
                            );
                }
            }
        }
        return regUpdate;
    }

 
    private <T extends Expr> Map<Integer, T> updateRegister(final int numReg, final int numArg, final Class<T> type, final VariableInject var, final boolean range){
        Map<Integer, T> regUpdate = new HashMap<>();
        if (! range){
            FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
            switch (numArg) {
                case 1:
                    regUpdate.put(numReg - numArg + 0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(numReg + 1 + 0, type.cast(var.get(instruction.getRegisterC())));
                    break;
                case 2:
                    regUpdate.put(numReg - numArg + 0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(numReg - numArg + 1, type.cast(var.get(instruction.getRegisterD())));
                    regUpdate.put(numReg + 1 + 0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(numReg + 1 + 1, type.cast(var.get(instruction.getRegisterD())));
                    break;
                case 3:
                    regUpdate.put(numReg - numArg + 0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(numReg - numArg + 1, type.cast(var.get(instruction.getRegisterD())));
                    regUpdate.put(numReg - numArg + 2, type.cast(var.get(instruction.getRegisterE())));
                    regUpdate.put(numReg + 1 + 0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(numReg + 1 + 1, type.cast(var.get(instruction.getRegisterD())));
                    regUpdate.put(numReg + 1 + 2, type.cast(var.get(instruction.getRegisterE())));
                    break;
                case 4:
                    regUpdate.put(numReg - numArg + 0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(numReg - numArg + 1, type.cast(var.get(instruction.getRegisterD())));
                    regUpdate.put(numReg - numArg + 2, type.cast(var.get(instruction.getRegisterE())));
                    regUpdate.put(numReg - numArg + 3, type.cast(var.get(instruction.getRegisterF())));
                    regUpdate.put(numReg + 1 + 0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(numReg + 1 + 1, type.cast(var.get(instruction.getRegisterD())));
                    regUpdate.put(numReg + 1 + 2, type.cast(var.get(instruction.getRegisterE())));
                    regUpdate.put(numReg + 1 + 3, type.cast(var.get(instruction.getRegisterF())));
                    break;
                case 5:
                    regUpdate.put(numReg - numArg + 0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(numReg - numArg + 1, type.cast(var.get(instruction.getRegisterD())));
                    regUpdate.put(numReg - numArg + 2, type.cast(var.get(instruction.getRegisterE())));
                    regUpdate.put(numReg - numArg + 3, type.cast(var.get(instruction.getRegisterF())));
                    regUpdate.put(numReg - numArg + 4, type.cast(var.get(instruction.getRegisterG())));
                    regUpdate.put(numReg + 1 +  0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(numReg + 1 +  1, type.cast(var.get(instruction.getRegisterD())));
                    regUpdate.put(numReg + 1 +  2, type.cast(var.get(instruction.getRegisterE())));
                    regUpdate.put(numReg + 1 +  3, type.cast(var.get(instruction.getRegisterF())));
                    regUpdate.put(numReg + 1 +  4, type.cast(var.get(instruction.getRegisterG())));
                    break;
            }
        } else {
            RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
            int startRegister = instruction.getStartRegister();
            int endRegister   =   startRegister+numReg-1;
            int count = 0;
            for (int reg = startRegister; reg <= endRegister; reg++ ) {
                regUpdate.put(reg, type.cast(var.get(count)));
                regUpdate.put(numReg + 1 + count, type.cast(var.get(count)));
                count ++;
            }
        }

        return regUpdate;
    }

    private <T extends Expr> Map<Integer, T> updateResult(final int numReg, final int numArg, final Class<T> type, final VariableInject var, final boolean range){
        Map<Integer, T> regUpdate = new HashMap<>();
        if (! range){
            FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
            switch (numArg) {
                case 1:
                    regUpdate.put(0, type.cast(var.get(instruction.getRegisterC())));
                    break;
                case 2:
                    regUpdate.put(0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(1, type.cast(var.get(instruction.getRegisterD())));
                    break;
                case 3:
                    regUpdate.put(0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(1, type.cast(var.get(instruction.getRegisterD())));
                    regUpdate.put(2, type.cast(var.get(instruction.getRegisterE())));
                    break;
                case 4:
                    regUpdate.put(0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(1, type.cast(var.get(instruction.getRegisterD())));
                    regUpdate.put(2, type.cast(var.get(instruction.getRegisterE())));
                    regUpdate.put(3, type.cast(var.get(instruction.getRegisterF())));
                    break;
                case 5:
                    regUpdate.put(0, type.cast(var.get(instruction.getRegisterC())));
                    regUpdate.put(1, type.cast(var.get(instruction.getRegisterD())));
                    regUpdate.put(2, type.cast(var.get(instruction.getRegisterE())));
                    regUpdate.put(3, type.cast(var.get(instruction.getRegisterF())));
                    regUpdate.put(4, type.cast(var.get(instruction.getRegisterG())));
                    break;
            }
        }
        else{
            RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
            int startRegister = instruction.getStartRegister();
            int endRegister   =   startRegister+numReg-1;
            int count = 0;
            for (int reg = startRegister; reg <= endRegister; reg++ )
            {
                regUpdate.put(count, type.cast(var.get(count)));
                count ++;
            }
        }

        return regUpdate;
    }
    
    
    
    /*
     * Local Heap handling functions    
     */
    
    
    private void liftObject(BoolExpr h, int allocationPoint){
        Map<Integer,Boolean> fields = analysis.getClassFields(analysis.getAllocationPointClass(allocationPoint), allocationPoint);
        int size = analysis.getSize();
        int referenceIntIndex = analysis.getAllocationPointClass(allocationPoint).hashCode();
        if (fields != null){
            int loopi = fsengine.getOffset(allocationPoint);
            for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                BoolExpr b = fsengine.hPred(fsengine.mkBitVector(referenceIntIndex, size),
                        fsengine.mkBitVector(allocationPoint, size),
                        fsengine.mkBitVector(fieldN.getKey(), size),
                        fsvar.getLHV(loopi),
                        fsvar.getLHH(loopi),
                        fsengine.or(fsvar.getLHL(loopi),fsvar.getLHG(loopi)));
                fsengine.addRule(fsengine.implies(h, b), null);
                loopi++;
            }   
        }
        else {
            BoolExpr b = fsengine.hPred(fsengine.mkBitVector(referenceIntIndex, size),
                    fsengine.mkBitVector(allocationPoint, size),
                    fsvar.getF(), fsengine.mkBitVector(0, size),
                    fsengine.mkFalse(), fsvar.getBf());
            fsengine.addRule(fsengine.implies(h, b), null);
        }
    }

    // Lift the whole local heap if 'h' holds
    // Besides apply the single register update 'u' after lifting
    private void liftIfLocal(BoolExpr h,FSSingleRegUpdate u){
        int size = analysis.getSize();
        //lift the registers to global heap pointers
        for (int i = 0; i <= numRegLoc  ; i++){
            regUpG.put(i,fsengine.or(fsvar.getG(i),fsvar.getL(i)));
            regUpL.put(i,fsengine.mkFalse());
        }
        //Reset the local heap
        //Adrien: everybody is overwritten by 0 here
        for (int i = 0; i < analysis.getLocalHeapSize();i++) {
            regUpLHV.put(i,fsengine.mkBitVector(0, size));
            regUpLHH.put(i,fsengine.mkFalse());
            regUpLHL.put(i,fsengine.mkFalse());
            regUpLHG.put(i,fsengine.mkFalse());
            regUpLHF.put(i,fsengine.mkTrue());
        }
        //Update the registers with u if necessary
        if (u != null) u.apply(regUpV, regUpH, regUpL, regUpG);
        BoolExpr b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
        fsengine.implies(h,b);

        regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();
        regUpLHV.clear(); regUpLHH.clear(); regUpLHL.clear(); regUpLHG.clear(); regUpLHF.clear();

        //create the new global heap objects
        for (int allocationPoint : analysis.getAllocationPoints()){
                this.liftObject(h, allocationPoint);
        }
    }

    // For comparison instruction. Jump iff boolexpr is true
    private void cmpInstruction(BoolExpr boolexpr,Analysis analysis){
        int jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        BoolExpr h = fsengine.and(
                fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                boolexpr
                );
        BoolExpr b = fsengine.rPred(classIndex, methodIndex, jump, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
        fsengine.addRule(fsengine.implies(h, b), null);

        h = fsengine.and(
                h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                fsengine.not(boolexpr)
                );
        b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
        fsengine.addRule(fsengine.implies(h, b), null);
    }

    private void liftLi(){
        int size = analysis.getSize();
        int vecsize = numRegLoc + 1;
        for (int i = 0; i < vecsize; i++){
            BoolExpr hl = fsengine.mkFalse();
            BoolExpr hg = fsengine.mkFalse();
            for (int j = 0; j < analysis.getLocalHeapNumberEntries(); j++){
                int instanceNum = analysis.getInstanceNumFromReverse(j);
                hg = fsengine.or(
                        hg,
                        fsengine.and(
                                fsvar.getLHCF(fsengine.getOffset(instanceNum)),
                                fsengine.eq(fsvar.getV(i), fsengine.mkBitVector(instanceNum, size))
                                )
                        );
                hl = fsengine.or(
                        hl,
                        fsengine.and(
                                fsengine.not(fsvar.getLHCF(fsengine.getOffset(instanceNum))),
                                fsengine.eq(fsvar.getV(i), fsengine.mkBitVector(instanceNum, size))
                                )
                        );
            }
            regUpG.put(i, 
                    fsengine.or(
                            fsvar.getG(i),
                            fsengine.and(fsvar.getL(i),hg)
                            )
                    );
            regUpL.put(i, 
                    fsengine.and(fsvar.getL(i),hl)
                    );
        }
    }


    /*
     * implementations: set of implementations of the invoked method
     */
    private void invokeImpKnown(final int referenceReg, final Set<DalvikImplementation> implementations, final Boolean range){
        int size = analysis.getSize();
        //int referenceIntIndex = referenceString.hashCode();
        //String referenceIndex = Utils.Dec(referenceIntIndex);
        for (final DalvikImplementation di : implementations){
            int numRegCall = di.getMethod().getNumReg();
            int numArgCall = di.getMethod().getNumArg();
            if (analysis.isSink(di.getDalvikClass().getType().hashCode(), referenceIntIndex)){
                if (range){
                    addQueryRange(fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                            className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
                }
                else{
                    addQuery(fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                            className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
                }
            }
            for (final DalvikInstance instance: di.getInstances()){
                BoolExpr h = fsengine.and(
                        fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                        fsengine.eq(
                                fsvar.getV(referenceReg),
                                fsengine.mkBitVector(instance.hashCode(), size)
                                )
                        );
                regUpV = updateRegister(numRegCall, numArgCall,BitVecExpr.class, fsvar.getInjectV(fsvar), false);
                regUpH = updateRegister(numRegCall, numArgCall,BoolExpr.class, fsvar.getInjectH(fsvar), false);
                regUpL = updateRegister(numRegCall, numArgCall,BoolExpr.class, fsvar.getInjectL(fsvar), false);
                regUpG = updateRegister(numRegCall, numArgCall,BoolExpr.class, fsvar.getInjectG(fsvar), false);

                for (int i = 0; i < analysis.getLocalHeapSize(); i++){
                    regUpLHF.put(i, fsengine.mkFalse());
                }

                BoolExpr b = fsengine.rPredInvok(Integer.toString(di.getDalvikClass().getType().hashCode()), Integer.toString(di.getMethod().getName().hashCode()), 0,
                        regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numArgCall, numRegCall, size);

                fsengine.addRule(fsengine.implies(h, b), null);


                regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();
                regUpLHF.clear();
            }

            for (final DalvikInstance instance: di.getInstances()){
                BoolExpr subh = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                regUpV = updateResult(numRegCall, numArgCall,BitVecExpr.class, fsvar.getInjectV(fsvar), false);
                regUpH = updateResult(numRegCall, numArgCall,BoolExpr.class, fsvar.getInjectH(fsvar), false);
                regUpL = updateResult(numRegCall, numArgCall,BoolExpr.class, fsvar.getInjectL(fsvar), false);
                regUpG = updateResult(numRegCall, numArgCall,BoolExpr.class, fsvar.getInjectG(fsvar), false);
                regUpV.put(numArgCall, fsvar.getRez());
                regUpH.put(numArgCall, fsvar.getHrez());
                regUpL.put(numArgCall, fsvar.getLrez());
                regUpG.put(numArgCall, fsvar.getGrez());

                this.initializeLHC();

                BoolExpr h = fsengine.and(
                        subh,
                        fsengine.resPred(Integer.toString(di.getDalvikClass().getType().hashCode()), Integer.toString(referenceIntIndex),
                                regUpV, regUpH, regUpL, regUpG, regUpLHCV, regUpLHCH, regUpLHCL, regUpLHCG, regUpLHCF, numArgCall),
                        fsengine.eq(
                                fsvar.getV(referenceReg),
                                fsengine.mkBitVector(instance.hashCode(), size)
                                )
                        );

                regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();

                BoolExpr returnLabel = analysis.isSource(di.getDalvikClass().getType().hashCode(), referenceIntIndex) ? fsengine.mkTrue() : fsvar.getHrez();

                this.liftLi();

                if (callReturns) {
                    regUpV.put(numRegLoc, fsvar.getRez());
                    regUpH.put(numRegLoc, returnLabel);
                    regUpL.put(numRegLoc, fsvar.getLrez());
                    regUpG.put(numRegLoc, fsvar.getGrez());
                }

                for (int i = 0; i < analysis.getLocalHeapSize(); i++){
                    regUpLHCF.put(i, fsengine.or(fsvar.getLHF(i), fsvar.getLHCF(i)));
                }

                BoolExpr b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHCV, regUpLHCH, regUpLHCL, regUpLHCG, regUpLHCF, numParLoc, numRegLoc);

                fsengine.addRule(fsengine.implies(h, b), null);

                regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();
                regUpLHCF.clear();
            }
        }
    }

    private void getImplementationsSpecialCase(final boolean superBool){
        Boolean modRes = false;
        if ((referenceIntIndex == "execute(Ljava/lang/Runnable;)V".hashCode()) && (referenceClassIndex == "Ljava/util/concurrent/ExecutorService;".hashCode())){
            implementations = analysis.getImplementations("Ljava/lang/Runnable;".hashCode(), "run()V".hashCode());
            if (implementations == null){
                analysis.putNotImpl("Ljava/lang/Runnable;".hashCode(), "run()V".hashCode());
            }
            else{
                analysis.putImplemented("Ljava/lang/Runnable;".hashCode(), "run()V".hashCode(), implementations);
            }
            modRes = true;
        }
        if (referenceIntIndex == "start()V".hashCode()){
            implementations = analysis.getImplementations(referenceClassIndex, "run()V".hashCode());
            if (implementations == null){
                analysis.putNotImpl(referenceClassIndex, "run()V".hashCode());
            }
            else{
                analysis.putImplemented(referenceClassIndex, "run()V".hashCode(), implementations);
            }
            modRes = true;
        }
        if (referenceIntIndex == "execute([Ljava/lang/Object;)Landroid/os/AsyncTask;".hashCode()){
            implementations = analysis.getImplementations(referenceClassIndex, "doInBackground([Ljava/lang/Object;)Ljava/lang/Object;".hashCode());
            if (implementations == null){
                analysis.putNotImpl(referenceClassIndex, "doInBackground([Ljava/lang/Object;)Ljava/lang/Object;".hashCode());
            }
            else{
                analysis.putImplemented(referenceClassIndex, "doInBackground([Ljava/lang/Object;)Ljava/lang/Object;".hashCode(), implementations);
            }
            modRes = true;
        }

        if (!modRes){
            if (!superBool)
                implementations = analysis.getImplementations(referenceClassIndex, referenceIntIndex);
            else
                implementations = analysis.getSuperImplementations(referenceClassIndex, referenceIntIndex);
            if (implementations == null){
                analysis.putNotImpl(referenceClassIndex, referenceIntIndex);
            }
            else{
                analysis.putImplemented(referenceClassIndex, referenceIntIndex, implementations);
            }
        }
    }

    
    private void invokeImpNotKnown(BoolExpr returnLabel, int ci, int mi, Boolean range){
        int size = analysis.getSize();
        
        if (analysis.isSink(referenceClassIndex, referenceIntIndex)){
            if (range){
                addQueryRange(fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                        className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
            }else{
                addQuery(fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                        className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
            }
        }
        //if (processIntent(ci, mi, referenceClassIndex, referenceIntIndex, referenceString)){
        //    return;
        //}

        BoolExpr subh = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);


        if (returnType.hashCode() == "Ljava/lang/String;".hashCode()){
            regUpV.put(numRegLoc, fsvar.getF());
            regUpH.put(numRegLoc, returnLabel);
            regUpL.put(numRegLoc, fsengine.mkFalse());
            regUpG.put(numRegLoc, fsengine.mkTrue());
        } else {
            if ((returnType.charAt(0) != '[') && (returnType.charAt(returnType.length() -1) == ';' )){
                instanceNum = analysis.getInstNum(ci, mi, codeAddress);

                Map<Integer,Boolean> fields = analysis.getClassFields(returnType, instanceNum);

                if (fields != null)
                    for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                        BoolExpr h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                        BoolExpr b = fsengine.hPred(fsengine.mkBitVector(returnTypeInt, size),
                                fsvar.getFpp(), fsengine.mkBitVector(fieldN.getKey(), size),
                                fsvar.getVfp(), returnLabel, fsengine.mkBool(fieldN.getValue()));
                        fsengine.addRule(fsengine.implies(h, b), null);
                    }
                else{
                    BoolExpr h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                    BoolExpr b = fsengine.hPred(fsengine.mkBitVector(returnTypeInt, size),
                            fsvar.getFpp(), fsvar.getF(), fsvar.getVfp(), returnLabel, fsvar.getBf());
                    fsengine.addRule(fsengine.implies(h, b), null);
                }
                regUpV.put(numRegLoc, fsvar.getFpp());
                regUpH.put(numRegLoc, returnLabel);
                regUpL.put(numRegLoc, fsengine.mkFalse());
                regUpG.put(numRegLoc, fsengine.mkTrue());
            } else {
                switch (returnType){
                case "V": break;

                case "Z": case "B": case "S": case "C": case "I": case "J": case "F": case "D":
                    regUpV.put(numRegLoc, fsvar.getF());
                    regUpH.put(numRegLoc, returnLabel);
                    regUpL.put(numRegLoc, fsengine.mkFalse());
                    regUpG.put(numRegLoc, fsengine.mkFalse());
                    break;
                default: //array
                    instanceNum = analysis.getInstNum(ci, mi, codeAddress);
                    BoolExpr h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
                    BoolExpr b = fsengine.hPred(fsengine.mkBitVector(returnTypeInt, size),
                            fsengine.mkBitVector(instanceNum, size),
                            fsvar.getF(), fsvar.getBuf(), returnLabel, fsvar.getBf());
                    fsengine.addRule(fsengine.implies(h, b), null);
                    regUpV.put(numRegLoc, fsengine.mkBitVector(instanceNum, size));
                    regUpH.put(numRegLoc, returnLabel);
                    regUpL.put(numRegLoc, fsengine.mkFalse());
                    regUpG.put(numRegLoc, fsengine.mkTrue());
                }
            }
        }
        
        regUpH = highReg(range, regUpH);

        BoolExpr b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
        fsengine.addRule(fsengine.implies(subh, b), null);
    }
    
    
    private void staticInvokeImpKnown( Map<DalvikClass, DalvikMethod> staticDefinitions, Boolean range){
        int size = analysis.getSize();
        for (final Map.Entry<DalvikClass, DalvikMethod> definition: staticDefinitions.entrySet()){
            int numRegCall = definition.getValue().getNumReg();
            int numArgCall = definition.getValue().getNumArg();
            if (analysis.isSink(referenceClassIndex, referenceIntIndex)){
                if (range) {
                    addQuery(fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                            className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
                }else{
                    addQuery(fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc),
                            className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
                }
            }
            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();

            BoolExpr h = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);
            regUpV = updateRegister(numRegCall, numArgCall,BitVecExpr.class, fsvar.getInjectV(fsvar), false);
            regUpH = updateRegister(numRegCall, numArgCall,BoolExpr.class, fsvar.getInjectH(fsvar), false);
            regUpL = updateRegister(numRegCall, numArgCall,BoolExpr.class, fsvar.getInjectL(fsvar), false);
            regUpG = updateRegister(numRegCall, numArgCall,BoolExpr.class, fsvar.getInjectG(fsvar), false);

            for (int i = 0; i < analysis.getLocalHeapSize(); i++){
                regUpLHF.put(i, fsengine.mkFalse());
            }

            BoolExpr b = fsengine.rPredInvok(referenceStringClassIndex, referenceIndex, 0, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numArgCall, numRegCall, size);
            fsengine.addRule(fsengine.implies(h, b), null);

            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();
            regUpLHV.clear(); regUpLHH.clear(); regUpLHL.clear(); regUpLHG.clear(); regUpLHF.clear();



            BoolExpr subh = fsengine.rPred(classIndex, methodIndex, codeAddress, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, numParLoc, numRegLoc);

            regUpV = updateResult(numRegCall, numArgCall,BitVecExpr.class, fsvar.getInjectV(fsvar), false);
            regUpH = updateResult(numRegCall, numArgCall,BoolExpr.class, fsvar.getInjectH(fsvar), false);
            regUpL = updateResult(numRegCall, numArgCall,BoolExpr.class, fsvar.getInjectL(fsvar), false);
            regUpG = updateResult(numRegCall, numArgCall,BoolExpr.class, fsvar.getInjectG(fsvar), false);
            regUpV.put(numArgCall, fsvar.getRez());
            regUpH.put(numArgCall, fsvar.getHrez());
            regUpL.put(numArgCall, fsvar.getLrez());
            regUpG.put(numArgCall, fsvar.getGrez());

            this.initializeLHC();

            h = fsengine.and(
                    subh,
                    fsengine.resPred(referenceStringClassIndex, referenceIndex,
                            regUpV, regUpH, regUpL, regUpG, regUpLHCV, regUpLHCH, regUpLHCL, regUpLHCG, regUpLHCF, numArgCall)
                    );

            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();

            BoolExpr returnLabel = analysis.isSource(referenceClassIndex, referenceIntIndex) ? fsengine.mkTrue() : fsvar.getHrez();

            this.liftLi();

            if (callReturns) {
                regUpV.put(numRegLoc, fsvar.getRez());
                regUpH.put(numRegLoc, returnLabel);
                regUpL.put(numRegLoc, fsvar.getLrez());
                regUpG.put(numRegLoc, fsvar.getGrez());
            }

            for (int i = 0; i < analysis.getLocalHeapSize(); i++){
                regUpLHCF.put(i, fsengine.or(fsvar.getLHF(i), fsvar.getLHCF(i)));
            }

            b = fsengine.rPred(classIndex, methodIndex, nextCode, regUpV, regUpH, regUpL, regUpG, regUpLHCV, regUpLHCH, regUpLHCL, regUpLHCG, regUpLHCF, numParLoc, numRegLoc);

            fsengine.addRule(fsengine.implies(h, b), null);


            regUpV.clear(); regUpH.clear(); regUpL.clear(); regUpG.clear();
            regUpLHCF.clear();
        }
    }
}