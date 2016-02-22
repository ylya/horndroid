package analysis;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;

import Dalvik.DalvikClass;
import Dalvik.DalvikImplementation;
import Dalvik.DalvikInstance;
import Dalvik.DalvikMethod;
import Dalvik.Implementation;
import Dalvik.StubImplementation;
import debugging.QUERY_TYPE;
import horndroid.options;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
import util.CMPair;
import util.StringPair;
import util.Utils;
import util.Utils.CallType;
import z3.*;

public class InstructionAnalysis {
    final private Analysis analysis;
    final private Z3Engine z3engine;
    private Z3Variable var;
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

    private String returnType;


    private int referenceClassIndex;

    Map<Integer, BitVecExpr> regUpdate;
    Map<Integer, BoolExpr> regUpdateL;
    Map<Integer, BoolExpr> regUpdateB;

    BoolExpr h, b;


    public InstructionAnalysis(final Analysis analysis, final Instruction instruction, final DalvikClass dc, final DalvikMethod dm, final int codeAddress){
        this.analysis = analysis;
        this.z3engine = analysis.getZ3Engine();
        this.var = z3engine.getVars();
        this.instruction = instruction;
        this.dc = dc;
        this.c = dc.getType().hashCode();
        this.dm = dm;
        this.m = dm.getName().hashCode();
        this.codeAddress = codeAddress;
    }
    public void CreateHornClauses(options options, Set<StringPair> apkClassesMethods){
        final Dispatch dispatch = analysis.makeDispatch();
        DispatchResult dispatchResult = null;
        Integer staticFieldClassName;
        DalvikMethod dmc;
        final int size = analysis.getSize();
        int instanceNum;
        callReturns = false;
        referenceStringClass = null;
        returnType = null;
        referenceClassIndex = -1;
        referenceIntIndex = -1;
        referenceString = null;

        nextCode = codeAddress + instruction.getCodeUnits();

        Map<Integer, Boolean> fields = Collections.synchronizedMap(new HashMap <Integer, Boolean>());

        if (instruction instanceof ReferenceInstruction) {
            ReferenceInstruction referenceInstruction = (ReferenceInstruction)instruction;
            Reference reference = referenceInstruction.getReference();
            referenceString = Utils.getShortReferenceString(reference);
            if (reference instanceof FieldReference) {
                referenceStringClass = ((FieldReference) reference).getDefiningClass();
                referenceClassIndex = referenceStringClass.hashCode();
            }
            else
                if (reference instanceof MethodReference){
                    referenceStringClass = ((MethodReference) reference).getDefiningClass();
                    referenceClassIndex = referenceStringClass.hashCode();
                    returnType = ((MethodReference) reference).getReturnType();
                    if (returnType.equals((String) "V")) callReturns = false;
                    else callReturns = true;
                }
            referenceIntIndex = referenceString.hashCode();
        }
        methodName = dm.getName();
        className = dc.getType();
        methodIndex = Utils.Dec(m);
        classIndex = Utils.Dec(c);
        numRegLoc = dm.getNumReg();
        numParLoc = dm.getNumArg();
        regUpdate = new HashMap<>();
        regUpdateL = new HashMap<>();
        regUpdateB = new HashMap<>();    
        
        if ((options.debug) && apkClassesMethods.contains(new StringPair(className, methodName))
                && (c == "Landroid/app/Activity;".hashCode()) && (m == "onCreate(Landroid/os/Bundle;)V".hashCode())){
            BoolExpr h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
            //for (int i = 0; i < numRegLoc; i++){
            int i =0;
                BoolExpr h2 = z3engine.and(var.getL(i),h);
                BoolExpr h3 = z3engine.and(var.getB(i),h);
                Z3Query q1 = new Z3Query(h,i,QUERY_TYPE.STANDARD_REACH,className,methodName,Integer.toString(codeAddress));
                Z3Query q2 = new Z3Query(h2,i,QUERY_TYPE.STANDARD_HIGH,className,methodName,Integer.toString(codeAddress));
                Z3Query q3 = new Z3Query(h3,i,QUERY_TYPE.STANDARD_BLOCK,className,methodName,Integer.toString(codeAddress));
                z3engine.addQueryDebug(q1);
                if (analysis.getDebugNumber() >= 2){
                    z3engine.addQueryDebug(q2);
                }
                if (analysis.getDebugNumber() >= 3){
                    z3engine.addQueryDebug(q3);
                }
            //}
        }


        BoolExpr htob;
        switch (instruction.getOpcode()){
        case NOP:
        case MONITOR_ENTER://((short)0x1d, "monitor-enter", ReferenceType.NONE, Format.Format11x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case MONITOR_EXIT://((short)0x1e, "monitor-exit", ReferenceType.NONE, Format.Format11x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
            buildH();
            buildB();
            buildRule();
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
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getV(((TwoRegisterInstruction) instruction).getRegisterB()));
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction) instruction).getRegisterB()));
            regUpdateB.put(((OneRegisterInstruction) instruction).getRegisterA(), var.getB(((TwoRegisterInstruction) instruction).getRegisterB()));
            buildB();
            buildRule();
            break;//((short)0x09, "move-object/16", ReferenceType.NONE, Format.Format32x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case MOVE_RESULT://((short)0x0a, "move-result", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MOVE_RESULT_WIDE://((short)0x0b, "move-result-wide", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case MOVE_RESULT_OBJECT:
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getV(numRegLoc));
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(numRegLoc));
            regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getB(numRegLoc));
            buildB();
            buildRule();
            break;//((short)0x0c, "move-result-object", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case MOVE_EXCEPTION:
            int previousCode = 0;
            for (final Instruction ins: dm.getInstructions()){
                if ((previousCode + ins.getCodeUnits()) == codeAddress){
                    h = z3engine.rPred(classIndex, methodIndex, previousCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    b = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    buildRule();
                }
                previousCode += ins.getCodeUnits();
            }
            buildH();
            buildB();
            buildRule();

            break;//((short)0x0d, "move-exception", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case RETURN_VOID:
            break;
            //((short)0x0e, "return-void", ReferenceType.NONE, Format.Format10x),


        case RETURN://((short)0x0f, "return", ReferenceType.NONE, Format.Format11x),
        case RETURN_WIDE://((short)0x10, "return-wide", ReferenceType.NONE, Format.Format11x),
        case RETURN_OBJECT:
            buildH();
            regUpdate.put(numParLoc, var.getV(((OneRegisterInstruction) instruction).getRegisterA()));
            regUpdateL.put(numParLoc, var.getL(((OneRegisterInstruction) instruction).getRegisterA()));
            regUpdateB.put(numParLoc, var.getB(((OneRegisterInstruction) instruction).getRegisterA()));
            int count = 0;
            for (int i = numRegLoc + 1; i <= numRegLoc + numParLoc; i++){
                regUpdate.put(count, var.getV(i));
                regUpdateL.put(count, var.getL(i));
                regUpdateB.put(count, var.getB(i));
                count++;
            }
            b = z3engine.resPred(classIndex, methodIndex, regUpdate, regUpdateL, regUpdateB, numParLoc);
            buildRule();
            break;//((short)0x11, "return-object", ReferenceType.NONE, Format.Format11x),


        case CONST_4://((short)0x12, "const/4", ReferenceType.NONE, Format.Format11n, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CONST_16://((short)0x13, "const/16", ReferenceType.NONE, Format.Format21s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CONST://((short)0x14, "const", ReferenceType.NONE, Format.Format31i, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CONST_HIGH16://((short)0x15, "const/high16", ReferenceType.NONE, Format.Format21ih, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CONST_WIDE_16://((short)0x16, "const-wide/16", ReferenceType.NONE, Format.Format21s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case CONST_WIDE_32://((short)0x17, "const-wide/32", ReferenceType.NONE, Format.Format31i, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case CONST_WIDE://((short)0x18, "const-wide", ReferenceType.NONE, Format.Format51l, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case CONST_WIDE_HIGH16:
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size));
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
            regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
            buildB();
            buildRule();
            break;//((short)0x19, "const-wide/high16", ReferenceType.NONE, Format.Format21lh, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


        case CONST_STRING://((short)0x1a, "const-string", ReferenceType.STRING, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER, (short)0x1b),
        case CONST_STRING_JUMBO:
        case CONST_CLASS://break;//((short)0x1c, "const-class", ReferenceType.TYPE, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(referenceIntIndex, size));
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
            regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
            buildB();
            buildRule();
            break;//((short)0x1b, "const-string/jumbo", ReferenceType.STRING, Format.Format31c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case CHECK_CAST:
            h = z3engine.and(
                    z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                    z3engine.eq(
                            var.getB(((OneRegisterInstruction)instruction).getRegisterA()),
                            z3engine.mkTrue()
                            ),
                    z3engine.bvugt(
                            var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                            z3engine.mkBitVector(0, size)
                            )
                    );
            buildB();
            buildRule();
            break;//((short)0x1f, "check-cast", ReferenceType.TYPE, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case INSTANCE_OF:
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(0, size));
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
            regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
            buildB();
            buildRule();

            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(1, size));
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
            regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
            buildB();
            buildRule();
            break;//((short)0x20, "instance-of", ReferenceType.TYPE, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case ARRAY_LENGTH:
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getF());
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getLf());
            regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
            buildB();
            htob = z3engine.implies(h, b);
            z3engine.addRule(htob, null);
            break;//((short)0x21, "array-length", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case NEW_INSTANCE:
            if (referenceIntIndex == "Landroid/content/Intent;".hashCode()){
                buildH();
                buildB();
                buildRule();
                break;
            }

            instanceNum = analysis.getInstNum(c, m, codeAddress);

            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(instanceNum, size));
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
            regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkTrue());
            buildB();
            buildRule();

            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

            fields = analysis.getClassFields(referenceString, instanceNum);
            if (fields != null)
                for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                    buildH();
                    b = z3engine.hPred(z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(fieldN.getKey(), size),
                            z3engine.mkBitVector(0, size),
                            z3engine.mkFalse(),
                            z3engine.mkBool(fieldN.getValue()));
                    buildRule();
                } else {
                    buildH();
                    b = z3engine.hPred(z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            var.getF(), z3engine.mkBitVector(0, size),
                            z3engine.mkFalse(), var.getBf());
                    buildRule();
                }

            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

            if (analysis.hasStaticConstructor(referenceIntIndex)){
                int staticConstNum = "<clinit>()V".hashCode();
                dmc = analysis.getExactMethod(referenceIntIndex, staticConstNum);
                if (dmc != null){
                    buildH();
                    b = z3engine.rPred(Integer.toString(referenceIntIndex), Integer.toString(staticConstNum), 0, regUpdate, regUpdateL, regUpdateB,
                            dmc.getNumArg(), dmc.getNumReg());
                    buildRule();
                }
                else{
                    System.err.println("Static consturctor implementation not found for the class: " + referenceStringClass);
                }
            }
            break;//((short)0x22, "new-instance", ReferenceType.TYPE, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case NEW_ARRAY:
            instanceNum = analysis.getInstNum(c, m, codeAddress);
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(instanceNum, size));
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
            regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkTrue());
            buildB();
            buildRule();

            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

            if (analysis.optionArrays()){
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.bvuge(
                                z3engine.mkBitVector(0, size),
                                var.getF()
                                ),
                        z3engine.bvult(
                                var.getF(),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                                )
                        );
                b = z3engine.hPred(
                        z3engine.mkBitVector(referenceIntIndex, size),
                        z3engine.mkBitVector(instanceNum, size),
                        var.getF(), z3engine.mkBitVector(0, size),
                        z3engine.mkFalse(), z3engine.mkFalse()
                        );
            } else {
                buildH();
                b = z3engine.hPred(
                        z3engine.mkBitVector(referenceIntIndex, size),
                        z3engine.mkBitVector(instanceNum, size),
                        z3engine.mkBitVector(0, size),
                        z3engine.mkBitVector(0, size),
                        z3engine.mkFalse(), z3engine.mkFalse()
                        );
            }
            buildRule();
            break;//((short)0x23, "new-array", ReferenceType.TYPE, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case FILLED_NEW_ARRAY:
            FiveRegisterInstruction instructionA = (FiveRegisterInstruction)this.instruction;
            final int regCount = instructionA.getRegisterCount();
            instanceNum = analysis.getInstNum(c, m, codeAddress);
            buildH();
            regUpdate.put(numRegLoc, z3engine.mkBitVector(instanceNum, size));
            regUpdateL.put(numRegLoc, z3engine.mkFalse());
            regUpdateB.put(numRegLoc, z3engine.mkTrue());
            buildB();
            htob = z3engine.implies(h, b);
            z3engine.addRule(htob, null);
            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

            if (analysis.optionArrays()){
                switch(regCount){
                case 5:
                    buildH();
                    b = z3engine.hPred(z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(4, size),
                            var.getV(instructionA.getRegisterG()),
                            var.getL(instructionA.getRegisterG()),
                            var.getB(instructionA.getRegisterG()));
                    htob = z3engine.implies(h, b);
                    z3engine.addRule(htob, null);
                case 4:
                    buildH();
                    b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(3, size),
                            var.getV(instructionA.getRegisterF()),
                            var.getL(instructionA.getRegisterF()),
                            var.getB(instructionA.getRegisterF()));
                    htob = z3engine.implies(h, b);
                    z3engine.addRule(htob, null);
                case 3:
                    buildH();
                    b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(2, size),
                            var.getV(instructionA.getRegisterE()),
                            var.getL(instructionA.getRegisterE()),
                            var.getB(instructionA.getRegisterE()));
                    htob = z3engine.implies(h, b);
                    z3engine.addRule(htob, null);
                case 2:
                    buildH();
                    b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(1, size),
                            var.getV(instructionA.getRegisterD()),
                            var.getL(instructionA.getRegisterD()),
                            var.getB(instructionA.getRegisterD()));
                    htob = z3engine.implies(h, b);
                    z3engine.addRule(htob, null);
                case 1:
                    buildH();
                    b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(0, size),
                            var.getV(instructionA.getRegisterC()),
                            var.getL(instructionA.getRegisterC()),
                            var.getB(instructionA.getRegisterC()));
                    htob = z3engine.implies(h, b);
                    z3engine.addRule(htob, null);
                }
            } else {
                switch(regCount){
                case 5:
                    buildH();
                    b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(0, size),
                            var.getV(instructionA.getRegisterG()),
                            var.getL(instructionA.getRegisterG()),
                            var.getB(instructionA.getRegisterG()));
                    htob = z3engine.implies(h, b);
                    z3engine.addRule(htob, null);
                case 4:
                    buildH();
                    b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(0, size),
                            var.getV(instructionA.getRegisterF()),
                            var.getL(instructionA.getRegisterF()),
                            var.getB(instructionA.getRegisterF()));
                    htob = z3engine.implies(h, b);
                    z3engine.addRule(htob, null);
                case 3:
                    buildH();
                    b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(0, size),
                            var.getV(instructionA.getRegisterE()),
                            var.getL(instructionA.getRegisterE()),
                            var.getB(instructionA.getRegisterE()));
                    htob = z3engine.implies(h, b);
                    z3engine.addRule(htob, null);
                case 2:
                    buildH();
                    b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(0, size),
                            var.getV(instructionA.getRegisterD()),
                            var.getL(instructionA.getRegisterD()),
                            var.getB(instructionA.getRegisterD()));
                    htob = z3engine.implies(h, b);
                    z3engine.addRule(htob, null);
                case 1:
                    buildH();
                    b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(0, size),
                            var.getV(instructionA.getRegisterC()),
                            var.getL(instructionA.getRegisterC()),
                            var.getB(instructionA.getRegisterC()));
                    htob = z3engine.implies(h, b);
                    z3engine.addRule(htob, null);
                }
            }
            break;//((short)0x24, "filled-new-array", ReferenceType.TYPE, Format.Format35c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),


        case FILLED_NEW_ARRAY_RANGE:
            instanceNum = analysis.getInstNum(c, m, codeAddress);
            buildH();
            regUpdate.put(numRegLoc, z3engine.mkBitVector(instanceNum, size));
            regUpdateL.put(numRegLoc, z3engine.mkFalse());
            regUpdateB.put(numRegLoc, z3engine.mkTrue());
            buildB();
            buildRule();
            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

            RegisterRangeInstruction instructionAr = (RegisterRangeInstruction)this.instruction;
            int regCountr = instructionAr.getRegisterCount();
            int startRegister = instructionAr.getStartRegister();
            int endRegister   =   startRegister+regCountr-1;
            int cr = 0;

            for (int reg = startRegister; reg <= endRegister; reg++){
                buildH();
                b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                        z3engine.mkBitVector(instanceNum, size),
                        z3engine.mkBitVector(cr, size),
                        var.getV(reg), var.getL(reg), var.getB(reg));
                buildRule();
                if (analysis.optionArrays()) cr++;
            }
            break;//((short)0x25, "filled-new-array/range", ReferenceType.TYPE, Format.Format3rc, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),


        case FILL_ARRAY_DATA:
            for (final ArrayData ad: analysis.getArrayData()){
                List<Number> elements = ad.getElements(c, m, codeAddress + ((Instruction31t)instruction).getCodeOffset());
                if (elements != null){
                    int elNum = 0;
                    BoolExpr mainh = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    BoolExpr mainb = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    for (final Number element: elements){
                        if (analysis.optionArrays()){
                            z3engine.addRule(z3engine.implies(mainh, mainb), null);
                            h = z3engine.and(
                                    z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                    z3engine.hPred(var.getCn(), var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                            z3engine.mkBitVector(0, size), z3engine.mkBitVector(0, size),
                                            var.getLf(), var.getBf())
                                    );
                            b = z3engine.hPred(var.getCn(), var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                    z3engine.mkBitVector(elNum, size),
                                    z3engine.mkBitVector(element.intValue(), size),
                                    z3engine.mkFalse(),
                                    z3engine.mkFalse());
                            buildRule();
                        } else {
                            h = z3engine.and(
                                    z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                    z3engine.hPred(var.getCn(), var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                            z3engine.mkBitVector(0, size), z3engine.mkBitVector(0, size), var.getLf(), var.getBf())
                                    );
                            b = z3engine.hPred(var.getCn(), var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                    z3engine.mkBitVector(0, size),
                                    z3engine.mkBitVector(element.intValue(), size),
                                    z3engine.mkFalse(),
                                    z3engine.mkFalse());
                            buildRule();
                        }
                        elNum++;
                    }
                    break;
                }
            }
            break;//((short)0x26, "fill-array-data", ReferenceType.NONE, Format.Format31t, Opcode.CAN_CONTINUE),


        case THROW:
            buildH();
            buildB();
            buildRule();
            break;//((short)0x27, "throw", ReferenceType.NONE, Format.Format11x, Opcode.CAN_THROW),


        case GOTO://((short)0x28, "goto", ReferenceType.NONE, Format.Format10t),
        case GOTO_16://((short)0x29, "goto/16", ReferenceType.NONE, Format.Format20t),
        case GOTO_32:
            buildH();
            b = z3engine.rPred(classIndex, methodIndex, codeAddress + ((OffsetInstruction)instruction).getCodeOffset(), regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
            buildRule();
            break;//((short)0x2a, "goto/32", ReferenceType.NONE, Format.Format30t),


        case PACKED_SWITCH:
            BoolExpr negationString = z3engine.mkFalse();
            for (final PackedSwitch ps: analysis.getPackedSwitch()){
                List<Number> targets = ps.getTargets(c, m, codeAddress + ((Instruction31t)instruction).getCodeOffset());
                if (targets != null){
                    negationString = z3engine.mkTrue();
                    int t = 0;
                    final int payloadAddress = codeAddress + ((Instruction31t)instruction).getCodeOffset();
                    for (final Number target: targets){
                        try {
                            h = z3engine.and(
                                    z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                    z3engine.eq(
                                            var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                            z3engine.mkBitVector(ps.getFirstKey(c, m, payloadAddress) + t, size)
                                            )
                                    );
                            b = z3engine.rPred(classIndex, methodIndex, target.intValue(), regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                            buildRule();
                        } catch (Exception e) {
                            e.printStackTrace();
                        }

                        try {
                            negationString = z3engine.and(
                                    negationString,
                                    z3engine.eq(
                                            var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                            z3engine.mkBitVector(ps.getFirstKey(c, m, payloadAddress) + t, size)
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
            h = z3engine.and(
                    z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                    z3engine.not(negationString)
                    );
            buildB();
            buildRule();
            break;//((short)0x2b, "packed-switch", ReferenceType.NONE, Format.Format31t, Opcode.CAN_CONTINUE),


        case SPARSE_SWITCH:
            negationString = z3engine.mkFalse();
            for (final SparseSwitch ss: analysis.getSparseSwitch()){
                Map<Integer, Integer> targets = ss.getTargets(c, m, codeAddress + ((Instruction31t)instruction).getCodeOffset());
                if (targets != null){
                    negationString = z3engine.mkTrue();
                    for (final Map.Entry<Integer, Integer> target: targets.entrySet()){
                        h = z3engine.and(
                                z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                z3engine.eq(
                                        var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                        z3engine.mkBitVector(target.getKey(), size)
                                        )
                                );
                        b = z3engine.rPred(classIndex, methodIndex, target.getValue(),
                                regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        buildRule();

                        negationString = z3engine.and(
                                negationString,
                                z3engine.eq(
                                        var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                        z3engine.mkBitVector(target.getKey(), size)
                                        )
                                );
                    }
                    break;
                }
            }
            h = z3engine.and(
                    z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                    z3engine.not(negationString)
                    );
            buildB();
            buildRule();
            break;//((short)0x2c, "sparse-switch", ReferenceType.NONE, Format.Format31t, Opcode.CAN_CONTINUE),


        case CMPL_FLOAT://((short)0x2d, "cmpl-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CMPG_FLOAT://((short)0x2e, "cmpg-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CMPL_DOUBLE://((short)0x2f, "cmpl-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CMPG_DOUBLE://((short)0x30, "cmpg-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case CMP_LONG:
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                    (BitVecExpr) z3engine.ite(
                            z3engine.eq(        //if
                                    var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                    var.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                                    ),
                            z3engine.mkBitVector(0, size), //then
                            z3engine.ite( //else
                                    z3engine.bvugt(//sub-if
                                            var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                            var.getV(((ThreeRegisterInstruction) instruction).getRegisterC())
                                            ),
                                    z3engine.mkBitVector(1, size), //sub-then
                                    z3engine.mkBitVector(-1, size) //sub-else
                                    )
                            )
                    );
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                    z3engine.or(var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                            var.getL(((ThreeRegisterInstruction) instruction).getRegisterC())));
            buildB();
            buildRule();

            break;//((short)0x31, "cmp-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case IF_EQ:
            BoolExpr boolexpr = z3engine.eq(
                    var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x32, "if-eq", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


        case IF_NE:
            boolexpr = z3engine.not(z3engine.eq(
                    var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                    ));
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x32, "if-eq", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),
            
        case IF_LT:
            boolexpr = z3engine.bvult(
                    var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x34, "if-lt", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


        case IF_GE:
            boolexpr = z3engine.bvuge(
                    var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x35, "if-ge", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


        case IF_GT:
            boolexpr = z3engine.bvugt(
                    var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                    );
            this.cmpInstruction(boolexpr, analysis);
             break;//((short)0x36, "if-gt", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


        case IF_LE:
            boolexpr = z3engine.bvule(
                    var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x37, "if-le", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


        case IF_EQZ:
            boolexpr = z3engine.eq(
                    var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    z3engine.mkBitVector(0, size)
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x38, "if-eqz", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


        case IF_NEZ:
            boolexpr = z3engine.not(z3engine.eq(
                    var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    z3engine.mkBitVector(0, size)
                    ));
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x39, "if-nez", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


        case IF_LTZ:
            boolexpr = z3engine.bvult(
                    var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    z3engine.mkBitVector(0, size)
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x3a, "if-ltz", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


        case IF_GEZ:
            boolexpr = z3engine.bvuge(
                    var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    z3engine.mkBitVector(0, size)
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x3b, "if-gez", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


        case IF_GTZ:
            boolexpr = z3engine.bvugt(
                    var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    z3engine.mkBitVector(0, size)
                    );
            this.cmpInstruction(boolexpr, analysis);
            break;//((short)0x3c, "if-gtz", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


        case IF_LEZ:
            boolexpr = z3engine.bvule(
                    var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                    z3engine.mkBitVector(0, size)
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
                h = z3engine.and(
                        z3engine.hPred(var.getCn(), var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getV(((ThreeRegisterInstruction) instruction).getRegisterC()),
                                var.getVal(), var.getLval(), var.getBval()),
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc)
                        );

                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getVal());
                regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getLval());
                regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getBval());
                buildB();
            } else {
                h = z3engine.and(
                        z3engine.hPred(var.getCn(), var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                z3engine.mkBitVector(0, size),
                                var.getVal(), var.getLval(), var.getBval()),
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc)
                        );
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getVal());
                regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getLval());
                regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getBval());
                buildB();
            }
            buildRule();
            break;//((short)0x4a, "aget-short", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case APUT://((short)0x4b, "aput", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case APUT_WIDE://((short)0x4c, "aput-wide", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case APUT_OBJECT://((short)0x4d, "aput-object", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case APUT_BOOLEAN://((short)0x4e, "aput-boolean", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case APUT_BYTE://((short)0x4f, "aput-byte", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case APUT_CHAR://((short)0x50, "aput-char", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case APUT_SHORT:
            buildH();
            regUpdateL.put(((TwoRegisterInstruction)instruction).getRegisterB(),
                    z3engine.or(var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                            var.getL(((OneRegisterInstruction)instruction).getRegisterA()))
                    );
            buildB();
            buildRule();

            regUpdateL.clear();

            h = z3engine.and(
                    z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                    z3engine.hPred( var.getCn(), var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                            z3engine.mkBitVector(0, size),
                            z3engine.mkBitVector(0, size),
                            var.getLf(), var.getBf())
                    );
            b = z3engine.hPred( var.getCn(), var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    (analysis.optionArrays()
                            ? var.getV(((ThreeRegisterInstruction) instruction).getRegisterC())
                                    : z3engine.mkBitVector(0, size)),
                    var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    var.getL(((OneRegisterInstruction)instruction).getRegisterA()),
                    var.getB(((OneRegisterInstruction)instruction).getRegisterA())
                    );
            buildRule();
            break;
            //((short)0x51, "aput-short", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),


        case IGET://((short)0x52, "iget", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IGET_WIDE://((short)0x53, "iget-wide", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case IGET_OBJECT://((short)0x54, "iget-object", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IGET_BOOLEAN://((short)0x55, "iget-boolean", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IGET_BYTE://((short)0x56, "iget-byte", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IGET_CHAR://((short)0x57, "iget-char", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case IGET_SHORT:
            h = z3engine.and(
                    z3engine.hPred(var.getCn(), var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                            z3engine.mkBitVector(referenceIntIndex, size),
                            var.getVal(), var.getLval(), var.getBval()),
                    z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc)
                    );
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getVal());
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getLval());
            regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getBval());
            buildB();
            buildRule();

            break;//((short)0x58, "iget-short", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case IPUT://((short)0x59, "iput", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_WIDE://((short)0x5a, "iput-wide", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_OBJECT://((short)0x5b, "iput-object", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_BOOLEAN://((short)0x5c, "iput-boolean", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_BYTE://((short)0x5d, "iput-byte", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_CHAR://((short)0x5e, "iput-char", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case IPUT_SHORT:
            buildH();
            regUpdateL.put(((TwoRegisterInstruction)instruction).getRegisterB(),
                    z3engine.or(
                            var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                            var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                            )
                    );
            buildB();
            buildRule();

            regUpdateL.clear();

            h = z3engine.and(
                    z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                    z3engine.hPred(var.getCn(), var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                            var.getF(), z3engine.mkBitVector(0, size),
                            var.getLf(), var.getBf())
                    );
            b = z3engine.hPred(
                    var.getCn(), var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                    z3engine.mkBitVector(referenceIntIndex, size),
                    var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    var.getL(((OneRegisterInstruction)instruction).getRegisterA()),
                    var.getB(((OneRegisterInstruction)instruction).getRegisterA())
                    );
            buildRule();

            break;//((short)0x5f, "iput-short", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),


        case SGET://((short)0x60, "sget", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SGET_WIDE://((short)0x61, "sget-wide", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        case SGET_OBJECT://((short)0x62, "sget-object", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SGET_BOOLEAN://((short)0x63, "sget-boolean", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SGET_BYTE://((short)0x64, "sget-byte", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SGET_CHAR://((short)0x65, "sget-char", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case SGET_SHORT:
            staticFieldClassName = analysis.staticFieldLookup(referenceClassIndex, referenceIntIndex);
            if (staticFieldClassName == null){
                staticFieldClassName = referenceClassIndex;
            }

            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(0, size));
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
            regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getBf());
            buildB();
            buildRule();

            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

            h = z3engine.and(
                    z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                    z3engine.sPred(z3engine.mkInt(staticFieldClassName), z3engine.mkInt(referenceIntIndex),
                            var.getF(), var.getLf(), var.getBf())
                    );
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getF());
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getLf());
            regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getBf());
            buildB();
            buildRule();

            break;//((short)0x66, "sget-short", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        case SPUT://((short)0x67, "sput", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SPUT_WIDE://((short)0x68, "sput-wide", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SPUT_OBJECT://((short)0x69, "sput-object", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SPUT_BOOLEAN://((short)0x6a, "sput-boolean", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SPUT_BYTE://((short)0x6b, "sput-byte", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SPUT_CHAR://((short)0x6c, "sput-char", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case SPUT_SHORT:
            staticFieldClassName = analysis.staticFieldLookup(referenceClassIndex, referenceIntIndex);
            if (staticFieldClassName == null){
                staticFieldClassName = referenceClassIndex;
            }
            buildH();
            buildB();
            buildRule();

            buildH();
            b = z3engine.sPred(z3engine.mkInt(staticFieldClassName), z3engine.mkInt(referenceIntIndex),
                    var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                    var.getL(((OneRegisterInstruction)instruction).getRegisterA()),
                    var.getB(((OneRegisterInstruction)instruction).getRegisterA()));
            buildRule();
            break;//((short)0x6d, "sput-short", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        case INVOKE_SUPER:
        {
            dispatchResult = dispatch.dispatch(referenceClassIndex, referenceIntIndex, referenceStringClass, referenceString, CallType.SUPER);
            int referenceReg = ((FiveRegisterInstruction)this.instruction).getRegisterC();
            if (dispatchResult != null){
                this.invoke(dispatchResult, false, referenceReg);
            }
            else{
                this.invokeNotKnown(false);
            }
        }
        break;
        
        case INVOKE_SUPER_RANGE:
        {
            dispatchResult = dispatch.dispatch(referenceClassIndex, referenceIntIndex, referenceStringClass, referenceString, CallType.SUPER);
            int referenceReg = ((RegisterRangeInstruction)this.instruction).getStartRegister();
            if (dispatchResult != null){
                this.invoke(dispatchResult, true, referenceReg);
            }
            else{
                this.invokeNotKnown(true);
            }
        }
        break;
            /*
             * Should be handled like invoke_virtual:
             * "invoke-interface is used to invoke an interface method, that is, 
             * on an object whose concrete class isn't known, using a method_id 
             * that refers to an interface."
             * Source : https://source.android.com/devices/tech/dalvik/dalvik-bytecode.html
             */
        case INVOKE_INTERFACE:
        {
            dispatchResult = dispatch.dispatch(referenceClassIndex, referenceIntIndex, referenceStringClass, referenceString, CallType.INTERFACE);
            int referenceReg = ((FiveRegisterInstruction)this.instruction).getRegisterC();
            if (dispatchResult != null){
                this.invoke(dispatchResult, false, referenceReg);
            }
            else{
                this.invokeNotKnown(false);
            }
        }
        break;
        case INVOKE_INTERFACE_RANGE:
        {
            dispatchResult = dispatch.dispatch(referenceClassIndex, referenceIntIndex, referenceStringClass, referenceString, CallType.INTERFACE);
            int referenceReg = ((RegisterRangeInstruction)this.instruction).getStartRegister();
            if (dispatchResult != null){
                this.invoke(dispatchResult, true, referenceReg);
            }
            else{
                this.invokeNotKnown(true);
            }
        }
        break;
        case INVOKE_VIRTUAL:
        {
            dispatchResult = dispatch.dispatch(referenceClassIndex, referenceIntIndex, referenceStringClass, referenceString, CallType.VIRTUAL);
            int referenceReg = ((FiveRegisterInstruction)this.instruction).getRegisterC();
            if (dispatchResult != null){
                this.invoke(dispatchResult, false, referenceReg);
            }
            else{
                this.invokeNotKnown(false);
            }
        }
        break;
        case INVOKE_VIRTUAL_RANGE:
        {
            dispatchResult = dispatch.dispatch(referenceClassIndex, referenceIntIndex, referenceStringClass, referenceString, CallType.VIRTUAL);
            int referenceReg = ((RegisterRangeInstruction)this.instruction).getStartRegister();
            if (dispatchResult != null){
                this.invoke(dispatchResult, true, referenceReg);
            }
            else{
                this.invokeNotKnown(true);
            }
        }
        break;
        case INVOKE_DIRECT:
            dispatchResult = dispatch.dispatch(referenceClassIndex, referenceIntIndex, referenceStringClass, referenceString, CallType.DIRECT);
            if (dispatchResult != null){
                this.invoke(dispatchResult, false, null);
            }
            else{
                this.invokeNotKnown(false);
            }
        break;
        case INVOKE_DIRECT_RANGE:
            dispatchResult = dispatch.dispatch(referenceClassIndex, referenceIntIndex, referenceStringClass, referenceString, CallType.DIRECT);
            if (dispatchResult != null){
                this.invoke(dispatchResult, true, null);
            }
            else{
                this.invokeNotKnown(true);
            }
        break;
        case INVOKE_STATIC:
        {
            dispatchResult = dispatch.dispatch(referenceClassIndex, referenceIntIndex, referenceStringClass, referenceString, CallType.STATIC);
            if (dispatchResult != null){
                this.invoke(dispatchResult, false, null);
            }
            else{
                this.invokeNotKnown(false);
            }
        }
        break;

        case INVOKE_STATIC_RANGE:
        {
            dispatchResult = dispatch.dispatch(referenceClassIndex, referenceIntIndex, referenceStringClass, referenceString, CallType.STATIC);
            if (dispatchResult != null){
                this.invoke(dispatchResult, true, null);
            }
            else{
                this.invokeNotKnown(true);
            }
        }
        break;

        case NEG_INT://((short)0x7b, "neg-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),

            BitVecExpr bv = z3engine.bvneg(regB(), Type.INT);
            this.unaryOp(bv);
            break;
        case NEG_LONG://((short)0x7d, "neg-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvneg(regB(), Type.LONG);
            this.unaryOp(bv);
            break;
        case NEG_FLOAT://((short)0x7f, "neg-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvneg(regB(), Type.FLOAT);
            this.unaryOp(bv);
            break;
        case NEG_DOUBLE:
            bv = z3engine.bvneg(regB(), Type.DOUBLE);
            this.unaryOp(bv);
            break;//((short)0x80, "neg-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


        case NOT_INT://((short)0x7c, "not-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvnot(regB(), Type.INT);
            this.unaryOp(bv);
            break;
        case NOT_LONG://((short)0x7e, "not-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvnot(regB(), Type.LONG);
            this.unaryOp(bv);
            break;

        case INT_TO_LONG://((short)0x81, "int-to-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.toLong(z3engine.toInt((regB())));
            this.unaryOp(bv);
            break;
        case INT_TO_FLOAT://((short)0x82, "int-to-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.uOpIntToFloat(regB());
            this.unaryOp(bv);
            break;
        case INT_TO_DOUBLE://((short)0x83, "int-to-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.uOpIntToDouble(regB());
            this.unaryOp(bv);
            break;
        case LONG_TO_INT://((short)0x84, "long-to-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.toLong(z3engine.toInt((regB())));
            this.unaryOp(bv);
            break;
        case LONG_TO_FLOAT://((short)0x85, "long-to-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.uOpLongToFloat(regB());
            this.unaryOp(bv);
            break;
        case LONG_TO_DOUBLE://((short)0x86, "long-to-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.uOpLongToDouble(regB());
            this.unaryOp(bv);
            break;
        case FLOAT_TO_INT://((short)0x87, "float-to-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.floatRoundToInt(regB());
            this.unaryOp(bv);
            break;
        case FLOAT_TO_LONG://((short)0x88, "float-to-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.floatRoundToLong(regB());
            this.unaryOp(bv);
            break;
        case FLOAT_TO_DOUBLE://((short)0x89, "float-to-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.floatToDouble(regB());
            this.unaryOp(bv);
            break;        
        case DOUBLE_TO_INT://((short)0x8a, "double-to-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.doubleRoundToInt(regB());
            this.unaryOp(bv);
            break;
        case DOUBLE_TO_LONG://((short)0x8b, "double-to-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.floatRoundToLong(regB());
            this.unaryOp(bv);
            break;
        case DOUBLE_TO_FLOAT://((short)0x8c, "double-to-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.doubleToFloat(regB());
            this.unaryOp(bv);
            break;
        case INT_TO_BYTE://((short)0x8d, "int-to-byte", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.intToByte(regB());
            this.unaryOp(bv);
            break;
        case INT_TO_CHAR://((short)0x8e, "int-to-char", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.intToChar(regB());
            this.unaryOp(bv);
            break;
        case INT_TO_SHORT://((short)0x8f, "int-to-short", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.intToShort(regB());
            this.unaryOp(bv);
            break;

        case ADD_INT://((short)0x90, "add-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvadd(
                    regB(),
                    regC(),Type.INT
                    );
            this.binaryOpC(bv);
            break;
        case ADD_LONG://((short)0x9b, "add-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvadd(
                    regB(),
                    regC(),Type.LONG
                    );
            this.binaryOpC(bv);
            break;
        case ADD_FLOAT://((short)0xa6, "add-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvadd(
                    regB(),
                    regC(),Type.FLOAT
                    );
            this.binaryOpC(bv);
            break;
        case ADD_DOUBLE://((short)0xab, "add-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvadd(
                    regB(),
                    regC(),Type.DOUBLE
                    );
            this.binaryOpC(bv);
            break;

        case RSUB_INT://((short)0xd1, "rsub-int", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvsub(
                    regB(),
                    regA(), Type.INT
                    );
            this.binaryOp(bv);
            break;
        case SUB_INT://((short)0x91, "sub-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvsub(
                    regB(),
                    regC(), Type.INT
                    );
            this.binaryOpC(bv);
            break;
        case SUB_LONG://((short)0x9c, "sub-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvsub(
                    regB(),
                    regC(), Type.LONG
                    );
            this.binaryOpC(bv);
            break;
        case SUB_FLOAT://((short)0xa7, "sub-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvsub(
                    regB(),
                    regC(), Type.FLOAT
                    );
            this.binaryOpC(bv);
            break;
        case SUB_DOUBLE://((short)0xac, "sub-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvsub(
                    regB(),
                    regC(), Type.DOUBLE
                    );
            this.binaryOpC(bv);
            break;

        case MUL_INT://((short)0x92, "mul-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvmul(
                    regB(),
                    regC(),Type.INT
                    );
            this.binaryOpC(bv);
            break;
        case MUL_LONG://((short)0x9d, "mul-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvmul(
                    regB(),
                    regC(),Type.LONG
                    );
            this.binaryOpC(bv);
            break;
        case MUL_FLOAT://((short)0xa8, "mul-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvmul(
                    regB(),
                    regC(),Type.FLOAT
                    );
            this.binaryOpC(bv);
            break;
        case MUL_DOUBLE://((short)0xad, "mul-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvmul(
                    regB(),
                    regC(),Type.DOUBLE
                    );
            this.binaryOpC(bv);
            break;

        case DIV_INT://((short)0x93, "div-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvdiv(
                    regB(),
                    regC(),Type.INT
                    );
            this.binaryOpC(bv);
            break;
        case DIV_LONG://((short)0x9e, "div-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvdiv(
                    regB(),
                    regC(),Type.LONG
                    );
            this.binaryOpC(bv);
            break;
        case DIV_FLOAT://((short)0xa9, "div-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvdiv(
                    regB(),
                    regC(),Type.FLOAT
                    );
            this.binaryOpC(bv);
            break;
        case DIV_DOUBLE://((short)0xae, "div-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvdiv(
                    regB(),
                    regC(),Type.DOUBLE
                    );
            this.binaryOpC(bv);
            break;

        case REM_INT://((short)0x94, "rem-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvrem(
                    regB(),
                    regC(),Type.INT
                    );
            this.binaryOpC(bv);
            break;
        case REM_LONG://((short)0x9f, "rem-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvrem(
                    regB(),
                    regC(),Type.LONG
                    );
            this.binaryOpC(bv);
            break;
        case REM_FLOAT://((short)0xaa, "rem-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvrem(
                    regB(),
                    regC(),Type.FLOAT
                    );
            this.binaryOpC(bv);
            break;
        case REM_DOUBLE://((short)0xaf, "rem-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvrem(
                    regB(),
                    regC(),Type.DOUBLE
                    );
            this.binaryOpC(bv);
            break;

        case AND_INT://((short)0x95, "and-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvand(
                    regB(),
                    regC(),Type.INT
                    );
            this.binaryOpC(bv);
            break;
        case AND_LONG://((short)0xa0, "and-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvand(
                    regB(),
                    regC(),Type.LONG
                    );
            this.binaryOpC(bv);
            break;

        case OR_INT://((short)0x96, "or-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvor(
                    regB(),
                    regC(),Type.INT
                    );
            this.binaryOpC(bv);
            break;
        case OR_LONG://((short)0xa1, "or-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvor(
                    regB(),
                    regC(),Type.LONG
                    );
            this.binaryOpC(bv);
            break;

        case XOR_INT://((short)0x97, "xor-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvxor(
                    regB(),
                    regC(),Type.INT
                    );
            this.binaryOpC(bv);
            break;
        case XOR_LONG://((short)0xa2, "xor-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvxor(
                    regB(),
                    regC(),Type.LONG
                    );
            this.binaryOpC(bv);
            break;

        case SHL_INT://((short)0x98, "shl-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvshl(
                    regB(),
                    regC(), Type.INT
                    );
            this.binaryOpC(bv);
            break;
        case SHL_LONG://((short)0xa3, "shl-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvshl(
                    regB(),
                    regC(), Type.LONG
                    );
            this.binaryOpC(bv);
            break;

        case SHR_LONG://((short)0xa4, "shr-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvashr(
                    regB(),
                    regC(), Type.LONG
                    );
            this.binaryOpC(bv);
            break;
        case SHR_INT://((short)0x99, "shr-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvashr(
                    regB(),
                    regC(), Type.INT
                    );
            this.binaryOpC(bv);
            break;

        case USHR_INT://((short)0x9a, "ushr-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvlshr(
                    regB(),
                    regC(), Type.INT
                    );
            this.binaryOpC(bv);
            break;
        case USHR_LONG://((short)0xa5, "ushr-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvlshr(
                    regB(),
                    regC(), Type.LONG
                    );
            this.binaryOpC(bv);
            break;

        case ADD_INT_2ADDR://((short)0xb0, "add-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvadd(
                    regA(),
                    regB(),Type.INT
                    );
            this.binaryOp(bv);
            break;
        case ADD_LONG_2ADDR://((short)0xc0, "and-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvadd(
                    regA(),
                    regB(),Type.LONG
                    );
            this.binaryOp(bv);
            break;
        case ADD_FLOAT_2ADDR://((short)0xc6, "add-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvadd(
                    regA(),
                    regB(),Type.FLOAT
                    );
            this.binaryOp(bv);
            break;        
        case ADD_DOUBLE_2ADDR://((short)0xcb, "add-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvadd(
                    regA(),
                    regB(),Type.DOUBLE
                    );
            this.binaryOp(bv);
            break;

        case SUB_INT_2ADDR://((short)0xb1, "sub-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvsub(
                    regA(),
                    regB(),Type.INT
                    );
            this.binaryOp(bv);
            break;
        case SUB_LONG_2ADDR://((short)0xbc, "sub-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvsub(
                    regA(),
                    regB(),Type.LONG
                    );
            this.binaryOp(bv);
            break;
        case SUB_FLOAT_2ADDR://((short)0xc7, "sub-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvsub(
                    regA(),
                    regB(),Type.FLOAT
                    );
            this.binaryOp(bv);
            break;
        case SUB_DOUBLE_2ADDR://((short)0xcc, "sub-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvsub(
                    regA(),
                    regB(),Type.DOUBLE
                    );
            this.binaryOp(bv);
            break;

        case MUL_INT_2ADDR://((short)0xb2, "mul-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvmul(
                    regA(),
                    regB(),Type.INT
                    );
            this.binaryOp(bv);
            break;
        case MUL_LONG_2ADDR://((short)0xbd, "mul-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvmul(
                    regA(),
                    regB(),Type.LONG
                    );
            this.binaryOp(bv);
            break;
        case MUL_FLOAT_2ADDR://((short)0xc8, "mul-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvmul(
                    regA(),
                    regB(),Type.FLOAT
                    );
            this.binaryOp(bv);
            break;
        case MUL_DOUBLE_2ADDR://((short)0xcd, "mul-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvmul(
                    regA(),
                    regB(),Type.DOUBLE
                    );
            this.binaryOp(bv);
            break;

        case DIV_INT_2ADDR://((short)0xb3, "div-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvdiv(
                    regA(),
                    regB(),Type.INT
                    );
            this.binaryOp(bv);
            break;
        case DIV_LONG_2ADDR://((short)0xbe, "div-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvdiv(
                    regA(),
                    regB(),Type.LONG
                    );
            this.binaryOp(bv);
            break;
        case DIV_FLOAT_2ADDR://((short)0xc9, "div-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvdiv(
                    regA(),
                    regB(),Type.FLOAT
                    );
            this.binaryOp(bv);
            break;
        case DIV_DOUBLE_2ADDR://((short)0xce, "div-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvdiv(
                    regA(),
                    regB(),Type.DOUBLE
                    );
            this.binaryOp(bv);
            break;

        case REM_INT_2ADDR://((short)0xb4, "rem-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvrem(
                    regA(),
                    regB(),Type.INT
                    );
            this.binaryOp(bv);
            break;
        case REM_LONG_2ADDR://((short)0xbf, "rem-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvrem(
                    regA(),
                    regB(),Type.LONG
                    );
            this.binaryOp(bv);
            break;
        case REM_FLOAT_2ADDR://((short)0xca, "rem-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvrem(
                    regA(),
                    regB(),Type.FLOAT
                    );
            this.binaryOp(bv);
            break;
        case REM_DOUBLE_2ADDR://((short)0xcf, "rem-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvrem(
                    regA(),
                    regB(),Type.DOUBLE
                    );
            this.binaryOp(bv);
            break;

        case AND_INT_2ADDR://((short)0xb5, "and-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvand(
                    regA(),
                    regB(), Type.INT
                    );
            this.binaryOp(bv);
            break;
        case AND_LONG_2ADDR://((short)0xbb, "add-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvand(
                    regA(),
                    regB(), Type.LONG
                    );
            this.binaryOp(bv);
            break;

        case OR_INT_2ADDR://((short)0xb6, "or-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvor(
                    regA(),
                    regB(), Type.INT
                    );
            this.binaryOp(bv);
            break;
        case OR_LONG_2ADDR://((short)0xc1, "or-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvor(
                    regA(),
                    regB(), Type.LONG
                    );
            this.binaryOp(bv);
            break;

        case XOR_INT_2ADDR://((short)0xb7, "xor-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvxor(
                    regA(),
                    regB(), Type.INT
                    );
            this.binaryOp(bv);
            break;
        case XOR_LONG_2ADDR://((short)0xc2, "xor-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvxor(
                    regA(),
                    regB(), Type.LONG
                    );
            this.binaryOp(bv);
            break;

        case SHL_INT_2ADDR://((short)0xb8, "shl-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvshl(
                    regA(),
                    regB(), Type.INT
                    );
            this.binaryOp(bv);
            break;
        case SHL_LONG_2ADDR://((short)0xc3, "shl-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvshl(
                    regA(),
                    regB(), Type.LONG
                    );
            this.binaryOp(bv);
            break;

        case SHR_INT_2ADDR://((short)0xb9, "shr-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvashr(
                    regA(),
                    regB(), Type.INT
                    );
            this.binaryOp(bv);
            break;
        case SHR_LONG_2ADDR://((short)0xc4, "shr-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvashr(
                    regA(),
                    regB(), Type.LONG
                    );
            this.binaryOp(bv);
            break;

        case USHR_INT_2ADDR://((short)0xba, "ushr-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvlshr(
                    regA(),
                    regB(), Type.INT
                    );
            this.binaryOp(bv);
            break;
        case USHR_LONG_2ADDR://((short)0xc5, "ushr-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
            bv = z3engine.bvlshr(
                    regA(),
                    regB(), Type.LONG
                    );
            this.binaryOp(bv);
            break;

        case ADD_INT_LIT16://((short)0xd0, "add-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case ADD_INT_LIT8://((short)0xd8, "add-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvadd(
                    regB(),
                    z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                    Type.INT);
            this.unaryOp(bv);
            break;

        case MUL_INT_LIT16://((short)0xd2, "mul-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case MUL_INT_LIT8://((short)0xda, "mul-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvmul(
                    regB(),
                    z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                    Type.INT);
            this.unaryOp(bv);
            break;

        case DIV_INT_LIT16://((short)0xd3, "div-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case DIV_INT_LIT8://((short)0xdb, "div-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvdiv(
                    regB(),
                    z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                    Type.INT);
            this.unaryOp(bv);
            break;

        case REM_INT_LIT16://((short)0xd4, "rem-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case REM_INT_LIT8://((short)0xdc, "rem-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvrem(
                    regB(),
                    z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                    Type.INT);
            this.unaryOp(bv);
            break;

        case AND_INT_LIT16://((short)0xd5, "and-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case AND_INT_LIT8://((short)0xdd, "and-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvand(
                    regB(),
                    z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                    Type.INT);
            this.unaryOp(bv);
            break;

        case OR_INT_LIT16://((short)0xd6, "or-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case OR_INT_LIT8://((short)0xde, "or-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvor(
                    regB(),
                    z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                    Type.INT);
            this.unaryOp(bv);
            break;

        case XOR_INT_LIT16://((short)0xd7, "xor-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        case XOR_INT_LIT8://((short)0xdf, "xor-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvxor(
                    regB(),
                    z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                    Type.INT);
            this.unaryOp(bv);
            break;

        case RSUB_INT_LIT8://((short)0xd9, "rsub-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvsub(
                    z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                    regB(),
                    Type.INT);
            this.unaryOp(bv);
            break;

        case SHL_INT_LIT8://((short)0xe0, "shl-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvshl(
                    regB(),
                    z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                    Type.INT);
            this.unaryOp(bv);
            break;

        case SHR_INT_LIT8://((short)0xe1, "shr-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvashr(
                    regB(),
                    z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                    Type.INT);
            this.unaryOp(bv);
            break;

        case USHR_INT_LIT8://((short)0xe2, "ushr-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
            bv = z3engine.bvlshr(
                    regB(),
                    z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                    Type.INT);
            this.unaryOp(bv);
            break;

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
            throw new RuntimeException("InstructionAnalysis: not supported "+ instruction.getOpcode().toString());
        case PACKED_SWITCH_PAYLOAD:
            break;//((short)0x100, "packed-switch-payload", ReferenceType.NONE, Format.PackedSwitchPayload, 0),
        case SPARSE_SWITCH_PAYLOAD:
            break;//((short)0x200, "sparse-switch-payload", ReferenceType.NONE, Format.SparseSwitchPayload, 0),
        case ARRAY_PAYLOAD:
            break;//((short)0x300, "array-payload", ReferenceType.NONE, Format.ArrayPayload, 0);
        default:
            throw new RuntimeException("InstructionAnalysis: not supported " + instruction.getOpcode().toString());
        }
    }

//    private void stubInvoke(StubImplementation implementation, boolean range, int referenceReg, boolean virtualDispatch) {
//        Map<CMPair, CMPair> dependentInvoke = implementation.getDependentInvokation();
//        for (DalvikImplementation di : implementation.getDalvikImp()){
//            CMPair cmp = new CMPair(di.getDalvikClass().getType().hashCode(),di.getMethod().getName().hashCode());
//            if (!dependentInvoke.values().contains(cmp)){
//                this.invoke(di, range, referenceReg, virtualDispatch);
//            }else{
//                DalvikImplementation from = implementation.getDalvikImpByID(dependentInvoke.get(cmp).hashCode());
//                this.directDalvikInvokeAux(z3engine.mkTrue(), di, range, from);
//            }
//        }
//    }
//    
    private BitVecExpr regA(){
        return var.getV(((OneRegisterInstruction)instruction).getRegisterA());
    }

    private BitVecExpr regB(){
        return var.getV(((TwoRegisterInstruction)instruction).getRegisterB());
    }

    private BitVecExpr regC(){
        return var.getV(((ThreeRegisterInstruction)instruction).getRegisterC());
    }
    
    // For comparison instruction. Jump iff boolexpr is true
    private void cmpInstruction(BoolExpr boolexpr,Analysis analysis){
        int jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
        buildH();
        h = z3engine.and(h,boolexpr);
        b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
        buildRule();

        buildH();
        h = z3engine.and(h,z3engine.not(boolexpr));
        buildB();
        buildRule();
    }



    private void unaryOp(BitVecExpr bv){
        if (analysis.getSize() == 64){
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),bv);
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
            buildB();
            buildRule();
        }else{
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),var.getVal());
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
            buildB();
            buildRule();            
        }

    }

    private void binaryOp(BitVecExpr bv){
        if (analysis.getSize() == 64){
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),bv);
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                    z3engine.or(
                            var.getL(((TwoRegisterInstruction)instruction).getRegisterA()),
                            var.getL(((TwoRegisterInstruction)instruction).getRegisterB())));
            buildB();
            buildRule();
        }else{
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),var.getVal());
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                    z3engine.or(
                            var.getL(((TwoRegisterInstruction)instruction).getRegisterA()),
                            var.getL(((TwoRegisterInstruction)instruction).getRegisterB())));
            buildB();
            buildRule();
        }
    }

    private void binaryOpC(BitVecExpr bv){
        if (analysis.getSize() == 64){
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),bv);
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                    z3engine.or(
                            var.getL(((ThreeRegisterInstruction)instruction).getRegisterB()),
                            var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())));
            buildB();
            buildRule();
        }else{
            buildH();
            regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),var.getVal());
            regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                    z3engine.or(
                            var.getL(((ThreeRegisterInstruction)instruction).getRegisterB()),
                            var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())));
            buildB();
            buildRule();
        }
    }

    private void addQueryRange(BoolExpr p, String className, String methodName, String pc, String sinkName, final boolean verboseOption){
        RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
        int regCount = instruction.getRegisterCount();
        int startRegister = instruction.getStartRegister();
        int endRegister = startRegister+regCount-1;

        for (int reg = startRegister; reg <= endRegister; reg++ ){
            BoolExpr q = z3engine.and(
                    p,
                    z3engine.eq(var.getL(reg), z3engine.mkTrue())
                    );
            String d = "Test if register " + Integer.toString(reg) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            z3engine.addQuery(new Z3Query(q, d, verboseOption, className, methodName, pc, sinkName));
        }
    }

    private void addQuery(BoolExpr p, String className, String methodName, String pc, String sinkName, final boolean verboseResults){
        FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
        final int regCount = instruction.getRegisterCount();

        switch (regCount) {
        case 5:
            BoolExpr q5 = z3engine.and(
                    p,
                    z3engine.eq(var.getL(instruction.getRegisterG()), z3engine.mkTrue())
                    );
            String d5 = "Test if register " + Integer.toString(instruction.getRegisterG()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            z3engine.addQuery(new Z3Query(q5, d5, verboseResults, className, methodName, pc, sinkName));
        case 4:
            BoolExpr q4 = z3engine.and(
                    p,
                    z3engine.eq(var.getL(instruction.getRegisterF()), z3engine.mkTrue())
                    );
            String d4 = "Test if register " + Integer.toString(instruction.getRegisterF()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            z3engine.addQuery(new Z3Query(q4, d4, verboseResults, className, methodName, pc, sinkName));
        case 3:
            BoolExpr q3 = z3engine.and(
                    p,
                    z3engine.eq(var.getL(instruction.getRegisterE()), z3engine.mkTrue())
                    );
            String d3 = "Test if register " + Integer.toString(instruction.getRegisterE()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            z3engine.addQuery(new Z3Query(q3, d3, verboseResults, className, methodName, pc, sinkName));
        case 2:
            BoolExpr q2 = z3engine.and(
                    p,
                    z3engine.eq(var.getL(instruction.getRegisterD()), z3engine.mkTrue())
                    );
            String d2 = "Test if register " + Integer.toString(instruction.getRegisterD()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            z3engine.addQuery(new Z3Query(q2, d2, verboseResults, className, methodName, pc, sinkName));
        case 1:
            BoolExpr q1 = z3engine.and(
                    p,
                    z3engine.eq(var.getL(instruction.getRegisterC()), z3engine.mkTrue())
                    );
            String d1 = "Test if register " + Integer.toString(instruction.getRegisterC()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            z3engine.addQuery(new Z3Query(q1, d1, verboseResults, className, methodName, pc, sinkName));
        }
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


    //TODO
    private boolean processIntent(final Z3Engine z3engine, final int ci, final int mi, final int numParLoc, final int numRegLoc, final int nextCode, final int c, final int m, final String shortMethodName,
            final int size){
        
        //http://developer.android.com/reference/android/content/Intent.html
        
        BoolExpr h2, b2;
        Map<Integer, Boolean> fields = Collections.synchronizedMap(new HashMap <Integer, Boolean>());

       /* 
        * Specify the exact class to be called (for an explicit intent)
        */
        
        if  (c == ("Landroid/content/Intent;".hashCode()) &&
                ("setComponent(Landroid/content/ComponentName;)Landroid/content/Intent;".hashCode()) == m){
            if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerC, registerD;
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                    registerD = ((FiveRegisterInstruction) instruction).getRegisterD();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                    registerD = ((RegisterRangeInstruction) instruction).getStartRegister() + 1;
                }
                /*
                 * HI predicate is the same as H but with a smaller arity as it does not contain any field information 
                 * (we are field-incensitive for intents).
                 * When intent is created the exact class might not be known, it is specified then by calling setComponent method,
                 * it replaces the original class ("cn") by the one spcified in the method call (registerD)
                 */
                h2 = z3engine.and(
                        z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.hiPred(
                                var.getCn(), var.getV(registerC), var.getVal(), var.getLf(), var.getBf())
                        );
                b2 = z3engine.hiPred(
                        var.getV(registerD), var.getV(registerC), var.getVal(), var.getLf(), var.getBf());
               
                
                z3engine.addRule(z3engine.implies(h2, b2), null);
                /*
                 * the result of the setComponent will be a new version of the intent which is stored in the same registerC, where it was before
                 */
                h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(registerC, var.getV(registerC));
                regUpdateL.put(registerC, var.getL(registerC));
                regUpdateB.put(registerC, var.getB(registerC));
                b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                
               
                buildRule();
                
                
                return true;
            }
        }
       /*
        * Create a new Intent (class is known, in Ljava/lang/Class;) aka (newintent r_d c')_pp
        */
        if  (c == ("Landroid/content/Intent;".hashCode()) &&
                ("<init>(Landroid/content/Context;Ljava/lang/Class;)V".hashCode()) == m){
            final int instanceNum = analysis.getInstNum(ci, mi, codeAddress);
            if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerC, //r_d
                    registerE; //c'
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                    registerE = ((FiveRegisterInstruction) instruction).getRegisterE();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                    registerE = ((RegisterRangeInstruction) instruction).getStartRegister() + 2;
                }
               /*
                * Put a new intent instance of the type c' on the heap
                */
                h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b2 = z3engine.hiPred(
                        var.getV(registerE), z3engine.mkBitVector(instanceNum, size), z3engine.mkBitVector(0, size), z3engine.mkFalse(), z3engine.mkFalse());
                z3engine.addRule(z3engine.implies(h2, b2), null);
                /*
                 * Put a refence to the intent into r_d
                 */
                h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(registerC, z3engine.mkBitVector(instanceNum, size));
                regUpdateL.put(registerC, z3engine.mkFalse());
                regUpdateB.put(registerC, z3engine.mkTrue());
                b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                buildRule();

                regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
                
               /*
                * Put default values for all fields of the intent
                */
                fields = analysis.getClassFields("Landroid/content/Intent;", instanceNum);
                if (fields != null)
                    for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                        BoolExpr h12 = z3engine.rPred(Utils.Dec(ci), Utils.Dec(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        BoolExpr b12 = z3engine.hPred(
                                z3engine.mkBitVector("Landroid/content/Intent;".hashCode(), size),
                                z3engine.mkBitVector(instanceNum, size), z3engine.mkBitVector(fieldN.getKey(), size),
                                z3engine.mkBitVector(0, size), z3engine.mkFalse(), z3engine.mkBool(fieldN.getValue()));
                        z3engine.addRule(z3engine.implies(h12, b12), null);
                    }

                return true;
            }
        }
        //TODO: this case looks like the previous one - merge?
        /*
         * Create a new Intent (class is known, in Ljava/lang/String;) aka (newintent r_d c')_pp
         */
        if  (c == ("Landroid/content/Intent;".hashCode()) &&
                ("<init>(Ljava/lang/String;)V".hashCode()) == m){
            final int instanceNum = analysis.getInstNum(ci, mi, codeAddress);
            if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerC, //r_d
                    registerE; //c'
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                    registerE = ((FiveRegisterInstruction) instruction).getRegisterE();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                    registerE = ((RegisterRangeInstruction) instruction).getStartRegister() + 2;
                }
                /*
                 * Put a new intent instance of the type c' on the heap
                 */
                h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b2 = z3engine.hiPred(
                        var.getV(registerE), z3engine.mkBitVector(instanceNum, size), z3engine.mkBitVector(0, size), z3engine.mkFalse(), z3engine.mkFalse());
                z3engine.addRule(z3engine.implies(h2, b2), null);
               /*
                * Put a refence to the intent into r_d
                */
                h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(registerC, z3engine.mkBitVector(instanceNum, size));
                regUpdateL.put(registerC, z3engine.mkFalse());
                regUpdateB.put(registerC, z3engine.mkTrue());
                b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                buildRule();

                regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
                /*
                 * Put default values for all fields of the intent
                 */
                fields = analysis.getClassFields("Landroid/content/Intent;", instanceNum);
                if (fields != null)
                    for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                        BoolExpr h12 = z3engine.rPred(Utils.Dec(ci), Utils.Dec(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        BoolExpr b12 = z3engine.hPred(
                                z3engine.mkBitVector("Landroid/content/Intent;".hashCode(), size), z3engine.mkBitVector(instanceNum, size), z3engine.mkBitVector(fieldN.getKey(), size), z3engine.mkBitVector(0, size), z3engine.mkFalse(), z3engine.mkBool(fieldN.getValue()));
                        z3engine.addRule(z3engine.implies(h12, b12), null);
                    }

                return true;
            }
        }
        /*
         * Create a new Intent (class is not known, unbounded variable f) aka (newintent r_d ?)_pp
         */
        if  (c == ("Landroid/content/Intent;".hashCode()) &&
                ("<init>()V".hashCode()) == m){
            final int instanceNum = analysis.getInstNum(ci, mi, codeAddress);
            if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerC; // r_d
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                }
                /*
                 * Put a new intent instance of the unknown type f on the heap
                 */
                h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b2 = z3engine.hiPred(
                        var.getF(), z3engine.mkBitVector(instanceNum, size),
                        z3engine.mkBitVector(0, size), z3engine.mkFalse(), z3engine.mkFalse());
                z3engine.addRule(z3engine.implies(h2, b2), null);
                /*
                 * Put a refence to the intent into r_d
                 */
                h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(registerC, z3engine.mkBitVector(instanceNum, size));
                regUpdateL.put(registerC, z3engine.mkFalse());
                regUpdateB.put(registerC, z3engine.mkTrue());
                b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                buildRule();

                regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
                /*
                 * Put default values for all fields of the intent
                 */
                fields = analysis.getClassFields("Landroid/content/Intent;", instanceNum);
                if (fields != null)
                    for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                        BoolExpr h12 = z3engine.rPred(Utils.Dec(ci), Utils.Dec(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        BoolExpr b12 = z3engine.hPred(
                                z3engine.mkBitVector("Landroid/content/Intent;".hashCode(), size), z3engine.mkBitVector(instanceNum, size), z3engine.mkBitVector(fieldN.getKey(), size), z3engine.mkBitVector(0, size), z3engine.mkFalse(), z3engine.mkBool(fieldN.getValue()));
                        z3engine.addRule(z3engine.implies(h12, b12), null);
                    }
                return true;
            }
        }
       /*
        * Start an activity referenced in specified register aka (start-activity r_i)_pp
        */
        if (("startActivity(Landroid/content/Intent;)V".hashCode() == m) || shortMethodName.contains("startActivityForResult")){
            if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerD; // r_i
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerD = ((FiveRegisterInstruction) instruction).getRegisterD();
                } else {
                    registerD = ((RegisterRangeInstruction) instruction).getStartRegister() + 1;
                }
               /*
                * Take a refence from r_i (R) and if there is an intent on the heap refeneced by it (HI) start an activity I
                */
                h = z3engine.and(
                        z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.hiPred(
                                var.getCn(), var.getV(registerD), var.getVal(), var.getLf(), var.getBf())
                        );
                b = z3engine.iPred(
                        var.getCn(), z3engine.mkBitVector(c, size), var.getVal(), var.getLf(), var.getBf());
                buildRule();
                // Go to the next pc with the intact register values
                h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h2, b2), null);
                
                
               /*
                * Act rule interpretation
                * In the first rule instead of using I predicate we use the same premice as was used for it's inference
                //TODO: this is sound due to the logical cut, but we better check 
                */
               /*
                * before cup, creates a rule for HI(in(c), _) inference
                */
                BoolExpr h3 = z3engine.and(
                        z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.hiPred(
                                var.getCn(), var.getV(registerD), var.getVal(), var.getLf(), var.getBf())
                        );
                //TODO: there are better ways of computing fresh in(c)
                final BitVecExpr inC = z3engine.mkBitVector((Utils.Dec(registerD) + Utils.Dec(c)).hashCode(), size); // in(c) = r_i + c
                BoolExpr b3 = z3engine.hiPred(var.getCn(), inC, var.getVal(), var.getLf(), var.getBf());
                z3engine.addRule(z3engine.implies(h3, b3), null);
               /*
                * after cup, addd default values to the (parent) and (intent) fields of the current intent as specified in the rule
                * (finished) field is ommitied due to the fact that it's values is oveapproximated in the anlysis and treated alwaus as {true, false}
                */
                BoolExpr h4 = z3engine.and(
                        z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.hiPred(
                                var.getCn(), var.getV(registerD), var.getVal(), var.getLf(), var.getBf())
                        );
                BoolExpr b4 = z3engine.hPred(
                        var.getCn(), var.getCn() , z3engine.mkBitVector("parent".hashCode(), size), z3engine.mkBitVector(c, size),
                        z3engine.mkFalse(), z3engine.mkTrue());
                z3engine.addRule(z3engine.implies(h4, b4), null);

                BoolExpr h5 = z3engine.and(
                        z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.hiPred(var.getCn(), var.getV(registerD), var.getVal(), var.getLf(), var.getBf())
                        );
                BoolExpr b5 = z3engine.hPred(var.getCn(), var.getCn(),
                        z3engine.mkBitVector("intent".hashCode(), size), inC,
                        z3engine.mkFalse(), z3engine.mkTrue());
                z3engine.addRule(z3engine.implies(h5, b5), null);

                return true;
            }
        }
       /*
        * Put informaton in the intent object with refence in r_i aka (put-extra r_i r_k k_j)_pp
        * note: r_k is ignore, vield insensitivity
        */
        if (shortMethodName.contains((String) "putExtra") && c == ("Landroid/content/Intent;".hashCode())){
            if (this.instruction instanceof FiveRegisterInstruction){
                FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
                h = z3engine.and(
                        z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.hiPred(
                                var.getCn(), 
                                var.getV(instruction.getRegisterC()), // r_i 
                                var.getVal(), var.getLf(), var.getBf())
                        );
                b = z3engine.hiPred(var.getCn(), var.getV(instruction.getRegisterC()),
                        var.getV(instruction.getRegisterE()), // r_j
                        var.getL(instruction.getRegisterE()), 
                        var.getB(instruction.getRegisterE()));
                buildRule();
               /*
                * Go to the next pc with the same register values, but raise the label of r_i to the (l_i join l_j)
                */
                h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdateL.put(instruction.getRegisterC(), z3engine.or(var.getL(instruction.getRegisterC()), var.getL(instruction.getRegisterE())));
                b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h2, b2), null);
                return true;
            }
        }
       /*
        * getAction returns a string which shows what to do with a data recieved from the intent
        * e.g.,     ACTION_VIEW content://contacts/people/1 -- Display information about the person whose identifier is "1".
        *           ACTION_DIAL content://contacts/people/1 -- Display the phone dialer with the person filled in.
        * as the reselut is always public (originates from the specification), we explicitly specify for it the low security label here
        */
        if  (c == ("Landroid/content/Intent;".hashCode()) &&
                ("getAction()Ljava/lang/String;".hashCode()) == m){
            h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
            regUpdate.put(numRegLoc, var.getVal());
            regUpdateL.put(numRegLoc, z3engine.mkFalse());
            regUpdateB.put(numRegLoc, var.getBf()); //TODO: should it be true? Strings are objects
            b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
            buildRule();
            return true;
        }
       /*
        * Get informaton from the intent object with refence in r_i aka (get-extra r_i r_k \tau)_pp
        * some of get are sources
        */
        //TODO: Might be getters missing
        if (shortMethodName.contains((String) "get") && c == ("Landroid/content/Intent;".hashCode())){
            //////////////////////////////////////////////////////
            //TODO: delete this?
            if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {
            //////////////////////////////////////////////////////
                int registerC; // r_i
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                }

                if (analysis.isSourceBis(c, m)){
                    // if getter is source - get the (top?) high value
                    //TODO; Check why hig value is top and not extracted from the heap, might be a mistake
                    h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    regUpdate.put(numRegLoc, var.getVal());
                    regUpdateL.put(numRegLoc, z3engine.mkTrue());
                    regUpdateB.put(numRegLoc, var.getBf());
                    b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    buildRule();
                } else {
                    // getter is not source - extract values from all fields of the intent, r_k ignored, field-insensitivity
                    h = z3engine.and(
                            z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                            z3engine.hiPred(
                                    var.getCn(), var.getV(registerC), var.getVal(), var.getLf(), var.getBf())
                            );
                    regUpdate.put(numRegLoc, var.getVal());
                    regUpdateL.put(numRegLoc, var.getLf());
                    regUpdateB.put(numRegLoc, var.getBf());
                    b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    buildRule();
                }
            } 
            /////////////////////////
            //TODO: the else branch seems to make no sence, as the function call is either FiveRegister or Range isntruction
            else {
                if (analysis.isSourceBis(c, m)){
                    h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    regUpdate.put(numRegLoc, var.getVal());
                    regUpdateL.put(numRegLoc, z3engine.mkTrue());
                    regUpdateB.put(numRegLoc, var.getBf());
                    b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    buildRule();
                } else {
                    h = z3engine.and(
                            z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                            z3engine.hiPred(var.getCn(), var.getF(), var.getVal(), var.getLf(), var.getBf())
                            );
                    regUpdate.put(numRegLoc, var.getVal());
                    regUpdateL.put(numRegLoc, var.getLf());
                    regUpdateB.put(numRegLoc, var.getBf());
                    b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    buildRule();
                }
                
             //////////////////////////
                return true;
            }
        }
       /*
        * Stores the registerE as the result of the current activity to the field (result)
        * This value will be afteron extracted by Res rule
        */
        if (m ==  "setResult(ILandroid/content/Intent;)V".hashCode()){
            if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerE; // reference to resulting intent
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerE = ((FiveRegisterInstruction) instruction).getRegisterE();
                } else {
                    registerE = ((RegisterRangeInstruction) instruction).getStartRegister() + 2;
                }

                h = z3engine.and(
                        z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.hiPred(
                                var.getCn(), var.getV(registerE), var.getVal(), var.getLf(), var.getBf())
                        );
                b = z3engine.hPred(
                        z3engine.mkBitVector(c, size), z3engine.mkBitVector(c, size), z3engine.mkBitVector("result".hashCode(), size),
                        var.getV(registerE), var.getL(registerE), var.getB(registerE));
                buildRule();
                
                //Progate the register values to the next pc
                h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h2, b2), null);
                return true;
            }
        }
       /*
        * Return the intent that started this activity
        //TODO: Currently, we check that the current activity was started and return as a result (top)
                This should be sound, but it is not precise enough
        */
        if (m ==  "getIntent()Landroid/content/Intent;".hashCode()){
            h = z3engine.and(
                    z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                    z3engine.hPred(z3engine.mkBitVector(c, size), z3engine.mkBitVector(c, size), 
                            z3engine.mkBitVector("intent".hashCode(), size), var.getVal(), var.getLf(), var.getBf())
                    );
            regUpdate.put(numRegLoc, var.getVal());
            regUpdateL.put(numRegLoc, var.getLf());
            regUpdateB.put(numRegLoc, var.getBf());
            b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
            buildRule();
            return true;
        }
        return false;
    }
    
    
    /*
     * Advances pc with a top values for the return value (if exists)
     */
    private void invokeNotKnown(final Boolean range){
        buildH();
        //put top value to the return register
        regUpdate.put(numRegLoc, var.getF());
        regUpdateL.put(numRegLoc, var.getLf());
        regUpdateB.put(numRegLoc, var.getBf());
        buildB();
        buildRule();
    }
    /*
     * Direct invocation of a method, whose implementation is either a dalvik implementation
     * or a stub
     */
    private void invoke(final DispatchResult dispatchResult,
            final Boolean range, final Integer referenceReg) {
        for (final DalvikImplementation di : dispatchResult
                .getImplementations()) {
            if (referenceReg != null) {
                this.virtualDalvikInvoke(di, referenceReg, range, dispatchResult.getInstances());
            } else {
                this.directDalvikInvoke(z3engine.mkTrue(), di, range);
            }
        }
    }
    
    /*
     * This method is used to performe virtual dispatch:
     * the generated Horn clauses check that the callee is of the correct class before invoking
     */
    private void virtualDalvikInvoke(final DalvikImplementation di, final int referenceReg, final Boolean range, final HashSet<DalvikInstance> instances){
        for (final DalvikInstance instance: instances){
            //TODO: this can be improved by adding a predicate Class and
            // doing Class(instance.hashcode(),classID) and Class(referenceReg,classID) 
            // so has to share all this between invocation
            BoolExpr precond = z3engine.eq(
                            var.getV(referenceReg),
                            z3engine.mkBitVector(instance.hashCode(), analysis.getSize())
                            );
            directDalvikInvoke(precond, di, range);
        }
    }
    
    /*
     * Invocation of a Dalvik Implementation with precondition 'precond'
     */
    private void directDalvikInvoke(BoolExpr precond, DalvikImplementation di, Boolean range){
        directDalvikInvokeAux(precond, di, range);
    }
    
    /*
     * if dependentInv is not null then the first argument of di's invocation is the result of dependentInv invocation
     */
    private void directDalvikInvokeAux(BoolExpr precond, DalvikImplementation di, Boolean range){
        int size = analysis.getSize();

        DalvikClass cInvoked = di.getDalvikClass();
        DalvikMethod mInvoked = di.getMethod();
        int numRegCall = mInvoked.getNumReg();
        int numArgCall = mInvoked.getNumArg();

        String classInvokedStringName = Integer.toString(cInvoked.getType().hashCode());
        String methodInvokedStringName = Integer.toString(mInvoked.getName().hashCode());
        if (analysis.isSink(className,methodName,cInvoked.getType().hashCode(), mInvoked.getName().hashCode())){
            if (range) {
                addQueryRange(z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        className, methodName, Integer.toString(codeAddress), mInvoked.getName(), analysis.optionVerbose());
            }else{
                addQuery(z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        className, methodName, Integer.toString(codeAddress), mInvoked.getName(), analysis.optionVerbose());
            }
        }

        regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

        buildH();        
//        if (dependentInv != null){
//            /*
//             * We get the Res predicate of the dependent invocation. 
//             * Observe that the call context of the dependent invocation is the same than the call context of the invoked method.
//             */
//            int numRegDependent = dependentInv.getMethod().getNumReg();
//            int numArgDependent = dependentInv.getMethod().getNumArg();
//
//            String classDependentStringName = Integer.toString(dependentInv.getDalvikClass().getType().hashCode());
//            String methodDependentStringName = Integer.toString(dependentInv.getMethod().getName().hashCode());
//
//            regUpdate = updateResult(numRegDependent, numArgDependent, BitVecExpr.class, var.getInjectV(var), range);
//            regUpdateL = updateResult(numRegDependent, numArgDependent, BoolExpr.class, var.getInjectL(var), range);
//            regUpdateB = updateResult(numRegDependent, numArgDependent, BoolExpr.class, var.getInjectB(var), range);
//            
//            // getRez, getLRez and getBRez contain the result of the dependent call
//            regUpdate.put(numArgDependent, var.getRez());
//            regUpdateL.put(numArgDependent, var.getLrez());
//            regUpdateB.put(numArgDependent, var.getBrez());
//
//            BoolExpr depExpr = z3engine.resPred(classDependentStringName, methodDependentStringName, regUpdate, regUpdateL, regUpdateB, numArgDependent);
//            
//            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
//            
//            h = z3engine.and(h,precond,depExpr);
//        }else{
//            h = z3engine.and(h,precond);
//        }
//        
//        
//        regUpdate = updateRegister(numRegCall, numArgCall, BitVecExpr.class, var.getInjectV(var), range);
//        regUpdateL = updateRegister(numRegCall, numArgCall, BoolExpr.class, var.getInjectL(var), range);
//        regUpdateB = updateRegister(numRegCall, numArgCall, BoolExpr.class, var.getInjectB(var), range);
//        
//        if (dependentInv != null){
//            //We use the result of the dependent call as the first argument of the invoked method
//            regUpdate.put(numRegCall - numArgCall, var.getRez());
//            regUpdateL.put(numRegCall - numArgCall, var.getLrez());
//            regUpdateB.put(numRegCall - numArgCall, var.getBrez());
//        }
        
        b = z3engine.rInvokePred(classInvokedStringName, methodInvokedStringName, 0, regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, size);
        buildRule();

        regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

        if (callReturns){
            BoolExpr subh = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
            regUpdate = updateResult(numRegCall, numArgCall, BitVecExpr.class, var.getInjectV(var), range);
            regUpdateL = updateResult(numRegCall, numArgCall, BoolExpr.class, var.getInjectL(var), range);
            regUpdateB = updateResult(numRegCall, numArgCall, BoolExpr.class, var.getInjectB(var), range);
            regUpdate.put(numArgCall, var.getRez());
            regUpdateL.put(numArgCall, var.getLrez());
            regUpdateB.put(numArgCall, var.getBrez());
            h = z3engine.and(
                    precond,
                    subh,
                    z3engine.resPred(classInvokedStringName, methodInvokedStringName, regUpdate, regUpdateL, regUpdateB, numArgCall)
                    );
            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

            BoolExpr returnLabel = analysis.isSource(className,methodName,cInvoked.getType().hashCode(), mInvoked.getName().hashCode()) ? z3engine.mkTrue() : var.getLrez();
            regUpdate.put(numRegLoc, var.getRez());
            regUpdateL.put(numRegLoc, returnLabel);
            regUpdateB.put(numRegLoc, var.getBrez());

        } else {
            buildH();
            h = z3engine.and(precond,h);
        }

        buildB();
        buildRule();
        regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

    }

    private void buildH(){
        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
    }
    private void buildB(){
        b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
    }
    private void buildRule(){
        z3engine.addRule(z3engine.implies(h, b), null);
    }

}
