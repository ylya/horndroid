package analysis;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;

import debugging.QUERY_TYPE;
import horndroid.options;

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

public class InstructionAnalysis {
	final private Analysis analysis;
    final private Z3Engine z3engine;
	final private Instruction instruction;
	final private DalvikClass dc;
	final private DalvikMethod dm;
	private final int c;
	private final int m;
	final private int codeAddress;
	public InstructionAnalysis(final Analysis analysis, final Instruction instruction, final DalvikClass dc, final DalvikMethod dm, final int codeAddress){
		this.analysis = analysis;
        this.z3engine = analysis.getZ3Engine();
		this.instruction = instruction;
		this.dc = dc;
		this.c = dc.getType().hashCode();
		this.dm = dm;
		this.m = dm.getName().hashCode();
		this.codeAddress = codeAddress;
	}
	public void CreateHornClauses(options options){
		boolean modRes;
		Integer staticFieldClassName;
		Set<DalvikImplementation> implementations = Collections.newSetFromMap(new ConcurrentHashMap<DalvikImplementation, Boolean>());
		Map<DalvikClass, DalvikMethod> staticDefinitions = new ConcurrentHashMap<DalvikClass, DalvikMethod>();
		DalvikMethod dmc;
		final int size = analysis.getSize();
        final Z3Engine z3engine = analysis.getZ3Engine();
        final Z3Variable var = z3engine.getVars();
		BoolExpr negationString = null;
	  	int jump = 0;
    	int referenceReg;
    	boolean isDefined;
    	int instanceNum;
    	boolean callReturns = false;
    	int numRegCall;
    	int numArgCall;
    	String referenceStringClass = null;
    	String referenceStringClassIndex = null;
    	String returnType = null;
    	int returnTypeInt = 0;
    	int referenceClassIndex = -1;
    	int referenceIntIndex = -1;
        Opcode opcode = instruction.getOpcode();
        String referenceString = null;
        String referenceIndex = null;
        int nextCode = codeAddress + instruction.getCodeUnits();

        Map<Integer, Boolean> fields = Collections.synchronizedMap(new HashMap <Integer, Boolean>());

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
        String methodName = dm.getName();
        String className = dc.getType();
        int mi = m;
        String methodIndex = Utils.Dec(mi);
        int ci = c;
        String classIndex = Utils.Dec(ci);
        final int numRegLoc = dm.getNumReg();
        final int numParLoc = dm.getNumArg();
        BoolExpr returnLabel;
        Map<Integer, BitVecExpr> regUpdate = new HashMap<>();
        Map<Integer, BoolExpr> regUpdateL = new HashMap<>();
        Map<Integer, BoolExpr> regUpdateB = new HashMap<>();
        
        if (options.debug && methodName.contains("onCreate")){
            BoolExpr h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
            for (int i = 0; i < numRegLoc; i++){
                BoolExpr h1 = h;
                BoolExpr h2 = z3engine.and(var.getL(i),h);
                BoolExpr h3 = z3engine.and(var.getB(i),h);
                Z3Query q1 = new Z3Query(h1,i,QUERY_TYPE.STANDARD_REACH,className,methodName,Integer.toString(codeAddress));
                Z3Query q2 = new Z3Query(h2,i,QUERY_TYPE.STANDARD_HIGH,className,methodName,Integer.toString(codeAddress));
                Z3Query q3 = new Z3Query(h3,i,QUERY_TYPE.STANDARD_BLOCK,className,methodName,Integer.toString(codeAddress));
                z3engine.addQueryDebug(q1);
                z3engine.addQueryDebug(q2);
                z3engine.addQueryDebug(q3);
                }
         }

        
        BoolExpr h, b, htob;
        switch (opcode){
        	case NOP:
           	case MONITOR_ENTER://((short)0x1d, "monitor-enter", ReferenceType.NONE, Format.Format11x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case MONITOR_EXIT://((short)0x1e, "monitor-exit", ReferenceType.NONE, Format.Format11x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
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
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getV(((TwoRegisterInstruction) instruction).getRegisterB()));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction) instruction).getRegisterB()));
        		regUpdateB.put(((OneRegisterInstruction) instruction).getRegisterA(), var.getB(((TwoRegisterInstruction) instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
                break;//((short)0x09, "move-object/16", ReferenceType.NONE, Format.Format32x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case MOVE_RESULT://((short)0x0a, "move-result", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MOVE_RESULT_WIDE://((short)0x0b, "move-result-wide", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case MOVE_RESULT_OBJECT:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getV(numRegLoc));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(numRegLoc));
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getB(numRegLoc));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x0c, "move-result-object", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case MOVE_EXCEPTION:
        		int previousCode = 0;
        		for (final Instruction ins: dm.getInstructions()){
        			if ((previousCode + ins.getCodeUnits()) == codeAddress){
        				h = z3engine.rPred(classIndex, methodIndex, previousCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                		b = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        z3engine.addRule(z3engine.implies(h, b), null);
        			}
        			previousCode += ins.getCodeUnits();
        		}
        		h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
        		b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0x0d, "move-exception", ReferenceType.NONE, Format.Format11x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case RETURN_VOID:
    			break;
        		//((short)0x0e, "return-void", ReferenceType.NONE, Format.Format10x),


            case RETURN://((short)0x0f, "return", ReferenceType.NONE, Format.Format11x),
        	case RETURN_WIDE://((short)0x10, "return-wide", ReferenceType.NONE, Format.Format11x),
        	case RETURN_OBJECT:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
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
                z3engine.addRule(z3engine.implies(h, b), null);
                break;//((short)0x11, "return-object", ReferenceType.NONE, Format.Format11x),


            case CONST_4://((short)0x12, "const/4", ReferenceType.NONE, Format.Format11n, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CONST_16://((short)0x13, "const/16", ReferenceType.NONE, Format.Format21s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CONST://((short)0x14, "const", ReferenceType.NONE, Format.Format31i, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CONST_HIGH16://((short)0x15, "const/high16", ReferenceType.NONE, Format.Format21ih, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CONST_WIDE_16://((short)0x16, "const-wide/16", ReferenceType.NONE, Format.Format21s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case CONST_WIDE_32://((short)0x17, "const-wide/32", ReferenceType.NONE, Format.Format31i, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case CONST_WIDE://((short)0x18, "const-wide", ReferenceType.NONE, Format.Format51l, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case CONST_WIDE_HIGH16:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x19, "const-wide/high16", ReferenceType.NONE, Format.Format21lh, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


            case CONST_STRING://((short)0x1a, "const-string", ReferenceType.STRING, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER, (short)0x1b),
        	case CONST_STRING_JUMBO:
        	case CONST_CLASS://break;//((short)0x1c, "const-class", ReferenceType.TYPE, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(referenceIntIndex, size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
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
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x1f, "check-cast", ReferenceType.TYPE, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case INSTANCE_OF:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(0, size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(1, size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
                break;//((short)0x20, "instance-of", ReferenceType.TYPE, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case ARRAY_LENGTH:
        		h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getF());
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getLf());
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                htob = z3engine.implies(h, b);
                z3engine.addRule(htob, null);
        		break;//((short)0x21, "array-length", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case NEW_INSTANCE:
        		if (referenceIntIndex == "Landroid/content/Intent;".hashCode()){
        			h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
            		b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    z3engine.addRule(z3engine.implies(h, b), null);
        			break;
        		}
        		
        		instanceNum = analysis.getInstNum(ci, mi, codeAddress);
        		
        		h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(instanceNum, size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkTrue());
        		b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
        		z3engine.addRule(z3engine.implies(h, b), null);

                regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

				fields = analysis.getClassFields(referenceString, instanceNum);
				if (fields != null)
                    for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        b = z3engine.hPred(z3engine.mkBitVector(referenceIntIndex, size),
                                z3engine.mkBitVector(instanceNum, size),
                                z3engine.mkBitVector(fieldN.getKey(), size),
                                z3engine.mkBitVector(0, size),
                                z3engine.mkFalse(),
                                z3engine.mkBool(fieldN.getValue()));
                        z3engine.addRule(z3engine.implies(h, b), null);
                    } else {
                        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        b = z3engine.hPred(z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            var.getF(), z3engine.mkBitVector(0, size),
                            z3engine.mkFalse(), var.getBf());
                        z3engine.addRule(z3engine.implies(h, b), null);
                    }

        		regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

        		if (analysis.hasStaticConstructor(referenceIntIndex)){
                    h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
        			int staticConstNum = "<clinit>()V".hashCode();
        			dmc = analysis.getExactMethod(referenceIntIndex, staticConstNum);

                    b = z3engine.rPred(Integer.toString(referenceIntIndex), Integer.toString(staticConstNum), 0, regUpdate, regUpdateL, regUpdateB,
        					dmc.getNumArg(), dmc.getNumReg());
                    z3engine.addRule(z3engine.implies(h, b), null);
        		}
        		break;//((short)0x22, "new-instance", ReferenceType.TYPE, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case NEW_ARRAY:
        		instanceNum = analysis.getInstNum(ci, mi, codeAddress);
        		h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(instanceNum, size));
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkTrue());
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

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
                    h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
        		    b = z3engine.hPred(
                            z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(0, size),
                            z3engine.mkBitVector(0, size),
                            z3engine.mkFalse(), z3engine.mkFalse()
                    );
                }
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x23, "new-array", ReferenceType.TYPE, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case FILLED_NEW_ARRAY:
        		FiveRegisterInstruction instructionA = (FiveRegisterInstruction)this.instruction;
                final int regCount = instructionA.getRegisterCount();
        		instanceNum = analysis.getInstNum(ci, mi, codeAddress);
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(numRegLoc, z3engine.mkBitVector(instanceNum, size));
        		regUpdateL.put(numRegLoc, z3engine.mkFalse());
        		regUpdateB.put(numRegLoc, z3engine.mkTrue());
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                htob = z3engine.implies(h, b);
                z3engine.addRule(htob, null);
                regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

        		if (analysis.optionArrays()){
        			switch(regCount){
        			case 5:
                        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        b = z3engine.hPred(z3engine.mkBitVector(referenceIntIndex, size),
                                           z3engine.mkBitVector(instanceNum, size),
                                           z3engine.mkBitVector(4, size),
                                           var.getV(instructionA.getRegisterG()),
                                           var.getL(instructionA.getRegisterG()),
                                           var.getB(instructionA.getRegisterG()));
                        htob = z3engine.implies(h, b);
                        z3engine.addRule(htob, null);
                    case 4:
                        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                                            z3engine.mkBitVector(instanceNum, size),
                                            z3engine.mkBitVector(3, size),
                                            var.getV(instructionA.getRegisterF()),
                                            var.getL(instructionA.getRegisterF()),
                                            var.getB(instructionA.getRegisterF()));
                        htob = z3engine.implies(h, b);
                        z3engine.addRule(htob, null);
                    case 3:
                        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                                            z3engine.mkBitVector(instanceNum, size),
                                            z3engine.mkBitVector(2, size),
                                            var.getV(instructionA.getRegisterE()),
                                            var.getL(instructionA.getRegisterE()),
                                            var.getB(instructionA.getRegisterE()));
                        htob = z3engine.implies(h, b);
                        z3engine.addRule(htob, null);
                    case 2:
                        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                                z3engine.mkBitVector(instanceNum, size),
                                z3engine.mkBitVector(1, size),
                                var.getV(instructionA.getRegisterD()),
                                var.getL(instructionA.getRegisterD()),
                                var.getB(instructionA.getRegisterD()));
                        htob = z3engine.implies(h, b);
                        z3engine.addRule(htob, null);
        			case 1:
                        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
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
                        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                                z3engine.mkBitVector(instanceNum, size),
                                z3engine.mkBitVector(0, size),
                                var.getV(instructionA.getRegisterG()),
                                var.getL(instructionA.getRegisterG()),
                                var.getB(instructionA.getRegisterG()));
                        htob = z3engine.implies(h, b);
                        z3engine.addRule(htob, null);
                    case 4:
                        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                                z3engine.mkBitVector(instanceNum, size),
                                z3engine.mkBitVector(0, size),
                                var.getV(instructionA.getRegisterF()),
                                var.getL(instructionA.getRegisterF()),
                                var.getB(instructionA.getRegisterF()));
                        htob = z3engine.implies(h, b);
                        z3engine.addRule(htob, null);
                    case 3:
                        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                                z3engine.mkBitVector(instanceNum, size),
                                z3engine.mkBitVector(0, size),
                                var.getV(instructionA.getRegisterE()),
                                var.getL(instructionA.getRegisterE()),
                                var.getB(instructionA.getRegisterE()));
                        htob = z3engine.implies(h, b);
                        z3engine.addRule(htob, null);
                    case 2:
                        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                                z3engine.mkBitVector(instanceNum, size),
                                z3engine.mkBitVector(0, size),
                                var.getV(instructionA.getRegisterD()),
                                var.getL(instructionA.getRegisterD()),
                                var.getB(instructionA.getRegisterD()));
                        htob = z3engine.implies(h, b);
                        z3engine.addRule(htob, null);
                    case 1:
                        h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
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
        		instanceNum = analysis.getInstNum(ci, mi, codeAddress);
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(numRegLoc, z3engine.mkBitVector(instanceNum, size));
        		regUpdateL.put(numRegLoc, z3engine.mkFalse());
        		regUpdateB.put(numRegLoc, z3engine.mkTrue());
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
                regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

        		RegisterRangeInstruction instructionAr = (RegisterRangeInstruction)this.instruction;
        		int regCountr = instructionAr.getRegisterCount();
    			int startRegister = instructionAr.getStartRegister();
            	int endRegister   =   startRegister+regCountr-1;
            	int cr = 0;

                for (int reg = startRegister; reg <= endRegister; reg++){
                    h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    b = z3engine.hPred( z3engine.mkBitVector(referenceIntIndex, size),
                            z3engine.mkBitVector(instanceNum, size),
                            z3engine.mkBitVector(cr, size),
                            var.getV(reg), var.getL(reg), var.getB(reg));
                    z3engine.addRule(z3engine.implies(h, b), null);
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
                                z3engine.addRule(z3engine.implies(h, b), null);
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
                                z3engine.addRule(z3engine.implies(h, b), null);
                            }
        					elNum++;
        				}
        			    break;
        			}
        		}
        		break;//((short)0x26, "fill-array-data", ReferenceType.NONE, Format.Format31t, Opcode.CAN_CONTINUE),


            case THROW:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x27, "throw", ReferenceType.NONE, Format.Format11x, Opcode.CAN_THROW),


            case GOTO://((short)0x28, "goto", ReferenceType.NONE, Format.Format10t),
        	case GOTO_16://((short)0x29, "goto/16", ReferenceType.NONE, Format.Format20t),
        	case GOTO_32:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x2a, "goto/32", ReferenceType.NONE, Format.Format30t),


            case PACKED_SWITCH:
                negationString = z3engine.mkFalse();
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
                                z3engine.addRule(z3engine.implies(h, b), null);
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
        		b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
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
                            z3engine.addRule(z3engine.implies(h, b), null);

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
        		b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x2c, "sparse-switch", ReferenceType.NONE, Format.Format31t, Opcode.CAN_CONTINUE),


            case CMPL_FLOAT://((short)0x2d, "cmpl-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CMPG_FLOAT://((short)0x2e, "cmpg-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CMPL_DOUBLE://((short)0x2f, "cmpl-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CMPG_DOUBLE://((short)0x30, "cmpg-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case CMP_LONG:
        		h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
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
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0x31, "cmp-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case IF_EQ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.not( z3engine.eq(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        ))
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.eq(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x32, "if-eq", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


            case IF_NE:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.eq(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.not( z3engine.eq(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        ))
                );
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0x33, "if-ne", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


            case IF_LT:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.not(z3engine.bvult(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                        ))
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.bvult(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0x34, "if-lt", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


            case IF_GE:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.not( z3engine.bvuge(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                        ))
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.bvuge(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x35, "if-ge", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


            case IF_GT:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.not( z3engine.bvugt(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                        ))
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.bvugt(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0x36, "if-gt", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


            case IF_LE:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.not( z3engine.bvule(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                        ))
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.bvule(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction) instruction).getRegisterB())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0x37, "if-le", ReferenceType.NONE, Format.Format22t, Opcode.CAN_CONTINUE),


            case IF_EQZ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.not( z3engine.eq(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                z3engine.mkBitVector(0, size)
                        ))
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.eq(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                z3engine.mkBitVector(0, size)
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0x38, "if-eqz", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


            case IF_NEZ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.eq(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                z3engine.mkBitVector(0, size)
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.not( z3engine.eq(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                z3engine.mkBitVector(0, size)
                        ))
                );
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0x39, "if-nez", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


            case IF_LTZ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.not( z3engine.bvult(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                z3engine.mkBitVector(0, size)
                        ))
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.bvult(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                z3engine.mkBitVector(0, size)
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0x3a, "if-ltz", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


            case IF_GEZ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.not( z3engine.bvuge(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                z3engine.mkBitVector(0, size)
                        ))
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.bvuge(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                z3engine.mkBitVector(0, size)
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0x3b, "if-gez", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


            case IF_GTZ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.not( z3engine.bvugt(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                z3engine.mkBitVector(0, size)
                        ))
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.bvugt(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                z3engine.mkBitVector(0, size)
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0x3c, "if-gtz", ReferenceType.NONE, Format.Format21t, Opcode.CAN_CONTINUE),


            case IF_LEZ:
        		jump = codeAddress + ((OffsetInstruction)instruction).getCodeOffset();
                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.not( z3engine.bvule(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                z3engine.mkBitVector(0, size)
                        ))
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.bvule(
                                var.getV(((OneRegisterInstruction) instruction).getRegisterA()),
                                z3engine.mkBitVector(0, size)
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, jump, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

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
                    b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
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
                    b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
        		}
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x4a, "aget-short", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case APUT://((short)0x4b, "aput", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case APUT_WIDE://((short)0x4c, "aput-wide", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case APUT_OBJECT://((short)0x4d, "aput-object", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case APUT_BOOLEAN://((short)0x4e, "aput-boolean", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case APUT_BYTE://((short)0x4f, "aput-byte", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case APUT_CHAR://((short)0x50, "aput-char", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case APUT_SHORT:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdateL.put(((TwoRegisterInstruction)instruction).getRegisterB(),
                        z3engine.or(var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                    var.getL(((OneRegisterInstruction)instruction).getRegisterA()))
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

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
                z3engine.addRule(z3engine.implies(h, b), null);
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
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0x58, "iget-short", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case IPUT://((short)0x59, "iput", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_WIDE://((short)0x5a, "iput-wide", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_OBJECT://((short)0x5b, "iput-object", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_BOOLEAN://((short)0x5c, "iput-boolean", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_BYTE://((short)0x5d, "iput-byte", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_CHAR://((short)0x5e, "iput-char", ReferenceType.FIELD, Format.Format22c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),
        	case IPUT_SHORT:
        		h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdateL.put(((TwoRegisterInstruction)instruction).getRegisterB(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

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
                z3engine.addRule(z3engine.implies(h, b), null);

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

                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkBitVector(0, size));
                regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), z3engine.mkFalse());
                regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getBf());
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

                h = z3engine.and(
                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.sPred(z3engine.mkInt(staticFieldClassName), z3engine.mkInt(referenceIntIndex),
                                        var.getF(), var.getLf(), var.getBf())
                );
        		regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getF());
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getLf());
        		regUpdateB.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getBf());
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

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
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
        		b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
        		b = z3engine.sPred(z3engine.mkInt(staticFieldClassName), z3engine.mkInt(referenceIntIndex),
                                    var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                    var.getL(((OneRegisterInstruction)instruction).getRegisterA()),
                                    var.getB(((OneRegisterInstruction)instruction).getRegisterA()));
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x6d, "sput-short", ReferenceType.FIELD, Format.Format21c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE),


            case INVOKE_VIRTUAL:
        	case INVOKE_SUPER:
                //TODO: should only look for the super implementation. CF What is done is FS analysis
        	case INVOKE_INTERFACE:
        		
        		
        		modRes = false;
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
    				implementations = analysis.getImplementations(referenceClassIndex, referenceIntIndex);
    				if (implementations == null){
        				analysis.putNotImpl(referenceClassIndex, referenceIntIndex);
        			}
        			else{
        				analysis.putImplemented(referenceClassIndex, referenceIntIndex, implementations);
        			}
    			}

        		isDefined = (implementations != null);

                FiveRegisterInstruction instr = (FiveRegisterInstruction)this.instruction;
            	if (isDefined){
            		for (final DalvikImplementation di : implementations){
            			numRegCall = di.getMethod().getNumReg();
            			numArgCall = di.getMethod().getNumArg();
            			if (analysis.isSink(di.getDalvikClass().getType().hashCode(), referenceIntIndex))
                			addQuery(z3engine, z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                    className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
        				referenceReg = instr.getRegisterC();

        				for (final DalvikInstance instance: di.getInstances()){
                            h = z3engine.and(
                                    z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                    z3engine.eq(
                                            var.getV(referenceReg),
                                            z3engine.mkBitVector(instance.hashCode(), size)
                                    )
                            );
                            
                           

        					regUpdate = updateRegister(numRegCall, numArgCall, BitVecExpr.class, var.getInjectV(var), false);
                            regUpdateL = updateRegister(numRegCall, numArgCall, BoolExpr.class, var.getInjectL(var), false);
                            regUpdateB = updateRegister(numRegCall, numArgCall, BoolExpr.class, var.getInjectB(var), false);

                            b = z3engine.rInvokePred(Integer.toString(di.getDalvikClass().getType().hashCode()), Integer.toString(di.getMethod().getName().hashCode()), 0,
                                    regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, size);

                            z3engine.addRule(z3engine.implies(h, b), null);
                            

                            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
        				}

        				if (callReturns){
        					for (final DalvikInstance instance: di.getInstances()){
                                BoolExpr subh = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                regUpdate = updateResult(numRegCall, numArgCall, BitVecExpr.class, var.getInjectV(var), false);
                                regUpdateL = updateResult(numRegCall, numArgCall, BoolExpr.class, var.getInjectL(var), false);
                                regUpdateB = updateResult(numRegCall, numArgCall, BoolExpr.class, var.getInjectB(var), false);
                                regUpdate.put(numArgCall, var.getRez());
                                regUpdateL.put(numArgCall, var.getLrez());
                                regUpdateB.put(numArgCall, var.getBrez());
                                h = z3engine.and(
                                        subh,
                                        z3engine.resPred(Integer.toString(di.getDalvikClass().getType().hashCode()), Integer.toString(referenceIntIndex), regUpdate, regUpdateL, regUpdateB, numArgCall),
                                        z3engine.eq(
                                                var.getV(referenceReg),
                                                z3engine.mkBitVector(instance.hashCode(), size)
                                        )
                                );
 
                                regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

                                returnLabel = analysis.isSource(di.getDalvikClass().getType().hashCode(), referenceIntIndex)
                                        ? z3engine.mkTrue()
                                        : var.getLrez();
                                if (callReturns) {
                                    regUpdate.put(numRegLoc, var.getRez());
                                    regUpdateL.put(numRegLoc, returnLabel);
                                }
                                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                                                
                                z3engine.addRule(z3engine.implies(h, b), null);
                                                               
                                regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
        					}
                		} else {
                            h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);

                            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

                            returnLabel = analysis.isSource(di.getDalvikClass().getType().hashCode(), referenceIntIndex)
                                    ? z3engine.mkTrue()
                                    : var.getLrez();
                			if (callReturns) {
                				regUpdate.put(numRegLoc, var.getRez());
                				regUpdateL.put(numRegLoc, returnLabel);
                			}
                            b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                            z3engine.addRule(z3engine.implies(h, b), null);

                            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
                		}

            		}
        		} else {
        			if (analysis.isSink(referenceClassIndex, referenceIntIndex)){
        				addQuery(z3engine, z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
        			}
        			if (processIntent(z3engine, ci, mi, numParLoc, numRegLoc, nextCode, referenceClassIndex, referenceIntIndex, referenceString, size))
        				break;
        			numRegCall = instr.getRegisterCount();

                    BoolExpr subh = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);

                    returnLabel = analysis.isSource(referenceClassIndex, referenceIntIndex)
                            ? z3engine.mkTrue()
                            : getLabels();

        			if (returnType.hashCode() == "Ljava/lang/String;".hashCode()){
        				regUpdate.put(numRegLoc, var.getF());
						regUpdateL.put(numRegLoc, returnLabel);
						regUpdateB.put(numRegLoc, z3engine.mkTrue());
        			} else {
                        if ((returnType.charAt(0) != '[') && (returnType.charAt(returnType.length() -1) == ';' )){
                            instanceNum = analysis.getInstNum(ci, mi, codeAddress);

                            fields = analysis.getClassFields(returnType, instanceNum);

                            if (fields != null)
                            for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                b = z3engine.hPred(z3engine.mkBitVector(returnTypeInt, size),
                                                    var.getFpp(), z3engine.mkBitVector(fieldN.getKey(), size),
                                                    var.getVfp(), returnLabel, z3engine.mkBool(fieldN.getValue()));
                                z3engine.addRule(z3engine.implies(h, b), null);
                            }
                            else{
                                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                b = z3engine.hPred(z3engine.mkBitVector(returnTypeInt, size),
                                                    var.getFpp(), var.getF(), var.getVfp(), returnLabel, var.getBf());
                                z3engine.addRule(z3engine.implies(h, b), null);
                            }
                            regUpdate.put(numRegLoc, var.getFpp());
                            regUpdateL.put(numRegLoc, returnLabel);
                            regUpdateB.put(numRegLoc, z3engine.mkTrue());
                        } else {
                            switch (returnType){
                                case "V": break;

                                case "Z": case "B": case "S": case "C": case "I": case "J": case "F": case "D":
                                    regUpdate.put(numRegLoc, var.getF());
                                    regUpdateL.put(numRegLoc, returnLabel);
                                    regUpdateB.put(numRegLoc, z3engine.mkFalse());
                                    break;
                                default: //array
                                    instanceNum = analysis.getInstNum(ci, mi, codeAddress);
                                    h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                    b = z3engine.hPred(z3engine.mkBitVector(returnTypeInt, size),
                                                        z3engine.mkBitVector(instanceNum, size),
                                                        var.getF(), var.getBuf(), returnLabel, var.getBf());
                                    z3engine.addRule(z3engine.implies(h, b), null);
                                    regUpdate.put(numRegLoc, z3engine.mkBitVector(instanceNum, size));
                                    regUpdateL.put(numRegLoc, returnLabel);
                                    regUpdateB.put(numRegLoc, z3engine.mkTrue());

                            }
                        }
        			}
        			regUpdateL = highReg(false, regUpdateL, z3engine);

                    BoolExpr subb = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    z3engine.addRule(z3engine.implies(subh, subb), null);
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

            				for (final DalvikInstance instance: di.getInstances()){
                                h = z3engine.and(
                                        z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                        z3engine.eq(
                                                var.getV(instr2.getRegisterD()),
                                                z3engine.mkBitVector(instance.hashCode(), size)
                                        )
                                );
                                numArgCall = di.getMethod().getNumArg();

                                regUpdate.put(numRegCall - numArgCall + 0, var.getV(instr2.getRegisterD()));
                                regUpdate.put(numRegCall + 1 + 0, var.getV(instr2.getRegisterD()));
                                regUpdateL.put(numRegCall - numArgCall + 0, var.getL(instr2.getRegisterD()));
                                regUpdateL.put(numRegCall + 1 + 0, var.getL(instr2.getRegisterD()));
                                regUpdateB.put(numRegCall - numArgCall + 0, var.getB(instr2.getRegisterD()));
                                regUpdateB.put(numRegCall + 1 + 0, var.getB(instr2.getRegisterD()));
                                b = z3engine.rInvokePred(
                                        Integer.toString(di.getDalvikClass().getType().hashCode()),
                                        Integer.toString("run()V".hashCode()),
                                        0, regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, size
                                );
                                z3engine.addRule(z3engine.implies(h, b), null);

                                regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
            				}

                			break;
            			}
            		}
        		}

        		staticDefinitions = analysis.isDefined(referenceClassIndex, referenceIntIndex);
        		isDefined = staticDefinitions != null;
        		if (!isDefined) analysis.putNotDefined(referenceClassIndex, referenceIntIndex);
                else analysis.putDefined(referenceClassIndex, referenceIntIndex, staticDefinitions);
        		if (isDefined){
        			for (final Map.Entry<DalvikClass, DalvikMethod> definition: staticDefinitions.entrySet()){
        				numRegCall = definition.getValue().getNumReg();
        				numArgCall = definition.getValue().getNumArg();
        				if (analysis.isSink(referenceClassIndex, referenceIntIndex))
                			addQuery(z3engine, z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                    className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
                		regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

                		h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        regUpdate = updateRegister(numRegCall, numArgCall, BitVecExpr.class, var.getInjectV(var), false);
                        regUpdateL = updateRegister(numRegCall, numArgCall, BoolExpr.class, var.getInjectL(var), false);
                        regUpdateB = updateRegister(numRegCall, numArgCall, BoolExpr.class, var.getInjectB(var), false);
                        b = z3engine.rInvokePred(referenceStringClassIndex, referenceIndex, 0, regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, size);
                        z3engine.addRule(z3engine.implies(h, b), null);

                        regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

                		if (callReturns){
                            BoolExpr subh = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                            regUpdate = updateResult(numRegCall, numArgCall, BitVecExpr.class, var.getInjectV(var), false);
                            regUpdateL = updateResult(numRegCall, numArgCall, BoolExpr.class, var.getInjectL(var), false);
                            regUpdateB = updateResult(numRegCall, numArgCall, BoolExpr.class, var.getInjectB(var), false);
                            regUpdate.put(numArgCall, var.getRez());
                			regUpdateL.put(numArgCall, var.getLrez());
                			regUpdateB.put(numArgCall, var.getBrez());
                            h = z3engine.and(
                                subh,
                                z3engine.resPred(referenceStringClassIndex, referenceIndex, regUpdate, regUpdateL, regUpdateB, numArgCall)
                            );
                		} else {
                			h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                		}

            			regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

            			returnLabel = analysis.isSource(referenceClassIndex, referenceIntIndex)
                                        ? z3engine.mkTrue()
                                        : var.getLrez();
                        if (callReturns) {
            				regUpdate.put(numRegLoc, var.getRez());
            				regUpdateL.put(numRegLoc, returnLabel);
            			}

                        b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        z3engine.addRule(z3engine.implies(h, b), null);
                    }
        		} else {
        			if (analysis.isSink(referenceClassIndex, referenceIntIndex))
            			addQuery(z3engine, z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
            		if (processIntent(z3engine, ci, mi, numParLoc, numRegLoc, nextCode, referenceClassIndex, referenceIntIndex, referenceString, size))
        				break;

                    BoolExpr subh = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);


                    returnLabel = analysis.isSource(referenceClassIndex, referenceIntIndex)
                            ? z3engine.mkTrue()
                            : getLabels();

        			if (returnType.equals("Ljava/lang/String;")){
        				regUpdate.put(numRegLoc, var.getF());
						regUpdateL.put(numRegLoc, returnLabel);
						regUpdateB.put(numRegLoc, z3engine.mkTrue());
        			} else {
                        if ((returnType.charAt(0) != '[') && (returnType.charAt(returnType.length() -1) == ';' )){
                            instanceNum = analysis.getInstNum(ci, mi, codeAddress);
                                fields = analysis.getClassFields(returnType, instanceNum);
                            if (fields != null)
                                for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                                    h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                    b = z3engine.hPred(z3engine.mkBitVector(returnTypeInt, size), var.getFpp(),
                                            z3engine.mkBitVector(fieldN.getKey(), size), var.getVfp(),
                                            returnLabel, z3engine.mkBool(fieldN.getValue()));
                                    z3engine.addRule(z3engine.implies(h, b), null);
                                } else {
                                    h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                    b = z3engine.hPred(z3engine.mkBitVector(returnTypeInt, size),
                                            var.getFpp(), var.getF(), var.getVfp(), returnLabel, var.getBf());
                                    z3engine.addRule(z3engine.implies(h, b), null);
                                }
                            regUpdate.put(numRegLoc, var.getFpp());
                            regUpdateL.put(numRegLoc, returnLabel);
                            regUpdateB.put(numRegLoc, z3engine.mkTrue());
                        } else {
                            switch (returnType){
                                case "V": break;
                                case "Z": case "B": case "S": case "C": case "I": case "J": case "F": case "D":
                                    regUpdate.put(numRegLoc, var.getF());
                                    regUpdateL.put(numRegLoc, returnLabel);
                                    regUpdateB.put(numRegLoc, z3engine.mkFalse());
                                    break;
                                default: //array
                                    instanceNum = analysis.getInstNum(ci, mi, codeAddress);

                                    h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                    b = z3engine.hPred(z3engine.mkBitVector(returnTypeInt, size),
                                            z3engine.mkBitVector(instanceNum, size), var.getF(),
                                            var.getBuf(), returnLabel, var.getBf());
                                    z3engine.addRule(z3engine.implies(h, b), null);

                                    regUpdate.put(numRegLoc, z3engine.mkBitVector(instanceNum, size));
                                    regUpdateL.put(numRegLoc, returnLabel);
                                    regUpdateB.put(numRegLoc, z3engine.mkTrue());

                            }
                        }
        			}
        			regUpdateL = highReg(false, regUpdateL, z3engine);
        			BoolExpr subb = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    z3engine.addRule(z3engine.implies(subh, subb), null);
        		}
        		break;
        		//((short)0x6e, "invoke-virtual", ReferenceType.METHOD, Format.Format35c, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),


            case INVOKE_VIRTUAL_RANGE:
        	case INVOKE_SUPER_RANGE:
        	    //TODO: should only look for the super implementation. CF What is done is FS analysis
        	case INVOKE_INTERFACE_RANGE:

        		modRes = false;
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
    				implementations = analysis.getImplementations(referenceClassIndex, referenceIntIndex);
    				if (implementations == null){
        				analysis.putNotImpl(referenceClassIndex, referenceIntIndex);
        			}
        			else{
        				analysis.putImplemented(referenceClassIndex, referenceIntIndex, implementations);
        			}
    			}

        		isDefined = (implementations != null);
        		if (implementations != null)
        			isDefined = true;
        		RegisterRangeInstruction instr3 = (RegisterRangeInstruction)this.instruction;
            	if (isDefined){
            		for (final DalvikImplementation di : implementations){

            			numRegCall = di.getMethod().getNumReg();
            			numArgCall = di.getMethod().getNumArg();
            			if (analysis.isSink(di.getDalvikClass().getType().hashCode(), referenceIntIndex))
                			addQueryRange(z3engine, z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                    className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
        				referenceReg = instr3.getStartRegister();

        				for (final DalvikInstance instance: di.getInstances()){
                            h = z3engine.and(
                                    z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                    z3engine.eq(
                                            var.getV(referenceReg),
                                            z3engine.mkBitVector(instance.hashCode(), size)
                                    )
                            );

                            regUpdate = updateRegister(numRegCall, numArgCall, BitVecExpr.class, var.getInjectV(var), true);
                            regUpdateL = updateRegister(numRegCall, numArgCall, BoolExpr.class, var.getInjectL(var), true);
                            regUpdateB = updateRegister(numRegCall, numArgCall, BoolExpr.class, var.getInjectB(var), true);

                            b = z3engine.rInvokePred(Integer.toString(di.getDalvikClass().getType().hashCode()), Integer.toString(di.getMethod().getName().hashCode()), 0,
                                    regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, size);

                            z3engine.addRule(z3engine.implies(h, b), null);

                            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
        				}

        				if (callReturns){
        					for (final DalvikInstance instance: di.getInstances()){
                                BoolExpr temph = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                regUpdate = updateResult(numRegCall, numArgCall, BitVecExpr.class, var.getInjectV(var), true);
                                regUpdateL = updateResult(numRegCall, numArgCall, BoolExpr.class,var.getInjectL(var), true);
                                regUpdateB = updateResult(numRegCall, numArgCall, BoolExpr.class, var.getInjectB(var), true);
                                regUpdate.put(numArgCall, var.getRez());
                                regUpdateL.put(numArgCall, var.getLrez());
                                regUpdateB.put(numArgCall, var.getBrez());
                                h = z3engine.and(
                                        temph,
                                        z3engine.resPred(Integer.toString(di.getDalvikClass().getType().hashCode()), referenceIndex, regUpdate, regUpdateL, regUpdateB, numArgCall),
                                        z3engine.eq(
                                                var.getV(referenceReg),
                                                z3engine.mkBitVector(instance.hashCode(), size)
                                        )
                                );

                                regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

                                returnLabel = analysis.isSource(di.getDalvikClass().getType().hashCode(), referenceIntIndex)
                                        ? z3engine.mkTrue()
                                        : var.getLrez();

                                if (callReturns) {
                                    regUpdate.put(numRegLoc, var.getRez());
                                    regUpdateL.put(numRegLoc, returnLabel);
                                }
                                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                z3engine.addRule(z3engine.implies(h, b), null);

                                regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
        					}
                		} else {
                            h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);

                            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

                            returnLabel = analysis.isSource(di.getDalvikClass().getType().hashCode(), referenceIntIndex)
                                    ? z3engine.mkTrue()
                                    : var.getLrez();
                            if (callReturns) {
                				regUpdate.put(numRegLoc, var.getRez());
                				regUpdateL.put(numRegLoc, returnLabel);
                			}
                            b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                            z3engine.addRule(z3engine.implies(h, b), null);

                            regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();
                		}

            		}
        		}
        		else{
        			if (analysis.isSink(referenceClassIndex, referenceIntIndex)){
        				addQueryRange(z3engine, z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
        			}
        			if (processIntent(z3engine, ci, mi, numParLoc, numRegLoc, nextCode, referenceClassIndex, referenceIntIndex, referenceString, size))
        				break;
        			numRegCall = instr3.getRegisterCount();

                    BoolExpr subh = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);

                    returnLabel = analysis.isSource(referenceClassIndex, referenceIntIndex)
                            ? z3engine.mkTrue()
                            : getLabelsRange();

        			if (returnType.hashCode() == "Ljava/lang/String;".hashCode()){
        				regUpdate.put(numRegLoc, var.getF());
						regUpdateL.put(numRegLoc, returnLabel);
						regUpdateB.put(numRegLoc, z3engine.mkTrue());
        			}
        			else{
        			if ((returnType.charAt(0) != '[') && (returnType.charAt(returnType.length() -1) == ';' )){
        				instanceNum = analysis.getInstNum(ci, mi, codeAddress);

					    fields = analysis.getClassFields(returnType, instanceNum);

					    if (fields != null)
                		for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                			h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                			b = z3engine.hPred(z3engine.mkBitVector(returnTypeInt, size),
                                    var.getFpp(), z3engine.mkBitVector(fieldN.getKey(), size),
                                    var.getVfp(), returnLabel, z3engine.mkBool(fieldN.getValue()));
                            z3engine.addRule(z3engine.implies(h, b), null);
                		} else {
                            h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                            b = z3engine.hPred(z3engine.mkBitVector(returnTypeInt, size),
                                    var.getFpp(), var.getF(), var.getVfp(), returnLabel, var.getBf());
                            z3engine.addRule(z3engine.implies(h, b), null);
					    }
                		regUpdate.put(numRegLoc, var.getFpp());
            			regUpdateL.put(numRegLoc, returnLabel);
            			regUpdateB.put(numRegLoc, z3engine.mkTrue());
        			}
        			else{
        				switch (returnType){
        				    case "V": break;

        					case "Z": case "B": case "S": case "C": case "I": case "J": case "F": case "D":
        						regUpdate.put(numRegLoc, var.getF());
        						regUpdateL.put(numRegLoc, returnLabel);
        						regUpdateB.put(numRegLoc, z3engine.mkFalse());
        						break;

        					default: //array
        						instanceNum = analysis.getInstNum(ci, mi, codeAddress);
                                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                b = z3engine.hPred(z3engine.mkBitVector(returnTypeInt, size),
                                        z3engine.mkBitVector(instanceNum, size),
                                        var.getF(), var.getBuf(), returnLabel, var.getBf());
                                z3engine.addRule(z3engine.implies(h, b), null);
                        		regUpdate.put(numRegLoc, z3engine.mkBitVector(instanceNum, size));
                    			regUpdateL.put(numRegLoc, returnLabel);
                    			regUpdateB.put(numRegLoc, z3engine.mkTrue());
        				}
        			}
        			}
        			regUpdateL = highReg(true, regUpdateL, z3engine);
        			BoolExpr subb = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    z3engine.addRule(z3engine.implies(subh, subb), null);
        		}
            	break;


            case INVOKE_DIRECT_RANGE:
        	case INVOKE_STATIC_RANGE:
        		staticDefinitions = analysis.isDefined(referenceClassIndex, referenceIntIndex);
                isDefined = staticDefinitions != null;
                if (!isDefined) analysis.putNotDefined(referenceClassIndex, referenceIntIndex);
                else analysis.putDefined(referenceClassIndex, referenceIntIndex, staticDefinitions);
        		if (isDefined){
        			for (final Map.Entry<DalvikClass, DalvikMethod> definition: staticDefinitions.entrySet()){
        				numRegCall = definition.getValue().getNumReg();
        				numArgCall = definition.getValue().getNumArg();
        				if (analysis.isSink(referenceClassIndex, referenceIntIndex))
                			addQueryRange(z3engine, z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                    className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());

                        regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

                		h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);


                        regUpdate = updateRegister(numRegCall, numArgCall, BitVecExpr.class, var.getInjectV(var), true);
                        regUpdateL = updateRegister(numRegCall, numArgCall, BoolExpr.class, var.getInjectL(var), true);
                        regUpdateB = updateRegister(numRegCall, numArgCall, BoolExpr.class, var.getInjectB(var), true);

                        b = z3engine.rInvokePred(referenceStringClassIndex, referenceIndex, 0, regUpdate, regUpdateL, regUpdateB, numArgCall, numRegCall, size);

                        z3engine.addRule(z3engine.implies(h, b), null);

                        regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

                        BoolExpr subh;

                        if (callReturns){
                            subh = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                            regUpdate = updateResult(numRegCall, numArgCall, BitVecExpr.class, var.getInjectV(var), true);
                            regUpdateL = updateResult(numRegCall, numArgCall, BoolExpr.class, var.getInjectL(var), true);
                            regUpdateB = updateResult(numRegCall, numArgCall, BoolExpr.class, var.getInjectB(var), true);
                            regUpdate.put(numArgCall, var.getRez());
                			regUpdateL.put(numArgCall, var.getLrez());
                			regUpdateB.put(numArgCall, var.getBrez());
                            subh = z3engine.and(
                                    subh,
                                    z3engine.resPred(referenceStringClassIndex, referenceIndex, regUpdate, regUpdateL, regUpdateB, numArgCall)
                            );
                		} else {
                            subh = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                		}

                        regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

                        returnLabel = analysis.isSource(referenceClassIndex, referenceIntIndex)
                                ? z3engine.mkTrue()
                                : var.getLrez();

                        if (callReturns) {
            				regUpdate.put(numRegLoc, var.getRez());
            				regUpdateL.put(numRegLoc, returnLabel);
            			}
            			BoolExpr subb = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                        z3engine.addRule(z3engine.implies(subh, subb), null);
                    }
        		} else {
        			if (analysis.isSink(referenceClassIndex, referenceIntIndex))
            			addQueryRange(z3engine, z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                                className, methodName, Integer.toString(codeAddress), referenceString, analysis.optionVerbose());
            		if (processIntent(z3engine, ci, mi, numParLoc, numRegLoc, nextCode, referenceClassIndex, referenceIntIndex, referenceString, size))
        				break;


                    BoolExpr subh = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);

                    returnLabel = analysis.isSource(referenceClassIndex, referenceIntIndex)
                            ? z3engine.mkTrue()
                            : getLabelsRange();

        			if (returnType.equals((String)"Ljava/lang/String;")){
        				regUpdate.put(numRegLoc, var.getF());
						regUpdateL.put(numRegLoc, returnLabel);
						regUpdateB.put(numRegLoc, z3engine.mkTrue());
        			} else {
                        if ((returnType.charAt(0) != '[') && (returnType.charAt(returnType.length() -1) == ';' )){
                            instanceNum = analysis.getInstNum(ci, mi, codeAddress);
                                fields = analysis.getClassFields(returnType, instanceNum);
                            if (fields != null)
                            for (Map.Entry<Integer, Boolean> fieldN : fields.entrySet()){
                                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                b = z3engine.hPred(z3engine.mkBitVector(returnTypeInt, size),
                                        var.getFpp(), z3engine.mkBitVector(fieldN.getKey(), size),
                                        var.getVfp(), returnLabel, z3engine.mkBool(fieldN.getValue()));
                                z3engine.addRule(z3engine.implies(h, b), null);

                            } else {
                                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                b = z3engine.hPred(z3engine.mkBitVector(returnTypeInt, size),
                                        var.getFpp(), var.getF(), var.getVfp(), returnLabel, var.getBf());
                                z3engine.addRule(z3engine.implies(h, b), null);
                            }
                            regUpdate.put(numRegLoc, var.getFpp());
                            regUpdateL.put(numRegLoc, returnLabel);
                            regUpdateB.put(numRegLoc, z3engine.mkTrue());
                        } else {
                            switch (returnType){
                                case "V": break;
                                case "Z": case "B": case "S": case "C": case "I": case "J": case "F": case "D":
                                    regUpdate.put(numRegLoc, var.getF());
                                    regUpdateL.put(numRegLoc, returnLabel);
                                    regUpdateB.put(numRegLoc, z3engine.mkFalse());
                                    break;
                                default: //array
                                    instanceNum = analysis.getInstNum(ci, mi, codeAddress);

                                    h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                                    b = z3engine.hPred(z3engine.mkBitVector(returnTypeInt, size), z3engine.mkBitVector(instanceNum, size),
                                                        var.getF(), var.getBuf(), returnLabel, var.getBf());
                                    z3engine.addRule(z3engine.implies(h, b), null);
                                    regUpdate.put(numRegLoc, z3engine.mkBitVector(instanceNum, size));
                                    regUpdateL.put(numRegLoc, returnLabel);
                                    regUpdateB.put(numRegLoc, z3engine.mkTrue());

                            }
                        }
        			}
        			regUpdateL = highReg(true, regUpdateL, z3engine);
        			BoolExpr subb = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                    z3engine.addRule(z3engine.implies(subh, subb), null);
                }
        		break;//((short)0x74, "invoke-virtual/range", ReferenceType.METHOD, Format.Format3rc, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_RESULT),


            case NEG_INT://((short)0x7b, "neg-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case NEG_LONG://((short)0x7d, "neg-long", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case NEG_FLOAT://((short)0x7f, "neg-float", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case NEG_DOUBLE:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvneg(var.getV(((TwoRegisterInstruction)instruction).getRegisterB()))
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x80, "neg-double", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


            case NOT_INT://((short)0x7c, "not-int", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case NOT_LONG:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvnot(var.getV(((TwoRegisterInstruction)instruction).getRegisterB()))
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
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
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x8f, "int-to-short", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case ADD_INT://((short)0x90, "add-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case ADD_LONG://((short)0x9b, "add-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case ADD_FLOAT://((short)0xa6, "add-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case ADD_DOUBLE:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvadd(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
                break;//((short)0xab, "add-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case SUB_INT://((short)0x91, "sub-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SUB_LONG://((short)0x9c, "sub-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case SUB_FLOAT://((short)0xa7, "sub-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SUB_DOUBLE:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvsub(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xac, "sub-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case MUL_INT://((short)0x92, "mul-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MUL_LONG://((short)0x9d, "mul-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case MUL_FLOAT://((short)0xa8, "mul-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MUL_DOUBLE:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvmul(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xad, "mul-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case DIV_INT://((short)0x93, "div-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case DIV_LONG://((short)0x9e, "div-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case DIV_FLOAT://((short)0xa9, "div-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case DIV_DOUBLE:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvudiv(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xae, "div-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case REM_INT://((short)0x94, "rem-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case REM_LONG://((short)0x9f, "rem-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case REM_FLOAT://((short)0xaa, "rem-float", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case REM_DOUBLE:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvurem(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xaf, "rem-double", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case AND_INT://((short)0x95, "and-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case AND_LONG:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvand(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xa0, "and-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case OR_INT://((short)0x96, "or-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case OR_LONG:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvor(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xa1, "or-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case XOR_INT://((short)0x97, "xor-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case XOR_LONG:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvxor(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xa2, "xor-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case SHL_INT://((short)0x98, "shl-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SHL_LONG:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvshl(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xa3, "shl-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


            case SHR_LONG://((short)0xa4, "shr-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case SHR_INT:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvashr(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0x99, "shr-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        	case USHR_INT://((short)0x9a, "ushr-int", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case USHR_LONG:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvlshr(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getV(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((ThreeRegisterInstruction)instruction).getRegisterC())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xa5, "ushr-long", ReferenceType.NONE, Format.Format23x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


            case ADD_INT_2ADDR://((short)0xb0, "add-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case ADD_LONG_2ADDR://((short)0xc0, "and-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case ADD_FLOAT_2ADDR://((short)0xc6, "add-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case ADD_DOUBLE_2ADDR:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvadd(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xcb, "add-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


        	case SUB_INT_2ADDR://((short)0xb1, "sub-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SUB_LONG_2ADDR://((short)0xbc, "sub-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case SUB_FLOAT_2ADDR://((short)0xc7, "sub-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SUB_DOUBLE_2ADDR:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvsub(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xcc, "sub-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case MUL_INT_2ADDR://((short)0xb2, "mul-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MUL_LONG_2ADDR://((short)0xbd, "mul-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case MUL_FLOAT_2ADDR://((short)0xc8, "mul-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MUL_DOUBLE_2ADDR:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvmul(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xcd, "mul-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case DIV_INT_2ADDR://((short)0xb3, "div-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case DIV_LONG_2ADDR://((short)0xbe, "div-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case DIV_FLOAT_2ADDR://((short)0xc9, "div-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case DIV_DOUBLE_2ADDR:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvudiv(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xce, "div-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case REM_INT_2ADDR://((short)0xb4, "rem-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case REM_LONG_2ADDR://((short)0xbf, "rem-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),
        	case REM_FLOAT_2ADDR://((short)0xca, "rem-float/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case REM_DOUBLE_2ADDR:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvurem(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xcf, "rem-double/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case AND_INT_2ADDR://((short)0xb5, "and-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case AND_LONG_2ADDR:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvand(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xbb, "add-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case OR_INT_2ADDR://((short)0xb6, "or-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case OR_LONG_2ADDR:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvor(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xc1, "or-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case XOR_INT_2ADDR://((short)0xb7, "xor-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case XOR_LONG_2ADDR:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvxor(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xc2, "xor-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case SHL_INT_2ADDR://((short)0xb8, "shl-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SHL_LONG_2ADDR:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvshl(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xc3, "shl-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),

        	case SHR_INT_2ADDR://((short)0xb9, "shr-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case SHR_LONG_2ADDR:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvashr(
                                var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                                var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                                var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xc4, "shr-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


            case USHR_INT_2ADDR://((short)0xba, "ushr-int/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case USHR_LONG_2ADDR:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvlshr(
                            var.getV(((OneRegisterInstruction)instruction).getRegisterA()),
                            var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.or(
                            var.getL(((TwoRegisterInstruction)instruction).getRegisterB()),
                            var.getL(((OneRegisterInstruction)instruction).getRegisterA())
                        )
                );
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0xc5, "ushr-long/2addr", ReferenceType.NONE, Format.Format12x, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER | Opcode.SETS_WIDE_REGISTER),


            case ADD_INT_LIT16://((short)0xd0, "add-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case ADD_INT_LIT8:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvadd(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xd8, "add-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


        	case MUL_INT_LIT16://((short)0xd2, "mul-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case MUL_INT_LIT8:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvmul(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
        		break;//((short)0xda, "mul-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case DIV_INT_LIT16://((short)0xd3, "div-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case DIV_INT_LIT8:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvudiv(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0xdb, "div-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case REM_INT_LIT16://((short)0xd4, "rem-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case REM_INT_LIT8:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvurem(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0xdc, "rem-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_THROW | Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case AND_INT_LIT16://((short)0xd5, "and-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case AND_INT_LIT8:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvand(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0xdd, "and-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case OR_INT_LIT16://((short)0xd6, "or-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case OR_INT_LIT8:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvor(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0xde, "or-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case XOR_INT_LIT16://((short)0xd7, "xor-int/lit16", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case XOR_INT_LIT8:
        		h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvxor(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0xdf, "xor-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case RSUB_INT://break;//((short)0xd1, "rsub-int", ReferenceType.NONE, Format.Format22s, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),
        	case RSUB_INT_LIT8:
        		h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvsub(
                                z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size),
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB())
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);

        		break;//((short)0xd9, "rsub-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case SHL_INT_LIT8:
        		h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                    z3engine.bvshl(var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                   z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size))
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                htob = z3engine.implies(h, b);
                z3engine.addRule(htob, null);

        		break;//((short)0xe0, "shl-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case SHR_INT_LIT8:
                h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvashr(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                htob = z3engine.implies(h, b);
                z3engine.addRule(htob, null);

        		break;//((short)0xe1, "shr-int/lit8", ReferenceType.NONE, Format.Format22b, Opcode.CAN_CONTINUE | Opcode.SETS_REGISTER),


            case USHR_INT_LIT8:
        		h = z3engine.rPred(classIndex, methodIndex, codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(((OneRegisterInstruction)instruction).getRegisterA(),
                        z3engine.bvlshr(
                                var.getV(((TwoRegisterInstruction)instruction).getRegisterB()),
                                z3engine.mkBitVector(((WideLiteralInstruction)instruction).getWideLiteral(), size)
                        )
                );
        		regUpdateL.put(((OneRegisterInstruction)instruction).getRegisterA(), var.getL(((TwoRegisterInstruction)instruction).getRegisterB()));
                b = z3engine.rPred(classIndex, methodIndex, nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                htob = z3engine.implies(h, b);
                z3engine.addRule(htob, null);

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
        	    throw new RuntimeException("InstructionAnalysis: not supported "+ opcode.toString());
        	case PACKED_SWITCH_PAYLOAD:
        		break;//((short)0x100, "packed-switch-payload", ReferenceType.NONE, Format.PackedSwitchPayload, 0),
        	case SPARSE_SWITCH_PAYLOAD:
        		break;//((short)0x200, "sparse-switch-payload", ReferenceType.NONE, Format.SparseSwitchPayload, 0),
        	case ARRAY_PAYLOAD:
        		break;//((short)0x300, "array-payload", ReferenceType.NONE, Format.ArrayPayload, 0);
        	default:
        	    throw new RuntimeException("InstructionAnalysis: not supported " + opcode.toString());
        }
	}


    private BoolExpr getLabels(){
    	FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
        final int regCount = instruction.getRegisterCount();
        switch (regCount) {
            case 1:
                return z3engine.or( z3engine.mkFalse(),
                                    z3engine.getVars().getL(instruction.getRegisterC()));
            case 2:
                return z3engine.or( z3engine.mkFalse(),
                                    z3engine.getVars().getL(instruction.getRegisterC()),
                                    z3engine.getVars().getL(instruction.getRegisterD()));
            case 3:
                return z3engine.or( z3engine.mkFalse(),
                                    z3engine.getVars().getL(instruction.getRegisterC()),
                                    z3engine.getVars().getL(instruction.getRegisterD()),
                                    z3engine.getVars().getL(instruction.getRegisterE()));
            case 4:
                return z3engine.or( z3engine.mkFalse(),
                                    z3engine.getVars().getL(instruction.getRegisterC()),
                                    z3engine.getVars().getL(instruction.getRegisterD()),
                                    z3engine.getVars().getL(instruction.getRegisterE()),
                                    z3engine.getVars().getL(instruction.getRegisterF()));

            case 5:
                return z3engine.or( z3engine.mkFalse(),
                                    z3engine.getVars().getL(instruction.getRegisterC()),
                                    z3engine.getVars().getL(instruction.getRegisterD()),
                                    z3engine.getVars().getL(instruction.getRegisterE()),
                                    z3engine.getVars().getL(instruction.getRegisterF()),
                                    z3engine.getVars().getL(instruction.getRegisterG()));
            default:
                return z3engine.mkFalse();
        }
    }

    private BoolExpr getLabelsRange(){
    	RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
        int regCount = instruction.getRegisterCount();
    	int startRegister = instruction.getStartRegister();
    	int endRegister   =   startRegister+regCount-1;

        BoolExpr labels = z3engine.mkFalse();
        for(int reg = startRegister; reg <= endRegister; reg++){
            labels = z3engine.or(
                    labels, z3engine.getVars().getL(reg)
            );
        }
        return z3engine.or(labels);
    }

    private void addQueryRange(final Z3Engine z3, BoolExpr p, String className, String methodName, String pc, String sinkName, final boolean verboseOption){
        Z3Variable var = z3.getVars();
        RegisterRangeInstruction instruction = (RegisterRangeInstruction)this.instruction;
        int regCount = instruction.getRegisterCount();
    	int startRegister = instruction.getStartRegister();
    	int endRegister   =   startRegister+regCount-1;

        for (int reg = startRegister; reg <= endRegister; reg++ ){
            BoolExpr q = z3.and(
                    p,
                    z3.eq(var.getL(reg), z3.mkTrue())
            );

            String d = "Test if register " + Integer.toString(reg) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            z3.addQuery(new Z3Query(q, d, verboseOption, className, methodName, pc, sinkName));
        }
    }

    private void addQuery(final Z3Engine z3, BoolExpr p, String className, String methodName, String pc, String sinkName, final boolean verboseResults){
        Z3Variable var = z3.getVars();
        FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
        final int regCount = instruction.getRegisterCount();

        switch (regCount) {
            case 5:
                BoolExpr q5 = z3.and(
                        p,
                        z3.eq(var.getL(instruction.getRegisterG()), z3.mkTrue())
                );
                String d5 = "Test if register " + Integer.toString(instruction.getRegisterG()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
                z3.addQuery(new Z3Query(q5, d5, verboseResults, className, methodName, pc, sinkName));
            case 4:
                BoolExpr q4 = z3.and(
                        p,
                        z3.eq(var.getL(instruction.getRegisterF()), z3.mkTrue())
                );
                String d4 = "Test if register " + Integer.toString(instruction.getRegisterF()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
                z3.addQuery(new Z3Query(q4, d4, verboseResults, className, methodName, pc, sinkName));
            case 3:
                BoolExpr q3 = z3.and(
                        p,
                        z3.eq(var.getL(instruction.getRegisterE()), z3.mkTrue())
                );
                String d3 = "Test if register " + Integer.toString(instruction.getRegisterE()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
                z3.addQuery(new Z3Query(q3, d3, verboseResults, className, methodName, pc, sinkName));
            case 2:
                BoolExpr q2 = z3.and(
                        p,
                        z3.eq(var.getL(instruction.getRegisterD()), z3.mkTrue())
                );
                String d2 = "Test if register " + Integer.toString(instruction.getRegisterD()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
                z3.addQuery(new Z3Query(q2, d2, verboseResults, className, methodName, pc, sinkName));
            case 1:
                BoolExpr q1 = z3.and(
                        p,
                        z3.eq(var.getL(instruction.getRegisterC()), z3.mkTrue())
                );
                String d1 = "Test if register " + Integer.toString(instruction.getRegisterC()) +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
            	z3.addQuery(new Z3Query(q1, d1, verboseResults, className, methodName, pc, sinkName));
        }
    }

    private Map<Integer, BoolExpr> highReg(final boolean range, Map<Integer, BoolExpr> regUpdate, Z3Engine z3engine){

        Z3Variable var = z3engine.getVars();

    	if (! range){
    		FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
    		final int regCount = instruction.getRegisterCount();
    		switch (regCount) {
                case 1:
                    regUpdate.put(instruction.getRegisterC(), var.getL(instruction.getRegisterC()));
                    break;

                case 2:
                    regUpdate.put(instruction.getRegisterC(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterC()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterC()),
                                            var.getL(instruction.getRegisterD())
                                    )
                            )
                    );
                    regUpdate.put(instruction.getRegisterD(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterD()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterD()),
                                            var.getL(instruction.getRegisterC())
                                    )
                            )
                    );
                    break;

                case 3:
                    regUpdate.put(instruction.getRegisterC(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterC()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterC()),
                                            z3engine.or(
                                                    var.getL(instruction.getRegisterD()),
                                                    var.getL(instruction.getRegisterE())
                                            )
                                    )
                            )
                    );
                    regUpdate.put(instruction.getRegisterD(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterD()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterD()),
                                            z3engine.or(
                                                    var.getL(instruction.getRegisterC()),
                                                    var.getL(instruction.getRegisterE())
                                            )
                                    )
                            )
                    );
                    regUpdate.put(instruction.getRegisterE(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterE()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterE()),
                                            z3engine.or(
                                                    var.getL(instruction.getRegisterC()),
                                                    var.getL(instruction.getRegisterD())
                                            )
                                    )
                            )
                    );
                    break;

                case 4:
                    regUpdate.put(instruction.getRegisterC(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterC()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterC()),
                                            z3engine.or(
                                                    var.getL(instruction.getRegisterD()),
                                                    var.getL(instruction.getRegisterE()),
                                                    var.getL(instruction.getRegisterF())
                                            )
                                    )
                            )
                    );
                    regUpdate.put(instruction.getRegisterD(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterD()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterD()),
                                            z3engine.or(
                                                    var.getL(instruction.getRegisterC()),
                                                    var.getL(instruction.getRegisterE()),
                                                    var.getL(instruction.getRegisterF())
                                            )
                                    )
                            )
                    );
                    regUpdate.put(instruction.getRegisterE(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterE()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterE()),
                                            z3engine.or(
                                                    var.getL(instruction.getRegisterD()),
                                                    var.getL(instruction.getRegisterC()),
                                                    var.getL(instruction.getRegisterF())
                                            )
                                    )
                            )
                    );
                    regUpdate.put(instruction.getRegisterF(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterF()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterF()),
                                            z3engine.or(
                                                    var.getL(instruction.getRegisterD()),
                                                    var.getL(instruction.getRegisterE()),
                                                    var.getL(instruction.getRegisterC())
                                            )
                                    )
                            )
                    );
                    break;
                case 5:
                    regUpdate.put(instruction.getRegisterC(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterC()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterC()),
                                            z3engine.or(
                                                    var.getL(instruction.getRegisterD()),
                                                    var.getL(instruction.getRegisterE()),
                                                    var.getL(instruction.getRegisterF()),
                                                    var.getL(instruction.getRegisterG())
                                            )
                                    )
                            )
                    );
                    regUpdate.put(instruction.getRegisterD(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterD()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterD()),
                                            z3engine.or(
                                                    var.getL(instruction.getRegisterC()),
                                                    var.getL(instruction.getRegisterE()),
                                                    var.getL(instruction.getRegisterF()),
                                                    var.getL(instruction.getRegisterG())
                                            )
                                    )
                            )
                    );
                    regUpdate.put(instruction.getRegisterE(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterE()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterE()),
                                            z3engine.or(
                                                    var.getL(instruction.getRegisterD()),
                                                    var.getL(instruction.getRegisterC()),
                                                    var.getL(instruction.getRegisterF()),
                                                    var.getL(instruction.getRegisterG())
                                            )
                                    )
                            )
                    );
                    regUpdate.put(instruction.getRegisterF(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterF()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterF()),
                                            z3engine.or(
                                                    var.getL(instruction.getRegisterD()),
                                                    var.getL(instruction.getRegisterE()),
                                                    var.getL(instruction.getRegisterC()),
                                                    var.getL(instruction.getRegisterG())
                                            )
                                    )
                            )
                    );
                    regUpdate.put(instruction.getRegisterG(),
                            z3engine.or(
                                    var.getL(instruction.getRegisterG()),
                                    z3engine.and(
                                            var.getB(instruction.getRegisterG()),
                                            z3engine.or(
                                                    var.getL(instruction.getRegisterD()),
                                                    var.getL(instruction.getRegisterE()),
                                                    var.getL(instruction.getRegisterF()),
                                                    var.getL(instruction.getRegisterC())
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
        	BoolExpr orLabels = z3engine.mkFalse();
        	switch (regCount){
                case 0: return regUpdate;
                case 1: return regUpdate;
                default:
                    for (int reg = startRegister; reg <= endRegister; reg++ ){
                        orLabels = z3engine.mkFalse();
                        for (int reg2 = startRegister; reg2 <= endRegister; reg2++ ){
                            if (reg2 == reg){ continue; }
                            z3engine.or(orLabels, var.getL(reg));
                        }
                        regUpdate.put(reg,
                                z3engine.or(
                                        var.getL(reg),
                                        z3engine.and(
                                                var.getB(reg),
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


    private boolean processIntent(final Z3Engine z3engine, final int ci, final int mi, final int numParLoc, final int numRegLoc, final int nextCode, final int c, final int m, final String shortMethodName,
   		 final int size){

        BoolExpr h, b, h2, b2, h6, b6;
        Z3Variable var = z3engine.getVars();
	    Map<Integer, BitVecExpr> regUpdate = new HashMap<>();
	    Map<Integer, BoolExpr> regUpdateL = new HashMap<>();
	    Map<Integer, BoolExpr> regUpdateB = new HashMap<>();
        Map<Integer, Boolean> fields = Collections.synchronizedMap(new HashMap <Integer, Boolean>());

       ////////////////////////////////////

       if  (c == ("Landroid/os/Parcel;".hashCode()) &&
   			("writeValue(Ljava/lang/Object;)V".hashCode()) == m){
       	    if (    this.instruction instanceof FiveRegisterInstruction
                ||  this.instruction instanceof RegisterRangeInstruction) {

                int registerC, registerD;
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                    registerD = ((FiveRegisterInstruction) instruction).getRegisterD();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                    registerD = ((RegisterRangeInstruction) instruction).getStartRegister() + 1;
                }

                h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b2 = z3engine.hPred(z3engine.mkBitVector("Landroid/os/Parcel;".hashCode(), size),
                var.getV(registerC), z3engine.mkBitVector(0, size),
                var.getV(registerD), var.getL(registerD), var.getB(registerD));
                z3engine.addRule(z3engine.implies(h2, b2), null);

                h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
                return true;
            }
       }
       if  (c == ("Landroid/os/Parcel;".hashCode()) &&
   			("marshall()[B".hashCode()) == m){
            if (    this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerC;
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                }

                h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(numRegLoc, var.getV(registerC));
                regUpdateL.put(numRegLoc, var.getL(registerC));
                regUpdateB.put(numRegLoc, var.getB(registerC));
                b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
                return true;
            }
       }
       if  (c == ("Landroid/os/Parcel;".hashCode()) &&
   			("unmarshall([BII)V".hashCode()) == m){
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

                h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                regUpdate.put(registerC, var.getV(registerD));
                regUpdateL.put(registerC, var.getL(registerD));
                regUpdateB.put(registerC, var.getB(registerD));
                b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
                return true;
            }
       }
       if  (c == ("Landroid/os/Parcel;".hashCode()) &&
   			("readValue(Ljava/lang/ClassLoader;)Ljava/lang/Object;".hashCode()) == m){
            if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerC;
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                }

                h = z3engine.and(
                        z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                        z3engine.hPred(z3engine.mkBitVector("Landroid/os/Parcel;".hashCode(), size),
                               var.getV(registerC), z3engine.mkBitVector(0, size),
                               var.getF(), var.getLf(), var.getBf())
                );
                regUpdate.put(numRegLoc, var.getF());
                regUpdateL.put(numRegLoc, var.getLf());
                regUpdateB.put(numRegLoc, var.getBf());
                b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
                return true;
            }
       }
       if  (c == ("Ljava/lang/RuntimeException;".hashCode()) &&
   			("<init>(Ljava/lang/String;)V".hashCode()) == m){
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

                h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b2 = z3engine.hPred(z3engine.mkBitVector("Ljava/lang/RuntimeException;".hashCode(), size),
                       var.getV(registerC), z3engine.mkBitVector("message".hashCode(), size),
                       var.getV(registerD), var.getL(registerD), var.getB(registerD));
                z3engine.addRule(z3engine.implies(h2, b2), null);
                h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
            } else {
                h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b2 = z3engine.hPred(z3engine.mkBitVector("Ljava/lang/RuntimeException;".hashCode(), size),
                var.getF(), z3engine.mkBitVector("message".hashCode(), size),
                var.getFpp(), var.getLf(), var.getBf());
                z3engine.addRule(z3engine.implies(h2, b2), null);
                h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                z3engine.addRule(z3engine.implies(h, b), null);
                return true;
            }
       }
       if  (c == ("Ljava/lang/RuntimeException;".hashCode()) &&
   			("getMessage()Ljava/lang/String;".hashCode()) == m){
            if (this.instruction instanceof FiveRegisterInstruction
                ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerC;
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                }

                h = z3engine.and(
                       z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                       z3engine.hPred(z3engine.mkBitVector("Ljava/lang/RuntimeException;".hashCode(), size),
                               var.getV(registerC), z3engine.mkBitVector("message".hashCode(), size),
                               var.getF(), var.getLf(), var.getBf())
                );
                regUpdate.put(numRegLoc, var.getF());
                regUpdateL.put(numRegLoc, var.getLf());
                regUpdateB.put(numRegLoc, var.getBf());
               b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               z3engine.addRule(z3engine.implies(h, b), null);
                return true;
            }
       }
       if  (c == ("Landroid/telephony/SmsManager;".hashCode()) &&
   			("getDefault()Landroid/telephony/SmsManager;".hashCode()) == m){
			final int instanceNum = analysis.getInstNum(ci, mi, codeAddress);
           h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           b2 = z3engine.hPred(z3engine.mkBitVector("Landroid/telephony/SmsManager;".hashCode(), size),
                   z3engine.mkBitVector(instanceNum, size), var.getF(), var.getVfp(), z3engine.mkFalse(), var.getBf());
           z3engine.addRule(z3engine.implies(h2, b2), null);
           h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
   		    regUpdate.put(numRegLoc, z3engine.mkBitVector(instanceNum, size));
			regUpdateL.put(numRegLoc, z3engine.mkFalse());
			regUpdateB.put(numRegLoc, z3engine.mkTrue());
           b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h, b), null);
			return true;
       }
       if  (c == ("Landroid/graphics/PointF;".hashCode()) &&
   			("<init>(FF)V".hashCode()) == m){
            if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerC, registerD, registerE;
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                    registerD = ((FiveRegisterInstruction) instruction).getRegisterD();
                    registerE = ((FiveRegisterInstruction) instruction).getRegisterE();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                    registerD = ((RegisterRangeInstruction) instruction).getStartRegister() + 1;
                    registerE = ((RegisterRangeInstruction) instruction).getStartRegister() + 2;
                }
               h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               b2 = z3engine.hPred(z3engine.mkBitVector("Landroid/graphics/PointF;".hashCode(), size),
                    var.getV(registerC), z3engine.mkBitVector("x:F".hashCode(), size),
                       var.getV(registerD), var.getL(registerD), var.getB(registerD));
               z3engine.addRule(z3engine.implies(h2, b2), null);
               h6 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               b6 = z3engine.hPred(z3engine.mkBitVector("Landroid/graphics/PointF;".hashCode(), size),
                       var.getV(registerC), z3engine.mkBitVector("y:F".hashCode(), size),
                       var.getV(registerE), var.getL(registerE), var.getB(registerE));
               z3engine.addRule(z3engine.implies(h6, b6), null);
               h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               z3engine.addRule(z3engine.implies(h, b), null);
                return true;
            }
       }
       if  (c == ("Ljava/util/Map;".hashCode()) &&
   			("put(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;".hashCode()) == m){
       	if (this.instruction instanceof FiveRegisterInstruction
                ||  this.instruction instanceof RegisterRangeInstruction ) {

            int registerC, registerD, registerE;
            if(this.instruction instanceof FiveRegisterInstruction){
                registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                registerD = ((FiveRegisterInstruction) instruction).getRegisterD();
                registerE = ((FiveRegisterInstruction) instruction).getRegisterE();
            } else {
                registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                registerD = ((RegisterRangeInstruction) instruction).getStartRegister() + 1;
                registerE = ((RegisterRangeInstruction) instruction).getStartRegister() + 2;
            }

           h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           b2 = z3engine.hPred(z3engine.mkBitVector("Ljava/util/Map;".hashCode(), size),
                   var.getV(registerC), var.getV(registerD),
                   var.getV(registerE), var.getL(registerE), var.getB(registerE));
           z3engine.addRule(z3engine.implies(h2, b2), null);
           h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h, b), null);
			return true;
       	}
       }
       if  (c == ("Ljava/util/Map;".hashCode()) &&
   			("get(Ljava/lang/Object;)Ljava/lang/Object;".hashCode()) == m){
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
           h = z3engine.and(
                   z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                   z3engine.hPred(z3engine.mkBitVector("Ljava/util/Map;".hashCode(), size),
                           var.getV(registerC), var.getV(registerD),
                           var.getF(), var.getLf(), var.getBf())
           );
   		regUpdate.put(numRegLoc, var.getF());
			regUpdateL.put(numRegLoc, var.getLf());
			regUpdateB.put(numRegLoc, var.getBf());
           b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h, b), null);
			return true;
       	}
       }
       if  (c == ("Ljava/lang/String;".hashCode()) &&
   			("getChars(II[CI)V".hashCode()) == m){
       	if (this.instruction instanceof FiveRegisterInstruction
                ||  this.instruction instanceof RegisterRangeInstruction ) {

            int registerC, registerF;
            if(this.instruction instanceof FiveRegisterInstruction){
                registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                registerF = ((FiveRegisterInstruction) instruction).getRegisterF();
            } else {
                registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                registerF = ((RegisterRangeInstruction) instruction).getStartRegister() + 3;
            }

           h = z3engine.and(
                   z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate,
                           regUpdateL, regUpdateB, numParLoc, numRegLoc),
                   z3engine.hPred( z3engine.mkBitVector("[C".hashCode(), size), var.getV(registerF),
                           z3engine.mkBitVector(0, size), var.getF(), var.getLf(), var.getBf())
           );
           b = z3engine.hPred(
                   z3engine.mkBitVector("[C".hashCode(), size), var.getV(registerF),
                   z3engine.mkBitVector(0, size), var.getFpp(), var.getL(registerC), var.getB(registerC));
           z3engine.addRule(z3engine.implies(h, b), null);
           h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h2, b2), null);
			return true;
       	}
       }
       if  (c == ("Ljava/util/Formatter;".hashCode()) &&
   			("<init>(Ljava/lang/Appendable;)V".hashCode()) == m){
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

               h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               b = z3engine.hPred(
                       z3engine.mkBitVector("Ljava/lang/StringBuffer;".hashCode(), size), var.getV(registerD),
                       z3engine.mkBitVector(0, size), var.getV(registerC), z3engine.mkFalse(), z3engine.mkTrue());
               z3engine.addRule(z3engine.implies(h, b), null);
               h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               z3engine.addRule(z3engine.implies(h2, b2), null);
       	} else {
               h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
   			b = z3engine.hPred(
                       z3engine.mkBitVector("Ljava/lang/StringBuffer;".hashCode(), size), var.getF(),
                       z3engine.mkBitVector(0, size), var.getFpp(), z3engine.mkFalse(), z3engine.mkTrue());
               z3engine.addRule(z3engine.implies(h, b), null);
               h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               z3engine.addRule(z3engine.implies(h2, b2), null);
   			return true;
       	}
       }
       if  (c == ("Ljava/util/Formatter;".hashCode()) &&
   			("format(Ljava/lang/String;[Ljava/lang/Object;)Ljava/util/Formatter;".hashCode()) == m){
       	if (this.instruction instanceof FiveRegisterInstruction
                ||  this.instruction instanceof RegisterRangeInstruction ) {

            int registerC, registerD, registerE;
            if(this.instruction instanceof FiveRegisterInstruction){
                registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                registerD = ((FiveRegisterInstruction) instruction).getRegisterD();
                registerE = ((FiveRegisterInstruction) instruction).getRegisterE();
            } else {
                registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                registerD = ((RegisterRangeInstruction) instruction).getStartRegister() + 1;
                registerE = ((RegisterRangeInstruction) instruction).getStartRegister() + 2;
            }

               h = z3engine.and(
                       z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress,
                               regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                       z3engine.hPred(
                               z3engine.mkBitVector("Ljava/lang/StringBuffer;".hashCode(), size), var.getF(),
                               z3engine.mkBitVector(0, size), var.getV(registerC),
                               z3engine.mkFalse(), z3engine.mkTrue())
               );
               b = z3engine.hPred(
                       z3engine.mkBitVector("Ljava/lang/StringBuffer;".hashCode(), size), var.getF(),
                       z3engine.mkBitVector(0, size), var.getV(registerC),
                       z3engine.or(var.getL(registerD), var.getL(registerE)),
                       z3engine.mkTrue());
               z3engine.addRule(z3engine.implies(h, b), null);
               h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               z3engine.addRule(z3engine.implies(h2, b2), null);
       	} else {
               h = z3engine.and(
                       z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress,
                               regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                       z3engine.hPred(
                               z3engine.mkBitVector("Ljava/lang/StringBuffer;".hashCode(), size), var.getF(),
                               z3engine.mkBitVector(0, size), var.getF(), z3engine.mkFalse(), z3engine.mkTrue())
               );
               b = z3engine.hPred(
                       z3engine.mkBitVector("Ljava/lang/StringBuffer;".hashCode(), size), var.getF(),
                       z3engine.mkBitVector(0, size), var.getF(), var.getLf(), z3engine.mkTrue());
               z3engine.addRule(z3engine.implies(h, b), null);
               h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               z3engine.addRule(z3engine.implies(h2, b2), null);
   			return true;
       	}
       }
       if  (c == ("Ljava/lang/StringBuffer;".hashCode()) &&
   			("toString()Ljava/lang/String;".hashCode()) == m){
       	if (this.instruction instanceof FiveRegisterInstruction
                ||  this.instruction instanceof RegisterRangeInstruction ) {

            int registerC;
            if(this.instruction instanceof FiveRegisterInstruction){
                registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
            } else {
                registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
            }
           h = z3engine.and(
                   z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress,
                           regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                   z3engine.hPred(
                           z3engine.mkBitVector("Ljava/lang/StringBuffer;".hashCode(), size),
                           var.getV(registerC),
                           z3engine.mkBitVector(0, size), var.getF(), var.getLf(), var.getBf())
           );
           regUpdate.put(numRegLoc, var.getFpp());
           regUpdateL.put(numRegLoc, var.getLf());
           regUpdateB.put(numRegLoc, var.getBf());
           b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h, b), null);
           return true;
       	}
       }
       if  (c == ("Ljava/lang/System;".hashCode()) &&
   			("arraycopy(Ljava/lang/Object;ILjava/lang/Object;II)V".hashCode()) == m){
       	if (this.instruction instanceof FiveRegisterInstruction
                ||  this.instruction instanceof RegisterRangeInstruction ) {

            int registerC, registerE;
            if(this.instruction instanceof FiveRegisterInstruction){
                registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                registerE = ((FiveRegisterInstruction) instruction).getRegisterE();
            } else {
                registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                registerE = ((RegisterRangeInstruction) instruction).getStartRegister() + 2;
            }

           h = z3engine.and(
                   z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                   z3engine.hPred(
                           var.getCn(), var.getV(registerC),
                           z3engine.mkBitVector(0, size), var.getVal(), var.getLf(), var.getBf())
           );
           b = z3engine.hPred(
					var.getCn(), var.getV(registerE),
					z3engine.mkBitVector(0, size), var.getVal(), var.getLf(), var.getBf());
           z3engine.addRule(z3engine.implies(h, b), null);
           h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h2, b2), null);
			return true;
       	}
       }
       if  (c == ("Landroid/widget/Button;".hashCode()) &&
   			("getHint()Ljava/lang/CharSequence;".hashCode()) == m){
       	if (this.instruction instanceof FiveRegisterInstruction
                ||  this.instruction instanceof RegisterRangeInstruction ) {

            int registerC;
            if(this.instruction instanceof FiveRegisterInstruction){
                registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
            } else {
                registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
            }

			h = z3engine.and(
                   z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                   z3engine.hPred(
                           z3engine.mkBitVector("Landroid/widget/Button;".hashCode(), size), var.getV(registerC),
                           z3engine.mkBitVector("hint".hashCode(), size), var.getVal(), var.getLf(), var.getBf())
           );
           regUpdate.put(numRegLoc, var.getVal());
			regUpdateL.put(numRegLoc, var.getLf());
			regUpdateB.put(numRegLoc, var.getBf());
			b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h, b), null);

			regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

           h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
			regUpdate.put(numRegLoc, z3engine.mkBitVector(0, size));
			regUpdateL.put(numRegLoc, z3engine.mkFalse());
			regUpdateB.put(numRegLoc, z3engine.mkTrue());
           b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h2, b2), null);
			return true;
       	}
       }
       if  (c == ("Landroid/widget/Button;".hashCode()) &&
   			("setHint(Ljava/lang/CharSequence;)V".hashCode()) == m){
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
           h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           b = z3engine.hPred(
                   z3engine.mkBitVector("Landroid/widget/Button;".hashCode(), size), var.getV(registerC),
                   z3engine.mkBitVector("hint".hashCode(), size), var.getV(registerD),
                   var.getL(registerD), var.getB(registerD));
           z3engine.addRule(z3engine.implies(h, b), null);
           h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h2, b2), null);
			return true;
       	}
       }
       if  ("getSystemService(Ljava/lang/String;)Ljava/lang/Object;".hashCode() == m){
       	if (this.instruction instanceof FiveRegisterInstruction
            || this.instruction instanceof RegisterRangeInstruction){
			final int instanceNum = analysis.getInstNum(ci, mi, codeAddress);
           h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           b2 = z3engine.hPred(z3engine.mkBitVector("Ljava/lang/Object;".hashCode(), size),
                   z3engine.mkBitVector(instanceNum, size), var.getF(), var.getVfp(), z3engine.mkFalse(), var.getBf());
           z3engine.addRule(z3engine.implies(h2, b2), null);
           h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
   		regUpdate.put(numRegLoc, z3engine.mkBitVector(instanceNum, size));
			regUpdateL.put(numRegLoc, z3engine.mkFalse());
			regUpdateB.put(numRegLoc, z3engine.mkTrue());
           b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h, b), null);
			return true;
       	}
       }
       ////////////////////////////////////


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

			h2 = z3engine.and(
                   z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                   z3engine.hiPred(
                           var.getCn(), var.getV(registerC), var.getVal(), var.getLf(), var.getBf())
           );
           b2 = z3engine.hiPred(
                   var.getV(registerD), var.getV(registerC), var.getVal(), var.getLf(), var.getBf());
           z3engine.addRule(z3engine.implies(h2, b2), null);
           h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
			regUpdate.put(registerC, var.getV(registerC));
			regUpdateL.put(registerC, var.getL(registerC));
			regUpdateB.put(registerC, var.getB(registerC));
           b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h, b), null);
       	return true;
       	}
       }

		if  (c == ("Landroid/content/Intent;".hashCode()) &&
			("<init>(Landroid/content/Context;Ljava/lang/Class;)V".hashCode()) == m){
			final int instanceNum = analysis.getInstNum(ci, mi, codeAddress);
			if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerC, registerE;
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                    registerE = ((FiveRegisterInstruction) instruction).getRegisterE();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                    registerE = ((RegisterRangeInstruction) instruction).getStartRegister() + 2;
                }

           h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           b2 = z3engine.hiPred(
                   var.getV(registerE), z3engine.mkBitVector(instanceNum, size), z3engine.mkBitVector(0, size), z3engine.mkFalse(), z3engine.mkFalse());
           z3engine.addRule(z3engine.implies(h2, b2), null);

           h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
			regUpdate.put(registerC, z3engine.mkBitVector(instanceNum, size));
			regUpdateL.put(registerC, z3engine.mkFalse());
			regUpdateB.put(registerC, z3engine.mkTrue());
           b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h, b), null);

			regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

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
		if  (c == ("Landroid/content/Intent;".hashCode()) &&
				("<init>(Ljava/lang/String;)V".hashCode()) == m){
           final int instanceNum = analysis.getInstNum(ci, mi, codeAddress);
           if (this.instruction instanceof FiveRegisterInstruction
                   ||  this.instruction instanceof RegisterRangeInstruction ) {

               int registerC, registerE;
               if(this.instruction instanceof FiveRegisterInstruction){
                   registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                   registerE = ((FiveRegisterInstruction) instruction).getRegisterE();
               } else {
                   registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                   registerE = ((RegisterRangeInstruction) instruction).getStartRegister() + 2;
               }

           h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           b2 = z3engine.hiPred(
                   var.getV(registerE), z3engine.mkBitVector(instanceNum, size), z3engine.mkBitVector(0, size), z3engine.mkFalse(), z3engine.mkFalse());
           z3engine.addRule(z3engine.implies(h2, b2), null);

           h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           regUpdate.put(registerC, z3engine.mkBitVector(instanceNum, size));
           regUpdateL.put(registerC, z3engine.mkFalse());
           regUpdateB.put(registerC, z3engine.mkTrue());
           b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h, b), null);

           regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

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
		if  (c == ("Landroid/content/Intent;".hashCode()) &&
				("<init>()V".hashCode()) == m){
				final int instanceNum = analysis.getInstNum(ci, mi, codeAddress);
            if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerC;
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                }

           h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           b2 = z3engine.hiPred(
                   var.getF(), z3engine.mkBitVector(instanceNum, size),
                   z3engine.mkBitVector(0, size), z3engine.mkFalse(), z3engine.mkFalse());
           z3engine.addRule(z3engine.implies(h2, b2), null);
           h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           regUpdate.put(registerC, z3engine.mkBitVector(instanceNum, size));
           regUpdateL.put(registerC, z3engine.mkFalse());
           regUpdateB.put(registerC, z3engine.mkTrue());
           b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h, b), null);

           regUpdate.clear(); regUpdateL.clear(); regUpdateB.clear();

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
		if (("startActivity(Landroid/content/Intent;)V".hashCode() == m) || shortMethodName.contains("startActivityForResult")){
			if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerD;
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerD = ((FiveRegisterInstruction) instruction).getRegisterD();
                } else {
                    registerD = ((RegisterRangeInstruction) instruction).getStartRegister() + 1;
                }

			h = z3engine.and(
                   z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                   z3engine.hiPred(
                           var.getCn(), var.getV(registerD), var.getVal(), var.getLf(), var.getBf())
           );
           b = z3engine.iPred(
                   var.getCn(), z3engine.mkBitVector(c, size), var.getVal(), var.getLf(), var.getBf());
           z3engine.addRule(z3engine.implies(h, b), null);

           h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h2, b2), null);

//			Clause cl3 = new Clause();
           BoolExpr h3 = z3engine.and(
                   z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                   z3engine.hiPred(
                           var.getCn(), var.getV(registerD), var.getVal(), var.getLf(), var.getBf())
           );
			final BitVecExpr inC = z3engine.mkBitVector((Utils.Dec(registerD) + Utils.Dec(c)).hashCode(), size); // in(c) = _ + _)
           BoolExpr b3 = z3engine.hiPred(var.getCn(), inC, var.getVal(), var.getLf(), var.getBf());
           z3engine.addRule(z3engine.implies(h3, b3), null);

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
		if (shortMethodName.contains((String) "putExtra") && c == ("Landroid/content/Intent;".hashCode())){
			if (this.instruction instanceof FiveRegisterInstruction){
			FiveRegisterInstruction instruction = (FiveRegisterInstruction)this.instruction;
			h = z3engine.and(
                   z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                   z3engine.hiPred(
                           var.getCn(), var.getV(instruction.getRegisterC()), var.getVal(), var.getLf(), var.getBf())
           );
           b = z3engine.hiPred(var.getCn(), var.getV(instruction.getRegisterC()),
                   var.getV(instruction.getRegisterE()), var.getL(instruction.getRegisterE()), var.getB(instruction.getRegisterE()));
           z3engine.addRule(z3engine.implies(h, b), null);

           h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
			regUpdateL.put(instruction.getRegisterC(), z3engine.or(var.getL(instruction.getRegisterC()), var.getL(instruction.getRegisterE())));
           b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h2, b2), null);
			return true;
			}
		}
		if  (c == ("Landroid/content/Intent;".hashCode()) &&
				("getAction()Ljava/lang/String;".hashCode()) == m){
           h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
			regUpdate.put(numRegLoc, var.getVal());
			regUpdateL.put(numRegLoc, z3engine.mkFalse());
			regUpdateB.put(numRegLoc, var.getBf());
           b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h, b), null);
			return true;
		}
		if (shortMethodName.contains((String) "get") && c == ("Landroid/content/Intent;".hashCode())){
			if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerC;
                if(this.instruction instanceof FiveRegisterInstruction){
                    registerC = ((FiveRegisterInstruction) instruction).getRegisterC();
                } else {
                    registerC = ((RegisterRangeInstruction) instruction).getStartRegister();
                }

               if (analysis.isSource(c, m)){
                   h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                   regUpdate.put(numRegLoc, var.getVal());
                   regUpdateL.put(numRegLoc, z3engine.mkTrue());
                   regUpdateB.put(numRegLoc, var.getBf());
                   b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                   z3engine.addRule(z3engine.implies(h, b), null);
               } else {
                   h = z3engine.and(
                           z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                           z3engine.hiPred(
                                   var.getCn(), var.getV(registerC), var.getVal(), var.getLf(), var.getBf())
                   );
                   regUpdate.put(numRegLoc, var.getVal());
                   regUpdateL.put(numRegLoc, var.getLf());
                   regUpdateB.put(numRegLoc, var.getBf());
                   b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                   z3engine.addRule(z3engine.implies(h, b), null);
               }
           } else {
				if (analysis.isSource(c, m)){
                   h = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
					regUpdate.put(numRegLoc, var.getVal());
					regUpdateL.put(numRegLoc, z3engine.mkTrue());
					regUpdateB.put(numRegLoc, var.getBf());
                   b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                   z3engine.addRule(z3engine.implies(h, b), null);
				} else {
                   h = z3engine.and(
                           z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                           z3engine.hiPred(var.getCn(), var.getF(), var.getVal(), var.getLf(), var.getBf())
                   );
					regUpdate.put(numRegLoc, var.getVal());
					regUpdateL.put(numRegLoc, var.getLf());
					regUpdateB.put(numRegLoc, var.getBf());
                   b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
                   z3engine.addRule(z3engine.implies(h, b), null);
				}
				return true;
			}
		}
		if (m ==  "setResult(ILandroid/content/Intent;)V".hashCode()){
			if (this.instruction instanceof FiveRegisterInstruction
                    ||  this.instruction instanceof RegisterRangeInstruction ) {

                int registerE;
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
               z3engine.addRule(z3engine.implies(h, b), null);
               h2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               b2 = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
               z3engine.addRule(z3engine.implies(h2, b2), null);
                return true;
            }
		}
		if (m ==  "getIntent()Landroid/content/Intent;".hashCode()){
			h = z3engine.and(
                   z3engine.rPred(Integer.toString(ci), Integer.toString(mi), codeAddress, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc),
                   z3engine.hPred(z3engine.mkBitVector(c, size), z3engine.mkBitVector(c, size), z3engine.mkBitVector("intent".hashCode(), size), var.getVal(), var.getLf(), var.getBf())
            );
           regUpdate.put(numRegLoc, var.getVal());
			regUpdateL.put(numRegLoc, var.getLf());
			regUpdateB.put(numRegLoc, var.getBf());
           b = z3engine.rPred(Integer.toString(ci), Integer.toString(mi), nextCode, regUpdate, regUpdateL, regUpdateB, numParLoc, numRegLoc);
           z3engine.addRule(z3engine.implies(h, b), null);
			return true;
		}
		return false;
	}

}
