package analysis;


import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;


import org.jf.baksmali.Adaptors.ClassDefinition;
import org.jf.baksmali.Adaptors.MethodDefinition;
import org.jf.baksmali.Adaptors.MethodDefinition.InvalidSwitchPayload;
import org.jf.dexlib2.AccessFlags;
import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.dexbacked.DexBackedClassDef;
import org.jf.dexlib2.iface.ClassDef;
import org.jf.dexlib2.iface.Field;
import org.jf.dexlib2.iface.Method;
import org.jf.dexlib2.iface.MethodImplementation;
import org.jf.dexlib2.iface.MethodParameter;
import org.jf.dexlib2.iface.instruction.FiveRegisterInstruction;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.OneRegisterInstruction;
import org.jf.dexlib2.iface.instruction.ReferenceInstruction;
import org.jf.dexlib2.iface.instruction.SwitchElement;
import org.jf.dexlib2.iface.instruction.formats.ArrayPayload;
import org.jf.dexlib2.iface.instruction.formats.Instruction31t;
import org.jf.dexlib2.iface.instruction.formats.PackedSwitchPayload;
import org.jf.dexlib2.iface.instruction.formats.SparseSwitchPayload;
import org.jf.dexlib2.iface.reference.FieldReference;
import org.jf.dexlib2.iface.reference.MethodReference;
import org.jf.dexlib2.iface.reference.Reference;
import org.jf.dexlib2.iface.value.EncodedValue;
import org.jf.dexlib2.util.ReferenceUtil;
import org.jf.dexlib2.util.TypeUtils;
import org.jf.util.ExceptionWithContext;

import payload.ArrayData;
import payload.PackedSwitch;
import payload.SparseSwitch;
import strings.ConstString;
import util.Utils;

import com.google.common.collect.ImmutableList;

import Dalvik.DalvikClass;
import Dalvik.DalvikField;
import Dalvik.DalvikInstance;
import Dalvik.DalvikMethod;
import Dalvik.DalvikStaticField;
import Dalvik.GeneralClass;
import Dalvik.Instances;

public class DataExtraction {
    final private Map<Integer,GeneralClass> classes;
    final private Instances instances;
    final private Set<ArrayData> arrayDataPayload;
    final private Set<PackedSwitch> packedSwitchPayload;
    final private Set<SparseSwitch> sparseSwitchPayload;
    final private Set<Integer> staticConstructor;
    final private Set<ConstString> constStrings;
    
    
    private final Set<Integer> launcherActivities;
    

    


    public DataExtraction(Map<Integer,GeneralClass> classes, Instances instances, Set<ArrayData> arrayDataPayload, 
             Set<PackedSwitch> packedSwitchPayload, Set<SparseSwitch> sparseSwitchPayload, 
             Set<Integer> staticConstructor, Set<ConstString> constStrings, Set<Integer> launcherActivities){
        this.classes = classes;
        this.instances = instances;
        this.arrayDataPayload = arrayDataPayload;
        this.packedSwitchPayload = packedSwitchPayload;
        this.sparseSwitchPayload = sparseSwitchPayload;
        this.staticConstructor = staticConstructor;
        this.constStrings = constStrings;
        
        this.launcherActivities = launcherActivities;
    }
    
    private void formClassStructure(){
        for (final GeneralClass c: classes.values()){
            if (c instanceof DalvikClass){
                final DalvikClass cd = (DalvikClass) c;
                if (cd.getSuperClass().getType() == null){
                    // Happens only for Ljava/lang/Object;
                    cd.putSuperClass(null);
                }else{
                    GeneralClass cs = classes.get(cd.getSuperClass().getType().hashCode());
                    if (cs != null){
                        cd.putSuperClass(cs);
                        if (cs instanceof DalvikClass){
                            ((DalvikClass) cs).putChildClass(cd);
                        }
                    }
                }
                
                final Set<GeneralClass> interfaces = cd.getInterfaces();
                for (final GeneralClass ic: interfaces){
                    final int interfaceClass = ic.getType().hashCode();
                    GeneralClass cs = classes.get(interfaceClass);
                    if (cs instanceof DalvikClass && !(ic instanceof DalvikClass)){
                        interfaces.remove(ic);
                        interfaces.add(cs);
                    }
                }
                cd.putInterfaces(interfaces);
                
                instances.changeType(cd);
            }
        }
    }
    


    public void collectData(final List<? extends ClassDef> classDefs) {
        ConcurrentHashMap<Integer,ClassDef> classDefsMap = new ConcurrentHashMap<Integer,ClassDef>();
        for (ClassDef classDef : classDefs){
            classDefsMap.put(classDef.getType().hashCode(),classDef);
        }
        
        for (final ClassDef classDef: classDefsMap.values()) {
            DalvikClass c = collectDataFromClass(classDefsMap, classDef);
            classes.put(c.getType().hashCode(),c);
        }
        formClassStructure();
    }       


    private DalvikClass collectDataFromClass(final Map<Integer,ClassDef> classDefsMap, final ClassDef classDef) {
        final DalvikClass dc = new DalvikClass(classDef.getType());
        dc.putSuperClass(new GeneralClass(classDef.getSuperclass()));
        final Set<GeneralClass> inter = Collections.newSetFromMap(new ConcurrentHashMap<GeneralClass,Boolean>());
        for (final String interfaceName: classDef.getInterfaces()){
            inter.add(new GeneralClass(interfaceName));
        }
        dc.putInterfaces(inter);

        Set<DalvikField> dalvikFields = collectDataFromFields(classDef, false);
        dalvikFields.addAll(collectDataFromFields(classDef, true));
        dc.putFields(dalvikFields);
        Set<DalvikMethod> dalvikMethods = collectDataFromMethods(classDefsMap, classDef, false); //direct
        dalvikMethods.addAll(collectDataFromMethods(classDefsMap, classDef, true)); //virtual
        dc.putMethods(dalvikMethods);
        return dc;
    }

    private Set<DalvikField> collectDataFromFields(final ClassDef classDef, final boolean dynamic){
        final Set<DalvikField> dalvikFields = Collections.newSetFromMap(new ConcurrentHashMap <DalvikField, Boolean>());
        Iterable<? extends Field> fields;
        if (!dynamic){
            if (classDef instanceof DexBackedClassDef) {
                fields = ((DexBackedClassDef)classDef).getStaticFields(false);
            } else {
                fields = classDef.getStaticFields();
            }
        }
        else{
            if (classDef instanceof DexBackedClassDef) {
                fields = ((DexBackedClassDef)classDef).getInstanceFields(false);
            } else {
                fields = classDef.getInstanceFields();
            }
        }

        for (Field field: fields) {
            EncodedValue initialValue = field.getInitialValue();
            if (initialValue != null) {

                DalvikStaticField dsf = new DalvikStaticField(ReferenceUtil.getShortFieldDescriptor(field), initialValue);
                dalvikFields.add(dsf);
            }
            else{
                final String fieldName = ReferenceUtil.getShortFieldDescriptor(field);                  
                dalvikFields.add(new DalvikField(fieldName));
            }
        }
        return dalvikFields;
    }

    private Set<DalvikMethod> collectDataFromMethods(final Map<Integer,ClassDef> classDefsMap, final ClassDef classDef, final boolean virtual) {
        final Set<DalvikMethod> dalvikMethods = Collections.newSetFromMap(new ConcurrentHashMap<DalvikMethod, Boolean>());
        Iterable<? extends Method> methods;
        if (!virtual){
            if (classDef instanceof DexBackedClassDef) {
                methods = ((DexBackedClassDef)classDef).getDirectMethods(false);
            } else {
                methods = classDef.getDirectMethods();
            }
        }
        else{
            if (classDef instanceof DexBackedClassDef) {
                methods = ((DexBackedClassDef)classDef).getVirtualMethods(false);
            } else {
                methods = classDef.getVirtualMethods();
            } 
        }
        for (Method method: methods) {
            String methodString = Utils.getShortMethodDescriptor(method);             
            String methodIndex  = Utils.Dec(methodString.hashCode());
            String classIndex  = Utils.Dec(classDef.getType().hashCode());
            MethodImplementation methodImpl = method.getImplementation();
            if (methodImpl == null) {
            } else {
                dalvikMethods.add(collectDataFromMethod(classDefsMap, method, methodImpl, methodString, classIndex, methodIndex, classDef));
            }
        }
        return dalvikMethods;
    }
    private DalvikMethod collectDataFromMethod(final Map<Integer,ClassDef> classDefsMap, final Method method, final MethodImplementation methodImpl, 
            final String methodString, final String classIndex, 
            final String methodIndex,
            final ClassDef classDef){
        int parameterRegisterCount = 0;
        if (!AccessFlags.STATIC.isSet(method.getAccessFlags())) {
            parameterRegisterCount++;
        }

        if (methodString.equals((String) "<clinit>()V")){
            this.putStaticConstructor(method.getDefiningClass().hashCode());
        }
        ImmutableList<MethodParameter> methodParameters = ImmutableList.copyOf(method.getParameters());
        for (MethodParameter parameter: methodParameters) {
            String type = parameter.getType();
            parameterRegisterCount++;
            if (TypeUtils.isWideType(type)) {
                parameterRegisterCount++;
            }
        }
        final boolean callReturns;
        final String returnType = method.getReturnType();
        if (returnType.equals((String) "V")) callReturns = false;
        else callReturns = true;
        Iterable<? extends Instruction> instructions = methodImpl.getInstructions();
        DalvikMethod dm = new DalvikMethod(methodString, parameterRegisterCount, methodImpl.getRegisterCount(), returnType, callReturns, ImmutableList.copyOf(instructions));
        int codeAddress = 0;
        for (Instruction instruction: instructions){
            collect(classDefsMap, instruction, codeAddress, Integer.parseInt(classIndex), Integer.parseInt(methodIndex), classDef, method);
            codeAddress += instruction.getCodeUnits();
        }    
        return dm;
    }
    private void collect(final Map<Integer,ClassDef> classDefsMap, final Instruction instruction, final int codeAddress, final int c, final int m, 
            final ClassDef classDef, final Method method){
        String referenceString = null;
        String referenceStringClass = null;
        int referenceClassIndex = -1;
        int referenceIntIndex = -1;
        String returnType = null;
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
                }
            referenceIntIndex = referenceString.hashCode();
            assert referenceString != null;
        }

        if (instruction instanceof Instruction31t) {
            try {
                ClassDefinition clD = new ClassDefinition(null, classDef);
                MethodDefinition methodDef = new MethodDefinition(clD, method, method.getImplementation());
                Opcode payloadOpcode;
                final int payloadAddress = codeAddress + ((Instruction31t)instruction).getCodeOffset();
                switch (instruction.getOpcode()) {
                case PACKED_SWITCH:
                    payloadOpcode = Opcode.PACKED_SWITCH_PAYLOAD;
                    PackedSwitchPayload psInst = (PackedSwitchPayload) methodDef.findSwitchPayload(codeAddress + ((Instruction31t)instruction).getCodeOffset(),
                            payloadOpcode);
                    boolean first = true;
                    int firstKey = -1;
                    final int basePCodeAddress = methodDef.getPackedSwitchBaseAddress(payloadAddress);
                    final List<Number> targets = new ArrayList<Number>();
                    for (SwitchElement switchElement: psInst.getSwitchElements()) {
                        if (first) {
                            firstKey = switchElement.getKey();
                            first = false;
                        }
                        targets.add(basePCodeAddress + switchElement.getOffset());
                    }
                    packedSwitchPayload.add(new PackedSwitch(c, m, payloadAddress, targets, firstKey));
                    break;
                case SPARSE_SWITCH:
                    payloadOpcode = Opcode.SPARSE_SWITCH_PAYLOAD;
                    final int baseSCodeAddress = methodDef.getSparseSwitchBaseAddress(codeAddress);
                    SparseSwitchPayload ssInst = (SparseSwitchPayload) methodDef.findSwitchPayload(codeAddress + ((Instruction31t)instruction).getCodeOffset(),
                            payloadOpcode);
                    final Map<Integer, Integer> sTargets  = Collections.synchronizedMap(new HashMap <Integer, Integer>());
                    for (SwitchElement switchElement: ssInst.getSwitchElements()) {
                        sTargets.put(switchElement.getKey(), baseSCodeAddress + switchElement.getOffset());
                    }
                    sparseSwitchPayload.add(new SparseSwitch(c, m, payloadAddress, sTargets));
                    break;
                case FILL_ARRAY_DATA:
                    payloadOpcode = Opcode.ARRAY_PAYLOAD;
                    ArrayPayload apInst = (ArrayPayload) methodDef.findSwitchPayload(codeAddress + ((Instruction31t)instruction).getCodeOffset(),
                            payloadOpcode);
                    List<Number> elements = apInst.getArrayElements();
                    arrayDataPayload.add(new ArrayData(c, m, payloadAddress, elements));
                    break;
                default:
                    throw new ExceptionWithContext("Invalid 31t opcode: %s", instruction.getOpcode());
                }
            } catch (InvalidSwitchPayload ex) {
            }
        }

        Opcode opcode = instruction.getOpcode();
        switch (instruction.getOpcode().format) {  
        case Format21c:
            if (opcode.name.equals((String)"const-string")){
                if (referenceString.contains(".")){
                    final String[] parts = referenceString.split("\\.");
                    final String classN = parts[parts.length -1].substring(0, parts[parts.length -1].length()-1);
                    final String dalvikName = "L" + referenceString.substring(1, referenceString.length()-1).replaceAll("\\.", "/") + ";";
                    constStrings.add(new ConstString(c, m, codeAddress, ((OneRegisterInstruction)instruction).getRegisterA(), classN.hashCode(), dalvikName));
                }
                break;
            }
            if (opcode.name.equals((String)"new-instance"))
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(referenceString), true));
            break;
        case Format22c:
            if (opcode.name.equals((String) "new-array"))
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(referenceString), false));
            break;
        case Format35c:

            if (opcode.name.equals((String) "filled-new-array")){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(referenceString), false));
                break;
            }


            if  ((referenceClassIndex == "Ljava/lang/Class;".hashCode()) && 
                    ("newInstance()Ljava/lang/Object;".hashCode() == referenceIntIndex)){
                FiveRegisterInstruction instruction1 = (FiveRegisterInstruction)instruction;
                for (final ConstString constString: constStrings){
                    if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction1.getRegisterC())){
                        instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(constString.getDalvikName()), true));
                        break;
                    }
                }
            }
            
            if  ((referenceClassIndex == "Landroid/content/ComponentName;".hashCode()) && 
                    ("<init>(Landroid/content/Context;Ljava/lang/String;)V".hashCode() == referenceIntIndex)){
                FiveRegisterInstruction instruction1 = (FiveRegisterInstruction)instruction;
                for (final ConstString constString: constStrings){
                    if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction1.getRegisterE())){
                        constString.putPC(codeAddress);
                        constString.putV(instruction1.getRegisterC());
                    }
                }
            }

            if  ((referenceClassIndex == "Landroid/content/Intent;".hashCode()) && 
                    ("setComponent(Landroid/content/ComponentName;)Landroid/content/Intent;".hashCode() == referenceIntIndex)){
                FiveRegisterInstruction instruction1 = (FiveRegisterInstruction)instruction;
                for (final ConstString constString: constStrings){
                    if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction1.getRegisterD())){
                        constString.putPC(codeAddress);
                        constString.putV(instruction1.getRegisterC());
                    }
                }
            }

            if  ("startActivity(Landroid/content/Intent;)V".hashCode() == referenceIntIndex){
                FiveRegisterInstruction instruction1 = (FiveRegisterInstruction)instruction;
                for (final ConstString constString: constStrings){
                    if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction1.getRegisterD())){
                        launcherActivities.add(constString.getVAL());
                    }
                }
            }

            
            if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
                    && (referenceIntIndex == "<init>(Landroid/content/Context;Ljava/lang/Class;)V".hashCode())){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true));
            }

            if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
                    && (referenceIntIndex == "<init>(Ljava/lang/String;)V".hashCode())){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true));
            }


            if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
                    && (referenceIntIndex == "<init>()V".hashCode())){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true));
            }
            try{
                if (returnType.length() > 0){
                    if (returnType.contains("[")){
                        instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(returnType), false));
                        break;
                    }
                    if (returnType.charAt(returnType.length() - 1) == ';'){
                        instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(returnType), true));
                        break;
                    }
                }
            }
            catch (NullPointerException e){
                System.err.println("While parsing instruction: " + instruction.toString());
            }
            break;
        case Format3rc:
            if (opcode.name.equals((String) "filled-new-array/range")){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(referenceString), false));
                break;
            }

            if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
                    && (referenceIntIndex == "<init>(Landroid/content/Context;Ljava/lang/Class;)V".hashCode())){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true));
            }

            if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
                    && (referenceIntIndex == "<init>(Ljava/lang/String;)V".hashCode())){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true));
            }

            if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
                    && (referenceIntIndex == "<init>()V".hashCode())){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true));
            }

            if (returnType.charAt(returnType.length() - 1) == ';'){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(returnType), true));
                break;
            }
            if (returnType.contains("["))
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(returnType), false));
            break;
        default:
            break;
        }
    }
    
    public void putStaticConstructor(int c){
        staticConstructor.add(c);
    }
    
}
