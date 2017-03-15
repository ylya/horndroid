package com.horndroid.analysis;


import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

import com.horndroid.Dalvik.*;
import com.horndroid.payload.ArrayData;
import com.horndroid.payload.PackedSwitch;
import com.horndroid.payload.SparseSwitch;
import com.horndroid.strings.ConstString;
import com.horndroid.util.CMPair;
import com.horndroid.util.SourcesSinks;
import com.horndroid.util.Utils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
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



import com.google.common.collect.ImmutableList;

public class DataExtraction {
    private static final Logger LOGGER = LogManager.getLogger(DataExtraction.class);

    private Map<Integer,GeneralClass> classes;
    private final Set<Integer> allowed;
    private int filterClasses;
    private boolean filterSound;
    final private Instances instances;
    final private Set<ArrayData> arrayDataPayload;
    final private Set<PackedSwitch> packedSwitchPayload;
    final private Set<SparseSwitch> sparseSwitchPayload;
    final private Set<Integer> staticConstructor;
    final private Set<ConstString> constStrings;
    final private SourcesSinks sourcesSinks;
    private Set<CMPair> refSources;
    private Set<CMPair> refSinks;
    final private Set<Integer> methodHasSink;
    
    private Interfaces interfaces;
    
    private final Set<Integer> launcherActivities;
    

    private final boolean fromApk;


    public DataExtraction(Map<Integer,GeneralClass> classes, Instances instances, Set<ArrayData> arrayDataPayload, 
             Set<PackedSwitch> packedSwitchPayload, Set<SparseSwitch> sparseSwitchPayload, 
             Set<Integer> staticConstructor, Set<ConstString> constStrings, Set<Integer> launcherActivities, final boolean fromApk,
             final SourcesSinks sourcesSinks,
             final Set<CMPair> refSources, final Set<CMPair> refSinks,
             final Set<Integer> methodHasSink,
             final Interfaces interfaces, final Set<Integer> allowed, final int filterClasses, final boolean filterSound){
        this.classes = classes;
        this.instances = instances;
        this.arrayDataPayload = arrayDataPayload;
        this.packedSwitchPayload = packedSwitchPayload;
        this.sparseSwitchPayload = sparseSwitchPayload;
        this.staticConstructor = staticConstructor;
        this.constStrings = constStrings;
        this.fromApk = fromApk;
        this.launcherActivities = launcherActivities;
        this.sourcesSinks = sourcesSinks;
        this.refSinks = refSinks;
        this.refSources = refSources;
        
        this.methodHasSink = methodHasSink;
        
        this.interfaces = interfaces;

        this.allowed = allowed;
        this.filterClasses = filterClasses;
        this.filterSound = filterSound;
    }
    public void putMethodHasSink(int cmHash){
        if (this.methodHasSink != null){
            this.methodHasSink.add(cmHash);
        }
    }

    private void addSinksFromFilteredClasses(Map<Integer, GeneralClass> modifiedClasses){
        for (final GeneralClass c: classes.values()){
            if (!modifiedClasses.containsKey(c.getType().hashCode())){
               if (c instanceof DalvikClass){
                   DalvikClass dc = (DalvikClass) c;
                   for (DalvikMethod dm: dc.getMethods()){
                       final CMPair cmp = new CMPair(dc.getType().hashCode(),dm.getName().hashCode());
                       if (methodHasSink.contains(cmp.hashCode())){
                           refSinks.add(cmp);
                       }
                   }
               }
            }
        }
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
                instances.changeType(cd);
            }
        }
        if (filterClasses > 0){
            final Map<Integer, GeneralClass> modifiedClasses = new ConcurrentHashMap<Integer, GeneralClass>();
            modifyClassStructure(modifiedClasses);
            if (filterSound){
                addSinksFromFilteredClasses(modifiedClasses);
            }
            classes.clear();
            classes.putAll(modifiedClasses);
        }
    }

    private void addChildrenToModification(final Map<Integer, GeneralClass> modifiedClasses,
                                           final DalvikClass dc){
        for (GeneralClass gc: dc.getChildClasses()){
            if (gc instanceof DalvikClass){
                DalvikClass dch = (DalvikClass) gc;
                modifiedClasses.put(dch.getType().hashCode(), dch);
                addChildrenToModification(modifiedClasses, dch);
            }
            else{
                modifiedClasses.put(gc.getType().hashCode(), gc);
            }
        }
    }

    private void addParentsToModification(final Map<Integer, GeneralClass> modifiedClasses,
                                          final DalvikClass dc){
        modifiedClasses.put(dc.getSuperClass().getType().hashCode(), dc);
        if (dc.getSuperClass() instanceof DalvikClass){
            addParentsToModification(modifiedClasses, (DalvikClass) dc.getSuperClass());
        }
    }

    private static String makeNameIgnoreDollar(final GeneralClass c) {
        final String formatClassName = c.getType().replaceAll("\\.", "/").substring(1, c.getType().replaceAll("\\.", "/").length() - 1);
        final String[] parts = formatClassName.split("/");
        final String classN = parts[parts.length - 1];
        final String[] parts$ = classN.split("\\$");
        final String classN$ = parts$[0];
        return classN$;
    }

    private void modifyClassStructure(final Map<Integer, GeneralClass> modifiedClasses){
        LOGGER.debug("Analysed classes:");
        for (final GeneralClass c: classes.values()){
            if (c instanceof DalvikClass){
                DalvikClass dc= (DalvikClass) c;
                if (allowed.contains(makeNameIgnoreDollar(dc).hashCode())){
                    LOGGER.debug(dc.getType());
                    modifiedClasses.put(dc.getType().hashCode(), dc);
                    addParentsToModification(modifiedClasses, dc);
                    addChildrenToModification(modifiedClasses, dc);
                }
                else{
                    if (filterClasses > 1){
                        LOGGER.debug(dc.getType());
                        modifiedClasses.put(dc.getType().hashCode(), dc);
                        addParentsToModification(modifiedClasses, dc);
                        addChildrenToModification(modifiedClasses, dc);
                        filterClasses--;
                    }
                }
            }
            else{
                modifiedClasses.put(c.getType().hashCode(), c);
                LOGGER.debug(c.getType());
            }
        }
    }
    


    public void collectData(final List<? extends ClassDef> classDefs) {
        ConcurrentHashMap<Integer,ClassDef> classDefsMap = new ConcurrentHashMap<Integer,ClassDef>();
        for (ClassDef classDef : classDefs){
            if (classDef.getType().startsWith("Landroid/support/v4/") || classDef.getType().startsWith("Landroid/support/v7/")){
                continue;
            }
            classDefsMap.put(classDef.getType().hashCode(),classDef);
        }
        
        for (final ClassDef classDef: classDefsMap.values()) {
            if (classDef.getType().startsWith("Landroid/support/v4/") || classDef.getType().startsWith("Landroid/support/v7/")){
                continue;
            }
            DalvikClass c = collectDataFromClass(classDefsMap, classDef);
            classes.put(c.getType().hashCode(),c);
        }
        formClassStructure();
    }       


    private DalvikClass collectDataFromClass(final Map<Integer,ClassDef> classDefsMap, final ClassDef classDef) {
        final DalvikClass dc = new DalvikClass(classDef.getType());
        dc.putSuperClass(new GeneralClass(classDef.getSuperclass()));
        //final Set<GeneralClass> inter = Collections.newSetFromMap(new ConcurrentHashMap<GeneralClass,Boolean>());
        for (final String interfaceName: classDef.getInterfaces()){
            interfaces.add(interfaceName.hashCode(), dc);
        }
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
                    final int baseSCodeAddress = methodDef.getSparseSwitchBaseAddress(payloadAddress);
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
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(referenceString), true, true));
            break;
        case Format22c:
            if (opcode.name.equals((String) "new-array"))
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(referenceString), false, true));
            break;
        case Format35c:
            
            if (fromApk && referenceStringClass != null && referenceString != null){
                if (!refSources.contains(new CMPair(referenceStringClass.hashCode(),referenceString.hashCode())) &&
                        !refSinks.contains(new CMPair(referenceStringClass.hashCode(),referenceString.hashCode()))){
                    Boolean isSourceSink = isSourceSink(referenceStringClass,referenceString);
                    if (isSourceSink != null) {
                        if (isSourceSink) {
                            refSources.add(new CMPair(referenceStringClass.hashCode(),referenceString.hashCode()));
                        } else {
                            this.putMethodHasSink((new CMPair(c,m)).hashCode());
                            refSinks.add(new CMPair(referenceStringClass.hashCode(),referenceString.hashCode()));
                        }
                    }
                }
            }
            
            if (opcode.name.equals((String) "filled-new-array")){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(referenceString), false, true));
                break;
            }


            if  ((referenceClassIndex == "Ljava/lang/Class;".hashCode()) && 
                    ("newInstance()Ljava/lang/Object;".hashCode() == referenceIntIndex)){
                FiveRegisterInstruction instruction1 = (FiveRegisterInstruction)instruction;
                for (final ConstString constString: constStrings){
                    if ((constString.getC() == c) && (constString.getM() == m) && (constString.getPC() < codeAddress) && (constString.getV() == instruction1.getRegisterC())){
                        instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(constString.getDalvikName()), true, true));
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
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true, true));
            }

            if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
                    && (referenceIntIndex == "<init>(Ljava/lang/String;)V".hashCode())){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true, true));
            }


            if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
                    && (referenceIntIndex == "<init>()V".hashCode())){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true, true));
            }
            try{
                if (returnType.length() > 0){
                    if (returnType.contains("[")){
                        instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(returnType), false, false));
                        break;
                    }
                    if (returnType.charAt(returnType.length() - 1) == ';'){
                        instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(returnType), true, false));
                        break;
                    }
                }
            }
            catch (NullPointerException e){
                System.err.println("While parsing instruction: " + instruction.toString());
            }
            break;
        case Format3rc:
            
            if (fromApk){
                if (!refSources.contains(new CMPair(referenceStringClass.hashCode(),referenceString.hashCode())) &&
                        !refSinks.contains(new CMPair(referenceStringClass.hashCode(),referenceString.hashCode()))){
                    Boolean isSourceSink = isSourceSink(referenceStringClass,referenceString);
                    if (isSourceSink != null) {
                        if (isSourceSink) {
                            refSources.add(new CMPair(referenceStringClass.hashCode(),referenceString.hashCode()));
                        } else {
                            this.putMethodHasSink((new CMPair(c,m)).hashCode());
                            refSinks.add(new CMPair(referenceStringClass.hashCode(),referenceString.hashCode()));
                        }
                    }
                }
            }
            
            if (opcode.name.equals((String) "filled-new-array/range")){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(referenceString), false, true));
                break;
            }

            if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
                    && (referenceIntIndex == "<init>(Landroid/content/Context;Ljava/lang/Class;)V".hashCode())){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true, true));
            }

            if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
                    && (referenceIntIndex == "<init>(Ljava/lang/String;)V".hashCode())){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true, true));
            }

            if ((referenceClassIndex == "Landroid/content/Intent;".hashCode())
                    && (referenceIntIndex == "<init>()V".hashCode())){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass("Landroid/content/Intent;"), true, true));
            }

            if (returnType.charAt(returnType.length() - 1) == ';'){
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(returnType), true, false));
                break;
            }
            if (returnType.contains("["))
                instances.add(new DalvikInstance(c, m, codeAddress, new GeneralClass(returnType), false, false));
            break;
        default:
            break;
        }
    }
    
    /*
     * Return true if classNameBis, methodName is a source, false if it is a sink and null otherwise
     * Where classNameBis is either className of or super class of className
     * 
     */
    private Boolean isSourceSink(final String className, final String methodName){
        final int classIndex = className.hashCode();
        final String classNameFormat = className.substring(1, className.length()-1);
        final String methodNameFormat = methodName.substring(0, methodName.indexOf('('));
        
        //Lookup in sourcesSinks to check if className, methodName appears
        Boolean bool = sourcesSinks.isSourceSink(classNameFormat, methodNameFormat);
        if (bool != null){
            return bool;
        }

        if (classes.containsKey(classIndex)){
            GeneralClass classDef = classes.get(classIndex);
            if (classDef instanceof DalvikClass){
                DalvikClass cd = (DalvikClass) classDef;
                if (cd.getSuperClass() != null){
                    return isSourceSink(cd.getSuperClass().getType(), methodName);
                }
            }
        }
        return null;
    }
    
    public void putStaticConstructor(int c){
        staticConstructor.add(c);
    }
    
}
