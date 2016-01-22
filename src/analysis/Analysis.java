package analysis;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;

import Dalvik.DalvikClass;
import Dalvik.DalvikField;
import Dalvik.DalvikImplementation;
import Dalvik.DalvikInstance;
import Dalvik.DalvikMethod;
import Dalvik.DalvikStaticField;
import Dalvik.GeneralClass;
import Dalvik.Implementation;
import Dalvik.Instances;
import Dalvik.StubImplementation;
import horndroid.options;

import java.util.AbstractMap;
import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;

import javax.annotation.Nonnull;


import org.jf.dexlib2.iface.ClassDef;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.ReferenceInstruction;
import org.jf.dexlib2.iface.reference.FieldReference;
import org.jf.dexlib2.iface.reference.MethodReference;
import org.jf.dexlib2.iface.reference.Reference;
import org.jf.dexlib2.iface.value.EncodedValue;

import payload.ArrayData;
import payload.PackedSwitch;
import payload.SparseSwitch;
import strings.ConstString;
import util.*;
import z3.FSEngine;
import z3.FSVariable;
import z3.Z3Engine;
import z3.Z3Variable;

public class Analysis {
    final private Map<Integer,GeneralClass> apkClasses;
    final private Map<Integer,GeneralClass> classes;
    final private Instances apkInstances;
    final private Instances instances;
    final private Set<Integer> disabledActivities;
    final private Set<Integer> activities;
    final private Set<Integer> applications;
    final private Set<Integer> launcherActivities;
    final private Set<ConstString> constStrings;
    final private Set<Integer> callbackImplementations;
    final private Set<String> callbacks;
    final private Set<ArrayData> arrayDataPayload;
    final private Set<PackedSwitch> packedSwitchPayload;
    final private Set<SparseSwitch> sparseSwitchPayload;
    final private Set<Integer> overapprox;
    final private SourcesSinks sourcesSinks;
    final private options options;
    final private Z3Engine z3engine;
    final private FSEngine fsengine;
    final private Z3Variable var;
    final private FSVariable fsvar;
    final private Stubs stubs;
    
    final ExecutorService instructionExecutorService;
    private Set<CMPair> refSources;
    private Set<CMPair> refSinks;
    
    @Nonnull private final Set<CMPair> methodIsEntryPoint;
    @Nonnull private final Set<Integer> staticConstructor;
    
    private Map<Integer, Integer> allocationPointNumbers = new HashMap <Integer, Integer>();
    private Map<Integer, Integer> allocationPointNumbersReverse = new HashMap <Integer, Integer>();
    private Map<Integer, Integer> allocationPointSize = new HashMap <Integer, Integer>();
    private Map<Integer, Integer> allocationPointOffset = new HashMap <Integer, Integer>();
    private Map<Integer, String> allocationPointClass = new HashMap <Integer, String>();
    private Map<Integer, String> allocationPointClassDebug = new HashMap <Integer, String>();
    private Map<Integer, String> allocationPointMethod = new HashMap <Integer, String>();
    private Map<Integer, Integer> allocationPointPC = new HashMap <Integer, Integer>();
    
    private Integer localHeapNumberEntries;
    private Integer localHeapSize;
    private HashSet<StringPair> apkClassesMethods;
    
    public Analysis(final Z3Engine z3engine,final FSEngine fsengine, 
            final SourcesSinks sourcesSinks, final options options, final ExecutorService instructionExecutorService,
            final Stubs stubs){
        this.apkClasses = new ConcurrentHashMap<Integer,GeneralClass>();
        this.classes = new ConcurrentHashMap<Integer,GeneralClass>();
        this.apkInstances = new Instances();
        this.instances = new Instances();
        this.disabledActivities = new HashSet<Integer>();
        this.activities = new HashSet<Integer>();
        this.applications = new HashSet<Integer>();
        this.launcherActivities = new HashSet <Integer>();
        this.constStrings = new HashSet <ConstString>();
        this.callbackImplementations = new HashSet <Integer>();
        this.callbacks = new HashSet <String>();
        this.arrayDataPayload = new HashSet <ArrayData>();
        this.packedSwitchPayload = new HashSet <PackedSwitch>();
        this.sparseSwitchPayload = new HashSet <SparseSwitch>();
        this.overapprox = new HashSet <Integer>();
        this.instructionExecutorService = instructionExecutorService;
        this.sourcesSinks = sourcesSinks;
        this.z3engine = z3engine;
        this.fsengine = fsengine;
        this.var = z3engine.getVars();
        this.fsvar = fsengine.getVars();
        this.options = options;
        
        this.stubs = stubs;

        this.refSources = new HashSet <CMPair>();
        this.refSinks = new HashSet <CMPair>();
        this.apkClassesMethods = new HashSet<StringPair>();
        
        this.overapprox.add("Landroid/content/ContentProvider;".hashCode());
        this.overapprox.add("Landroid/app/Service;".hashCode());
        this.overapprox.add("Landroid/content/BroadcastReceiver;".hashCode());
        this.overapprox.add("Landroid/app/Fragment;".hashCode());
        this.overapprox.add("Landroid/support/v4/app/FragmentActivity;".hashCode());
        this.overapprox.add("Landroid/support/v4/app/Fragment;".hashCode());
        this.overapprox.add("Landroid/app/ListFragment;".hashCode());
        this.overapprox.add("Landroid/support/v4/app/ListFragment;".hashCode());
        this.overapprox.add("Landroid/os/Handler;".hashCode());
        
        /*
        this.callbacks.add("onCreate"); 
        this.callbacks.add("onDestroy");
        this.callbacks.add("onStart");
        this.callbacks.add("onPause");
        this.callbacks.add("onStop");
        this.callbacks.add("onRestart");
        this.callbacks.add("onResume");
        */
        
        this.methodIsEntryPoint = new HashSet<CMPair>();
        this.staticConstructor = new HashSet<Integer>();
    }
    public  Set<Integer> getDisabledActivities(){
        return disabledActivities;
    }
    public  Set<Integer> getActivities(){
        return activities;
    }
    public  Set<Integer> getApplications(){
        return applications;
    }
    public  Set<String> getCallbacks(){
        return callbacks;
    }
    public  Set<Integer> getCallbackImplementations(){
        return callbackImplementations;
    }
    public  Set<Integer> getLauncherActivities(){
        return launcherActivities;
    }

    public Z3Engine getZ3Engine(){
        if (options.fsanalysis){
            throw (new RuntimeException("Requested Z3Engine during a FS analysis"));
        }
        return z3engine;
    }
    public boolean isDebugging(){
        return options.debug;
    }
    public int getSize(){
        return options.bitvectorSize;
    }
    public boolean optionArrays(){
        return options.arrays;
    }
    public boolean optionVerbose(){
        return options.verboseResults;
    }
    public Set<ArrayData> getArrayData(){
        return arrayDataPayload;
    }
    public Set<PackedSwitch> getPackedSwitch(){
        return packedSwitchPayload;
    }
    public Set<SparseSwitch> getSparseSwitch(){
        return sparseSwitchPayload;
    }
    public FSEngine getFSEngine(){
        if (!fsengine.isInitialized()) {
            throw new RuntimeException("Analysis.getFSEngine:FSEngine not initialized");
        }
        return fsengine;
    }
    
    public Set<Integer> getAllocationPoints(){
        return allocationPointOffset.keySet();
    }
    
    /*
     * Populate apkClasses and apkInstances with the classes and instances from the analysed apk
     * Also gather additional information: payloads data, switches information, static constructor and strings
     */
    public void collectDataFromApk( List<? extends ClassDef> classDefs){
        DataExtraction de = new DataExtraction(apkClasses, apkInstances, arrayDataPayload, packedSwitchPayload, sparseSwitchPayload, staticConstructor, constStrings, launcherActivities);
        de.collectData(classDefs);
        
    }
    
    /*
     * Should only be used in staticFieldLookUp(int, int)
     */
    private Integer staticFieldLookup(final GeneralClass ci, final int fi){
        if (ci instanceof DalvikClass){
            final DalvikClass dc = (DalvikClass) ci;
            for (final DalvikField f: dc.getExactFields()){
                if (f.getName().hashCode() == fi)
                    return ci.getType().hashCode();
            }
            if(dc.getSuperClass() != null){
                return staticFieldLookup(dc.getSuperClass(), fi);
            }
        }
        return null;
    }
    
    /*
     * Return the hashcode of the name of the super class of ci where fi is defined
     */
    public Integer staticFieldLookup(final int ci, final int fi){
        if (classes.containsKey(ci)){
            GeneralClass c = classes.get(ci);
            return staticFieldLookup(c,fi);
        }
        return null;
    }
    
    public DalvikMethod getExactMethod(final int ci, final int mi){
        if (classes.containsKey(ci)){
            GeneralClass c = classes.get(ci);
            if (c instanceof DalvikClass){
                for (final DalvikMethod m: ((DalvikClass) c).getMethods()){
                    if (m.getName().hashCode() == mi){
                        return m;
                    }
                }
            }
        }
        return null;
    }
    
    public String getClassString(final int ci){
        if (classes.containsKey(ci)){
            GeneralClass c = classes.get(ci);
            if ((c instanceof DalvikClass) && c.getType() != null){
                return c.getType();
            }
        }
        return Integer.toString(ci);
    }
    
    public String getMethodString(final int ci, final int mi){
        if (classes.containsKey(ci)){
            GeneralClass c = classes.get(ci);
            if ((c instanceof DalvikClass)){
                for (final DalvikMethod m: ((DalvikClass) c).getMethods()){
                    if (m.getName().hashCode() == mi && m.getName() != null){
                        return m.getName();
                    }
                }
            }
        }
        return Integer.toString(mi);
    }
    
    /*
     * Return a bijective mapping (i --> field_i) between [[0;inputMap.size() - 1]] and the inputMap key-space
     */
    public Map<Integer,Integer> classFieldsMapping(final Map<Integer,Boolean> inputMap){
        Map<Integer, Integer> result = Collections.synchronizedMap(new HashMap <Integer, Integer>(inputMap.size()));
        List<Integer> list = new ArrayList<Integer>(inputMap.keySet());
        Collections.sort(list);
        for (int i =  0; i < inputMap.size(); i++){
            result.put(i, list.get(i));
        }
        return result;
    }
    
    private void initializeAllocationMapping(){
        Integer itNumber = 0;
        Integer offset = 0;
        for (DalvikInstance i : instances.getAll()){
            final int instanceNum = i.hashCode();
            final String referenceString = i.getType().getType();
            final Map<Integer, Boolean> fieldsMap = getClassFields(referenceString, instanceNum);
            TreeSet<Integer> fields = null;
            if (fieldsMap != null)
                fields = new TreeSet<Integer>(fieldsMap.keySet());
            else
                fields = new TreeSet<Integer>();
            allocationPointClass.put(instanceNum,referenceString);
            allocationPointClassDebug.put(instanceNum,this.getClassString(i.getC()));
            allocationPointMethod.put(instanceNum,this.getMethodString(i.getC(), i.getM()));
            allocationPointPC.put(instanceNum,i.getPC());
            allocationPointNumbers.put(instanceNum, itNumber);
            allocationPointNumbersReverse.put(itNumber,instanceNum);
            allocationPointSize.put(instanceNum, fields.size());
            allocationPointOffset.put(instanceNum, offset);
            offset += fields.size() + 1;
            itNumber += 1;
        }
        localHeapSize = offset;
        localHeapNumberEntries = itNumber;
    }
    
    public int getInstanceNumFromReverse(int i){
        return allocationPointNumbersReverse.get(i);
    }
    
    public int getFieldOffset(int allocationPoint, int fieldIntReference){
        TreeSet<Integer> fields = new TreeSet<Integer>(this.getClassFields(allocationPointClass.get(allocationPoint), allocationPoint).keySet());
        int i = 0;
        for (int field : fields){
            if (field == fieldIntReference){
                return i;
            }
            i++;
        }
        throw new RuntimeException("Analysis: getOffset: field does not exist");
    }
    
    public String getAllocationPointClass(int instanceNum){
        return new String(allocationPointClass.get(instanceNum));
    }
    
    public String getAllocationPointClassDebug(int instanceNum){
        return new String(allocationPointClassDebug.get(instanceNum));
    }
    
    public String getAllocationPointMethod(int instanceNum){
        return new String(allocationPointMethod.get(instanceNum));
    }
    
    public int getAllocationPointPC(int instanceNum){
        return allocationPointPC.get(instanceNum);
    }
    
    public TreeMap<Integer, Boolean> getClassFields(final String className, final int instanceNum){
        TreeMap<Integer, Boolean> result = new TreeMap <Integer, Boolean>();
        boolean found = false;
        boolean prim;
        if (classes.containsKey(className)){
            GeneralClass c = classes.get(className);
            if (c instanceof DalvikClass && c != null){
                final DalvikClass dc = (DalvikClass) c;
                found = true;
                for (DalvikField field: dc.getFields()) {
                    prim = false;
                    final String fieldName = field.getName();
                    switch (fieldName){
                    case "Z": case "B": case "S": case "C": case "I": case "J": case "F": case "D": 
                        prim = true;
                    }
                    result.put(fieldName.hashCode(), prim);
                }
            }else{
                System.out.println("getClassField " + className);
            }
        }

        if (!found){
            String javaName = Utils.toStandardJavaClassName(className);
            try {
                Class<?> cc = Class.forName(javaName);
                java.lang.reflect.Field[] fields = cc.getFields();
                if (fields.length != 0)
                    for (java.lang.reflect.Field f: fields){
                        result.put((className + "->" + f.getName() + ':' + Utils.toDalvikType(f.getType().toString())).hashCode(), f.getType().isPrimitive());
                    }
            }	
            catch (Exception e) {
                return null;
            }
            catch(Error e){
                return null;
            } 	
        }
        if (result.isEmpty()) return null;
        return result;
    }
    
    public Integer getInstNum(final int c, final int m, final int pc){
        return DalvikInstance.hashCode(c, m, pc);
    }
    
    private void addToMain(final DalvikClass dc, final int methodIndex, final int numRegCall, final int regCount){
        final int classIndex = dc.getType().hashCode();
        if (options.fsanalysis){
            Map<Integer, BitVecExpr> regUpV = new HashMap<>();
            Map<Integer, BoolExpr> regUpH = new HashMap<>();
            Map<Integer, BoolExpr> regUpL = new HashMap<>();
            Map<Integer, BoolExpr> regUpG = new HashMap<>();
            Map<Integer, BitVecExpr> regUpLHV = new HashMap<>();
            Map<Integer, BoolExpr> regUpLHH = new HashMap<>();
            Map<Integer, BoolExpr> regUpLHL = new HashMap<>();
            Map<Integer, BoolExpr> regUpLHG = new HashMap<>();
            Map<Integer, BoolExpr> regUpLHF = new HashMap<>();

            for (int i = 0; i<= numRegCall + regCount; i++){
                regUpH.put(i, fsengine.mkFalse());
            }
            
            for (int i = 0; i < this.getLocalHeapSize(); i++){
                regUpLHV.put(i, fsengine.mkBitVector(0, this.getSize()));
                regUpLHH.put(i, fsengine.mkFalse());
                regUpLHL.put(i, fsengine.mkFalse());
                regUpLHG.put(i, fsengine.mkFalse());
                regUpLHF.put(i, fsengine.mkFalse());
            }
            
            BoolExpr h = fsengine.rPred(Integer.toString(classIndex), Integer.toString(methodIndex), 0, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, regCount, numRegCall);
            fsengine.addRule(h, dc.toString() + methodIndex + "zz");
        }else{
            Map<Integer, BitVecExpr> regUpdate = new HashMap<>();
            Map<Integer, BoolExpr> regUpdateL = new HashMap<>();
            Map<Integer, BoolExpr> regUpdateB = new HashMap<>();
            for (int i = 0; i<= numRegCall + regCount; i++){
                regUpdateL.put(i, z3engine.mkFalse());
            }

            BoolExpr b1 = z3engine.rPred(Integer.toString(classIndex), Integer.toString(methodIndex),
                    0, regUpdate, regUpdateL, regUpdateB, regCount, numRegCall);
            z3engine.addRule(b1, dc.toString() + methodIndex + "zz");
        }
    }
    
    private void addToMainHeap(final DalvikClass dc, final int methodIndex, final int numRegCall, final int regCount){
        this.addToMain(dc, methodIndex, numRegCall, regCount);
        
        final int classIndex = dc.getType().hashCode();
        if (options.fsanalysis){
            BoolExpr b2 = fsengine.hPred( fsengine.mkBitVector(classIndex, options.bitvectorSize),
                    fsvar.getFpp(), fsvar.getF(), fsvar.getVal(),
                    fsengine.mkFalse(), fsengine.mkTrue());
            fsengine.addRule(b2, null);
        }else{
            BoolExpr b2 = z3engine.hPred( z3engine.mkBitVector(classIndex, options.bitvectorSize),
                    var.getFpp(), var.getF(), var.getVal(),
                    z3engine.mkFalse(), z3engine.mkTrue());
            z3engine.addRule(b2, null);
        }
    }


    public void processClass(final DalvikClass dc, final boolean isDisabledActivity, final boolean isCallbackImplementation,
            final boolean isLauncherActivity, final boolean isApplication, final boolean isOverApprox){
        for (final DalvikMethod m: dc.getMethods()){            
            boolean isCallback = false;
            for (final String callback: callbacks){
                if (m.getName().contains(callback)){
                    isCallback = true;
                }
            }
            final boolean isEntryPoint = testEntryPoint(dc, m.getName().hashCode());
            if (isCallbackImplementation){
                addToMain(dc, m.getName().hashCode(), m.getNumReg(), m.getNumArg());
            }

            if (isEntryPoint){
                final int numRegCall = m.getNumReg();
                final int regCount = m.getNumArg();
                if(options.fsanalysis){
                    Map<Integer, BitVecExpr> regUpV = new HashMap<>();
                    Map<Integer, BoolExpr> regUpH = new HashMap<>();
                    Map<Integer, BoolExpr> regUpL = new HashMap<>();
                    Map<Integer, BoolExpr> regUpG = new HashMap<>();
                    Map<Integer, BitVecExpr> regUpLHV = new HashMap<>();
                    Map<Integer, BoolExpr> regUpLHH = new HashMap<>();
                    Map<Integer, BoolExpr> regUpLHL = new HashMap<>();
                    Map<Integer, BoolExpr> regUpLHG = new HashMap<>();
                    Map<Integer, BoolExpr> regUpLHF = new HashMap<>();

                    for (int i = 0; i<= numRegCall + regCount; i++){
                        regUpH.put(i, fsengine.mkFalse());
                    }
                    
                    for (int i = 0; i < this.getLocalHeapSize(); i++){
                        regUpLHV.put(i, fsengine.mkBitVector(0, this.getSize()));
                        regUpLHH.put(i, fsengine.mkFalse());
                        regUpLHL.put(i, fsengine.mkFalse());
                        regUpLHG.put(i, fsengine.mkFalse());
                        regUpLHF.put(i, fsengine.mkFalse());
                    }
                    
                    BoolExpr b1 = fsengine.iPred(fsvar.getCn(),
                            fsengine.mkBitVector(dc.getType().hashCode(), options.bitvectorSize),
                            fsvar.getVal(), fsvar.getLf(), fsvar.getBf());
                    
                    BoolExpr b2 = fsengine.rPred(Integer.toString(dc.getType().hashCode()), Integer.toString(m.getName().hashCode()), 0, regUpV, regUpH, regUpL, regUpG, regUpLHV, regUpLHH, regUpLHL, regUpLHG, regUpLHF, regCount, numRegCall);
                
                    fsengine.addRule(fsengine.implies(b1, b2), null);
                }else{
                    Map<Integer, BitVecExpr> regUpdate = new HashMap<>();
                    Map<Integer, BoolExpr> regUpdateL = new HashMap<>();
                    Map<Integer, BoolExpr> regUpdateB = new HashMap<>();
                    int i;
                    for (i = 0; i<= numRegCall + regCount; i++){
                        regUpdateL.put(i, z3engine.mkFalse());
                    }

                    BoolExpr b1 = z3engine.iPred(var.getCn(),
                            z3engine.mkBitVector(dc.getType().hashCode(), options.bitvectorSize),
                            var.getVal(), var.getLf(), var.getBf());

                    BoolExpr b2 = z3engine.rPred(Integer.toString(dc.getType().hashCode()),
                            Integer.toString(m.getName().hashCode()),
                            0, regUpdate, regUpdateL, regUpdateB, regCount, numRegCall);

                    BoolExpr b1tob2 = z3engine.implies(b1, b2);
                    z3engine.addRule(b1tob2, null);
                }
            }

            if (!isDisabledActivity && isEntryPoint && (isLauncherActivity || isApplication || isOverApprox)){
                addToMainHeap(dc, m.getName().hashCode(), m.getNumReg(), m.getNumArg());
            }

            if (isCallback){
                addToMain(dc, m.getName().hashCode(), m.getNumReg(), m.getNumArg());
            }

            int codeAddress = 0;
            for (final Instruction instruction: m.getInstructions()){
                if (options.fsanalysis){
                    FSInstructionAnalysis ia = new FSInstructionAnalysis(this, instruction, dc, m, codeAddress);
                    ia.CreateHornClauses(options, apkClassesMethods);
                }else{
                    InstructionAnalysis ia = new InstructionAnalysis(this, instruction, dc, m, codeAddress);
                    ia.CreateHornClauses(options, apkClassesMethods);                    
                }
                codeAddress += instruction.getCodeUnits();
            }
        }
    }
    
    private String makeName(final GeneralClass c){
        final String formatClassName = c.getType().replaceAll("\\.", "/").substring(1, c.getType().replaceAll("\\.", "/").length() -1);
        final String[] parts = formatClassName.split("/");
        final String classN =  parts[parts.length - 1];
        return classN;
    }
    
    /*
     * Return true if c'.getType().hashCode() is in overapprox where c' is either c or a super class of c
     */
    private boolean superIsInOverapprox(GeneralClass c){
        if (overapprox.contains(c.getType().hashCode())){
            return true;
        }else{
            if (c instanceof DalvikClass){
                if (((DalvikClass) c).getSuperClass() != null){
                    return superIsInOverapprox(((DalvikClass) c).getSuperClass());   
                }
            }
        }
        return false;
    }    

    
    /*
     * Check if c is in Overapprox:
     * more precisely if a child of c is in overapprox, or a superclass of c is in overapprox
     */
    private boolean testOverapprox(final GeneralClass c){
        if (superIsInOverapprox(c)){
            return true;
        }else{
            if (c instanceof DalvikClass){
                final DalvikClass dc = (DalvikClass) c;
                for (final DalvikClass childClass: dc.getChildClasses()){
                    if (overapprox.contains(childClass.getType().hashCode())){
                        return true;
                    }
                }
            }
        }
        return false;
    }
    
    /*
     * Return true if makeName(c').hashCode() is in set where c' is either c or a super class of c
     */
    private boolean superIsInSet(Set<Integer> set, GeneralClass c){
        if (set.contains(makeName(c).hashCode())){
            return true;
        }else{
            if (c instanceof DalvikClass){
                if (((DalvikClass) c).getSuperClass() != null){
                    return superIsInSet(set,((DalvikClass) c).getSuperClass());   
                }
            }
        }
        return false;
    }

    /*
     * Check if c is in launcherActivities:
     * more precisely if a child of c is in launcherActivities, or a superclass of c is in launcherActivities
     */
    private boolean testLauncherActivity(final GeneralClass c){
        if (c.getType() == null){
            return false;
        }
        
        if (superIsInSet(launcherActivities,c)){
            return true;
        }
        else{
            if (c instanceof DalvikClass){
                final DalvikClass dc = (DalvikClass) c;
                for (final DalvikClass childClass: dc.getChildClasses()){
                    if (launcherActivities.contains(makeName(childClass).hashCode())){
                        return true;
                    }
                }
            }
        }
        return false;
    }

    private boolean testDisabledActivity(final GeneralClass c){
        return disabledActivities.contains(makeName(c).hashCode());
    }
    
    /*
     * Check if c is in applications:
     * more precisely if a child of c is in applications, or a superclass of c is in applications
     */
    private boolean testApplication(final GeneralClass c){
        if (c.getType() == null){
            return false;
        }
        
        if (superIsInSet(applications,c)){
            return true;
        }
        else{
            if (c instanceof DalvikClass){
                final DalvikClass dc = (DalvikClass) c;
                for (final DalvikClass childClass: dc.getChildClasses()){
                    if (applications.contains(makeName(childClass).hashCode())){
                        return true;
                    }
                }
            }
        }
        return false;
    }

    // generate labels for the R predicates
    public String mkLabel(DalvikClass c, DalvikMethod m, int pc){
        return Integer.toString(c.getType().hashCode()) + "_" + Integer.toString(m.getName().hashCode()) + "_" + Integer.toString(pc);
    }
    
    private void addStaticFieldsValues(){
        for (GeneralClass c: classes.values()){
            if (!(c instanceof DalvikClass)) continue;
            for (DalvikField f: ((DalvikClass) c).getFields()){
                if (f instanceof DalvikStaticField){
                    final EncodedValue initialValue = ((DalvikStaticField) f).getDefaultValue();
                    if (options.fsanalysis){
                        BoolExpr rule = fsengine.sPred( fsengine.mkInt(Utils.Dec(c.getType().hashCode())),
                                fsengine.mkInt(Utils.Dec(f.getName().hashCode())),
                                FormatEncodedValue.toBitVec(fsengine, initialValue, options.bitvectorSize),
                                fsengine.mkFalse(), fsvar.getBf());
                        fsengine.addRule(rule, null);
                    }else{
                        BoolExpr rule = z3engine.sPred( z3engine.mkInt(Utils.Dec(c.getType().hashCode())),
                                z3engine.mkInt(Utils.Dec(f.getName().hashCode())),
                                FormatEncodedValue.toBitVec(z3engine, initialValue, options.bitvectorSize),
                                z3engine.mkFalse(), var.getBf());
                        z3engine.addRule(rule, null);
                    }
                }
            }
        }
    }
    

    private void addClass(final GeneralClass cp, final Set<GeneralClass> addedInPool){
        if(!addedInPool.contains(cp) && cp != null){
            addedInPool.add(cp);
            
            classes.put(cp.getType().hashCode(),cp);
            if (cp instanceof DalvikClass){
                // Add the superclass of cp
                GeneralClass superClass = ((DalvikClass)cp).getSuperClass();
                if (! (superClass == null)){
                    if(apkClasses.containsKey(superClass.getType().hashCode())){
                        GeneralClass supClass = apkClasses.get(superClass.getType().hashCode());
                        addClass(supClass, addedInPool);
                    }else{                    
                        GeneralClass stub = stubs.getClasses().get(superClass.getType().hashCode());
                        if (stub != null){
                            ((DalvikClass) cp).putSuperClass(stub);
                            addClass(stub,addedInPool);
                        }else{
                            throw new RuntimeException("addClass " + cp.getType());
                        }
                    }
                }else{
                    if (!cp.getType().equals("Ljava/lang/Object;")){
                        System.out.println("Should be Ljava/lang/Object; " + cp.getType());
                    }
                }
            }
            
        }
    }
    

    private void addClassFromApk(final GeneralClass cp, final LinkedList<SimpleEntry<GeneralClass,String>> pool,
            final Set<GeneralClass> addedInPool, final Set<CMPair> processCM){
        if(!addedInPool.contains(cp) && cp != null){
            addedInPool.add(cp);

            classes.put(cp.getType().hashCode(), cp);
            if (cp instanceof DalvikClass){
                // Add all cp's methods to the pool and processCM set
                for (DalvikMethod m : ((DalvikClass)cp).getMethods()){
                    pool.add(new SimpleEntry<GeneralClass,String>(cp,m.getName()));
                    processCM.add(new CMPair(cp.getType().hashCode(),m.getName().hashCode()));
                }

                // Add the superclass of cp
                GeneralClass superClass = ((DalvikClass)cp).getSuperClass();
                if (superClass != null){
                    if(apkClasses.containsKey(superClass.getType().hashCode())){
                        GeneralClass supClass = apkClasses.get(superClass.getType().hashCode());

                        addClass(supClass, addedInPool);
                    }else{                    
                        GeneralClass stub = stubs.getClasses().get(superClass.getType().hashCode());

                        ((DalvikClass) cp).putSuperClass(stub);
                        addClass(stub,addedInPool);
                    }
                }
            }
        }
    }
    private void addToPool(LazyUnion lazyUnion, final LinkedList<SimpleEntry<GeneralClass,String>> pool,
            final Set<CMPair> processCM, Map<DalvikClass,DalvikMethod> cmMap){
        if (cmMap != null){
            for (Entry<DalvikClass,DalvikMethod> entry : cmMap.entrySet()){
                CMPair cmp = new CMPair(entry.getKey().getType().hashCode(),entry.getValue().getName().hashCode());
                if (!processCM.contains(cmp)){
                    processCM.add(cmp);
                    pool.add(new SimpleEntry<GeneralClass,String>(entry.getKey(),entry.getValue().getName()));
                }
            }
        }
    }
    
    /*
     * Fetch the classes from standard java and android for all unknown classes
     */
    private Set<CMPair> fetchUnknownMethod(){
        LinkedList<SimpleEntry<GeneralClass,String>> pool = new LinkedList<SimpleEntry<GeneralClass,String>>();
        Set<GeneralClass> addedInPool = new HashSet<GeneralClass>();
        Set<CMPair> processCM  = new HashSet<CMPair>();
        
        LazyUnion lazyUnion = new LazyUnion(apkClasses, stubs.getClasses());
        
        // We initialize the pool
        for (final GeneralClass c: classes.values()){
            addClassFromApk(c, pool, addedInPool, processCM);
        }

        // We treat the pool until it is empty
        while(!pool.isEmpty()){
            SimpleEntry<GeneralClass,String> entry = pool.poll();
            GeneralClass c = entry.getKey();
            String mString = entry.getValue();
 
            addClass(c,addedInPool);

            if (c instanceof DalvikClass){
                final DalvikClass dc = (DalvikClass) c;
                DalvikMethod m = dc.getMethod(mString.hashCode());
                if (m == null){
                    continue; //we fetch implementation that does not exist, e.g., method is implemented in super class only but we ask its child for the implementation
                }
                // We look for classes and method in the instructions of m
                for (Instruction instruction : m.getInstructions()){
                    if (instruction instanceof ReferenceInstruction) {
                        Reference reference = ((ReferenceInstruction)instruction).getReference();
                        if (reference instanceof FieldReference) {
                            int referenceClassIndex = ((FieldReference) reference).getDefiningClass().hashCode();
                            addClass(lazyUnion.get(referenceClassIndex),addedInPool);
                        }
                        else{
                            if (reference instanceof MethodReference){
                                String referenceString = Utils.getShortReferenceString(reference);
                                String referenceClass = ((MethodReference) reference).getDefiningClass();
                                int referenceClassIndex = ((MethodReference) reference).getDefiningClass().hashCode();
                               /*
                                * cloning for arrays is inherited from java.lang.Object
                                */
                                if (referenceString.equals("clone()Ljava/lang/Object;")
                                        && referenceClass.contains("[")){
                                    referenceClass = "Ljava/lang/Object;";
                                    referenceClassIndex = referenceClass.hashCode();
                                }
                                
                                Map<DalvikClass,DalvikMethod> cmMap = new HashMap<DalvikClass,DalvikMethod>();
                                switch (instruction.getOpcode()){
                                case INVOKE_SUPER:
                                case INVOKE_SUPER_RANGE:
                                {
                                    {
                                        Implementation implementation = getSuperImplementation(lazyUnion, referenceClassIndex, referenceString.hashCode());
                                        if (implementation != null && implementation instanceof DalvikImplementation){
                                            DalvikImplementation di = (DalvikImplementation) implementation;
                                            if (!di.getInstances().isEmpty()){
                                                cmMap.put(di.getDalvikClass(), di.getMethod());
                                            }
                                        }else{
                                            if (implementation != null && implementation instanceof StubImplementation){
                                                StubImplementation si = (StubImplementation) implementation;

                                                for (DalvikImplementation di : si.getDalvikImp()){
                                                    if (!di.getInstances().isEmpty()){
                                                        cmMap.put(di.getDalvikClass(),di.getMethod());
                                                    }
                                                }
                                            }else{
                                                System.out.println("Not Found :" + ((MethodReference) reference).getDefiningClass() + " " + referenceString+ " " + instruction.getOpcode().toString());
                                            }
                                        }
                                    }
                                }
                                break;
                                    
                                case INVOKE_INTERFACE:
                                case INVOKE_VIRTUAL:
                                case INVOKE_VIRTUAL_RANGE:
                                case INVOKE_INTERFACE_RANGE:
                                {
                                    
                                    Map<Integer,Implementation> implementations = getVirtualImplementations(lazyUnion,referenceClassIndex, referenceString.hashCode(),
                                            referenceClass, referenceString);
                                    if (implementations != null){
                                        for (Implementation implementation : implementations.values()){
                                            if (implementation instanceof DalvikImplementation){
                                                DalvikImplementation di = (DalvikImplementation) implementation;   
                                                if (!di.getInstances().isEmpty()){
                                                    cmMap.put(di.getDalvikClass(), di.getMethod());
                                                }
                                            }else{
                                                if (implementation instanceof StubImplementation){
                                                    StubImplementation si = (StubImplementation) implementation;
                                                    for (DalvikImplementation di : si.getDalvikImp()){
                                                        if (!di.getInstances().isEmpty()){
                                                            cmMap.put(di.getDalvikClass(),di.getMethod());
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                break;

                                    
                                case INVOKE_DIRECT:
                                case INVOKE_DIRECT_RANGE:
                                {
                                    Implementation implementation = getDirectImplementation(lazyUnion, referenceClassIndex, referenceString.hashCode());
                                    if (implementation != null && implementation instanceof DalvikImplementation){
                                        DalvikImplementation di = (DalvikImplementation) implementation;
                                        if (!di.getInstances().isEmpty()){
                                            cmMap.put(di.getDalvikClass(), di.getMethod());
                                        }
                                    }else{
                                        if (implementation != null && implementation instanceof StubImplementation){
                                            StubImplementation si = (StubImplementation) implementation;
                                            
                                            for (DalvikImplementation di : si.getDalvikImp()){
                                                if (!di.getInstances().isEmpty()){
                                                    cmMap.put(di.getDalvikClass(),di.getMethod());
                                                }
                                            }
                                        }else{
                                            System.out.println("Not Found :" + ((MethodReference) reference).getDefiningClass() + " " + referenceString+ " " + instruction.getOpcode().toString());
                                        }
                                    }
                                }
                                break;
                                case INVOKE_STATIC:
                                case INVOKE_STATIC_RANGE:
                                {
                                    Implementation implementation = getDirectImplementation(lazyUnion, referenceClassIndex, referenceString.hashCode());
                                    if (implementation != null && implementation instanceof DalvikImplementation){
                                        DalvikImplementation di = (DalvikImplementation) implementation;
                                        cmMap.put(di.getDalvikClass(), di.getMethod());
                                    }else{
                                        if (implementation != null && implementation instanceof StubImplementation){
                                            StubImplementation si = (StubImplementation) implementation;
                                            
                                            for (DalvikImplementation di : si.getDalvikImp()){
                                                cmMap.put(di.getDalvikClass(),di.getMethod());
                                            }
                                        }else{
                                            System.out.println("Not Found :" + ((MethodReference) reference).getDefiningClass() + " " + referenceString+ " " + instruction.getOpcode().toString());
                                        }
                                    }
                                }
                                break;

                                default:
                                    throw new RuntimeException("MethodReference in a instruction which is not a invocation: "+ instruction.getOpcode().toString());
                                }
                                addClass(lazyUnion.get(referenceClassIndex),addedInPool);
                                addToPool(lazyUnion,pool, processCM, cmMap);
                            }
                        }
                    }
                }
            }
        }
        fetchAdditionalInfo(processCM);
        return processCM;
    }

    /*
     * Get the additional information from the added classes, by querying stubs object and apkInstances
     * Should only be used once
     */
    private void fetchAdditionalInfo(Set<CMPair> processCM){
        for (DalvikInstance instance: stubs.getInstances().getAll()){
            if (processCM.contains(new CMPair(instance.getC(), instance.getM()))){
                instances.add(instance);
            }
        }
        for (DalvikInstance instance: apkInstances.getAll()){
            if (processCM.contains(new CMPair(instance.getC(), instance.getM()))){
                instances.add(instance);
            }
        }
        
        for (ArrayData aData : stubs.getArrayDataPayload()){
            if (processCM.contains(new CMPair(aData.getC(), aData.getM()))){
                arrayDataPayload.add(aData);
            }
        }
        
        for (ConstString cString : stubs.getConstStrings()){
            if (processCM.contains(new CMPair(cString.getC(),cString.getM()))){
                constStrings.add(cString);
            }
        }

        for (PackedSwitch pSwitch : stubs.getPackedSwitchPayload()){
            if (processCM.contains(new CMPair(pSwitch.getC(),pSwitch.getM()))){
                packedSwitchPayload.add(pSwitch);
            }
        }

        for (SparseSwitch sSwitch : stubs.getSparseSwitchPayload()){
            if (processCM.contains(new CMPair(sSwitch.getC(),sSwitch.getM()))){
                sparseSwitchPayload.add(sSwitch);
            }
        }
        staticConstructor.addAll(stubs.getStaticConstructor());
    }
    
    public void createHornClauses(){
        System.out.println("Ready to start generating Horn Clauses:");

        /*
         * Initialize the set classes, which must be done *before* fetching
         * the unknown implementations from Java standard library.
         * We do not put in this set the classes or methods that contains "Landroid/support/v4/"
         * At the same time we count the number of elements in APK only
         */
        int methodNumberAPK = 0;
        int instructionNumberAPK = 0;
        int classNumberAPK = 0;
        for (GeneralClass c : apkClasses.values()){
            if(!c.getType().startsWith("Landroid/support/v4/")){
                classes.put(c.getType().hashCode(), c);
                classNumberAPK++;
                
                if (c instanceof DalvikClass){
                    for (DalvikMethod m :((DalvikClass) c).getMethods()){
                        methodNumberAPK++;
                        instructionNumberAPK += m.getInstructions().size();
                    }
                }
            }
        }
        System.out.println("Number of classes in APK : " + classNumberAPK);
        System.out.println("Number of methods in APK: " + methodNumberAPK);
        System.out.println("Number of instructions in APK: "+ instructionNumberAPK);

        
        // Get the unknown classes from Java standard and Android libraries
        Set<CMPair> processCM = fetchUnknownMethod();
                
        //Counting the number of instructions and initializing apkClassMethods
        int instructionNumber = 0;
        for (CMPair cmp : processCM){
            GeneralClass c = classes.get(cmp.getC());
            if ((c instanceof DalvikClass)){
                DalvikMethod m = ((DalvikClass) c).getMethod(cmp.getM());  
                if (m !=  null){ // will be null if method is defined in a super class
                    apkClassesMethods.add(new StringPair(c.getType(),m.getName()));
                    instructionNumber += m.getInstructions().size();
                }
            }
        }
        
        System.out.println("Ready to start generating Horn Clauses:");
        System.out.println("Number of classes : " + classes.size());
        System.out.println("Number of methods: " + processCM.size());
        System.out.println("Number of instructions: "+ instructionNumber);
        System.out.println("Number of instances : " + instances.size());

        addEntryPointsInstances();
        addStaticFieldsValues();
        
        // Populate refSources and refSinks with sources and sinks
        setSourceSink();
                
        // Initialize allocationPointOffset,allocationPointNumbers and allocationPointSize
        initializeAllocationMapping();
        // Correctly set the corresponding fields in the FSEngine
        fsengine.initialize(localHeapSize, allocationPointOffset, allocationPointSize);
        
        
        for (final GeneralClass c: classes.values()){
            if ((c instanceof DalvikClass)){
                final DalvikClass dc = (DalvikClass) c;

                final boolean isDisabledActivity = testDisabledActivity(dc);
                final boolean isLauncherActivity = testLauncherActivity(dc);
                final boolean isApplication = testApplication(dc);
                final boolean isOverapprox = testOverapprox(dc);
                boolean isCallbackImplementation = false;
                for (final GeneralClass interfaceC: dc.getInterfaces()){
                    if (callbackImplementations.contains(interfaceC.getType().hashCode())){
                        isCallbackImplementation = true;
                    }
                }

                final boolean isci = isCallbackImplementation;
                processClass(dc, isDisabledActivity, isci, isLauncherActivity, isApplication, isOverapprox);
            }
        }
    }
    
    
    private boolean testEntryPoint(final GeneralClass c, final int methodIndex){
        if (this.isEntryPoint(c.getType().hashCode(), methodIndex)){
            return true;
        }
        
        if (c instanceof DalvikClass){
            final DalvikClass dc = (DalvikClass) c;
            final GeneralClass superClass = dc.getSuperClass();
            if (superClass == null){
                return false;
            }else{
                return testEntryPoint(superClass, methodIndex);
            }
        }
        return false;

    }
    private void addEntryPointsInstances(){
        for (final GeneralClass c: classes.values()){
            if (c instanceof DalvikClass){
                final DalvikClass dc = (DalvikClass) c;
                for (final DalvikMethod method: dc.getMethods()){
                    final int methodIndex = method.getName().hashCode();
                    if (!testDisabledActivity(dc) && testEntryPoint(dc, methodIndex)
                            && (testLauncherActivity(dc)
                                    || testApplication(dc)
                                    || testOverapprox(dc))){
                        instances.add(new DalvikInstance(0, 0, 0, dc, true));
                        break;
                    }
                }
            }
        }
    }
    

    public int getLocalHeapSize(){
        return localHeapSize;
    }
    
    public int getLocalHeapNumberEntries(){
        return localHeapNumberEntries;
    }
    

    /*
     * Return the implementations of mi in ci and in its child classes.
     * Return null if no implementation was found
     */
    public Map<Integer,Implementation> getVirtualImplementations(final int ci, final int mi, final String className, final String methodName){
        return getVirtualImplementations(classes,ci,mi, className, methodName);
    }

    private Map<Integer,Implementation> getVirtualImplementations(Map<Integer,GeneralClass> classes,final int ci, final int mi, final String className, final String methodName){
        StubImplementation stub = threadStubs(ci,mi);
        if (stub.hasStub()){
            HashMap<Integer,Implementation> hm = new HashMap<Integer,Implementation>();
            for (CMPair cmp : stub.getStubsCM()){
                for (Entry<Integer, DalvikImplementation> entry : getVirtualDalvikImplementations(classes, cmp.getC(), cmp.getM(), className, methodName).entrySet()){
                    if (!hm.containsKey(entry.getKey())){
                        hm.put(entry.getKey(), new StubImplementation(entry.getKey(),cmp.getM()));
                    }

                    StubImplementation si = (StubImplementation) hm.get(entry.getKey());
                    si.addMethod(cmp);
                    si.addDalvikImp(entry.getValue());
                }
            }
            return hm;
        }else{
            HashMap<Integer,Implementation> hm = new HashMap<Integer,Implementation>();
            Map<Integer,DalvikImplementation> mDalvik = getVirtualDalvikImplementations(classes, ci, mi, className, methodName);
            if (mDalvik != null){
                for (Entry<Integer, DalvikImplementation> entry :mDalvik.entrySet()){
                    hm.put(entry.getKey(),(Implementation) entry.getValue());
                }
                return hm;
            }
            else{
                return null;
            }
        }
        
    }
    
    /*
     * Return a mapping between the hashcode of the class names of all child classes
     * of ci to the DalvikImplementation of mi in this child class.
     * This compute a virtual dispatch table
     */
    private Map<Integer,DalvikImplementation> getVirtualDalvikImplementations(Map<Integer,GeneralClass> classes,final int ci, final int mi,
            final String className, final String methodName){
        Map<Integer,DalvikImplementation> vd = new HashMap<Integer,DalvikImplementation>();     
        if (classes.containsKey(ci)){
            GeneralClass c = classes.get(ci);
            if (c instanceof DalvikClass){
                DalvikClass dc = (DalvikClass) c;
                DalvikImplementation di = getDalvikImplementation(classes,ci,mi);
                DalvikMethod m = null;
                if (di == null){
                    DalvikImplementation sdi = getSuperDalvikImplementation(classes,ci,mi);
                    if (sdi != null){
                        m = sdi.getMethod();
                        vd.put(ci, sdi);
                    }
                }else{
                    m = di.getMethod();
                    vd.put(ci, di);
                }
                virtualDispatchPopulate(classes,mi,dc,vd,m);
                return vd;
            }
        }
        System.err.println("Virtual Dispatch failed for: " + className + "->" + methodName);
        return null;
    }

    /*
     * Go through the class tree and build the implementation of all child classes of dc
     * Should only be called on getVirtualImplementations
     */
    private void virtualDispatchPopulate(Map<Integer,GeneralClass> classes, int m, DalvikClass dc, Map<Integer,DalvikImplementation> vd, DalvikMethod superM){

        for (final DalvikClass child : dc.getChildClasses()){
           
            DalvikMethod childMethod = superM;
            DalvikMethod newMethod = child.getMethod(m);
            if (newMethod != null){
                childMethod = newMethod;
            }
            if (childMethod != null){
                DalvikImplementation di = new DalvikImplementation(child,childMethod);

                for( DalvikInstance childInstance : instances.getByType(child.getType().hashCode())){
                    di.putInstance(childInstance);
                }
                vd.put(dc.getType().hashCode(), di);
                virtualDispatchPopulate(classes, m, child, vd, childMethod);
            }else{
                System.out.println(m + " not implemented in " + dc.getType());
            }
        }
    }

    /*
     * Return the implementation (which is either a Dalvik Implementation or a Stub Implementation)
     * of mi in class ci.
     * Return null if no implementation was found
     */
    public Implementation getDirectImplementation(final int ci, final int mi){
        return getDirectImplementation(classes,ci,mi);
    }

    private Implementation getDirectImplementation(Map<Integer,GeneralClass> classes, final int ci, final int mi){
        StubImplementation stub = threadStubs(ci,mi);
        if (stub.hasStub()){
            for (CMPair cmp : stub.getStubsCM()){
                stub.addDalvikImp(getDalvikImplementation(classes,cmp.getC(),cmp.getM()));
            }
            return stub;
        }else{
            return getDalvikImplementation(classes, ci, mi);
        }
    }
    
    /*
     * Return the DalvikImplementation of some method ci,mi by looking into the set of classes in argument
     */
    private DalvikImplementation getDalvikImplementation(Map<Integer,GeneralClass> classes, final int ci, final int mi){
        if (classes.containsKey(ci)){
            GeneralClass c = classes.get(ci);
            if (c instanceof DalvikClass){
                DalvikClass dc = (DalvikClass) c;
                DalvikMethod m = dc.getMethod(mi);
                if (m != null){
                    final DalvikImplementation di = new DalvikImplementation(dc, m);
                    for (DalvikInstance instance : instances.getByType(ci)){
                        di.putInstance(instance);
                    }
                    return di;
                }
            }
        }
        return null;
    }


    /*
     * Return the implementation (Dalvik or stub) of mi in the super classes of ci
     * Return null if no implementation was found
     */
    public Implementation getSuperImplementation(final int ci, final int mi){
        return getSuperImplementation(classes,ci, mi);
    }
        
    private Implementation getSuperImplementation(Map<Integer,GeneralClass> classes, final int ci, final int mi){
        StubImplementation stub = threadStubs(ci,mi);
        if (stub.hasStub()){
            for (CMPair cmp : stub.getStubsCM()){
                stub.addDalvikImp(getSuperDalvikImplementation(classes,cmp.getC(),cmp.getM()));
            }
            return stub;
        }else{
            return getSuperDalvikImplementation(classes, ci, mi);
        }
    }

    private DalvikImplementation getSuperDalvikImplementation(Map<Integer,GeneralClass> classes,final int ci, final int mi){
    final AbstractMap.SimpleEntry<DalvikClass, DalvikMethod> definition = getSuperMethod(classes,ci, mi);
        if (definition != null){
            final DalvikImplementation di = new DalvikImplementation(definition.getKey(), definition.getValue());
            for (DalvikInstance instance : instances.getByType(ci)){
                di.putInstance(instance);
            }
            return di;
        }
        return null;
    }

    
    private StubImplementation threadStubs(int ci, int mi){
        StubImplementation stub = new StubImplementation(ci,mi);
        boolean isThread = isThread(ci);
        
        /*
         * AsynTask: we start all possible thread directly
         * http://developer.android.com/reference/android/os/AsyncTask.html
         */
        if (isThread && (mi == "execute([Ljava/lang/Object;)Landroid/os/AsyncTask;".hashCode())){
            // On the background thread. Should contain the interesting computations
            stub.addMethod(new CMPair(ci,"doInBackground([Ljava/lang/Object;)Ljava/lang/Object;".hashCode()));
            // On the UI thread
            stub.addMethod(new CMPair(ci,"onPreExecute()V".hashCode()));
            // On the UI thread
            // This method should get the result from doInBackground
            stub.addDependentMethod(new CMPair(ci,"doInBackground([Ljava/lang/Object;)Ljava/lang/Object;".hashCode()), new CMPair(ci,"onPostExecute(Ljava/lang/Object;)V".hashCode()));
        }
        
        /*
         * Executor: we over approximate by starting any runnable
         * (instead of just the runnable sent to the executor)
         */
        if (isThread && (mi == "execute(Ljava/lang/Runnable;)V".hashCode())){
            stub.addMethod(new CMPair("Ljava/lang/Runnable;".hashCode(),"run()V".hashCode()));
        }

        if (isThread && (mi == "start()V".hashCode())){
            stub.addMethod(new CMPair(ci,"run()V".hashCode()));
        }
        
        return stub;
    }
    
    /*
     * Return the dalvik class and dalvik method implementing mi in ci's super classes (including ci)
     * Return null if this method is not found
     */
    private AbstractMap.SimpleEntry<DalvikClass, DalvikMethod> getSuperMethod(Map<Integer,GeneralClass> classes,final int ci, int mi){ 
        if (classes.containsKey(ci)){
            GeneralClass c = classes.get(ci);
            if (c instanceof DalvikClass){
                final DalvikClass cd = ((DalvikClass) c);

                DalvikMethod m = cd.getMethod(mi);
                if (m != null){
                    return new AbstractMap.SimpleEntry<DalvikClass, DalvikMethod>(cd, m);
                }else{
                    final GeneralClass superClass = cd.getSuperClass();
                    if (superClass != null){
                        if (superClass instanceof DalvikClass){
                            final DalvikClass scd = (DalvikClass) superClass;
                            return getSuperMethod(classes,scd.getType().hashCode(), mi);
                        }
                    }
                }
            }
        }
        return null;
    }

        
    
    /*
     * Return true is classInd is the identifier of a thread class by checking if :
     * c or its superclasses implements java/lang/Runnable
     * c or its superclasses implements java/util/concurrent/Executor
     * c extends java/lang/Thread
     * c extends Android/os/AsyncTask
     */
    private boolean isThread(final int classInd){        
        if (classes.containsKey(classInd)){
            GeneralClass c = classes.get(classInd);
            if (c instanceof DalvikClass){
                return isThreadAux((DalvikClass) c);   
            }  
        }
        
        return false;
    }

    /*
     * Return true if the super class of c is a thread class
     * Should not be used except in isThreadByInt
     */
    private boolean isThreadAux(final DalvikClass c){

        final String className = c.getType();
        if ((className.equals("Ljava/lang/Thread;")) || (className.equals("Landroid/os/AsyncTask;"))){
            return true;
        }
        for (final GeneralClass interfaceName: c.getInterfaces()){
            if (interfaceName.getType().equals("Ljava/lang/Runnable;")){
                return true;
            }
            if (interfaceName.getType().equals("Ljava/util/concurrent/Executor;")){
                return true;
            }
        }
        final GeneralClass sc = c.getSuperClass();
        if (sc != null && sc instanceof DalvikClass){
            return isThreadAux((DalvikClass) sc);
        }else{
            return false;
        }
    }
    
 

    /*
     * Return true if c,m is a source, and if className, methodName is a method in the initial apk, and not
     * a method fetched from Java standard library or Android library
     */
    //TODO:
    public boolean isSource(String className, String methodName, final int c, final int m){
        return (refSources.contains(new CMPair(c,m)));
                //&& (apkClassesMethods.contains(new StringPair(className,methodName))));
    }
    
    //TODO: used only in processIntent in standard analysis, should probably be removed
    public boolean isSourceBis(final int c, final int m){
        return refSources.contains(new CMPair(c,m));
    }

    /*
     * Return true if c,m is a sink, and if className, methodName is a method in the initial apk, and not
     * a method fetched from Java standard library or Android library
     */
    //TODO:
    public boolean isSink(String className, String methodName, final int c, final int m){
        return (refSinks.contains(new CMPair(c,m)));
                //&& (apkClassesMethods.contains(new StringPair(className,methodName))));
    }

    public void putEntryPoint(int c, int m){
        methodIsEntryPoint.add(new CMPair (c, m));
    }
    
    public boolean isEntryPoint(int c, int m){
        return methodIsEntryPoint.contains(new CMPair(c, m));
    }
    
    public boolean hasStaticConstructor(int c){
        return staticConstructor.contains(c);
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
                for (GeneralClass interfaceClass: cd.getInterfaces()){
                    final String interfaceNameFormat = interfaceClass.getType().substring(1, interfaceClass.getType().length()-1);
                    
                    Boolean boolInterface = sourcesSinks.isSourceSink(interfaceNameFormat, methodNameFormat);
                    if (boolInterface != null){
                        return bool;
                    }
                }

                if (cd.getSuperClass() != null){
                    return isSourceSink(cd.getSuperClass().getType(), methodName);
                }
            }
        }
        return null;
    }

    /*
     * Populate the sets refSources and refSinks with sources and sinks
     * Should be called only once
     */
    private void setSourceSink() {
        for (GeneralClass generalC : classes.values()){
            if (generalC instanceof DalvikClass){
                DalvikClass dc = (DalvikClass) generalC;
                for (DalvikMethod dm : dc.getMethods()){
                    if (apkClassesMethods.contains(new StringPair(dc.getType(),dm.getName()))){
                        Boolean isSourceSink = isSourceSink(dc.getType(), dm.getName());
                        if (isSourceSink != null){
                            if (isSourceSink){
                                refSources.add(new CMPair(dc.getType().hashCode(), dm.getName().hashCode()));
                            }else{
                                refSinks.add(new CMPair(dc.getType().hashCode(), dm.getName().hashCode()));
                            }
                        }
                    }
                }
            }
        }
        System.out.println("Number of sources: " + refSources.size());
        System.out.println("Number of sinks: " + refSinks.size());
    }
    public boolean isFlowSens() {
        return options.fsanalysis;
    }
    public int getDebugNumber() {
        return options.debugInt;
    }

}
