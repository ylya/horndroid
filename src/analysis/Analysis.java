package analysis;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;

import horndroid.options;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
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
    final private Map<Integer,GeneralClass> classes;
    final private Set<DalvikInstance> instances;
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
    final private Set<SourceSinkMethod> sourcesSinks;
    final private options options;
    final private Z3Engine z3engine;
    final private FSEngine fsengine;
    final private Z3Variable var;
    final private FSVariable fsvar;
    final private Stubs stubs;
    
    final ExecutorService instructionExecutorService;
    private Set<CMPair> refSources;
    private Set<CMPair> refSinks;
    private Set<CMPair> refNull;
    private final Set<CMPair> isNotDefined;
    private final Set<CMPair> isNotImpl;
    final private Map<CMPair, Set<DalvikImplementation>> allImplementations;
    final private Map<CMPair, Map<DalvikClass, DalvikMethod>> allDefinitions;
    
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

    
    //private int numberAllocationPoints;
    //private Map<Integer,String> allocationsPoints;
    
    
    public Analysis(final Z3Engine z3engine,final FSEngine fsengine, 
            final Set<SourceSinkMethod> sourcesSinks, final options options, final ExecutorService instructionExecutorService,
            final Stubs stubs){
        this.classes = new ConcurrentHashMap<Integer,GeneralClass>();
        this.instances = new HashSet<DalvikInstance>();
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
        this.refNull = new HashSet <CMPair>();
        this.allImplementations = new ConcurrentHashMap <CMPair, Set<DalvikImplementation>>();
        this.allDefinitions = new ConcurrentHashMap <CMPair, Map<DalvikClass, DalvikMethod>>();

        this.isNotDefined = new HashSet <CMPair>();
        this.isNotImpl = new HashSet <CMPair>();

        this.overapprox.add("Landroid/content/ContentProvider;".hashCode());
        this.overapprox.add("Landroid/app/Service;".hashCode());
        this.overapprox.add("Landroid/content/BroadcastReceiver;".hashCode());
        this.overapprox.add("Landroid/app/Fragment;".hashCode());
        this.overapprox.add("Landroid/support/v4/app/FragmentActivity;".hashCode());
        this.overapprox.add("Landroid/support/v4/app/Fragment;".hashCode());
        this.overapprox.add("Landroid/app/ListFragment;".hashCode());
        this.overapprox.add("Landroid/support/v4/app/ListFragment;".hashCode());
        this.overapprox.add("Landroid/os/Handler;".hashCode());
        
        this.methodIsEntryPoint = new HashSet<CMPair>();
        this.staticConstructor = new HashSet<Integer>();

        //this.numberAllocationPoints = 0;
        //this.allocationsPoints = new HashSet<Integer,String>();
    }
    public void putNotImpl(final int c, final int m){
        isNotImpl.add(new CMPair(c, m));
    }
    public void putImplemented(final int c, final int m, final Set<DalvikImplementation> implementations){
        allImplementations.put(new CMPair(c,  m), implementations);
    }
    public void putNotDefined(final int c, final int m){
        isNotDefined.add(new CMPair(c, m));
    }
    public void putDefined(final int c, final int m, final Map <DalvikClass, DalvikMethod> definitions){
        allDefinitions.put(new CMPair(c, m), definitions);
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
        if (!fsengine.isInitialized()) throw new RuntimeException("Analysis.getFSEngine:FSEngine not initialized");
        return fsengine;
    }
    
    public Set<Integer> getAllocationPoints(){
        return allocationPointOffset.keySet();
    }
    public void collectDataFromApk( List<? extends ClassDef> classDefs){
        DataExtraction de = new DataExtraction(classes, instances, arrayDataPayload, packedSwitchPayload, sparseSwitchPayload, staticConstructor, constStrings, sourcesSinks, launcherActivities);
        de.collectDataFromStandard(classDefs);
        refNull = de.getRefNull();
        refSinks = de.getRefSinks();
        refSources = de.getRefSources();
        
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
        for (DalvikInstance i : instances){
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
        // This is rather inefficient
        for (final DalvikInstance instance: instances){
            if ((instance.getC() == c) && (instance.getM() == m) && (instance.getPC() == pc)){
                return instance.hashCode();
            }
        }
        //throw new RuntimeException("ae");
        return null;
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
                    ia.CreateHornClauses();
                }else{
                    InstructionAnalysis ia = new InstructionAnalysis(this, instruction, dc, m, codeAddress);
                    ia.CreateHornClauses();                    
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
    
    private void addClassFromStubs(final GeneralClass cp, final LinkedList<GeneralClass> toProcess,
            final Set<GeneralClass> processed, final Set<Integer> stubProcessed){
        if(!processed.contains(cp) && cp != null){
            processed.add(cp);
            toProcess.add(cp);
            stubProcessed.add(cp.getType().hashCode());
            
            classes.put(cp.getType().hashCode(),cp);
            if (cp instanceof DalvikClass){
                if (((DalvikClass) cp).getSuperClass() != null){
                    addClassFromStubs(((DalvikClass)cp).getSuperClass(), toProcess, processed, stubProcessed);
                }
            }
            
        }
        else return;
    }
    
    private void addClassFromApk(final GeneralClass cp, final LinkedList<GeneralClass> toProcess,
            final Set<GeneralClass> processed, final Set<Integer> stubProcessed){
        processed.add(cp);
        toProcess.add(cp);
        if (cp instanceof DalvikClass){
            GeneralClass superClass = ((DalvikClass)cp).getSuperClass();
            if (superClass == null){
                //TODO: why some classes have no super class? Uncomment the next line to get those classes' name
                //System.out.println("This class has no super class " + cp.getType());
            }else{
                if (!classes.containsKey(superClass.getType().hashCode())){
                    GeneralClass stub = stubs.getClasses().get(superClass.getType().hashCode());
                    ((DalvikClass) cp).putSuperClass(stub);
                    addClassFromStubs(stub, toProcess, processed, stubProcessed);
                }
            }
        }
    }
    
    /*
     * Get the additional information from the added classes, by querying stubs object
     * Should only be used once
     */
    private void fetchAdditionalInfo(final Set<Integer> stubProcessed){
        for (DalvikInstance instance : stubs.getInstances()){
            if (stubProcessed.contains(instance.getC())){
                instances.add(instance);
            }
        }
        
        for (ArrayData aData : stubs.getArrayDataPayload()){
            if (stubProcessed.contains(aData.getC())){
                arrayDataPayload.add(aData);
            }
        }
        
        for (ConstString cString : stubs.getConstStrings()){
            if (stubProcessed.contains(cString.getC())){
                constStrings.add(cString);
            }
        }

        for (PackedSwitch pSwitch : stubs.getPackedSwitchPayload()){
            if (stubProcessed.contains(pSwitch.getC())){
                packedSwitchPayload.add(pSwitch);
            }
        }

        for (SparseSwitch sSwitch : stubs.getSparseSwitchPayload()){
            if (stubProcessed.contains(sSwitch.getC())){
                sparseSwitchPayload.add(sSwitch);
            }
        }
        
        staticConstructor.addAll(stubs.getStaticConstructor());
    }
    
    /*
     * Fetch the classes from standard java and android for all unknown classes
     */
    private void fetchUnknownMethod(){
        //TODO: remove the useless toProcess pool and use only a recursive function
        LinkedList<GeneralClass> toProcess = new LinkedList<GeneralClass>();
        Set<GeneralClass> processed = new HashSet<GeneralClass>();
        Set<Integer> stubProcessed = new HashSet<Integer>();
        for (final GeneralClass c: classes.values()){
            addClassFromApk(c, toProcess, processed, stubProcessed);
        }
        while(!toProcess.isEmpty()){
            GeneralClass c = toProcess.poll();
            if (c instanceof DalvikClass){
                final DalvikClass dc = (DalvikClass) c;
                for (DalvikMethod m : dc.getMethods()){
                    for (Instruction instruction : m.getInstructions()){
                        String referenceStringClass;
                        Integer referenceClassIndex = null;
                        if (instruction instanceof ReferenceInstruction) {
                            ReferenceInstruction referenceInstruction = (ReferenceInstruction)instruction;
                            Reference reference = referenceInstruction.getReference();

                            if (reference instanceof FieldReference) {
                                referenceStringClass = ((FieldReference) reference).getDefiningClass();
                                referenceClassIndex = referenceStringClass.hashCode();
                            }
                            else
                                if (reference instanceof MethodReference){
                                    referenceStringClass = ((MethodReference) reference).getDefiningClass();
                                    referenceClassIndex = referenceStringClass.hashCode();
                                }

                        }
                        if ((referenceClassIndex != null) && !classes.containsKey(referenceClassIndex)){
                            GeneralClass cp = stubs.getClasses().get(referenceClassIndex);
                            if (cp instanceof DalvikClass){
                                addClassFromStubs(cp, toProcess, processed, stubProcessed);
                            }
                        }
                    }
                }
            }
        }
        fetchAdditionalInfo(stubProcessed);
    }

    
    
    public void createHornClauses(){
        fetchUnknownMethod(); 
                
        addEntryPointsInstances();
        addStaticFieldsValues();
        // Initialize allocationPointOffset,allocationPointNumbers and allocationPointSize
        initializeAllocationMapping();
        // Correctly set the corresponding fields in the FSEngine
        fsengine.initialize(localHeapNumberEntries, localHeapSize, allocationPointOffset, allocationPointSize);
        
        System.out.println("Ready to start generating Horn Clauses:");
        System.out.println("Number of classes : " + classes.size());
        System.out.println("Number of instances : " + instances.size());
        for (final GeneralClass c: classes.values()){
            if ((c instanceof DalvikClass) && (!c.getType().contains("Landroid"))){
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
                boolean execByDefault = false;
                for (final DalvikMethod method: dc.getMethods()){
                    final int methodIndex = method.getName().hashCode();
                    if (!testDisabledActivity(dc) && testEntryPoint(dc, methodIndex)
                            && (testLauncherActivity(dc)
                                    || testApplication(dc)
                                    || testOverapprox(dc))){
                        execByDefault = true;
                        break;
                    }
                }

                if (execByDefault){
                    instances.add(new DalvikInstance(0, 0, 0, dc, true));
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
    public Set<DalvikImplementation> getImplementations(final int ci, final int mi){
        if (isNotImpl.contains(new CMPair(ci, mi))){
            return null;
        }
        if (allImplementations.containsKey(new CMPair(ci, mi))){
            return allImplementations.get(new CMPair(ci, mi));
        }
        final Set<DalvikImplementation> implementations = new HashSet<DalvikImplementation>();
        final Map<DalvikClass, DalvikMethod> definitions = isDefined(ci, mi);
        if (definitions == null) 
        {
            isNotDefined.add(new CMPair(ci, mi));
            return null;
        }
        else{
            allDefinitions.put(new CMPair(ci, mi), definitions);
        }
        for (Map.Entry<DalvikClass, DalvikMethod> entry : definitions.entrySet()){
            final DalvikImplementation di = new DalvikImplementation(entry.getKey(), entry.getValue());
            for (final DalvikInstance instance: instances){
                if (entry.getKey().getType().hashCode() == instance.getType().getType().hashCode()){
                    di.putInstance(instance);
                    for (final DalvikClass child: entry.getKey().getChildClasses()){
                        for (final DalvikInstance childInstance: instances){
                            if (child.getType().hashCode() == childInstance.getType().getType().hashCode()){
                                di.putInstance(childInstance);
                            }
                        }
                    }
                }
            }
            implementations.add(di);

        }
        return implementations;
    }
    
    /*
     * Return the implementation of mi in the super classes of ci only
     * Return null if no implementation was found
     */
    public Set<DalvikImplementation> getSuperImplementations(final int ci, final int mi){
        final Set<DalvikImplementation> implementations = new HashSet<DalvikImplementation>();
        final AbstractMap.SimpleEntry<DalvikClass, DalvikMethod> definition = isSuperDefined(ci, mi);
        if (definition == null){
            return null;
        }else{
            final DalvikImplementation di = new DalvikImplementation(definition.getKey(), definition.getValue());
            for (final DalvikInstance instance: instances){
                if (definition.getKey().getType().hashCode() == instance.getType().getType().hashCode()){
                    di.putInstance(instance);
                }
            }
            implementations.add(di);

        }
        return implementations;
    }
    
    /*
     * Return the dalvik class and dalvik method implementing mi in ci super classes
     * Return null if this method is not found
     */
    private AbstractMap.SimpleEntry<DalvikClass, DalvikMethod> isSuperDefined(final int ci, int mi){  
        final boolean isThread = isThreadByInt(ci);
        if (isThread && (mi == "execute([Ljava/lang/Object;)Landroid/os/AsyncTask;".hashCode())){
            mi = "doInBackground([Ljava/lang/Object;)Ljava/lang/Object;".hashCode();
        }
        if (isThread && (mi == "start()V".hashCode())){
            mi = "run()V".hashCode();
        }
        if (classes.containsKey(ci)){
            GeneralClass c = classes.get(ci);
            if (c instanceof DalvikClass){
                final DalvikClass cd = ((DalvikClass) c);   
                final GeneralClass superClass = cd.getSuperClass();
                if (superClass == null){
                    return null;
                }else{
                    if (superClass instanceof DalvikClass){
                        final DalvikClass scd = (DalvikClass) superClass;
                        for (final DalvikMethod m: scd.getMethods()){
                            if (m.getName().hashCode() == mi){
                                 return new AbstractMap.SimpleEntry<DalvikClass, DalvikMethod>(cd, m);
                            }
                        }
                        isSuperDefined(scd.getType().hashCode(), mi);
                    }
                }
            }
        }
        return null;
    }
    
    /*
     * Return the set of classes*method implementing some method ci,mi by looking in class ci and all its child classes
     * Return null if ci,mi is not defined
     */
    public Map<DalvikClass, DalvikMethod> isDefined(final int ci, int mi){	
        if (isNotDefined.contains(new CMPair(ci, mi))){
            return null;
        }
        Map<DalvikClass, DalvikMethod> resolvents = new ConcurrentHashMap<DalvikClass, DalvikMethod>();
        Map<DalvikClass, DalvikMethod> exResolvents = allDefinitions.get(new CMPair(ci, mi));
        if (exResolvents != null){
            return exResolvents;
        }


        final boolean isThread = isThreadByInt(ci);
        if (isThread && (mi == "execute([Ljava/lang/Object;)Landroid/os/AsyncTask;".hashCode())){
            mi = "doInBackground([Ljava/lang/Object;)Ljava/lang/Object;".hashCode();
        }
        if (isThread && (mi == "start()V".hashCode())){
            mi = "run()V".hashCode();
        }
        
        if (classes.containsKey(ci)){
            GeneralClass c = classes.get(ci);
            if ((c instanceof DalvikClass)){
                final DalvikClass cd = ((DalvikClass) c);
                
                for (final DalvikMethod m: cd.getMethods()){
                    if (m.getName().hashCode() == mi){

                        resolvents.put(cd, m);
                        break;
                    }
                }
                
                for (final DalvikClass sc: cd.getChildClasses()){
                    if (sc != null){
                        final Map<DalvikClass, DalvikMethod> resolventsChild = isDefined(sc.getType().hashCode(), mi);
                        if (resolventsChild != null)
                            resolvents.putAll(resolventsChild);
                    }
                }
                
                for (final GeneralClass cint: cd.getInterfaces()){
                    if ((cint.getType().hashCode() == ci)){
                        for (final DalvikMethod m: 
                            cd.getMethods()){
                            if (m.getName().hashCode() == mi){
                                resolvents.put(cd, m);
                                break;
                            }
                        }
                    }
                }
            }
        }        
        
        if (resolvents.isEmpty()){
            return null;
        }else{
        return resolvents;
        }
    }

    /*
     * Return true if the super class of c is a thread class
     * Should not be used except in isThreadByInt
     */
    private boolean isThread(final GeneralClass c){
        if (c instanceof DalvikClass){
            final DalvikClass dc = (DalvikClass) c;
            final GeneralClass sc = dc.getSuperClass();
            if (sc != null){
                final int superClass = sc.getType().hashCode();
                if ((superClass == "Ljava/lang/Thread;".hashCode()) || (superClass == "Landroid/os/AsyncTask;".hashCode())){
                    return true;
                }
                else{
                    return isThread(sc);
                }
            }else{
                return false;
            }
        }
        return false;
    }

    /*
     * Return true is classInd is the identifier of a thread class
     */
    public boolean isThreadByInt(final int classInd){        
        if (classes.containsKey(classInd)){
            GeneralClass c = classes.get(classInd);
            if (c instanceof DalvikClass){
                final DalvikClass dc = (DalvikClass) c;
                final Set <GeneralClass> interfaces = dc.getInterfaces();

                if (interfaces.size() != 0) {
                    for (final GeneralClass interfaceName: interfaces){
                        if (interfaceName.getType().hashCode() == "Ljava/lang/Runnable;".hashCode()){
                            return true;
                        }
                    }
                }
                return isThread(c);   
            }  
        }
        
        return false;
    }
    
 

    public boolean isSource(final int c, final int m){
        return refSources.contains(new CMPair(c,m));
    }

    public boolean isSink(final int c, final int m){
        return refSinks.contains(new CMPair(c,m));
    }


    
    public void putEntryPoint(int c, int m){ methodIsEntryPoint.add(new CMPair (c, m));}
    public boolean isEntryPoint(int c, int m){
        return methodIsEntryPoint.contains(new CMPair(c, m));
    }
    public boolean hasStaticConstructor(int c){
        return staticConstructor.contains(c);
    }
   
}
