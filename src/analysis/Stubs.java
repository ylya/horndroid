package analysis;

import com.google.common.collect.Sets;
import horndroid.options;

import java.io.File;
import java.io.IOException;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import org.jf.dexlib2.DexFileFactory;
import org.jf.dexlib2.dexbacked.DexBackedDexFile;
import org.jf.dexlib2.iface.ClassDef;

import payload.ArrayData;
import payload.PackedSwitch;
import payload.SparseSwitch;
import strings.ConstString;

import com.google.common.collect.Ordering;

import Dalvik.GeneralClass;
import Dalvik.Instances;

public class Stubs {
    final private Map<Integer,GeneralClass> classes;
    final private Instances instances;
    final private Set<ArrayData> arrayDataPayload;
    final private Set<PackedSwitch> packedSwitchPayload;
    final private Set<SparseSwitch> sparseSwitchPayload;
    final private Set<Integer> staticConstructor;
    final private Set<ConstString> constStrings;
    final private options options;

    public Stubs(options options){
        //TODO: beautiful definitions like the one for classes
        this.classes = new ConcurrentHashMap<Integer, GeneralClass>();
        this.instances = new Instances();
        this.constStrings = Collections.synchronizedSet(new HashSet <ConstString>());
        this.arrayDataPayload = Collections.synchronizedSet(new HashSet <ArrayData>());
        this.packedSwitchPayload = Collections.synchronizedSet(new HashSet <PackedSwitch>());
        this.sparseSwitchPayload = Collections.synchronizedSet(new HashSet <SparseSwitch>());
        this.options = options;
        this.staticConstructor = Collections.synchronizedSet(new HashSet<Integer>());
    }
    public void process(){
        long startTime, endTime;

        File andFile = new File("classes.dex");
        File andFile2 = new File("classes2.dex");

        if (!andFile.exists() || !andFile2.exists()) {
            System.err.println("Can't find the file android.dex");
            System.exit(1);
        }
        DexBackedDexFile dexFile = null;
        DexBackedDexFile dexFile2 = null;
        try {
            System.out.println("Loading dex files....");
            startTime = System.nanoTime();
            dexFile = DexFileFactory.loadDexFile(andFile, options.apiLevel, false);
            dexFile2 = DexFileFactory.loadDexFile(andFile2, options.apiLevel, false);
            if (dexFile.isOdexFile() || dexFile2.isOdexFile()) {
                System.err.println("Error: Odex files are not supported");
            }
            endTime = System.nanoTime();
            System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");
        } catch (IOException e) {
            System.err.println("Error: Loading dex file failed!");
            System.exit(1);
        }
//        List<? extends ClassDef> classDefs = Ordering.natural().sortedCopy(dexFile.getClasses(), dexFile2.getClasses());
        System.out.println("union-ing and sorting dex classes...");
        startTime = System.nanoTime();
        List<? extends ClassDef> classDefs = Ordering.natural().sortedCopy(Sets.union(dexFile.getClasses(), dexFile2.getClasses()));
        endTime = System.nanoTime();
        System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");

        System.out.println("data extracting...");
        startTime = System.nanoTime();
        DataExtraction de = new DataExtraction(classes, instances, arrayDataPayload, packedSwitchPayload, sparseSwitchPayload, staticConstructor, constStrings, new HashSet<Integer>());
        de.collectData(classDefs);
        endTime = System.nanoTime();
        System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");

    }
    public Map<Integer,GeneralClass> getClasses() {
        return classes;
    }
    
    
    public Instances getInstances(){
        return instances;
    }
    
    public Set<PackedSwitch> getPackedSwitchPayload(){
        return packedSwitchPayload;
    }
    
    public Set<SparseSwitch> getSparseSwitchPayload(){
        return sparseSwitchPayload;
    }
    
    public Set<Integer> getStaticConstructor(){
        return staticConstructor;
    }
    
    public Set<ConstString> getConstStrings(){
        return constStrings;
    }
    
    public Set<ArrayData> getArrayDataPayload(){
        return arrayDataPayload;
    }

}
