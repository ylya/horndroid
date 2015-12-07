package analysis;

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
import util.SourceSinkMethod;

import com.google.common.collect.Ordering;

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
        File andFile = new File("android.dex");
        if (!andFile.exists()) {
            System.err.println("Can't find the file android.dex");
            System.exit(1);
        }
        DexBackedDexFile dexFile = null;
        try {
            dexFile = DexFileFactory.loadDexFile(andFile, options.apiLevel, false);
            if (dexFile.isOdexFile()) {
                System.err.println("Error: Odex files are not supported");
            }
        } catch (IOException e) {
            System.err.println("Error: Loading dex file failed!");
            System.exit(1);
        }
        List<? extends ClassDef> classDefs = Ordering.natural().sortedCopy(dexFile.getClasses());
        DataExtraction de = new DataExtraction(classes, instances, arrayDataPayload, packedSwitchPayload, sparseSwitchPayload, staticConstructor, constStrings, new HashSet<SourceSinkMethod>(), new HashSet<Integer>());
        de.collectDataFromStandard(classDefs);
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
