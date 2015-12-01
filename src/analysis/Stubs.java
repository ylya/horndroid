package analysis;

import horndroid.options;

import java.io.File;
import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
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

public class Stubs {
    final private Set<GeneralClass> classes;
    final private Set<DalvikInstance> instances;
    final private Set<ArrayData> arrayDataPayload;
    final private Set<PackedSwitch> packedSwitchPayload;
    final private Set<SparseSwitch> sparseSwitchPayload;
    final private Set<Integer> staticConstructor;
    final private Set<ConstString> constStrings;
    final private options options;

    public Stubs(options options){
        //TODO: beautiful definitions like the one for classes
        this.classes = Collections.synchronizedSet(new HashSet<GeneralClass>());
        this.instances = Collections.synchronizedSet(Collections.newSetFromMap(new HashMap<DalvikInstance, Boolean>()));
        this.constStrings = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <ConstString, Boolean>()));
        this.arrayDataPayload = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <ArrayData, Boolean>()));
        this.packedSwitchPayload = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <PackedSwitch, Boolean>()));
        this.sparseSwitchPayload = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap <SparseSwitch, Boolean>()));
        this.options = options;
        this.staticConstructor = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<Integer, Boolean>()));
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
        DataExtraction de = new DataExtraction(classes, instances, arrayDataPayload, packedSwitchPayload, sparseSwitchPayload, staticConstructor, constStrings);
        de.collectDataFromStandard(classDefs);
    }
    public Set<GeneralClass> getClasses() {
        return classes;
    }
}
