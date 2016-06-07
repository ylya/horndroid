package analysis;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import util.CMPair;
import util.LazyUnion;
import util.StringPair;
import util.Utils.CallType;
import Dalvik.DalvikClass;
import Dalvik.DalvikImplementation;
import Dalvik.DalvikInstance;
import Dalvik.GeneralClass;
import Dalvik.Instances;

public class Dispatch {
    final private Instances instances;
    final private Map<Integer,GeneralClass> classes;
    final private Map<Integer,HashSet<DalvikInstance>> dispatchedInstances;
    final private Map<Integer,HashSet<DalvikImplementation>> dispatchedImplementations;
    final private Map<Integer,StringPair> failedDispatch;
    
    public Dispatch(final Instances instances, final Map<Integer,GeneralClass> classes){
        this.instances = instances;
        this.classes = classes;
        this.dispatchedImplementations = new ConcurrentHashMap<Integer,HashSet<DalvikImplementation>>();
        this.dispatchedInstances = new ConcurrentHashMap<Integer,HashSet<DalvikInstance>>();
        this.failedDispatch = new ConcurrentHashMap<Integer,StringPair>();
    }
    
    private int makeNumber(final int c, final int m){
        return (Integer.toString(c) + Integer.toString(m)).hashCode();
    }
    
    private HashSet<DalvikImplementation> getImplementations(final int c, final int m){
        return dispatchedImplementations.get(makeNumber(c,m));
    }
    
    private HashSet<DalvikInstance> getInstances(final int c, final int m){
        return dispatchedInstances.get(makeNumber(c,m));
    }
    
    private void putImplementations(final int c, final int m, final HashSet<DalvikImplementation> diSet){
        dispatchedImplementations.put(makeNumber(c,m), diSet);
    }
    
    private void putInstances(final int c, final int m, final HashSet<DalvikInstance> diSet){
        dispatchedInstances.put(makeNumber(c,m), diSet);
    }
    
    private StringPair getFailed(final int c, final int m){
        return failedDispatch.get(makeNumber(c,m));
    }
    
    private void putFailed(final int c, final int m, final String className, final String methodName){
        failedDispatch.put(makeNumber(c,m),new StringPair(className, methodName));
    }
    
    private Set<CMPair> threadInvokes(int ci, int mi){
        Set<CMPair> threadInvokes = new HashSet<CMPair>();
        boolean isThread = isThread(ci);
        /*
         * AsynTask: we start all possible thread directly
         * http://developer.android.com/reference/android/os/AsyncTask.html
         */
        if (isThread && (mi == "execute([Ljava/lang/Object;)Landroid/os/AsyncTask;".hashCode())){
            // On the background thread. Should contain the interesting computations
            threadInvokes.add(new CMPair(ci,"doInBackground([Ljava/lang/Object;)Ljava/lang/Object;".hashCode()));
            // On the UI thread
            threadInvokes.add(new CMPair(ci,"onPreExecute()V".hashCode()));
            // On the UI thread
            // This method should get the result from doInBackground
            threadInvokes.add(new CMPair(ci,"doInBackground([Ljava/lang/Object;)Ljava/lang/Object;".hashCode())); 
            threadInvokes.add(new CMPair(ci,"onPostExecute(Ljava/lang/Object;)V".hashCode()));
        }
        
        /*
         * Executor: we over approximate by starting any runnable
         * (instead of just the runnable sent to the executor)
         */
        if (isThread && (mi == "execute(Ljava/lang/Runnable;)V".hashCode())){
            threadInvokes.add(new CMPair("Ljava/lang/Runnable;".hashCode(),"run()V".hashCode()));
        }

        if (isThread && (mi == "start()V".hashCode())){
            threadInvokes.add(new CMPair(ci,"run()V".hashCode()));
        }
        //we do a resolution on thread init, not on thread start, as at thread start the class information is lost
        //(it is stored somewhere in the thread class by the operating system, we can also simulate that storing class name somewhere).
        //on the other hand, if one initializes the thread and never spawns it? rare
        //JavaThread2 for the reference
        if ((ci == "Ljava/lang/Thread;".hashCode()) && (mi == "<init>(Ljava/lang/Runnable;)V".hashCode())){
            threadInvokes.add(new CMPair("Ljava/lang/Runnable;".hashCode(),"run()V".hashCode()));
        }
        
        return threadInvokes;
    }
    
    /*
     * Return true is classInd is the identifier of a thread class by checking if :
     * c or its superclasses implements java/lang/Runnable
     * c or its superclasses implements java/util/concurrent/Executor
     * c extends java/lang/Thread
     * c extends Android/os/AsyncTask
     */
    protected boolean isThread(final int classInd){
        if (classInd == "Ljava/lang/Thread;".hashCode()
                || classInd == "Landroid/os/AsyncTask;".hashCode()
                || classInd == "Ljava/lang/Runnable;".hashCode()
                || classInd == "Ljava/util/concurrent/Executor;".hashCode()
                || classInd == "Ljava/util/concurrent/ExecutorService;".hashCode()){
            return true;
        }
        if (classes.containsKey(classInd)){
            GeneralClass c = classes.get(classInd);
            return isThreadAux(c);   
        }
        return false;
    }

    /*
     * Return true if the super class of c is a thread class
     * Should not be used except in isThreadByInt
     */
    private boolean isThreadAux(final GeneralClass gc){
        final String className = gc.getType();
        if ((className.equals("Ljava/lang/Thread;")) || (className.equals("Landroid/os/AsyncTask;"))){
            return true;
        }
        if (gc instanceof DalvikClass){
            final DalvikClass c = (DalvikClass) gc;
            for (final GeneralClass interfaceName: c.getInterfaces()){
                if (interfaceName.getType().equals("Ljava/lang/Runnable;")){
                    return true;
                }
                if (interfaceName.getType().equals("Ljava/util/concurrent/Executor;")){
                    return true;
                }
                if (interfaceName.getType().equals("Ljava/util/concurrent/ExecutorService;")){
                    return true;
                }
                
            }           
            final GeneralClass sc = c.getSuperClass();
            if (sc != null){
                return isThreadAux(sc);
            }else{
                return false;
            }
        }
        return false;
    }
    
    public DispatchResult dispatch(final int c, final int m,
            final String className, final String methodName, CallType callType){
        
        Set<CMPair> threadInvokes = threadInvokes(c, m);
        DispatchResult dr = null;
        DispatchResult dr2 = null;
        if (!threadInvokes.isEmpty()) {
            for (CMPair cmp : threadInvokes) {
                final int newC = cmp.getC();
                final int newM = cmp.getM();
                switch (callType) {
                case SUPER:
                    dr2 = superDispatch(newC, newM, className, methodName);
                    if (dr != null && dr2 != null){
                        dr.mergeResults(dr2);
                    }
                    else{
                        if (dr2 != null){
                            dr = dr2;
                        }                    }
                    break;
                case STATIC:
                    dr2 = staticDispatch(newC, newM, className, methodName);
                    if (dr != null && dr2 != null){
                        dr.mergeResults(dr2);
                    }
                    else{
                        if (dr2 != null){
                            dr = dr2;
                        }                    }
                    break;
                case DIRECT:
                    dr2 = directDispatch(newC, newM, className, methodName);
                    if (dr != null && dr2 != null){
                        dr.mergeResults(dr2);
                    }
                    else{
                        if (dr2 != null){
                            dr = dr2;
                        }                    }
                    break;
                case INTERFACE:
                    dr2 = interfaceDispatch(newC, newM, className, methodName);
                    if (dr != null && dr2 != null){
                        dr.mergeResults(dr2);
                    }
                    else{
                        if (dr2 != null){
                            dr = dr2;
                        }                    }
                    break;
                case VIRTUAL:
                    dr2 = virtualDispatch(newC, newM, className, methodName);
                    if (dr != null && dr2 != null){
                        dr.mergeResults(dr2);
                    }
                    else{
                        if (dr2 != null){
                            dr = dr2;
                        }
                    }
                    break;
                }
            }
            return dr;
        } else {
            switch (callType) {
            case SUPER:
                return superDispatch(c, m, className, methodName);
            case STATIC:
                return staticDispatch(c, m, className, methodName);
            case DIRECT:
                return directDispatch(c, m, className, methodName);
            case INTERFACE:
                return interfaceDispatch(c, m, className, methodName);
            case VIRTUAL:
                return virtualDispatch(c, m, className, methodName);
            }
        }
        return null;
    }
    
    private void superVirtualDispatch(final DalvikClass dc, final int m, final Set<DalvikInstance> instSet, 
            final Set<DalvikImplementation> implSet){
        if (instances.getByType(dc.getType().hashCode()) != null){
            instSet.addAll(instances.getByType(dc.getType().hashCode()));
        }        
        if (dc.getMethod(m) != null){
            implSet.add(new DalvikImplementation(dc, dc.getMethod(m)));
        }
        else{
            if (dc.getSuperClass() instanceof DalvikClass){
                superVirtualDispatch((DalvikClass) dc.getSuperClass(), m, instSet, implSet);
            }
        }
    }
    
    private void childVirtualDispatch(final DalvikClass dc, final int m, final Set<DalvikInstance> instSet, 
            final Set<DalvikImplementation> implSet){
        
        for (final GeneralClass childClass : dc.getChildClasses()){
            final DalvikClass cc = (DalvikClass) childClass;
            if (childClass instanceof DalvikClass){
                if (instances.getByType(cc.getType().hashCode()) != null){
                    instSet.addAll(instances.getByType(cc.getType().hashCode()));
                }        
                if (cc.getMethod(m) != null){
                    implSet.add(new DalvikImplementation(cc, cc.getMethod(m)));
                }
                childVirtualDispatch(cc, m, instSet, implSet);
            }
        }
    }
    
    private DispatchResult staticDispatch(final int c, final int m,
            final String className, final String methodName) {
        final StringPair checkFailed = getFailed(c, m);
        if (checkFailed != null) {
            return null;
        } else {
            if ((getImplementations(c, m) != null)) {
                return new DispatchResult(null, getImplementations(c, m));
            } else {
                final HashSet<DalvikImplementation> implSet = new HashSet<DalvikImplementation>();
                final GeneralClass gc = classes.get(c);
                if (gc instanceof DalvikClass) {
                    final DalvikClass dc = (DalvikClass) gc;
                    if (dc.getMethod(m) != null) {
                        implSet.add(new DalvikImplementation(dc, dc
                                .getMethod(m)));
                    }
                    if (implSet.isEmpty()) {
                        putFailed(c,m,className,methodName);
                        return null;
                    }
                    else{
                        putImplementations(c,m,implSet);
                        return new DispatchResult(null, implSet);
                    }
                }
                else{
                    putFailed(c,m,className,methodName);
                    return null;
                }
                
            }
        }
    }
    
    private DispatchResult directDispatch(final int c, final int m,
            final String className, final String methodName) {
        final StringPair checkFailed = getFailed(c, m);
        if (checkFailed != null) {
            return null;
        } else {
            if ((getImplementations(c, m) != null)) {
                return new DispatchResult(null, getImplementations(c, m));
            } else {
                final HashSet<DalvikImplementation> implSet = new HashSet<DalvikImplementation>();
                final GeneralClass gc = classes.get(c);
                if (gc instanceof DalvikClass) {
                    final DalvikClass dc = (DalvikClass) gc;
                    if (dc.getMethod(m) != null) {
                        implSet.add(new DalvikImplementation(dc, dc
                                .getMethod(m)));
                    }
                    if (implSet.isEmpty()) {
                        putFailed(c,m,className,methodName);
                        return null;
                    }
                    else{
                        putImplementations(c,m,implSet);
                        return new DispatchResult(null, implSet);
                    }
                }
                else{
                    putFailed(c,m,className,methodName);
                    return null;
                }
                
            }
        }
    }
    
    private DispatchResult superDispatch(final int c, final int m,
            final String className, final String methodName) {
        final StringPair checkFailed = getFailed(c, m);
        if (checkFailed != null) {
            return null;
        } else {
            if ((getImplementations(c, m) != null)
                    && (getInstances(c, m) != null)) {
                return new DispatchResult(getInstances(c, m), getImplementations(c, m));
            } else {
                final HashSet<DalvikInstance> instSet = new HashSet<DalvikInstance>();
                final HashSet<DalvikImplementation> implSet = new HashSet<DalvikImplementation>();
                final GeneralClass gc = classes.get(c);
                if (instances.getByType(c) != null){
                    instSet.addAll(instances.getByType(c));
                }
                if (gc instanceof DalvikClass) {
                    final DalvikClass dc = (DalvikClass) gc;
                    if (dc.getMethod(m) != null) {
                        implSet.add(new DalvikImplementation(dc, dc
                                .getMethod(m)));
                    }
                    if (dc.getSuperClass() instanceof DalvikClass) {
                        superVirtualDispatch((DalvikClass) dc.getSuperClass(),
                                m, instSet, implSet);
                    }
                    if (instSet.isEmpty()
                            || implSet.isEmpty()) {
                        putFailed(c,m,className,methodName);
                        return null;
                    }
                    else{
                        putImplementations(c,m,implSet);
                        putInstances(c,m,instSet);
                        return new DispatchResult(instSet, implSet);
                    }
                }
                else{
                    putFailed(c,m,className,methodName);
                    return null;
                }
                
            }
        }
    }
    
    private DispatchResult interfaceDispatch(final int c, final int m,
            final String className, final String methodName) {
        final StringPair checkFailed = getFailed(c, m);
        if (checkFailed != null) {
            return null;
        } else {
            if ((getImplementations(c, m) != null)
                    && (getInstances(c, m) != null)) {
                return new DispatchResult(getInstances(c, m), getImplementations(c, m));
            } else {
                final HashSet<DalvikInstance> instSet = new HashSet<DalvikInstance>();
                final HashSet<DalvikImplementation> implSet = new HashSet<DalvikImplementation>();
                if (!(classes instanceof LazyUnion)) {
                    for (final GeneralClass gc : classes.values()) {
                        if ((gc instanceof DalvikClass)) {
                            final DalvikClass dc = (DalvikClass) gc;
                            for (final GeneralClass ic : dc.getInterfaces()) {
                                if ((dc.getMethod(m) != null)
                                        && (ic.getType().hashCode() == c)) {
                                    if (instances.getByType(dc.getType().hashCode()) != null) {
                                        instSet.addAll(instances.getByType(dc
                                                .getType().hashCode()));
                                    }
                                    implSet.add(new DalvikImplementation(dc, dc
                                            .getMethod(m)));
                                }
                            }
                        }
                    }
                }
                else{
                    for (final GeneralClass gc : ((LazyUnion)classes).values1()) {
                        if ((gc instanceof DalvikClass)) {
                            final DalvikClass dc = (DalvikClass) gc;
                            for (final GeneralClass ic : dc.getInterfaces()) {
                                if ((dc.getMethod(m) != null)
                                        && (ic.getType().hashCode() == c)) {
                                    if (instances.getByType(dc.getType().hashCode()) != null) {
                                        instSet.addAll(instances.getByType(dc
                                                .getType().hashCode()));
                                    }
                                    implSet.add(new DalvikImplementation(dc, dc
                                            .getMethod(m)));
                                }
                            }
                        }
                    }
                    for (final GeneralClass gc : ((LazyUnion)classes).values2()) {
                        if ((gc instanceof DalvikClass)) {
                            final DalvikClass dc = (DalvikClass) gc;
                            for (final GeneralClass ic : dc.getInterfaces()) {
                                if ((dc.getMethod(m) != null)
                                        && (ic.getType().hashCode() == c)) {
                                    if (instances.getByType(dc.getType().hashCode()) != null) {
                                        instSet.addAll(instances.getByType(dc
                                                .getType().hashCode()));
                                    }
                                    implSet.add(new DalvikImplementation(dc, dc
                                            .getMethod(m)));
                                }
                            }
                        }
                    }
                }
                if (instSet.isEmpty()
                   || implSet.isEmpty()) {
                   putFailed(c,m,className,methodName);
                   return null;
                }
                else{
                   putImplementations(c,m,implSet);
                   putInstances(c,m,instSet);
                   return new DispatchResult(instSet, implSet);
                   }
             }
         }
    }
    
    private DispatchResult virtualDispatch(final int c, final int m,
            final String className, final String methodName) {
        final StringPair checkFailed = getFailed(c, m);
        if (checkFailed != null) {
            return null;
        } else {
            if ((getImplementations(c, m) != null)
                    && (getInstances(c, m) != null)) {
                return new DispatchResult(getInstances(c, m), getImplementations(c, m));
            } else {
                final HashSet<DalvikInstance> instSet = new HashSet<DalvikInstance>();
                final HashSet<DalvikImplementation> implSet = new HashSet<DalvikImplementation>();
                final GeneralClass gc = classes.get(c);
                if (instances.getByType(c) != null){
                    instSet.addAll(instances.getByType(c));
                }
                if (gc instanceof DalvikClass) {
                    final DalvikClass dc = (DalvikClass) gc;
                    childVirtualDispatch(dc, m, instSet, implSet);

                    if (dc.getMethod(m) != null) {
                        implSet.add(new DalvikImplementation(dc, dc
                                .getMethod(m)));
                    }
                    if (dc.getSuperClass() instanceof DalvikClass) {
                        superVirtualDispatch((DalvikClass) dc.getSuperClass(),
                                m, instSet, implSet);
                    }
                    if (instSet.isEmpty() || implSet.isEmpty()) {
                        for (final DalvikClass child : dc.getChildClasses()) {
                            if (instances.getByType(child.getType()
                                    .hashCode()) != null){
                                instSet.addAll(instances.getByType(child.getType()
                                        .hashCode()));
                            }
                            if (child.getMethod(m) != null) {
                                implSet.add(new DalvikImplementation(child,
                                        child.getMethod(m)));
                            }
                        }
                    }
                    if (instSet.isEmpty()
                            || implSet.isEmpty()) {
                        putFailed(c,m,className,methodName);
                        return null;
                    }
                    else{
                        putImplementations(c,m,implSet);
                        putInstances(c,m,instSet);
                        return new DispatchResult(instSet, implSet);
                    }
                }
                else{
                    /*boolean found = false;
                    if (!(classes instanceof LazyUnion)) {
                        for (final GeneralClass genCl : classes.values()) {
                            if (genCl instanceof DalvikClass){
                                final DalvikClass dalCl = (DalvikClass) genCl;
                                if (dalCl.getSuperClass().getType().hashCode() == c){
                                    final DispatchResult dr = virtualDispatch(dalCl.getType().hashCode(), m, className, methodName);
                                    if (dr != null){
                                        putImplementations(c,m,dr.getImplementations());
                                        putInstances(c,m,dr.getInstances());
                                        implSet.addAll(dr.getImplementations());
                                        instSet.addAll(dr.getInstances());
                                        found = true;
                                    }
                                }
                            }
                        }
                    }
                    else{
                        for (final GeneralClass genCl : ((LazyUnion)classes).values1()) {
                            if (genCl instanceof DalvikClass){
                                final DalvikClass dalCl = (DalvikClass) genCl;
                                if (dalCl.getSuperClass().getType().hashCode() == c){
                                    final DispatchResult dr = virtualDispatch(dalCl.getType().hashCode(), m, className, methodName);
                                    if (dr != null){
                                        putImplementations(c,m,dr.getImplementations());
                                        putInstances(c,m,dr.getInstances());
                                        implSet.addAll(dr.getImplementations());
                                        instSet.addAll(dr.getInstances());
                                        found = true;
                                    }
                                }
                            }
                        }
                        for (final GeneralClass genCl : ((LazyUnion)classes).values2()) {
                            if (genCl instanceof DalvikClass){
                                final DalvikClass dalCl = (DalvikClass) genCl;
                                if (dalCl.getSuperClass().getType().hashCode() == c){
                                    final DispatchResult dr = virtualDispatch(dalCl.getType().hashCode(), m, className, methodName);
                                    if (dr != null){
                                        putImplementations(c,m,dr.getImplementations());
                                        putInstances(c,m,dr.getInstances());
                                        implSet.addAll(dr.getImplementations());
                                        instSet.addAll(dr.getInstances());
                                        found = true;
                                    }
                                }
                            }
                        }
                    }
                    if (found){
                        return new DispatchResult(instSet, implSet);
                    }
                    else{*/
                        putFailed(c,m,className,methodName);
                        return null;
                    //}
                }
            }
        }
    }
    
    
    /*public DispatchResult expensiveImplementationSearch(final int c, final int m, final String className, final String methodName) {
        boolean found = false;
        final HashSet<DalvikInstance> instSet = new HashSet<DalvikInstance>();
        final HashSet<DalvikImplementation> implSet = new HashSet<DalvikImplementation>();
        if (!(classes instanceof LazyUnion)) {
            for (final GeneralClass genCl : classes.values()) {
                if (genCl instanceof DalvikClass) {
                    final DalvikClass dalCl = (DalvikClass) genCl;
                    if (dalCl.getSuperClass().getType().hashCode() == c) {
                        final DispatchResult dr = virtualDispatch(dalCl
                                .getType().hashCode(), m, className, methodName);
                        if (dr != null) {
                            putImplementations(c, m, dr.getImplementations());
                            putInstances(c, m, dr.getInstances());
                            implSet.addAll(dr.getImplementations());
                            instSet.addAll(dr.getInstances());
                            found = true;
                        }
                    }
                }
            }
        } else {
            for (final GeneralClass genCl : ((LazyUnion) classes).values1()) {
                if (genCl instanceof DalvikClass) {
                    final DalvikClass dalCl = (DalvikClass) genCl;
                    if (dalCl.getSuperClass().getType().hashCode() == c) {
                        final DispatchResult dr = virtualDispatch(dalCl
                                .getType().hashCode(), m, className, methodName);
                        if (dr != null) {
                            putImplementations(c, m, dr.getImplementations());
                            putInstances(c, m, dr.getInstances());
                            implSet.addAll(dr.getImplementations());
                            instSet.addAll(dr.getInstances());
                            found = true;
                        }
                    }
                }
            }
            for (final GeneralClass genCl : ((LazyUnion) classes).values2()) {
                if (genCl instanceof DalvikClass) {
                    final DalvikClass dalCl = (DalvikClass) genCl;
                    if (dalCl.getSuperClass().getType().hashCode() == c) {
                        final DispatchResult dr = virtualDispatch(dalCl
                                .getType().hashCode(), m, className, methodName);
                        if (dr != null) {
                            putImplementations(c, m, dr.getImplementations());
                            putInstances(c, m, dr.getInstances());
                            implSet.addAll(dr.getImplementations());
                            instSet.addAll(dr.getInstances());
                            found = true;
                        }
                    }
                }
            }
        }
        if (found) {
            return new DispatchResult(instSet, implSet);
        } else {
            putFailed(c, m, className, methodName);
            return null;
        }
    }*/
    
//    //////////////////////////////
//    
//    /*
//     * Return all instances whose type name string hashcode is typeHash
//     * If there is no instance mathching, then return an empty set
//     */
//    public Set<DalvikInstance> getExactByType(int typeHash){
//        Set<DalvikInstance> set = instances.get(typeHash);
//        if (set == null){
//            return new HashSet<DalvikInstance>();
//        }else{
//            return set;
//        }
//    }
//    
//    /*
//     * Return all instances who implement c
//     * If there is no instance mathching, then return an empty set
//     */
//    public Set<DalvikInstance> getInterfaceByType(GeneralClass c, final Map<Integer,GeneralClass> classes){
//        Set<DalvikInstance> set = new HashSet<DalvikInstance>();
//        for (final GeneralClass gc: classes.values()){
//            if (gc instanceof DalvikClass){
//                final DalvikClass dc = (DalvikClass) gc;
//                for (final GeneralClass ic: dc.getInterfaces()){
//                    if (ic.getType().hashCode() == c.getType().hashCode()){
//                        set.addAll(getExactByType(dc.getType().hashCode()));
//                    }
//                }
//            }
//        }
//        return set;
//    }
    
    ///////////////////////////////////////
    
    
//    /*
//     * Return the implementations of mi in ci and in its child classes. Return
//     * null if no implementation was found
//     */
//    public Map<Integer, Implementation> getVirtualImplentations(final int ci,
//            final int mi, final String className, final String methodName) {
//        return getVirtualImplentations(classes, ci, mi, className, methodName);
//    }
//
//    private Map<Integer, Implementation> getVirtualImplentations(
//            Map<Integer, GeneralClass> classes, final int ci, final int mi,
//            final String className, final String methodName) {
//        StubImplementation stub = threadStubs(ci, mi);
//        if (stub.hasStub()) {
//            HashMap<Integer, Implementation> hm = new HashMap<Integer, Implementation>();
//            for (CMPair cmp : stub.getStubsCM()) {
//                for (Entry<Integer, DalvikImplementation> entry : getVirtualDalvikImplentation(
//                        classes, cmp.getC(), cmp.getM(), className, methodName)
//                        .entrySet()) {
//                    if (!hm.containsKey(entry.getKey())) {
//                        hm.put(entry.getKey(),
//                                new StubImplementation(entry.getKey(), cmp
//                                        .getM()));
//                    }
//
//                    StubImplementation si = (StubImplementation) hm.get(entry
//                            .getKey());
//                    si.addMethod(cmp);
//                    si.addDalvikImp(entry.getValue());
//                }
//            }
//            return hm;
//        } else {
//            HashMap<Integer, Implementation> hm = new HashMap<Integer, Implementation>();
//            Map<Integer, DalvikImplementation> mDalvik = getVirtualDalvikImplentation(
//                    classes, ci, mi, className, methodName);
//            if (mDalvik != null) {
//                for (Entry<Integer, DalvikImplementation> entry : mDalvik
//                        .entrySet()) {
//                    hm.put(entry.getKey(), (Implementation) entry.getValue());
//                }
//                return hm;
//            } else {
//                return null;
//            }
//        }
//
//    }
//
//    /*
//     * Return a mapping between the hashcode of the class names of all child
//     * classes of ci to the DalvikImplementation of mi in this child class. This
//     * compute a virtual dispatch table
//     */
//    private Map<Integer, DalvikImplementation> getVirtualDalvikImplentation(
//            Map<Integer, GeneralClass> classes, final int ci, final int mi,
//            final String className, final String methodName) {
//        Map<Integer, DalvikImplementation> vd = new HashMap<Integer, DalvikImplementation>();
//        if (classes.containsKey(ci)) {
//            GeneralClass c = classes.get(ci);
//            if (c instanceof DalvikClass) {
//                DalvikClass dc = (DalvikClass) c;
//                DalvikImplementation di = getDirectDalvikImplementation(
//                        classes, ci, mi);
//                DalvikMethod m = null;
//                if (di == null) {
//                    DalvikImplementation sdi = getSuperDalvikImplementation(
//                            classes, ci, mi);
//                    if (sdi != null) {
//                        m = sdi.getMethod();
//                        vd.put(ci, sdi);
//                    }
//                } else {
//                    m = di.getMethod();
//                    vd.put(ci, di);
//                }
//                virtualDispatchPopulate(classes, mi, dc, vd, m);
//                return vd;
//            }
//        }
//        System.err.println("Virtual Dispatch failed for: " + className + "->"
//                + methodName);
//        return null;
//    }
//
//    /*
//     * Go through the class tree and build the implementation of all child
//     * classes of dc Should only be called on getVirtualImplementations
//     */
//    private void virtualDispatchPopulate(Map<Integer, GeneralClass> classes,
//            int m, DalvikClass dc, Map<Integer, DalvikImplementation> vd,
//            DalvikMethod superM) {
//
//        for (final DalvikClass child : dc.getChildClasses()) {
//
//            DalvikMethod childMethod = superM;
//            DalvikMethod newMethod = child.getMethod(m);
//            if (newMethod != null) {
//                childMethod = newMethod;
//            }
//            if (childMethod != null) {
//                DalvikImplementation di = new DalvikImplementation(child,
//                        childMethod);
//
//                for (DalvikInstance childInstance : instances
//                        .getExactByType(child.getType().hashCode())) {
//                    di.putInstance(childInstance);
//                }
//                if (!di.getInstances().isEmpty()) {
//                    vd.put(dc.getType().hashCode(), di);
//                }
//                virtualDispatchPopulate(classes, m, child, vd, childMethod);
//            } else {
//                System.out.println(m + " not implemented in " + dc.getType());
//            }
//        }
//    }
//
//    /*
//     * Return the implementation (which is either a Dalvik Implementation or a
//     * Stub Implementation) of mi in class ci. Return null if no implementation
//     * was found
//     */
//    public Implementation getDirectImplementation(final int ci, final int mi) {
//        return getDirectImplementation(classes, ci, mi);
//    }
//
//    private Implementation getDirectImplementation(
//            Map<Integer, GeneralClass> classes, final int ci, final int mi) {
//        StubImplementation stub = threadStubs(ci, mi);
//        if (stub.hasStub()) {
//            for (CMPair cmp : stub.getStubsCM()) {
//                stub.addDalvikImp(getDirectDalvikImplementation(classes,
//                        cmp.getC(), cmp.getM()));
//            }
//            return stub;
//        } else {
//            return getDirectDalvikImplementation(classes, ci, mi);
//        }
//    }
//
//    /*
//     * Return the Interface DalvikImplementation of some method ci,mi by looking
//     * into the set of classes in argument
//     */
//    private DalvikImplementation getInterfaceDalvikImplementation(
//            Map<Integer, GeneralClass> classes, final int ci, final int mi) {
//        if (classes.containsKey(ci)) {
//            GeneralClass c = classes.get(ci);
//            if (c instanceof DalvikClass) {
//                DalvikClass dc = (DalvikClass) c;
//                DalvikMethod m = dc.getMethod(mi);
//                if (m != null) {
//                    final DalvikImplementation di = new DalvikImplementation(
//                            dc, m);
//                    for (DalvikInstance instance : instances
//                            .getInterfaceByType(dc, classes)) {
//                        di.putInstance(instance);
//                    }
//                    return di;
//                }
//            }
//        }
//        return null;
//    }
//
//    /*
//     * Return the Virtual DalvikImplementation of some method ci,mi by looking
//     * into the set of classes in argument
//     */
//    private DalvikImplementation getVirtualDalvikImplementation(
//            Map<Integer, GeneralClass> classes, final int ci, final int mi) {
//        if (classes.containsKey(ci)) {
//            GeneralClass c = classes.get(ci);
//            if (c instanceof DalvikClass) {
//                DalvikClass dc = (DalvikClass) c;
//                DalvikMethod m = dc.getMethod(mi);
//                if (m != null) {
//                    final DalvikImplementation di = new DalvikImplementation(
//                            dc, m);
//                    for (DalvikInstance instance : instances
//                            .getVirtualByType(dc)) {
//                        di.putInstance(instance);
//                    }
//                    return di;
//                }
//            }
//        }
//        return null;
//    }
//
//    /*
//     * Return the Direct DalvikImplementation of some method ci,mi by looking
//     * into the set of classes in argument
//     */
//    private DalvikImplementation getDirectDalvikImplementation(
//            Map<Integer, GeneralClass> classes, final int ci, final int mi) {
//        if (classes.containsKey(ci)) {
//            GeneralClass c = classes.get(ci);
//            if (c instanceof DalvikClass) {
//                DalvikClass dc = (DalvikClass) c;
//                DalvikMethod m = dc.getMethod(mi);
//                if (m != null) {
//                    final DalvikImplementation di = new DalvikImplementation(
//                            dc, m);
//                    for (DalvikInstance instance : getExactByType(ci)) {
//                        di.putInstance(instance);
//                    }
//                    return di;
//                }
//            }
//        }
//        return null;
//    }
//
//    /*
//     * Return the implementation (Dalvik or stub) of mi in the super classes of
//     * ci Return null if no implementation was found
//     */
//    public Implementation getSuperImplementation(final int ci, final int mi) {
//        return getSuperImplementation(classes, ci, mi);
//    }
//
//    private Implementation getSuperImplementation(
//            Map<Integer, GeneralClass> classes, final int ci, final int mi) {
//        StubImplementation stub = threadStubs(ci, mi);
//        if (stub.hasStub()) {
//            for (CMPair cmp : stub.getStubsCM()) {
//                stub.addDalvikImp(getSuperDalvikImplementation(classes,
//                        cmp.getC(), cmp.getM()));
//            }
//            return stub;
//        } else {
//            return getSuperDalvikImplementation(classes, ci, mi);
//        }
//    }
//
//    private DalvikImplementation getSuperDalvikImplementation(
//            Map<Integer, GeneralClass> classes, final int ci, final int mi) {
//        final AbstractMap.SimpleEntry<DalvikClass, DalvikMethod> definition = getSuperMethod(
//                classes, ci, mi);
//        if (definition != null) {
//            final DalvikImplementation di = new DalvikImplementation(
//                    definition.getKey(), definition.getValue());
//            for (DalvikInstance instance : instances
//                    .getVirtualByType(definition.getKey())) {
//                di.putInstance(instance);
//            }
//            return di;
//        }
//        return null;
//    }
    
//    /*
//     * Return the dalvik class and dalvik method implementing mi in ci's super classes (including ci)
//     * Return null if this method is not found
//     */
//    private AbstractMap.SimpleEntry<DalvikClass, DalvikMethod> getSuperMethod(Map<Integer,GeneralClass> classes,final int ci, int mi){ 
//        if (classes.containsKey(ci)){
//            GeneralClass c = classes.get(ci);
//            if (c instanceof DalvikClass){
//                final DalvikClass cd = ((DalvikClass) c);
//
//                DalvikMethod m = cd.getMethod(mi);
//                if (m != null){
//                    return new AbstractMap.SimpleEntry<DalvikClass, DalvikMethod>(cd, m);
//                }else{
//                    final GeneralClass superClass = cd.getSuperClass();
//                    if (superClass != null){
//                        if (superClass instanceof DalvikClass){
//                            final DalvikClass scd = (DalvikClass) superClass;
//                            return getSuperMethod(classes,scd.getType().hashCode(), mi);
//                        }
//                    }
//                }
//            }
//        }
//        return null;
//    }
 
}
