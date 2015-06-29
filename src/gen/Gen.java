package gen;



import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import javax.annotation.Nonnull;


import util.CMPair;

public class Gen {
	public int verRange;
	
	String outputDirectory;
	@Nonnull private final Set<CMPair> methodIsDefined;
	@Nonnull private final Set<CMPair> methodIsSource;
	@Nonnull private final Set<CMPair> methodIsSink;
	@Nonnull private final Set<CMPair> methodIsEntryPoint;
	
	@Nonnull private final Set<Integer> staticConstructor;
	@Nonnull private final Set<String> vars;
	@Nonnull private final Set<String> defs;
	@Nonnull private final Set<Clause> clauses;
	@Nonnull private final Set<String> mainMethod;
	@Nonnull private final Set<String> queries;
	@Nonnull private final Set<String> queriesV;
	public Gen(int verRange, String outputDirectory){
		this.verRange = verRange;
		this.outputDirectory = outputDirectory;
		this.clauses = Collections.synchronizedSet(new HashSet<Clause>());
		this.defs = Collections.synchronizedSet(new HashSet<String>());
		this.vars = Collections.synchronizedSet(new HashSet<String>());
		this.queries = Collections.synchronizedSet(new HashSet<String>());
		this.queriesV = Collections.synchronizedSet(new HashSet<String>());
		this.mainMethod = Collections.synchronizedSet(new HashSet<String>());
		this.methodIsDefined =  Collections.synchronizedSet(new HashSet <CMPair>());
		this.methodIsSink = Collections.synchronizedSet(new HashSet <CMPair>());
		this.methodIsSource = Collections.synchronizedSet(new HashSet <CMPair>());
		this.methodIsEntryPoint = Collections.synchronizedSet(new HashSet <CMPair>());
		this.staticConstructor = Collections.synchronizedSet(new HashSet <Integer>());
		
	}
	public int numberOfQueries(){
		return queries.size();
	}
	public boolean isSource(int c, int m){
		return methodIsSource.contains(new CMPair(c, m));
	}
	public boolean isSink(int c, int m){
		return methodIsSink.contains(new CMPair(c, m));
	}
	public boolean isDefined(int c, int m){
		return methodIsDefined.contains(new CMPair(c, m));
	}
	public boolean isEntryPoint(int c, int m){
		return methodIsEntryPoint.contains(new CMPair(c, m));
	}
	public boolean hasStaticConstructor(int c){
		return staticConstructor.contains(c);
	}
	public void putStaticConstructor(int c){
		staticConstructor.add(c);
	}
	public void putSource(int c, int m){
		methodIsSource.add(new CMPair (c, m));
	}
	public void putEntryPoint(int c, int m){
		methodIsEntryPoint.add(new CMPair (c, m));
	}
	public void putSink(int c, int m){
		methodIsSink.add(new CMPair (c, m));
	}
	public void putDefined(int c, int m){
		methodIsDefined.add(new CMPair (c, m));
	}
	public void addQuery(String query){
		queries.add(query);
	}
	public void addQueryV(String queryV){
		queriesV.add(queryV);
	}
	public Set<String> getQueriesV(){
		return queriesV;
	}
	public void addMain(String main){
		mainMethod.add(main);
	}
	public void addDef(String def){
		defs.add(def);
	}
	public void addVar(String var){
		vars.add(var);
	}
	public boolean isDef(String def){
		if (defs.contains(def)) return true;
		else return false;
	}
	public void addClause(Clause cl){
		clauses.add(cl);
	}
	/*private void processMethod(List<? extends ClassDef> classDefs, IndStr indStr, Method method, int c){
		int m, numReg;
		if (method.getImplementation() == null) continue;
		m = indStr.get(ReferenceUtil.getShortReferenceString(method), 'm');
		numReg = method.getImplementation().getRegisterCount();
		Iterator<? extends Instruction> it = method.getImplementation().getInstructions().iterator();
		while (it.hasNext()){
			Instruction inst= it.next();
			Opcode op = inst.getOpcode().PACKED_SWITCH_PAYLOAD;
			switch (op) {
				case op
			}
		}
	}
	public void formClases(List<? extends ClassDef> classDefs, IndStr indStr){
		Iterable<? extends Method> directMethods;
		Iterable<? extends Method> virtualMethods;
		int c;
		for (final ClassDef classDef: classDefs) {
			c = indStr.get(classDef.getType(), 'c');
			if (classDef instanceof DexBackedClassDef) {
				directMethods = ((DexBackedClassDef)classDef).getDirectMethods(false);
	    		virtualMethods = ((DexBackedClassDef)classDef).getVirtualMethods(false);
	    		} else {
	    		directMethods = classDef.getDirectMethods();
	    		virtualMethods = classDef.getVirtualMethods();
	    		}	
			for (Method method: directMethods)
				processMethod(classDefs, indStr, method, c);
			for (Method method: virtualMethods)
				processMethod(classDefs, indStr, method, c);
		}
	}*/
	public void write(){
		Iterator<String> itq = this.queries.iterator();
		int count = 0;
		while (itq.hasNext()){
			File clausesFile = new File (outputDirectory + "/clauses" + Integer.toString(count) + ".smt2");
			if (clausesFile.exists()) clausesFile.delete();
			try
			(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
				out.println(" (set-option :pp.bv-literals false) \n (set-option :fixedpoint.engine pdr) \n (define-sort bv64 () (_ BitVec 64)) \n");
			}catch (IOException e) {
			}
			Iterator<String> it = this.vars.iterator();
			while (it.hasNext()){
				String var = it.next();
				try
				(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
	    			out.println(var);
	    		}catch (IOException e) {
	    		}
			}
			it = this.defs.iterator();
			while (it.hasNext()){
				String def = it.next();
				try
				(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
	    			out.println(def);
	    		}catch (IOException e) {
	    		}
			}
			Iterator<Clause> it2 = this.clauses.iterator();
			while (it2.hasNext()){
				Clause cl = it2.next();
				try
				(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
	    			out.println(cl.toString());
	    		}catch (IOException e) {
	    		}
			}
			it = this.mainMethod.iterator();
			while (it.hasNext()){
				String main = it.next();
				try
				(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
	    			out.println(main);
	    		}catch (IOException e) {
	    		}
			}
			String query = itq.next();
			try
			(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
    			out.println(query);
    		}catch (IOException e) {
    		}
			count++;
		}
	}
	
	public void writeOne(){
		File clausesFile = new File (outputDirectory + "/clauses.smt2");
		if (clausesFile.exists()) clausesFile.delete();
		try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
			out.println(" (set-option :pp.bv-literals false) \n (set-option :fixedpoint.engine pdr) \n (define-sort bv64 () (_ BitVec 64)) \n");
		}catch (IOException e) {
		}
		Iterator<String> it = this.vars.iterator();
		while (it.hasNext()){
			String var = it.next();
			try
			(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
    			out.println(var);
    		}catch (IOException e) {
    		}
		}
		it = this.defs.iterator();
		while (it.hasNext()){
			String def = it.next();
			try
			(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
    			out.println(def);
    		}catch (IOException e) {
    		}
		}
		Iterator<Clause> it2 = this.clauses.iterator();
		while (it2.hasNext()){
			Clause cl = it2.next();
			try
			(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
    			out.println(cl.toString());
    		}catch (IOException e) {
    		}
		}
		it = this.mainMethod.iterator();
		while (it.hasNext()){
			String main = it.next();
			try
			(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
    			out.println(main);
    		}catch (IOException e) {
    		}
		}
		it = this.queries.iterator();
		while (it.hasNext()){
			String query = it.next();
			try
			(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
    			out.println(query);
    		}catch (IOException e) {
    		}
		}
	}
}