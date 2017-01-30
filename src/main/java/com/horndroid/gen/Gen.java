
package com.horndroid.gen;

import com.horndroid.util.CMPair;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.Collections;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import javax.annotation.Nonnull;



public class Gen {
	
	//String outputDirectory;
	@Nonnull private final Set<CMPair> methodIsDefined;
	@Nonnull private final Set<CMPair> methodIsSource;
	@Nonnull private final Set<CMPair> methodIsSink;
	@Nonnull private final Set<CMPair> methodIsEntryPoint;
	
	@Nonnull private final Set<Integer> staticConstructor;
	@Nonnull private final Set<Integer> vars;
	//@Nonnull private final Set<String> defs;
	//@Nonnull private final Set<Clause> clauses;
	//@Nonnull private final Set<String> mainMethod;
	//@Nonnull private final Set<String> queries;
	//@Nonnull private final Set<String> queriesV;
	private int numQueries;
	private int numStringQueries;
	private int numFileQueries;
	private final String outputFolder;
	private int biggestRegisterNumber;
	public Gen(final String outputFolder){
		//this.outputDirectory = outputDirectory;
		/*this.clauses = Collections.synchronizedSet(new HashSet<Clause>());
		this.defs = Collections.synchronizedSet(new HashSet<String>());
		this.vars = Collections.synchronizedSet(new HashSet<String>());
		this.queries = Collections.synchronizedSet(new HashSet<String>());
		this.queriesV = Collections.synchronizedSet(new HashSet<String>());
		this.mainMethod = Collections.synchronizedSet(new HashSet<String>());
		this.methodIsDefined =  Collections.synchronizedSet(new HashSet <CMPair>());
		this.methodIsSink = Collections.synchronizedSet(new HashSet <CMPair>());
		this.methodIsSource = Collections.synchronizedSet(new HashSet <CMPair>());
		this.methodIsEntryPoint = Collections.synchronizedSet(new HashSet <CMPair>());
		this.staticConstructor = Collections.synchronizedSet(new HashSet <Integer>());*/
		//this.clauses = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<Clause, Boolean>()));
		//this.defs = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<String, Boolean>()));
		this.vars = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<Integer, Boolean>()));
		//this.varsB = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<Integer, Boolean>()));
		//this.varsL = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<Integer, Boolean>()));
		//this.queries = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<String, Boolean>()));
		//this.queriesV = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<String, Boolean>()));
		//this.mainMethod = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<String, Boolean>()));
		this.methodIsDefined = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<CMPair, Boolean>()));
		this.methodIsSink = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<CMPair, Boolean>()));
		this.methodIsSource = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<CMPair, Boolean>()));
		this.methodIsEntryPoint = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<CMPair, Boolean>()));
		this.staticConstructor = Collections.synchronizedSet(Collections.newSetFromMap(new ConcurrentHashMap<Integer, Boolean>()));
		this.numQueries = 0;
		this.numStringQueries = 0;
		this.outputFolder = outputFolder;
		this.numFileQueries = 0;
		this.biggestRegisterNumber = 0;
	}
	public void putVar(final int i){
		vars.add(i);
	}
	public void updateBiggestRegister(final int i){
		if (i > this.biggestRegisterNumber) biggestRegisterNumber = i;
	}
	public boolean containsVar(final int i){
		return vars.contains(i);
	}

	public int numberOfQueries(){
		//return queries.size();
		return numQueries;
	}
	//public boolean isSource(int c, int m){
	//	return methodIsSource.contains(new CMPair(c, m));
	//}
	//public boolean isSink(int c, int m){
	//	return methodIsSink.contains(new CMPair(c, m));
	//}
	//public boolean isDefined(int c, int m){
	//	return methodIsDefined.contains(new CMPair(c, m));
	//}
	public boolean isEntryPoint(int c, int m){
		return methodIsEntryPoint.contains(new CMPair(c, m));
	}
	public boolean hasStaticConstructor(int c){
		return staticConstructor.contains(c);
	}
	public void putStaticConstructor(int c){
		staticConstructor.add(c);
	}
	//public void putSource(int c, int m){
	//	methodIsSource.add(new CMPair (c, m));
	//}
	public void putEntryPoint(int c, int m){
		methodIsEntryPoint.add(new CMPair (c, m));
	}
	//public void putSink(int c, int m){
	//	methodIsSink.add(new CMPair (c, m));
	//}
	//public void putDefined(int c, int m){
	//	methodIsDefined.add(new CMPair (c, m));
	//}
	public void addQuery(final String query, final int fileModifier){
		try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(new File(outputFolder + "query" + Integer.toString(fileModifier) + ".txt"), true)))) {
			out.println(query);
		}catch (IOException e) {
		}
		this.numQueries ++;
	}
	public void addQueryV(final String queryV, final int fileModifier){
		try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(new File(outputFolder +"solved" + Integer.toString(fileModifier) + ".txt"), true)))) {
			out.println(Integer.toString(numStringQueries) + queryV);
		}catch (IOException e) {
		}
		this.numStringQueries ++;
	}
	/*public Set<String> getQueriesV(){
		return queriesV;
	}*/
	public void addMain(final String main, final int fileModifier){
		try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(new File(outputFolder +"main" + Integer.toString(fileModifier) + ".txt"), true)))) {
			out.println(main);
		}catch (IOException e) {
		}
	}
	public void addDef(final String def, final int fileModifier){
		try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(new File(outputFolder +"def" + Integer.toString(fileModifier) + ".txt"), true)))) {
			out.println(def);
		}catch (IOException e) {
		}
	}
	/*public void addVar(final String var, final int fileModifier){
		try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(new File(outputFolder +"var" + Integer.toString(fileModifier) + ".txt"), true)))) {
			out.println(var);
		}catch (IOException e) {
			System.err.println("Error writing " + (new File(outputFolder +"var" + Integer.toString(fileModifier) + ".txt")).getAbsolutePath());
			
		}
	}*/
	
	/*public boolean isDef(String def){
		if (defs.contains(def)) return true;
		else return false;
	}*/
	public int getNumFileQueries(){
		return numFileQueries;
	}
	public void addClause(final Clause cl, final int fileModifier){
		try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(new File(outputFolder +"clause" + Integer.toString(fileModifier) + ".txt"), true)))) {
			out.println(cl.toString());
		}catch (IOException e) {
		}
	}
	private void addVars(){
		final File varsFile = new File(outputFolder + "outvar.txt");
		try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(varsFile, true)))) {
			out.println("(declare-var rez bv64)");
			out.println("(declare-var rezp bv64)");
			out.println("(declare-var buf bv64)");
			out.println("(declare-var bufp bv64)");
			out.println("(declare-var lrez Bool)");
			out.println("(declare-var brez Bool)");
			out.println("(declare-var lrezp Bool)");
			out.println("(declare-var lbuf Bool)");
			out.println("(declare-var lbufp Bool)");
			out.println("(declare-var fnum Int)");
			out.println("(declare-var f bv64)");
			out.println("(declare-var fpp bv64)");
			out.println("(declare-var vfp bv64)");
			out.println("(declare-var lfp Bool)");
			out.println("(declare-var bfp Bool)");
			out.println("(declare-var cn bv64)");
			out.println("(declare-var lf Bool)");
			out.println("(declare-var bf Bool)");
			out.println("(declare-var val bv64)");
			out.println("(declare-var lval Bool)");
			out.println("(declare-var bval Bool)");
			out.println("(declare-var cnum Int)");
			for (int i =0; i<= biggestRegisterNumber; i++){
				out.println("(declare-var " + "v" + Integer.toString(i) + " bv64)");
				out.println("(declare-var " + "l" + Integer.toString(i) + " Bool)");
				out.println("(declare-var " + "b" + Integer.toString(i) + " Bool)");
			}
		}catch (IOException e) {
		}
	}
	public void writeOne(final int size){
		addVars();
		File clausesFile = new File (outputFolder + "clauses.smt2");
		if (clausesFile.exists()) clausesFile.delete();
		try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
			out.println(" (set-option :pp.bv-literals false) \n (set-option :fixedpoint.engine pdr) \n (define-sort bv64 () (_ BitVec " + Integer.toString(size) + "))\n");
			out.println("(declare-rel H (bv64 bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
			out.println("(declare-rel HI (bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
			out.println("(declare-rel I (bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
			out.println("(declare-rel S (Int Int bv64 Bool Bool) interval_relation bound_relation)"); 
		}catch (IOException e) {
		}
		Runtime runtime = Runtime.getRuntime();
		Process proc;
		try {
			proc = runtime.exec(new String[]{"/bin/sh", "-c",
					"cd " + outputFolder + ';' + 
	" cat main*.txt > outmain.txt; sort def*.txt | uniq > outdef.txt; cat query*.txt > outquery.txt;"
	+ " cat clause*.txt > outclause.txt; cat outvar.txt >> clauses.smt2; cat outdef.txt >> clauses.smt2; cat outclause.txt >> clauses.smt2; cat outmain.txt"
	+ " >> clauses.smt2; cat outquery.txt >> clauses.smt2"});
		
		BufferedReader stdInput = new BufferedReader(new 
	             InputStreamReader(proc.getInputStream()));

	    BufferedReader stdError = new BufferedReader(new 
	             InputStreamReader(proc.getErrorStream()));

	    // read the output from the command
	    String s = null;
	    while ((s = stdInput.readLine()) != null) {
	    	System.out.println(s);
	    }

	    // read any errors from the attempted command
	    if (stdError.readLine() != null)
	    	System.out.println("Here is the standard error of the command (if any):\n");
	    	while ((s = stdError.readLine()) != null) {
	    		System.out.println(s);
	        }
	    proc.destroy();
		}
	    catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	public void write(final int size){
		addVars();
		Runtime runtime = Runtime.getRuntime();
		Process proc;
		try {
			proc = runtime.exec(new String[]{"/bin/sh", "-c",
					"cd " + outputFolder + ';' + 
	" cat main*.txt > outmain.txt; sort def*.txt | uniq > outdef.txt;"
	+ " cat clause*.txt > outclause.txt"});
		
		BufferedReader stdInput = new BufferedReader(new 
	             InputStreamReader(proc.getInputStream()));

	    BufferedReader stdError = new BufferedReader(new 
	             InputStreamReader(proc.getErrorStream()));

	    // read the output from the command
	    String s = null;
	    while ((s = stdInput.readLine()) != null) {
	    	System.out.println(s);
	    }

	    // read any errors from the attempted command
	    if (stdError.readLine() != null)
	    	System.out.println("Here is the standard error of the command (if any):\n");
	    	while ((s = stdError.readLine()) != null) {
	    		System.out.println(s);
	        }
	    proc.destroy();
		}
	    catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		File dir = new File (outputFolder);
		 File[] files = dir.listFiles();
	        if (files != null) {
	            for(File file: files) {
	                if (file.isFile()) {
	                   if (file.getName().endsWith(".txt") && file.getName().startsWith("query") && (file.length() > 0)) {
	                	   File clausesFile = new File (outputFolder + "clauses" + Integer.toString(numFileQueries) + ".smt2");
	               		if (clausesFile.exists()) clausesFile.delete();
	               		try
	               		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
	               		
	               			out.println(" (set-option :pp.bv-literals false) \n (set-option :fixedpoint.engine pdr) \n (define-sort bv64 () (_ BitVec " + Integer.toString(size) + "))\n");
	               			out.println("(declare-rel H (bv64 bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
	            			out.println("(declare-rel HI (bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
	            			out.println("(declare-rel I (bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
	            			out.println("(declare-rel S (Int Int bv64 Bool Bool) interval_relation bound_relation)");
	               			
	               		}catch (IOException e) {
	               		}
	                		try {
	                			final String path = file.getAbsolutePath() + " >> clauses" + Integer.toString(numFileQueries) + ".smt2";
	                			proc = runtime.exec(new String[]{"/bin/sh", "-c",
	                					"cd " + outputFolder + ';' + 
	                	" cat outvar.txt >> " + path + "; cat outdef.txt >> " + path + "; cat outclause.txt >> " + path + "; cat outmain.txt >> " 
	                	+ path + "; cat " + file.getName() + " >> " + path});
	                		
	                		BufferedReader stdInput = new BufferedReader(new 
	                	             InputStreamReader(proc.getInputStream()));

	                	    BufferedReader stdError = new BufferedReader(new 
	                	             InputStreamReader(proc.getErrorStream()));

	                	    // read the output from the command
	                	    String s = null;
	                	    while ((s = stdInput.readLine()) != null) {
	                	    	System.out.println(s);
	                	    }

	                	    // read any errors from the attempted command
	                	    if (stdError.readLine() != null)
	                	    	System.out.println("Here is the standard error of the command (if any):\n");
	                	    	while ((s = stdError.readLine()) != null) {
	                	    		System.out.println(s);
	                	        }
	                	    proc.destroy();
	                		}
	                	    catch (IOException e) {
	                			// TODO Auto-generated catch block
	                			e.printStackTrace();
	                		}
	                		numFileQueries ++;
	                   }
	                }
	            }
	        }
		
		
	
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
	/*public void write(options options){
		int count = 0;
		Iterator<String> itq = this.queries.iterator();
		System.out.println("Number of queries to solve: " + queries.size());
		while (itq.hasNext()){
			File clausesFile = new File (options.outputDirectory + "/clauses" + Integer.toString(count) + ".smt2");
			if (clausesFile.exists()) clausesFile.delete();
			try
			(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
				out.println(" (set-option :pp.bv-literals false) \n (set-option :fixedpoint.engine pdr) \n (define-sort bv64 () (_ BitVec " + Integer.toString(options.bitvectorSize) + "))\n");
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
			int numQueriesWritten = 0;
			while (itq.hasNext() && numQueriesWritten < options.numQueries){
			String query = itq.next();
			try
			(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
    			out.println(query);
    		}catch (IOException e) {
    		}
			numQueriesWritten++;
			}
			count++;
		}
	}
	
	public void writeOne(options options){
		System.out.println("Number of queries to solve: " + queries.size());
		File clausesFile = new File (options.outputDirectory + "/clauses.smt2");
		if (clausesFile.exists()) clausesFile.delete();
		try
		(PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(clausesFile, true)))) {
			out.println(" (set-option :pp.bv-literals false) \n (set-option :fixedpoint.engine pdr) \n (define-sort bv64 () (_ BitVec " + Integer.toString(options.bitvectorSize) + "))\n");
		}catch (IOException e) {
			System.out.println("Cannot write to a file!");
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
	}*/
}