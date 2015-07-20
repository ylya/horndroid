/*
 * [The "BSD licence"]
 * Copyright (c) 2015 Ilya Grishchenko
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package horndroid;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.cli.PosixParser;
import org.apache.commons.io.FilenameUtils;
import org.jf.dexlib2.DexFileFactory;
import org.jf.dexlib2.dexbacked.DexBackedClassDef;
import org.jf.dexlib2.dexbacked.DexBackedDexFile;
import org.jf.dexlib2.iface.ClassDef;
import org.jf.dexlib2.iface.Method;
import org.jf.util.ConsoleUtil;
import org.jf.util.SmaliHelpFormatter;
import org.xml.sax.SAXException;

import payload.ArrayData;
import payload.PackedSwitch;
import payload.SparseSwitch;

import com.google.common.collect.Lists;
import com.google.common.collect.Ordering;

import strings.ConstString;
import util.IndStrDef;
import util.NumLoc;
import util.RefClassElement;
import util.SourceSinkMethod;
import util.SourceSinkParser;
import util.Utils;
import util.iface.IndStr;
import gen.Gen;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import javax.xml.parsers.ParserConfigurationException;

public class main {
	
    private static final Options options;
    
    static {
        options = new Options();
        options.addOption("q", false, "precise query results");
        options.addOption("w", false, "sensitive array indexes");
        options.addOption("s", false, "one query per file, run Z3 in parallel saving results to the /out folder");
        options.addOption("n", true, "bitvector size (default 64)");
    }
    
    public static void main(String[] args) throws Exception {
    	System.out.println("Starting Horndroid...");
        ExecutorService executorService = Executors.newCachedThreadPool();
        CommandLineParser parser = new PosixParser();
        CommandLine commandLine;
        try {
            commandLine = parser.parse(options, args);
        } catch (ParseException ex) {
            usage();
            return;
        }

        options options = new options();
        
        String[] otherArgs = commandLine.getArgs();
        Option[] clOptions = commandLine.getOptions();  
        
        for (int i=0; i<clOptions.length; i++) {
            Option option = clOptions[i];
            String opt = option.getOpt();
            switch (opt.charAt(0)) {
                case 'w':
                	 options.arrays = true;
                    break;
                case 'q':
                	options.verboseResults = true;
                    break;
                case 's':
                	options.oneQuery = true;
                    break;
                case 'n':
                	options.bitvectorSize = Integer.parseInt(commandLine.getOptionValue("n"));
                	break;
            }
        }
        
        if (otherArgs.length != 3) {
            usage();
            return;
        }
        
        String z3Folder = otherArgs[0];
        String apktoolFolder = otherArgs[1];
        String inputApk = otherArgs[2];
   
        final String sourcesSinksF = "SourcesAndSinks.txt";        
        File sourceSinkFile = new File(sourcesSinksF);
        final Set<SourceSinkMethod> sourcesSinks = Collections.synchronizedSet(new HashSet <SourceSinkMethod>());
       
   	    long startTime = System.nanoTime();
        System.out.print("Parsing sources and sinks...");
        SourceSinkParser.parseSourceSink(sourceSinkFile, sourcesSinks);
        long endTime = System.nanoTime();
        System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");
        
               
		File inputApkFile = new File(inputApk);
		LinkedHashSet<File> filesToProcess = new LinkedHashSet<File>();
        if (!inputApkFile.exists()) { throw new RuntimeException("Cannot find file or directory \"" + inputApk + "\"");}
        startTime = System.nanoTime();
        System.out.print("Collecting apk files to process...");
        if (inputApkFile.isDirectory()) {getApkFilesInDir(inputApkFile, filesToProcess);} 
        else if (inputApkFile.isFile()) {filesToProcess.add(inputApkFile);}
        endTime = System.nanoTime();
        System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");
        for (final File file: filesToProcess) {
        	 System.out.println("Analysing " + file.getName());
        	 startTime = System.nanoTime();
        	 final Set<Integer> disabledActivities = Collections.synchronizedSet(new HashSet <Integer>());
        	 final Set<Integer> activities = Collections.synchronizedSet(new HashSet <Integer>());
        	 final Set<Integer> applications = Collections.synchronizedSet(new HashSet <Integer>());
        	 final Set<Integer> launcherActivities = Collections.synchronizedSet(new HashSet <Integer>());
        	 final Set<ConstString> constStrings = Collections.synchronizedSet(new HashSet <ConstString>());

             final Set<Integer> callbackImplementations = Collections.synchronizedSet(new HashSet <Integer>());
             final Set<String> callbacks = Collections.synchronizedSet(new HashSet <String>());;

             final Set<ArrayData> arrayDataPayload = Collections.synchronizedSet(new HashSet <ArrayData>());
             final Set<PackedSwitch> packedSwitchPayload = Collections.synchronizedSet(new HashSet <PackedSwitch>());
             final Set<SparseSwitch> sparseSwitchPayload = Collections.synchronizedSet(new HashSet <SparseSwitch>());
             
             
        	 final IndStr indStr = new IndStrDef(); //contains the mapping from immutable strings to integers (index)
             final RefClassElement refClassElement = new RefClassElement();
             final NumLoc numLoc = new NumLoc();
        	 final String shortFilename = FilenameUtils.removeExtension(file.getName());
        	 final String fullPath      = '/' + FilenameUtils.getPath(file.getPath());
        	 String inputApkFileName = '/' + FilenameUtils.getPath(file.getPath()) + file.getName();
        	 options.outputDirectory  = fullPath + shortFilename;
        
        	 File apkFile = new File(inputApkFileName);
        	 if (!apkFile.exists()) {
        		 System.err.println("Can't find the file " + inputApkFileName);
        		 System.exit(1);
        	 }

        	 DexBackedDexFile dexFile = DexFileFactory.loadDexFile(apkFile, options.apiLevel, false);
        	 if (dexFile.isOdexFile()) {
                System.err.println("Error: Odex files are not supported");
        	 }

             
             final Gen gen = new Gen(6, options.outputDirectory);
             initGen(gen, refClassElement, indStr, options);
             
             System.out.print("Collecting data for Horn Clause generation...");
             horndroid.collectDataFromApk(numLoc, refClassElement, indStr, dexFile, options, gen, activities,  constStrings, launcherActivities,
            		 arrayDataPayload, packedSwitchPayload, sparseSwitchPayload);
             endTime = System.nanoTime();
             System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");
             List<? extends ClassDef> classDefs = Ordering.natural().sortedCopy(dexFile.getClasses());
            	 
             refClassElement.formGen(classDefs, indStr, options.outputDirectory, sourcesSinks, gen);
             
             startTime = System.nanoTime();
             System.out.print("Parsing entry points...");
             SourceSinkParser.parseEntryPoint(gen, indStr);
             endTime = System.nanoTime();
             System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");
             startTime = System.nanoTime();
             System.out.print("Parsing callbacks and disabled activities...");
             SourceSinkParser.parseCallbacksFromXml(callbacks, options.outputDirectory, file.getAbsolutePath(), disabledActivities, activities, launcherActivities, indStr, callbackImplementations,
            		 applications, apktoolFolder);
             endTime = System.nanoTime();
             System.out.println("...done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");
             
             startTime = System.nanoTime();
             refClassElement.formClassDefGen(classDefs, indStr);
             refClassElement.formHeapDef(gen);
 
             System.out.print("Generating Horn Clauses...");
        
             //add instances that were created for entry points
             for (final ClassDef classDef: classDefs){
            	String formatClassName = classDef.getType().replaceAll("\\.", "/").substring(1, classDef.getType().replaceAll("\\.", "/").length() -1);
                String[] parts = formatClassName.split("/");
         		String classN =  parts[parts.length - 1];
         		
         		Iterable<? extends Method> methods;
         		if (classDef instanceof DexBackedClassDef) {
                    methods = ((DexBackedClassDef)classDef).getDirectMethods(false);
                } else {
                    methods = classDef.getDirectMethods();
                }
         		boolean execByDefault = false;
                String classIndex = Utils.Dec(indStr.get(classDef.getType(), 'c'));
         		for (Method method: methods) {
                     String methodString = Utils.getShortMethodDescriptor(method);
                     String methodIndex  = Utils.Dec(indStr.get(methodString, 'm'));
                    		 if ((!disabledActivities.contains(indStr.get(classN, 'c'))) && (horndroid.testEntryPoint(classDefs, classDef, Integer.parseInt(methodIndex), gen, indStr))
                    				 && (launcherActivities.contains(indStr.get(classN, 'c')))){
                    			 execByDefault = true;
                    			 break;
                    		 }
         		}
         		
         		if (execByDefault){
         			//!create an instance of the entrypoint class
         			refClassElement.putInstance(0, 0, 0, Integer.parseInt(classIndex), true);    		
         			//even more: if an activity implements an interface we should add instance also
         			/*List<String> interfaces1 = Lists.newArrayList(classDef.getInterfaces());
         			for (final String interfaceName: interfaces1){
         				refClassElement.putInstance(0, 0, 0, indStr.get(interfaceName, 'c'), true);
         			}*/
         		}
         		
         		execByDefault = false;
         		
         		if (classDef instanceof DexBackedClassDef) {
                    methods = ((DexBackedClassDef)classDef).getVirtualMethods(false);
                } else {
                    methods = classDef.getVirtualMethods();
                }	
         		
         		for (Method method: methods) {
                    String methodString = Utils.getShortMethodDescriptor(method);
                    String methodIndex  = Utils.Dec(indStr.get(methodString, 'm'));
                   		 if ((!disabledActivities.contains(indStr.get(classN, 'c'))) && (horndroid.testEntryPoint(classDefs, classDef, Integer.parseInt(methodIndex), gen, indStr))
                   				 && (launcherActivities.contains(indStr.get(classN, 'c')))){
                   			 execByDefault = true;
                   			 break;
                   		 }
        		}
         		
         		if (execByDefault){
         			//!create an instance of the entrypoint class
         			refClassElement.putInstance(0, 0, 0, Integer.parseInt(classIndex), true);    		
         			//even more: if an activity implements an interface we should add instance also
         			List<String> interfaces1 = Lists.newArrayList(classDef.getInterfaces());
         			for (final String interfaceName: interfaces1){
         				refClassElement.putInstance(0, 0, 0, indStr.get(interfaceName, 'c'), true);
         			}
         		}
         		
            	
             }
            
             //
             
             horndroid.smtApkFile(numLoc, refClassElement, indStr, dexFile, options, gen, callbacks, disabledActivities, activities, launcherActivities,
            		 callbackImplementations, applications, options.bitvectorSize, arrayDataPayload, packedSwitchPayload, sparseSwitchPayload);
        
             refClassElement.putConcurSynRange(refClassElement.getSynRange() + 1);
       
	         endTime = System.nanoTime();
	         System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");

	         if (!options.oneQuery){
	         gen.writeOne(options);
        
	         String smtFile = options.outputDirectory + '/' + "clauses.smt2";
	         try {
	        	 startTime = System.nanoTime();
	        	 runZ3(z3Folder, smtFile, gen);
	         } catch (InterruptedException e) {
	        	 e.printStackTrace();
	         }
	         System.out.println("----------------------------------------------------------------------------");
	         }
	         else{
	         
	        	 gen.write(options);
       
	        	 final String outputDirectory = options.outputDirectory;
	        	 final String z3f = z3Folder;
        
	        	 for (int i = 0; i < gen.numberOfQueries(); i++){
	        		 final int count = i;
	        		 executorService.submit(new Runnable() {
	        			 @Override
	        			 public void run() {
	        				 try {
	        					 Process process = new ProcessBuilder("/bin/sh", "-c", runZ3(outputDirectory, z3f, shortFilename, fullPath, count)).start();
	        				 } catch (IOException e) {
	        					 e.printStackTrace();  
	        				 }

	        			 }
	        		 });
	        	 }
	         }
        }
    }
    
    private static void initGen(final Gen gen, final RefClassElement refClassElement, final IndStr indStr, final options options){
    	 gen.addVar("(declare-var rez bv64)");
         gen.addVar("(declare-var rezp bv64)");
         gen.addVar("(declare-var buf bv64)");
         gen.addVar("(declare-var bufp bv64)");
         gen.addVar("(declare-var lrez Bool)");
         gen.addVar("(declare-var brez Bool)");
         gen.addVar("(declare-var lrezp Bool)");
         gen.addVar("(declare-var lbuf Bool)");
         gen.addVar("(declare-var lbufp Bool)");
         gen.addVar("(declare-var fnum Int)");
         gen.addVar("(declare-var f bv64)");
         gen.addVar("(declare-var fpp bv64)");
         gen.addVar("(declare-var vfp bv64)");
         gen.addVar("(declare-var lfp Bool)");
         gen.addVar("(declare-var bfp Bool)");
         gen.addVar("(declare-var cn bv64)");
         gen.addVar("(declare-var lf Bool)");
         gen.addVar("(declare-var bf Bool)");
         gen.addVar("(declare-var val bv64)");
         gen.addVar("(declare-var lval Bool)");
         gen.addVar("(declare-var bval Bool)");
         gen.addVar("(declare-var cnum Int)");
         gen.addDef("(declare-rel H (bv64 bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
         gen.addDef("(declare-rel HI (bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
         gen.addDef("(declare-rel I (bv64 bv64 bv64 Bool Bool) interval_relation bound_relation)");
         gen.addDef("(declare-rel S (Int Int bv64 Bool Bool) interval_relation bound_relation)");         
         gen.addMain("(rule (=> (and " + refClassElement.hPred("cn", "cn", Utils.hexDec64(indStr.get("parent", 'f'), options.bitvectorSize), "f", "lf", "bf") + ' ' +
         		refClassElement.hPred("cn", "cn", Utils.hexDec64(indStr.get("result", 'f'), options.bitvectorSize), "val", "lval", "bval") + ' ' +
         		refClassElement.hPred("f", "f", "fpp", "vfp", "lfp", "bfp") + ')' + ' ' +
         		refClassElement.hPred("f", "f", Utils.hexDec64(indStr.get("result", 'f'), options.bitvectorSize), "val", "lval", "bval")
         		+ "))");
    }
    
    private static void printQueries(final Gen gen){
        Set<String> queriesV = Collections.synchronizedSet(new HashSet<String>());
        queriesV = gen.getQueriesV();
        System.out.println("Solved queries:");
        int i = 1;
        for (String queryV: queriesV){
        	System.out.println(Integer.toString(i) + " " + queryV);
        	i++;
        }
    }
    
    private static void runZ3(final String z3Folder, final String smtFile, final Gen gen) throws IOException, InterruptedException{
		System.out.println("Run Z3...");
		long startTime = System.nanoTime();
        Runtime runtime = Runtime.getRuntime();
		Process proc = runtime.exec(new String[]{"/bin/sh", "-c",
			"cd " + z3Folder + ';' + " ./z3 " + smtFile});
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
        printQueries(gen);
        System.out.println("Analysis...done in " + Long.toString((System.nanoTime() - startTime) / 1000000) + " milliseconds");
}
    
    /*private static String runZ3One(String directory, String z3Folder, String filename, String fullpath) throws IOException{
    	String smtFile = directory + '/' + "clauses.smt2";
    	//Runtime runtime = Runtime.getRuntime();
    	return "cd " + z3Folder + ';' + " ./z3 " + smtFile + " > " + fullpath + "out/" + filename +".txt";
    	//Process proc = runtime.exec(new String[]{"/bin/sh", "-c",
		//	"cd " + z3Folder + ';' + " ./z3 " + smtFile + " > " + directory + '/' + "output.txt"});	
    }*/
    
    private static String runZ3(String directory, String z3Folder, String filename, String fullpath, int numberOfQuery) throws IOException{
    	String smtFile = directory + '/' + "clauses" + Integer.toString(numberOfQuery) + ".smt2";
    	File output = new File(fullpath + "out/");
    	if (output.exists()){}
    	else
    		output.mkdirs();
    	return "cd " + z3Folder + ';' + " ./z3 " + smtFile + " > " + fullpath + "out/" + filename + Integer.toString(numberOfQuery) +".txt";
    }
    
    
    
    
    private static void getApkFilesInDir(File dir, Set<File> apkFiles) {
        File[] files = dir.listFiles();
        if (files != null) {
            for(File file: files) {
                if (file.isFile()) {
                   if (file.getName().endsWith(".apk")) {
                    apkFiles.add(file);
                   }
                }
                   else if (file.isDirectory())
                	   getApkFilesInDir(file.getAbsoluteFile(), apkFiles);
            }
        }
    }

    private static void usage() {
    	 SmaliHelpFormatter formatter = new SmaliHelpFormatter();
         int consoleWidth = ConsoleUtil.getConsoleWidth();
         if (consoleWidth <= 0) {
             consoleWidth = 100;
         }
         formatter.setWidth(consoleWidth);
         System.out.println("java -jar HornDroid.jar [options] %Z3Home%/bin %apktool%/ <apk-file> | <apk-folder> \n finds leaks in the app");
         System.out.println("options:");
         System.out.println("-q precise query results");
         System.out.println("-w sensitive array indexes");
         System.out.println("-s one query per file, run Z3 in parallel saving results to the /out folder");
         System.out.println("-n bitvector size (default 64)");
    }
}