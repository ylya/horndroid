package horndroid;

import java.io.File;
import java.io.IOException;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import javax.xml.parsers.ParserConfigurationException;


import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.cli.PosixParser;
import org.apache.commons.io.FilenameUtils;
import org.jf.dexlib2.DexFileFactory;
import org.jf.dexlib2.dexbacked.DexBackedDexFile;
import org.jf.dexlib2.iface.ClassDef;
import org.jf.util.ConsoleUtil;
import org.jf.util.SmaliHelpFormatter;
import org.xml.sax.SAXException;

import com.google.common.collect.Ordering;

import analysis.Analysis;
import analysis.Stubs;
import util.SourceSinkParser;
import util.SourcesSinks;
import z3.FSEngine;

@SuppressWarnings("deprecation")
public class main {
    private static final Options options;
    private static options hornDroidOptions = new options();
    private static String[] otherArgs;
    private static Option[] clOptions;
    private static String apktoolFolder;
    private static String inputApk;
    static {
        options = new Options();
        options.addOption("q", false, "precise query results");
        options.addOption("d", true,  "print debugging information (argument: integer 1, 2 or 3)");
        options.addOption("w", false, "sensitive array indexes");
        options.addOption("n", true,  "bitvector size (default 64)");
        options.addOption("t", false, "fetch stubs");
        options.addOption("o", true,  "timeout per query (default 30 min)");
        options.addOption("l", false, "stop after fisrt leak found");
        options.addOption("s", false, "flow sensitive heap only for the objects created in the method that contains a call to a sink");
        options.addOption("m", false, "another (old) treatment for the unknown methods");
        options.addOption("i", false, "flow insensitive heap");
        options.addOption("p", false, "merging pointers");
        options.addOption("g", false, "skip uknown methods");
        options.addOption("r", true,  "number of queries");
    }
    public static void main(String[] args) {
        parseCommandLine(args);

        if (!hornDroidOptions.nfsanalysis){
            System.out.println("Flow Sensitive Analysis on "+ hornDroidOptions.bitvectorSize + " bitvectors size");
        }else{
            System.out.println("Standard Analysis on "+ hornDroidOptions.bitvectorSize + " bitvectors size");
        }
        
        Stubs stubs = new Stubs(hornDroidOptions);
        if (hornDroidOptions.stubs) {
            long startTimeA = System.nanoTime();
            System.out.print("Loading Standard Java and Android libraries ...");
            stubs.process();
            long endTimeA = System.nanoTime();
            System.out.println("done in "
                    + Long.toString((endTimeA - startTimeA) / 1000000)
                    + " milliseconds");
        }
        else{
            System.out.println("Not Loading stubs!");
        }
        
        //add all known sources and sinks
        final SourcesSinks sourcesSinks = new SourcesSinks();
        File sourceSinkFile = new File("SourcesAndSinksDroidSafe.txt");
        long startTime = System.nanoTime();
        System.out.print("Parsing sources and sinks...");
        try {
            SourceSinkParser.parseSourceSink(sourceSinkFile, sourcesSinks);
        } catch (IOException e) {
            System.err.println("Error: Parsing sources/sinks file failed!");
            System.exit(1);
        }
        long endTime = System.nanoTime();
        System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");
        //add all known sources and sinks

        //collect all apk files to process
        File inputApkFile = new File(inputApk);
        LinkedHashSet<File> filesToProcess = new LinkedHashSet<File>();
        if (!inputApkFile.exists()) { throw new RuntimeException("Cannot find file or directory \"" + inputApk + "\"");}
        startTime = System.nanoTime();
        System.out.print("Collecting apk files to process...");
        if (inputApkFile.isDirectory()){
        	getApkFilesInDir(inputApkFile, filesToProcess);
        }else if (inputApkFile.isFile()){
        	filesToProcess.add(inputApkFile);
        }else{
        	throw new RuntimeException("Neither a directory nor a normal file");
        }
        endTime = System.nanoTime();
        System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");
        //collect all apk files to process

        for (final File file: filesToProcess) {
            final String shortFilename = FilenameUtils.removeExtension(file.getName());
            final String fullPath      = FilenameUtils.getFullPath(file.getPath());
            final String inputApkFileName = FilenameUtils.getFullPath(file.getPath()) + file.getName();
            hornDroidOptions.outputDirectory  = fullPath + shortFilename;
            final FSEngine fsengine = new FSEngine(hornDroidOptions);

            final ExecutorService instructionExecutorService = Executors.newCachedThreadPool();
            Analysis analysis = new Analysis(fsengine, sourcesSinks, hornDroidOptions, instructionExecutorService, stubs);
            System.out.println("Analysing " + file.getName());
            startTime = System.nanoTime();

            File apkFile = new File(inputApkFileName);
            if (!apkFile.exists()) {
                System.err.println("Can't find the file " + inputApkFileName);
                System.exit(1);
            }
            DexBackedDexFile dexFile = null;
            try {
                dexFile = DexFileFactory.loadDexFile(apkFile, hornDroidOptions.apiLevel, false);
                if (dexFile.isOdexFile()) {
                    System.err.println("Error: Odex files are not supported");
                }
            } catch (IOException e) {
                System.err.println("Error: Loading dex file failed!");
                System.exit(1);
            }

            //////////////////////////////////////

            System.out.print("Parsing entry points...");
            try {
                SourceSinkParser.parseEntryPoint(analysis);
            } catch (IOException e1) {
                System.err.println("Error: Can't read entry points file! " + inputApkFileName);
                System.exit(1);
            }
            endTime = System.nanoTime();
            System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");

            //////////////////////////////////////
            
            startTime = System.nanoTime();
            System.out.print("Parsing callbacks and disabled activities...");
            try {
                SourceSinkParser.parseCallbacksFromXml(analysis, hornDroidOptions.outputDirectory, apkFile.getAbsolutePath(), apktoolFolder);
            } catch (IOException e) {
                System.err.println("Error: IOException : Can't read xml! " + inputApkFileName);
                System.exit(1);
            } catch (SAXException e) {
                System.err.println("Error: SAXException : Can't read xml! " + inputApkFileName);
                System.exit(1);
            } catch (ParserConfigurationException e) {
                System.err.println("Error: ParserConfigurationException : Can't read xml! " + inputApkFileName);
                System.exit(1);
            }
            endTime = System.nanoTime();
            System.out.println("...done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");

            //////////////////////////////////////

            System.out.print("Sorting classes...");
            startTime = System.nanoTime();
            List<? extends ClassDef> classDefs = Ordering.natural().sortedCopy(dexFile.getClasses());
            endTime = System.nanoTime();
            System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");

            //////////////////////////////////////

            System.out.print("Collecting data for Horn Clause generation...");
            startTime = System.nanoTime();
            analysis.collectDataFromApk(classDefs);
            endTime = System.nanoTime();
            System.out.println("done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");

            //////////////////////////////////////

            System.out.print("Generating Horn Clauses..");
            startTime = System.nanoTime();
            analysis.createHornClauses();
            endTime = System.nanoTime();
            System.out.println("...done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");

            System.out.print("Waiting for treads to terminate...");
            startTime = System.nanoTime();
            instructionExecutorService.shutdown();
            try {
                instructionExecutorService.awaitTermination(2, TimeUnit.DAYS);
            } catch (InterruptedException e1) {
                e1.printStackTrace();
            }
            endTime = System.nanoTime();
            System.out.println("...done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");

            //////////////////////////////////////////////////

            System.out.println("Executing all queries...");
            startTime = System.nanoTime();
            fsengine.executeAllQueries(analysis);
            
            endTime = System.nanoTime();
            System.out.println("...done in " + Long.toString((endTime - startTime) / 1000000) + " milliseconds");
        }
    }

    public static void parseCommandLine(String[] args){
        System.out.println("Starting Horndroid...");
        CommandLineParser parser = new PosixParser();
        CommandLine commandLine;
        try {
            commandLine = parser.parse(options, args);
        } catch (ParseException ex) {
            usage();
            return;
        }
        otherArgs = commandLine.getArgs();
        clOptions = commandLine.getOptions();

        for (int i=0; i<clOptions.length; i++) {
            Option option = clOptions[i];
            String opt = option.getOpt();
            switch (opt.charAt(0)) {
            case 'w':
                hornDroidOptions.arrays = true;
                break;
            case 'q':
                hornDroidOptions.verboseResults = true;
                break;
            case 'd':
                {
                    hornDroidOptions.debug = true;
                    String optionArg= commandLine.getOptionValue("d");
                    if (optionArg != null){
                        int dint = Integer.parseInt(optionArg);
                        hornDroidOptions.debugInt = dint;
                    }
                }
                break;
            case 't':
                hornDroidOptions.stubs = true;
                break;
            case 's':
                hornDroidOptions.sensIfHasSink = true;
                break;
            case 'n':
                hornDroidOptions.bitvectorSize = Integer.parseInt(commandLine.getOptionValue("n"));
                break;
            case 'o':
                hornDroidOptions.timeout= Integer.parseInt(commandLine.getOptionValue("o"));
                break;
            case 'r':
                hornDroidOptions.maxQueries= Integer.parseInt(commandLine.getOptionValue("r"));
                break;
            case 'l':
                hornDroidOptions.tillFirstLeak = true;
                break;
            case 'm':
                hornDroidOptions.oldUnknown = true;
                break;
            case 'i':
                hornDroidOptions.nfsanalysis = true;
                break;
            case 'p':
                hornDroidOptions.pointersMerge = true;
                break;
            case 'g':
                hornDroidOptions.nopUnknown = true;
                break;
            }
            
        }
        if (otherArgs.length != 2) {
            usage();
            return;
        }
        apktoolFolder = otherArgs[0];
        inputApk = otherArgs[1];
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
        System.out.println("java -jar fs.jar [options] %Z3Home%/bin %apktool%/ <apk-file> | <apk-folder> \n finds leaks in the app");
        System.out.println("options:");
        System.out.println("-q precise query results");
        System.out.println("-d print debugging information (argument: integer 1, 2 or 3)");
        System.out.println("-w sensitive array indexes");
        System.out.println("-n bitvector size (default 64)");
        System.out.println("-t fetch stubs");
        System.out.println("-o timeout (default 30 min)");
        System.out.println("-l stop after fisrt leak found");
        System.out.println("-s flow sensitive heap only for the objects created in the method that contains a call to a sink");
        System.out.println("-m another (old) treatment for the unknown methods");
        System.out.println("-i flow insensitive analysis");
        System.out.println("-p merging pointers");
        System.out.println("-g skip uknown methods");
        System.out.println("-r number of queries");
    }
}
