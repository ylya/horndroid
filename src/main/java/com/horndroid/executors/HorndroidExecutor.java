package com.horndroid.executors;

import com.google.common.collect.Ordering;
import com.horndroid.Options;
import com.horndroid.analysis.Analysis;
import com.horndroid.analysis.Stubs;
import com.horndroid.model.Report;
import com.horndroid.util.SourceSinkParser;
import com.horndroid.util.SourcesSinks;
import com.horndroid.z3.FSEngine;
import org.apache.commons.io.FilenameUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jf.dexlib2.DexFileFactory;
import org.jf.dexlib2.dexbacked.DexBackedDexFile;
import org.jf.dexlib2.iface.ClassDef;
import org.xml.sax.SAXException;

import javax.xml.parsers.ParserConfigurationException;
import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import static com.horndroid.constants.TimeConstants.MILLISECONDS_IN_SECOND_CONSTANT;
import static com.horndroid.constants.TimeConstants.TIME_DISPLAY_MILLISECONDS_CONSTANT;

/**
 * Executes the horndroid tool
 *
 */
public class HorndroidExecutor {

    private static final Logger LOGGER = LogManager.getLogger(HorndroidExecutor.class);
    private Options hornDroidOptions = new Options();
    private String apkToolDirPath = "./";
    private String inputApkPath = "";


    public HorndroidExecutor(Options hornDroidOptions, String apkToolPath, String inputApkPath) {
        this.hornDroidOptions = hornDroidOptions;
        this.apkToolDirPath = apkToolPath;
        this.inputApkPath = inputApkPath;
    }

    public HorndroidExecutor(Options hornDroidOptions, String inputApkPath) {
        this.hornDroidOptions = hornDroidOptions;
        this.inputApkPath = inputApkPath;
    }

    private static void confirmApkExistence(String inputApkFileName, File apkFile) {
        if (!apkFile.exists()) {
            LOGGER.error("Can't find the file " + inputApkFileName);
            System.exit(1);
        }
    }

    private LinkedHashSet<File> getFilesToProcess() {
        long startTime;
        long endTime;
        File inputApkFile = new File(inputApkPath);
        LinkedHashSet<File> filesToProcess = new LinkedHashSet<File>();
        if (!inputApkFile.exists()) {
            throw new RuntimeException("Cannot find file or directory \"" + inputApkFile + "\"");
        }
        startTime = System.nanoTime();
        LOGGER.debug("Collecting apk files to process...");
        if (inputApkFile.isDirectory()) {
            getApkFilesInDir(inputApkFile, filesToProcess);
        } else if (inputApkFile.isFile()) {
            filesToProcess.add(inputApkFile);
        }
        endTime = System.nanoTime();
        LOGGER.debug("done in " + Long.toString((endTime - startTime) / MILLISECONDS_IN_SECOND_CONSTANT) +
                TIME_DISPLAY_MILLISECONDS_CONSTANT);
        return filesToProcess;
    }

    /**
     * Add all known sources and sinks
     *
     * @return Set<SourceSinkParser>
     */
    private SourcesSinks getSourcesAndSinks() {

        final SourcesSinks sourcesSinks = new SourcesSinks();
        File sourceSinkFile = new File("bin/SourcesAndSinksDroidSafe.txt");
        long startTime = System.nanoTime();
        LOGGER.debug("Parsing sources and sinks...");
        try {
            SourceSinkParser.parseSourceSink(sourceSinkFile, sourcesSinks);
        } catch (IOException e) {
            LOGGER.error("Error: Parsing sources/sinks file failed! with exception", e);
            System.exit(1);
        }
        long endTime = System.nanoTime();
        LOGGER.debug("done in " + Long.toString((endTime - startTime) / MILLISECONDS_IN_SECOND_CONSTANT) +
                TIME_DISPLAY_MILLISECONDS_CONSTANT);

        return sourcesSinks;
    }


    private void awaitThreadTermination(ExecutorService instructionExecutorService) {
        long startTime;
        long endTime;
        LOGGER.debug("Waiting for treads to terminate...");
        startTime = System.nanoTime();
        instructionExecutorService.shutdown();
        try {
            instructionExecutorService.awaitTermination(2, TimeUnit.DAYS);
        } catch (InterruptedException e1) {
            LOGGER.error(e1);
        }
        endTime = System.nanoTime();
        LOGGER.debug("...done in " + Long.toString((endTime - startTime) / MILLISECONDS_IN_SECOND_CONSTANT) +
                TIME_DISPLAY_MILLISECONDS_CONSTANT);
    }

    private Report executeQueries(FSEngine fsEngine,Analysis analysis, String tag) {
        long startTime;
        long endTime;
        LOGGER.debug("Executing all queries...");
        startTime = System.nanoTime();

        Report report = fsEngine.executeAllQueries(analysis,tag);
        endTime = System.nanoTime();
        LOGGER.debug("...done in " + Long.toString((endTime - startTime) / MILLISECONDS_IN_SECOND_CONSTANT) +
                TIME_DISPLAY_MILLISECONDS_CONSTANT);
        return report;
    }

    private void generateHornClauses(Analysis analysis, List<? extends ClassDef> classDefs,
                                     final Set<Integer> allowed) {
        long startTime;
        long endTime;
        LOGGER.debug("Collecting data for Horn Clause generation...");
        startTime = System.nanoTime();
        analysis.collectDataFromApk(classDefs, allowed);
        endTime = System.nanoTime();
        LOGGER.debug("done in " + Long.toString((endTime - startTime) / MILLISECONDS_IN_SECOND_CONSTANT) +
                TIME_DISPLAY_MILLISECONDS_CONSTANT);


        LOGGER.debug("Generating Horn Clauses..");
        startTime = System.nanoTime();
        analysis.createHornClauses();
        endTime = System.nanoTime();
        LOGGER.debug("...done in " + Long.toString((endTime - startTime) / MILLISECONDS_IN_SECOND_CONSTANT) +
                TIME_DISPLAY_MILLISECONDS_CONSTANT);
    }

    private List<? extends ClassDef> sortClasses(DexBackedDexFile dexFile) {
        long startTime;
        long endTime;

        LOGGER.debug("Sorting classes...");
        startTime = System.nanoTime();
        List<? extends ClassDef> classDefs = Ordering.natural().sortedCopy(dexFile.getClasses());
        endTime = System.nanoTime();
        LOGGER.debug("done in " + Long.toString((endTime - startTime) / MILLISECONDS_IN_SECOND_CONSTANT) +
                TIME_DISPLAY_MILLISECONDS_CONSTANT);

        return classDefs;
    }

    private void parseCallBacksAndDisabledActivities(File file, String inputApkFileName, Analysis analysis) {
        long startTime;
        long endTime;

        startTime = System.nanoTime();
        LOGGER.debug("Parsing callbacks and disabled activities...");
        try {
            SourceSinkParser.parseCallbacksFromXml(analysis,
                    hornDroidOptions.outputDirectory, file.getAbsolutePath(), apkToolDirPath);
        } catch (SAXException | ParserConfigurationException | IOException e) {
            LOGGER.error("Error: Can't read xml! " + inputApkFileName, e);
            System.exit(1);
        }
        endTime = System.nanoTime();
        LOGGER.debug("...done in " + Long.toString((endTime - startTime) / MILLISECONDS_IN_SECOND_CONSTANT)
                + TIME_DISPLAY_MILLISECONDS_CONSTANT);
    }

    private void parseEntryPoints(String inputApkFileName, Analysis analysis) {
        long startTime;
        long endTime;
        startTime = System.nanoTime();
        LOGGER.debug("Parsing entry points...");
        try {
            SourceSinkParser.parseEntryPoint(analysis);
        } catch (IOException e1) {
            LOGGER.error("Error: Can't read entry points file! " + inputApkFileName);
            System.exit(1);
        }
        endTime = System.nanoTime();
        LOGGER.debug("done in " + Long.toString((endTime - startTime) / MILLISECONDS_IN_SECOND_CONSTANT)
                + TIME_DISPLAY_MILLISECONDS_CONSTANT);
    }

    private FSEngine initializeHornDroid(String shortFilename, String fullPath) {
        hornDroidOptions.outputDirectory = fullPath + shortFilename;
        return new FSEngine(hornDroidOptions);
    }

    private DexBackedDexFile getDexBackedDexFile(File apkFile) {
        DexBackedDexFile dexFile = null;
        try {
            dexFile = DexFileFactory.loadDexFile(apkFile, hornDroidOptions.apiLevel, false);
            if (dexFile.isOdexFile()) {
                LOGGER.error("Error: Odex files are not supported");
            }
        } catch (IOException e) {
            LOGGER.error("Error: Loading dex file failed!");
            System.exit(1);
        }
        return dexFile;
    }

    private void getApkFilesInDir(File dir, Set<File> apkFiles) {
        File[] files = dir.listFiles();
        if (files != null) {
            for (File file : files) {
                if (file.isFile()) {
                    if (file.getName().endsWith(".apk")) {
                        apkFiles.add(file);
                    }
                } else if (file.isDirectory())
                    getApkFilesInDir(file.getAbsoluteFile(), apkFiles);
            }
        }
    }

    private Set<Integer> getAllowedClasses(){

        return new HashSet<Integer>();
    }

    private List<Report> processFiles(SourcesSinks sourcesSinks, LinkedHashSet<File> filesToProcess,
                                      final Set<Integer> allowed) {
        Stubs stubs = new Stubs(hornDroidOptions);
        List<Report> reports = new ArrayList<>();
        for (final File file : filesToProcess) {
            final String shortFilename = FilenameUtils.removeExtension(file.getName());
            final String fullPath = '/' + FilenameUtils.getPath(file.getPath());
            final String inputApkFileName = '/' + FilenameUtils.getPath(file.getPath()) + file.getName();
            final FSEngine fsengine = initializeHornDroid(shortFilename, fullPath);

            final ExecutorService instructionExecutorService = Executors.newCachedThreadPool();
            Analysis analysis = new Analysis(fsengine, sourcesSinks, hornDroidOptions, instructionExecutorService, stubs);
            LOGGER.info("Analysing " + file.getName());

            File apkFile = new File(inputApkFileName);
            confirmApkExistence(inputApkFileName, apkFile);
            DexBackedDexFile dexFile = getDexBackedDexFile(apkFile);
            parseEntryPoints(inputApkFileName,analysis);
            parseCallBacksAndDisabledActivities(file, inputApkFileName, analysis);
            List<? extends ClassDef> classDefs = sortClasses(dexFile);
            generateHornClauses(analysis, classDefs, allowed);
            awaitThreadTermination(instructionExecutorService);
            Report report = executeQueries(fsengine, analysis,file.getName());
            reports.add(report);

        }
        return reports;
    }

    /**
     * Executes the horndroid tool with the provided options and returns a report for each input apk
     *
     * @return List<Report> reports
     */
    public List<Report> execute() {
        final SourcesSinks sourcesSinks = getSourcesAndSinks();
        LinkedHashSet<File> filesToProcess = getFilesToProcess();
        final Set<Integer> allowed = getAllowedClasses();
        return processFiles(sourcesSinks, filesToProcess, allowed);
    }
}

