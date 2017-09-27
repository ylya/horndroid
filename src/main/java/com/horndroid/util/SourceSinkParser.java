/*
 * MIT License
 *
 * Copyright (c) 2017 TU Wien
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

package com.horndroid.util;

import com.horndroid.Main;
import com.horndroid.analysis.Analysis;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.*;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.regex.Pattern;

public class SourceSinkParser {

    private static final Logger LOGGER = LogManager.getLogger(SourceSinkParser.class);

    public static void parseSourceSink(File sourceSinkFile, final SourcesSinks sourcesSinks) throws IOException {
        try (BufferedReader br = new BufferedReader(new FileReader(sourceSinkFile))) {
            String line;
            String[] parts = null, parts2 = null;
            String className = null, methodName = null;
            while ((line = br.readLine()) != null) {
                if (line.length() < 1) continue;
                if (line.charAt(0) == '%') continue;
                parts = line.split(Pattern.quote("> -> _S"));
                parts2 = parts[0].split(Pattern.quote(": "));
                className = parts2[0].substring(1);
                methodName = parts2[1].split(" ")[1];

                if (parts[1].charAt(0) == 'O')
                    sourcesSinks.put(className.replaceAll("\\.", "/"), methodName.substring(0, methodName.indexOf('(')), true);
                else
                    sourcesSinks.put(className.replaceAll("\\.", "/"), methodName.substring(0, methodName.indexOf('(')), false);
            }
        }
    }

    public static void parseEntryPoint(final Analysis analysis) throws IOException {
        try (BufferedReader br = new BufferedReader(new FileReader(new File("bin/EntryPoints.txt")))) {
            String line;
            while ((line = br.readLine()) != null) {
                if (line.charAt(0) == '%') continue;
                String[] parts = line.split(Pattern.quote(" "));
                int c = parts[0].hashCode();
                int m = parts[1].hashCode();
                analysis.putEntryPoint(c, m);
            }
        }
    }

    public static void parseCallbacksFromXml(final Analysis analysis, final String outputDirectory,
                                             final String apkFileName, final String apktoolFolder) throws IOException,
            SAXException, ParserConfigurationException {
        final Set<String> callbacks = analysis.getCallbacks();
        final Set<Integer> disabledActivities = analysis.getDisabledActivities();
        final Set<Integer> activities = analysis.getActivities();
        final Set<Integer> launcherActivities = analysis.getLauncherActivities();
        final Set<Integer> callbackImplementations = analysis.getCallbackImplementations();
        final Set<Integer> applications = analysis.getApplications();
        LOGGER.info("Running apktool to obtain manifest xml and layout files");

        ProcessBuilder processBuilder = new ProcessBuilder("java", "-jar", apktoolFolder+"apktool.jar","d", apkFileName
                , "-s", "-f", "-o", outputDirectory+"/apktool");
        Process proc = processBuilder.start();
        try {
            LOGGER.info("Exit Code:"+ proc.waitFor());
        } catch (InterruptedException e) {
            LOGGER.error(e);
            throw new RuntimeException(e);
        }
        BufferedReader stdInput = new BufferedReader(new
                InputStreamReader(proc.getInputStream()));

        BufferedReader stdError = new BufferedReader(new
                InputStreamReader(proc.getErrorStream()));
        String s;


        while ((s = stdInput.readLine()) != null) {
            LOGGER.info("STDOUT:"+s);
        }
        if (stdError.readLine() != null)
            LOGGER.info("Here is the standard error of the command (if any):\n");
        while ((s = stdError.readLine()) != null) {
            LOGGER.info(s);
        }

        LinkedHashSet<File> filesToProcess = new LinkedHashSet<File>();
        getXmlFilesInDir(new File(outputDirectory + "/apktool/res"), filesToProcess);
        for (final File file : filesToProcess) {
            DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
            DocumentBuilder db = dbf.newDocumentBuilder();
            Document doc = db.parse(file);
            doc.getDocumentElement().normalize();
            NodeList nodeList = doc.getElementsByTagName("Button");
            if (nodeList != null && nodeList.getLength() > 0) {
                for (int j = 0; j < nodeList.getLength(); j++) {
                    Element el = (org.w3c.dom.Element) nodeList.item(j);
                    if (el.hasAttribute("android:onClick")) {
                        callbacks.add(el.getAttribute("android:onClick"));
                    }
                }
            }

        }

        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        dbf.setValidating(false);
        dbf.setNamespaceAware(true);
        DocumentBuilder db = dbf.newDocumentBuilder();
        db.setErrorHandler(new SimpleErrorHandler());
        Document doc = db.parse(new File(outputDirectory + "/apktool/AndroidManifest.xml"));
        doc.getDocumentElement().normalize();
        NodeList nodeList = doc.getElementsByTagName("activity");
        if (nodeList != null && nodeList.getLength() > 0) {
            for (int j = 0; j < nodeList.getLength(); j++) {
                Element el = (org.w3c.dom.Element) nodeList.item(j);
                if (el.hasAttribute("android:enabled") && (!Boolean.parseBoolean(el.getAttribute("android:enabled")))) {
                    String formatClassName = el.getAttribute("android:name").replaceAll("\\.", "/");
                    String[] parts = formatClassName.split("/");
                    String classN = parts[parts.length - 1];
                    disabledActivities.add(classN.hashCode());
                } else {
                    String formatClassName = el.getAttribute("android:name").replaceAll("\\.", "/");
                    String[] parts = formatClassName.split("/");
                    String classN = parts[parts.length - 1];
                    activities.add(classN.hashCode());
                    NodeList nodeList2 = doc.getElementsByTagName("category");
                    if (nodeList2 != null && nodeList2.getLength() > 0) {
                        for (int k = 0; k < nodeList2.getLength(); k++) {
                            Element el2 = (org.w3c.dom.Element) nodeList2.item(k);
                            if (el2.getAttribute("android:name").equals((String) "android.intent.category.LAUNCHER") ||
                                    (el2.getAttribute("android:name").equals((String) "android.intent.category.DEFAULT"))) {
                                Element el3 = (org.w3c.dom.Element) el2.getParentNode().getParentNode();
                                formatClassName = el3.getAttribute("android:name").replaceAll("\\.", "/");
                                parts = formatClassName.split("/");
                                classN = parts[parts.length - 1];
                                launcherActivities.add(classN.hashCode());
                            }
                        }
                    }
                    nodeList2 = el.getElementsByTagName("intent-filter");
                    if (nodeList2 != null && nodeList2.getLength() > 0) {
                        formatClassName = el.getAttribute("android:name").replaceAll("\\.", "/");
                        parts = formatClassName.split("/");
                        classN = parts[parts.length - 1];
                        launcherActivities.add(classN.hashCode());
                    }
                }
            }
        }

        nodeList = doc.getElementsByTagName("application");
        if (nodeList != null && nodeList.getLength() > 0) {
            for (int j = 0; j < nodeList.getLength(); j++) {
                Element el = (org.w3c.dom.Element) nodeList.item(j);
                String formatClassName = el.getAttribute("android:name").replaceAll("\\.", "/");
                String[] parts = formatClassName.split("/");
                String classN = parts[parts.length - 1];
                applications.add(classN.hashCode());
            }
        }

        try (BufferedReader br = new BufferedReader(new FileReader(new File("bin/Callbacks.txt")))) {
            String line;
            while ((line = br.readLine()) != null) {
                if (line.charAt(0) == '%') continue;
                String noWhiteSpaces = line.replaceAll(" ", "");
                String formatClassName = 'L' + noWhiteSpaces.replaceAll("\\.", "/") + ';';
                callbackImplementations.add(formatClassName.hashCode());
            }
        }
    }

    private static void getXmlFilesInDir(File dir, Set<File> xmlFiles) {
        File[] files = dir.listFiles();
        if (files != null) {
            for (File file : files) {
                if (file.isFile()) {
                    if (file.getName().endsWith(".xml")) {
                        xmlFiles.add(file);
                    }
                } else if (file.isDirectory())
                    getXmlFilesInDir(file.getAbsoluteFile(), xmlFiles);
            }
        }
    }
}