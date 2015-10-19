
package util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.regex.Pattern;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import analysis.Analysis;
import z3.Z3Engine;

public class SourceSinkParser {
	
	public static void parseSourceSink(File sourceSinkFile, final Set<SourceSinkMethod> sourcesSinks) throws IOException{
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
		    		sourcesSinks.add(new SourceSinkMethod(methodName.substring(0, methodName.indexOf('(')), className.replaceAll("\\.", "/"), true));
		    	else
		    		sourcesSinks.add(new SourceSinkMethod(methodName.substring(0, methodName.indexOf('(')), className.replaceAll("\\.", "/"), false));
		    }
		}
	}
	public static void parseEntryPoint(final Z3Engine z3engine) throws IOException{
		try (BufferedReader br = new BufferedReader(new FileReader(new File("EntryPoints.txt")))) {
		    String line;
		    while ((line = br.readLine()) != null) {
		    	if (line.charAt(0) == '%') continue;
		    	String[] parts = line.split(Pattern.quote(" "));
		    	int c = parts[0].hashCode();
		    	int m = parts[1].hashCode();
                z3engine.putEntryPoint(c, m);
		    }
		}
	}
	
	public static void parseCallbacksFromXml(final Analysis analysis, final String outputDirectory, final String apkFileName, final String apktoolFolder) throws IOException, SAXException, ParserConfigurationException{
		 final Set<String> callbacks = analysis.getCallbacks();
		 final Set<Integer> disabledActivities = analysis.getDisabledActivities();
		 final Set<Integer> activities = analysis.getActivities();
		 final Set<Integer> launcherActivities = analysis.getLauncherActivities();
		 final Set<Integer> callbackImplementations = analysis.getCallbackImplementations();
		 final Set<Integer> applications = analysis.getApplications();
		 System.out.println("Running apktool to obtain manifest xml and layout files");
	     Runtime runtime = Runtime.getRuntime();
		 Process proc = runtime.exec(new String[]{"java -jar " + apktoolFolder + "apktool.jar d " + apkFileName + " -s -f -o " + outputDirectory + "/apktool"});
//        Process proc = runtime.exec("java -jar C:\\Users\\rtongchenchitt\\Desktop\\hiwi\\horndroid-new-copy\\lib\\apktool.jar d " + apkFileName + " -s -f -o " + outputDirectory + File.separator + "apktool");

        BufferedReader stdInput = new BufferedReader(new
	     InputStreamReader(proc.getInputStream()));

	     BufferedReader stdError = new BufferedReader(new 
	             InputStreamReader(proc.getErrorStream()));
	        String s = null;
	        while ((s = stdInput.readLine()) != null) {
	            System.out.println(s);
	     }
	     if (stdError.readLine() != null)
	        	System.out.println("Here is the standard error of the command (if any):\n");
	        while ((s = stdError.readLine()) != null) {
	            System.out.println(s);
	     }
	     proc.destroy();
	     LinkedHashSet<File> filesToProcess = new LinkedHashSet<File>();
	     getXmlFilesInDir(new File (outputDirectory + "/apktool/res"), filesToProcess);
	     for (final File file: filesToProcess) {
	    	 DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
	    	 DocumentBuilder db = dbf.newDocumentBuilder();
	    	 Document doc = db.parse(file);
	    	 doc.getDocumentElement().normalize();
	    	 NodeList nodeList = doc.getElementsByTagName("Button");
	    	 if(nodeList != null && nodeList.getLength() > 0){
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
    	 if(nodeList != null && nodeList.getLength() > 0){
    	     for (int j = 0; j < nodeList.getLength(); j++) {
    	         Element el = (org.w3c.dom.Element) nodeList.item(j);
    	         if (el.hasAttribute("android:enabled") && (!Boolean.parseBoolean(el.getAttribute("android:enabled")))) {
    	        	 String formatClassName = el.getAttribute("android:name").replaceAll("\\.", "/");
    	        	 String[] parts = formatClassName.split("/");
    	    		 String classN =  parts[parts.length - 1];
    	        	 disabledActivities.add(classN.hashCode());
    	         }
    	         else{
    	        	 String formatClassName = el.getAttribute("android:name").replaceAll("\\.", "/");
    	        	 String[] parts = formatClassName.split("/");
    	    		 String classN =  parts[parts.length - 1];
    	        	 activities.add(classN.hashCode());
    	        	 NodeList nodeList2 = doc.getElementsByTagName("category");
    	        	 if(nodeList2 != null && nodeList2.getLength() > 0){
    	        	     for (int k = 0; k < nodeList2.getLength(); k++) {
    	        	    	 Element el2 = (org.w3c.dom.Element) nodeList2.item(k);
    	        	    	 if (el2.getAttribute("android:name").equals((String) "android.intent.category.LAUNCHER") ||
    	        	    			 (el2.getAttribute("android:name").equals((String) "android.intent.category.DEFAULT")))
    	        	    	 {
    	        	    		 Element el3 = (org.w3c.dom.Element) el2.getParentNode().getParentNode();
    	        	    		 formatClassName = el3.getAttribute("android:name").replaceAll("\\.", "/");
    	        	    		 parts = formatClassName.split("/");
    	        	    		 classN =  parts[parts.length - 1];
    	        	    		 launcherActivities.add(classN.hashCode());
    	        	    	 }
    	        	     }
    	        	 }
    	        	 nodeList2 = el.getElementsByTagName("intent-filter");
    	        	 if(nodeList2 != null && nodeList2.getLength() > 0){
    	        	    formatClassName = el.getAttribute("android:name").replaceAll("\\.", "/");
    	        	    parts = formatClassName.split("/");
    	        	    classN =  parts[parts.length - 1];
    	        	    launcherActivities.add(classN.hashCode());
    	        	 }
    	         }
    	     }
    	 }
    	 
    	 nodeList = doc.getElementsByTagName("application");
    	 if(nodeList != null && nodeList.getLength() > 0){
    	     for (int j = 0; j < nodeList.getLength(); j++) {
    	    	 Element el = (org.w3c.dom.Element) nodeList.item(j);
    	    	 String formatClassName = el.getAttribute("android:name").replaceAll("\\.", "/");
	        	 String[] parts = formatClassName.split("/");
	    		 String classN =  parts[parts.length - 1];
	        	 applications.add(classN.hashCode());
    	     }
    	 }
	     
    	 try (BufferedReader br = new BufferedReader(new FileReader(new File("Callbacks.txt")))) {
 		    String line;
 		    while ((line = br.readLine()) != null) {
 		    	if (line.charAt(0) == '%') continue;
 		    	String noWhiteSpaces = 	line.replaceAll(" ", "");
 		    	String formatClassName = 'L' + noWhiteSpaces .replaceAll("\\.", "/") + ';';
 		    	callbackImplementations.add(formatClassName.hashCode());
 		    }
 		}
	}
	
	private static void getXmlFilesInDir(File dir, Set<File> xmlFiles) {
        File[] files = dir.listFiles();
        if (files != null) {
            for(File file: files) {
                if (file.isFile()) {
                   if (file.getName().endsWith(".xml")) {
                    xmlFiles.add(file);
                   }
                }
                   else if (file.isDirectory())
                	   getXmlFilesInDir(file.getAbsoluteFile(), xmlFiles);
            }
        }
    }
}