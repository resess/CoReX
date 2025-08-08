package resess;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Stack;

import org.apache.commons.io.FileUtils;
import org.apache.poi.ss.usermodel.Row;
import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;

import tregression.empiricalstudy.Defects4jProjectConfig;
import tregression.empiricalstudy.TestCase;

public class projConfig extends Defects4jProjectConfig{
	public String srcTestFolder;
	public String srcSourceFolder;
	public String bytecodeTestFolder;
	public String bytecodeSourceFolder;
	public String buildFolder;
	
	public List<String> additionalSourceFolder = new ArrayList<>();
	
	public String projectName;
	public int bugID;
	public String configFile;
	public int assertionLine;
	
	public String rootPath = ""+File.separator+"home"+File.separator+"linyun"+File.separator+"doc"+File.separator+"git_space"+File.separator+"defects4j"+File.separator+"framework"+File.separator+"bin"+File.separator+"defects4j";
	//public String javaHome = Activator.getDefault().getPreferenceStore().getString(MicrobatPreference.JAVA7HOME_PATH);
	public String javaHome = System.getProperty("java.home");
	private projConfig(String srcTestFolder, String srcSourceFolder, String bytecodeTestFolder,
			String bytecodeSourceFolder, String buildFolder, String projectName, int bugID) {
		super(srcTestFolder,srcSourceFolder,bytecodeTestFolder,bytecodeSourceFolder,buildFolder,projectName,bugID);
		this.configFile = "E";
		this.assertionLine = 0;
	}
	public static projConfig getConfig(String baseProjPath, String projectName, int bugID, String ereasOrSlicer) throws IOException, InterruptedException {
		projConfig config = null;
	    String proPath = baseProjPath + projectName + "/" + bugID;
		String buggyPath = proPath + "/bug/";
		String fixPath = proPath + "/fix/";
		////////////////////////////////////////////////////////////////
		if (projectName.equals("InPreSS")) {
			if(bugID==1){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = "E";
				config.assertionLine = 176;
//				config.assertionLine = getAssertionLine(baseProjPath, "target"+File.separator+"test-classes", "target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
//				config.configFile = "S";
//				if(config.configFile.contentEquals("S"))
//					getSlice(baseProjPath, "target"+File.separator+"test-classes", "target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else if(bugID==2){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
//				config.configFile = "E";
				config.configFile = "S";
				config.assertionLine = 86;
//				if(config.configFile.contentEquals("S"))
//					getSlice(baseProjPath, "target"+File.separator+"test-classes", "target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else if(bugID==3){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
//				config.configFile = "E";
				config.configFile = "S";
//				if(config.configFile.contentEquals("S"))
//					getSlice(baseProjPath, "target"+File.separator+"test-classes", "target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else if(bugID==4){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
//				config.configFile = "E";
				config.configFile = "S";
				config.assertionLine = 69;
//				if(config.configFile.contentEquals("S"))
//					getSlice(baseProjPath, "target"+File.separator+"test-classes", "target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else if(bugID==5){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = "E";
//				config.configFile = "S";
				config.assertionLine = 79;
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath, "target"+File.separator+"test-classes", "target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else if(bugID==6){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
//				config.configFile = "E";
				config.configFile = "S";
//				if(config.configFile.contentEquals("S"))
//					getSlice(baseProjPath, "target"+File.separator+"test-classes", "target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else if(bugID==7){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
//				config.configFile = "E";
				config.configFile = "S";
				config.assertionLine = 914;
//				if(config.configFile.contentEquals("S"))
//					getSlice(baseProjPath, "target"+File.separator+"test-classes", "target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else if(bugID==8){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
//				config.configFile = "E";
				config.configFile = "S";
//				if(config.configFile.contentEquals("S"))
//					getSlice(baseProjPath, "target"+File.separator+"test-classes", "target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else if(bugID==9){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = "S";
			}
		}
		if (projectName.equals("Toy")) {
			if(bugID<21){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = ereasOrSlicer;
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath, "target"+File.separator+"test-classes", "target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}			
		}
		////////////////////////////////////////////////////////////////
		
		else if(projectName.equals("Chart")) {
            Path newPath = Paths.get(buggyPath+"build");
            Path oldPath = Paths.get(fixPath+"build");
            Path newPathT = Paths.get(buggyPath+"build-tests");
            Path oldPathT = Paths.get(fixPath+"build-tests");
//			if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
			if(!Files.exists(newPath) || !Files.exists(newPathT)) {
				saveBugAndTerminate(baseProjPath,projectName, bugID);
				System.exit(0);
			}	
			config = new projConfig("tests", "source", "build-tests", "build", "build", projectName, bugID);
			config.configFile = ereasOrSlicer;
			config.assertionLine = getAssertionLine(baseProjPath, "build-tests", "build", projectName, bugID,"lib");
			if(config.configFile.contentEquals("S"))
				getSlice(baseProjPath, "build-tests", "build", projectName, bugID,"lib");
		}
		
		else if (projectName.equals("Closure")) {
            Path newPath = Paths.get(buggyPath+"build");
            Path oldPath = Paths.get(fixPath+"build");
//			if(!Files.exists(newPath) || !Files.exists(oldPath)) {
            if(!Files.exists(newPath)) {
				saveBugAndTerminate(baseProjPath,projectName, bugID);
				System.exit(0);
			}			
			config = new projConfig("test", "src", "build"+File.separator+"test", "build"+File.separator+"classes", "build", projectName, bugID);
			config.configFile = ereasOrSlicer;
			
            Path path = Paths.get(buggyPath + "build/lib")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "build/lib");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}			
				source = new File(fixPath + "build/lib");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			config.assertionLine = getAssertionLine(baseProjPath, "build"+File.separator+"test","build"+File.separator+"classes", projectName, bugID,"lib");
			if(config.configFile.contentEquals("S"))
				getSlice(baseProjPath, "build"+File.separator+"test","build"+File.separator+"classes", projectName, bugID,"lib");
		}
			
		else if (projectName.equals("Lang")) {
			if(bugID<21){
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"tests");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"tests");
//				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
				if(!Files.exists(newPath) || !Files.exists(newPathT)) {
						
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}					
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"tests", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = ereasOrSlicer;
				config.assertionLine = getAssertionLine(baseProjPath,  "target"+File.separator+"tests","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"tests","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			   
			}
			else if(bugID>=36 && bugID<=41){
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"test-classes");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"test-classes");
//				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
	            if(!Files.exists(newPath) || !Files.exists(newPathT)) {					
	            	saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test", "src"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);				
				config.configFile = ereasOrSlicer;
				config.assertionLine = getAssertionLine(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else if(bugID<42){
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"test-classes");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"test-classes");
//				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
	            if(!Files.exists(newPath) || !Files.exists(newPathT)) {						
	            	saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);				
				config.configFile = ereasOrSlicer;
				config.assertionLine = getAssertionLine(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else{
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"tests");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"tests");
//				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
				if(!Files.exists(newPath) || !Files.exists(newPathT)) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test", "src"+File.separator+"java", "target"+File.separator+"tests", "target"+File.separator+"classes", "target", projectName, bugID);				
				config.configFile = ereasOrSlicer;
				config.assertionLine = getAssertionLine(baseProjPath,  "target"+File.separator+"tests","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"tests","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			
//			if(bugID>=36 && bugID<=41){
//				config.srcSourceFolder = "src"+File.separator+"java";
//				config.srcTestFolder = "src"+File.separator+"test";
//			}
		}
		
		else if (projectName.equals("Math")) {
			if(bugID<85){
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"test-classes");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"test-classes");
//				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
					if(!Files.exists(newPath) || !Files.exists(newPathT)) {
						
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);	
				config.configFile = ereasOrSlicer;
//				config.assertionLine = getAssertionLine(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else{
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"test-classes");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"test-classes");
//				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
				if(!Files.exists(newPath) || !Files.exists(newPathT) ) {						
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test", "src"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);
				config.configFile = ereasOrSlicer;
				config.assertionLine = getAssertionLine(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
		}
		else if (projectName.equals("Mockito")) {
			Path path = Paths.get(buggyPath + "build/lib")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "build/lib");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "build/lib");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			path = Paths.get(buggyPath + "lib/build")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "lib/build");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "lib/build");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			path = Paths.get(buggyPath + "compileLib")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "compileLib");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "compileLib");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			path = Paths.get(buggyPath + "lib/repackaged")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "lib/repackaged");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "lib/repackaged");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			path = Paths.get(buggyPath + "lib/sources")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "lib/sources");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "lib/sources");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
		    path = Paths.get(buggyPath + "lib/test")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "lib/test");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "lib/test");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			path = Paths.get(buggyPath + "lib/compile")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "lib/compile");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "lib/compile");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			path = Paths.get(buggyPath + "lib/run")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "lib/run");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "lib/run");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			if(bugID<12 || bugID==20 || bugID==21 || bugID==18 || bugID==19){
				Path newPath = Paths.get(buggyPath+"build"+File.separator+"classes"+File.separator+"main");
	            Path oldPath = Paths.get(fixPath+"build"+File.separator+"classes"+File.separator+"main");
	            Path newPathT = Paths.get(buggyPath+"build"+File.separator+"classes"+File.separator+"test");
	            Path oldPathT = Paths.get(fixPath+"build"+File.separator+"classes"+File.separator+"test");
//				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
				if(!Files.exists(newPath) || !Files.exists(newPathT) ) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				
				config = new projConfig("test", "src", "build"+File.separator+"classes"+File.separator+"test", "build"+File.separator+"classes"+File.separator+"main", "build", projectName, bugID);	
				config.configFile = ereasOrSlicer;
				config.assertionLine = getAssertionLine(baseProjPath, "build"+File.separator+"classes"+File.separator+"test","build"+File.separator+"classes"+File.separator+"main", projectName, bugID,"lib");
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath, "build"+File.separator+"classes"+File.separator+"test","build"+File.separator+"classes"+File.separator+"main", projectName, bugID,"lib");
			}
			else{
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"test-classes");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"test-classes");
//				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
				if(!Files.exists(newPath) || !Files.exists(newPathT) ) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("test", "src", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);
				config.configFile = ereasOrSlicer;
				config.assertionLine = getAssertionLine(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"lib");
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"lib");
			}
			
			List<String> addSrcList = new ArrayList<>();
			addSrcList.add("mockmaker" + File.separator + "bytebuddy"+ File.separator + "main" + File.separator + "java");
			addSrcList.add("mockmaker" + File.separator + "bytebuddy"+ File.separator + "test" + File.separator + "java");
			addSrcList.add("mockmaker" + File.separator + "cglib"+ File.separator + "main" + File.separator + "java");
			addSrcList.add("mockmaker" + File.separator + "cglib"+ File.separator + "test" + File.separator + "java");
			config.additionalSourceFolder = addSrcList;
		}
		else if (projectName.equals("Time")) {
			if(bugID<12){
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"test-classes");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"test-classes");
//				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
				if(!Files.exists(newPath) || !Files.exists(newPathT) ) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);				
				config.configFile = ereasOrSlicer;
				config.assertionLine = getAssertionLine(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else{
				Path newPath = Paths.get(buggyPath+"build"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"build"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"build"+File.separator+"tests");
	            Path oldPathT = Paths.get(fixPath+"build"+File.separator+"tests");
//				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
				if(!Files.exists(newPath) || !Files.exists(newPathT) ) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "build"+File.separator+"tests", "build"+File.separator+"classes", "build", projectName, bugID);
				config.configFile = ereasOrSlicer;
				config.assertionLine = getAssertionLine(baseProjPath,  "build"+File.separator+"tests","build"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "build"+File.separator+"tests","build"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
		}
		
		return config;
	}
private static int getAssertionLine(String baseProj, String testFolder, String classFolder, String projectName, int bugID, String depPath) throws IOException, InterruptedException {
    String proPath = baseProj + projectName + "/" + bugID;
	String buggyPath = proPath + "/bug/";
	String failingFile = buggyPath  + "failing_tests";
	Path path1 = Paths.get(failingFile);
	File file = new File(path1.toAbsolutePath().toString());
	BufferedReader reader = new BufferedReader(new FileReader(file));
	String testClass = "";
	String testMethod = "";
	String sliceLine = "";	
	String sliceClass = "";
	String line = null;
	int testCounter = 0;
	boolean junitFound = false;
	while ((line = reader.readLine()) != null) {
		if (line.startsWith("---")) {
			if(testCounter==0) {
			 testCounter++;
			 testClass = line.substring(line.indexOf(" ") + 1, line.indexOf("::"));
			 testMethod = line.substring(line.indexOf("::") + 2, line.length());
			}
			else {
				break;
			}
			 
		}
		else {
//			if (line.contains(testClass) && line.contains(testMethod)) {
//				found = true;
//				String temp = (line.split(":")[1]);
////				System.out.println(temp);
////				if (temp.contains(")"))
////					System.out.println(temp.indexOf(")"));
//				sliceLine = temp.substring(0, temp.indexOf(")"));
////				System.out.println(sliceLine);
//				break;
//			}	
			if (line.contains("at ")){
				if (line.contains("at junit."))
					junitFound = true;	
				else {
					if (line.contains("com.squareup")||line.contains("com.actiontech")||
							line.contains("com.fasterxml.jackson")||line.contains("org.openapitools")||
							line.contains("com.intuit.wasabi")||line.contains("com.fizzed")||
							line.contains("dagger.")||line.contains("com.thoughtworks")||
							line.contains("at org.jfree") || line.contains("at com.google.javascript") || line.contains("at org.apache.commons")|| 
							line.contains("at org.mockito") || line.contains("at com.google.debugging") || line.contains("at org.joda.time")|| line.contains("at com.hanan")) {
						if(line.contains(":")) {								
							String temp = (line.split(":")[1]);
//							System.out.println(temp);
//							if (temp.contains(")"))
//								System.out.println(temp.indexOf(")"));
//							System.out.println(line.substring(0, line.indexOf("(")));
							String temp2 = line.substring(0, line.indexOf("(")).split("at ")[1];
							sliceClass = temp2.substring(0, temp2.lastIndexOf("."));
							if (sliceClass.contains("$")) {
								String sclass = sliceClass.substring(0,sliceClass.lastIndexOf("$"));
								sliceClass=sclass;
							}
							sliceLine = temp.substring(0, temp.indexOf(")"));
							System.out.println(sliceClass+":"+sliceLine);
							break;
						}
					}
				}						
			}
		}					
	}
	reader.close();
	if(!sliceLine.equals(""))
		return Integer.valueOf(sliceLine);
	return 0;
	
	}
private static void saveBugAndTerminate(String baseProjPath, String projectName2, int bugID2) {
	String results = baseProjPath+"/results/"+projectName2+"NoBuild.xlsx";
    File tempFile = new File(results);
    boolean FirstTime = false;
    /////////////////#######////#######////#######////#######////#######////#######
    /////////////////#######////#######////#######////#######////#######////#######
    /////////////////#######////#######////#######////#######////#######////#######
    /////////////////#######////#######////#######////#######////#######////#######	
	if (!tempFile.exists()) {
        FirstTime=true;
        XSSFWorkbook workbook = new XSSFWorkbook();
        XSSFSheet sheet = workbook.createSheet("stats");
        try {
        	FileOutputStream outputStream = new FileOutputStream(results);
            workbook.write(outputStream);
            workbook.close();
        	outputStream.close();
        } catch (Exception e) {
        }
    }		

    if (FirstTime) {		    	
        String[] header = {"Bug ID"};
        WriteToExcel(results, header, "stats",false, true);
    }
    String[] data = {String.valueOf(bugID2)};
    WriteToExcel(results,data,"stats",false, false);	
		
	}
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
public static void WriteToExcel(String ExcelFilePath, String[] RowData, String sheetName,boolean existing,boolean firstTime){
    try {
  
    	    FileInputStream myxls = new FileInputStream(ExcelFilePath);
            XSSFWorkbook ExcelWorkbook = new XSSFWorkbook(myxls);
            XSSFSheet worksheet;
   
            if (existing) {
            	if (firstTime)
            		worksheet = ExcelWorkbook.createSheet(sheetName);
            	else 
            		worksheet = ExcelWorkbook.getSheet(sheetName);	            		            	
            }
            else {
//            XSSFSheet worksheet = ExcelWorkbook.getSheetAt(id);
            	 worksheet = ExcelWorkbook.getSheet(sheetName);
            }
            int lastRow=worksheet.getLastRowNum();          
            if(!firstTime)
            	lastRow++;
            Row row = worksheet.createRow(lastRow);
            for (int index = 0; index < RowData.length; index++) {
                row.createCell(index).setCellValue(RowData[index]);
            }
            
            myxls.close();

            try {
            	FileOutputStream output_file =new FileOutputStream(new File(ExcelFilePath));
                ExcelWorkbook.write(output_file);
                output_file.close();
                ExcelWorkbook.close();
            }
            catch(Exception e){}
    }
    catch(Exception e){
    }
}
	////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
	private static void getSlice(String baseProj, String testFolder, String classFolder, String projectName, int bugID, String depPath) throws IOException, InterruptedException {
			
//	        String slicerFullPath = System.getProperty("user.dir")+"/deps/Slicer4J/scripts/slicer4j.py";
		    String slicerFullPath = "/Users/sahar1/Documents/Github/InPreSS/InPreSS/deps/Slicer4J/scripts/slicer4j.py";
		    String slicerOnlyPath = "/Users/sahar1/Documents/Github/InPreSS/InPreSS/deps/Slicer4J/scripts/slicer4jGetSlice.py";
			
//		    String slicerFullPath = "/data/shrbadihi/projects/client_library/libre/JarNewSlicer4J/deps/Slicer4J/scripts/slicer4j.py";//thanos
//		    String slicerOnlyPath = "/data/shrbadihi/projects/client_library/libre/JarNewSlicer4J/deps/Slicer4J/scripts/slicer4jGetSlice.py";
        /////////// /////////// /////////// /////////// /////////// /////////// ///////////
			/////////// /////////// /////////// /////////// /////////// /////////// ///////////
		    String proPath = baseProj + projectName + "/" + bugID;
			String buggyPath = proPath + "/bug/";
			String fixPath = proPath + "/fix/";
			Path path = Paths.get(proPath+"/results");		
			if(!Files.exists(path)) {
				new File(proPath+"/results").mkdirs();
				new File(proPath+"/results/new").mkdirs();
				new File(proPath+"/results/old").mkdirs();				

			}
			new File(proPath+"/results/old/Slicer4JResults").mkdirs();
			new File(proPath+"/results/new/Slicer4JResults").mkdirs();
			
	        String failingFile = buggyPath  + "failing_tests";
			File file = new File(failingFile);
			BufferedReader reader = new BufferedReader(new FileReader(file));
			String testClass = "";
			String testMethod = "";
			String sliceLine = "";	
			String sliceClass = "";
			String line = null;
			int testCounter = 0;
			boolean junitFound = false;
			while ((line = reader.readLine()) != null) {
				if (line.startsWith("---")) {
					if(testCounter==0) {
					 testCounter++;
					 testClass = line.substring(line.indexOf(" ") + 1, line.indexOf("::"));
					 testMethod = line.substring(line.indexOf("::") + 2, line.length());
					}
					else {
						break;
					}
					 
				}
				else {
//					if (line.contains(testClass) && line.contains(testMethod)) {
//						found = true;
//						String temp = (line.split(":")[1]);
////						System.out.println(temp);
////						if (temp.contains(")"))
////							System.out.println(temp.indexOf(")"));
//						sliceLine = temp.substring(0, temp.indexOf(")"));
////						System.out.println(sliceLine);
//						break;
//					}	
					if (line.contains("at ")){
						if (line.contains("at junit."))
							junitFound = true;	
						else {
							if (line.contains("com.squareup")||line.contains("com.actiontech")||
									line.contains("com.fasterxml.jackson")||line.contains("org.openapitools")||
									line.contains("com.intuit.wasabi")||line.contains("com.fizzed")||
									line.contains("dagger.")||line.contains("com.thoughtworks")||
									line.contains("at org.jfree") || line.contains("at com.google.javascript") || line.contains("at org.apache.commons")|| 
									line.contains("at org.mockito") || line.contains("at com.google.debugging") || line.contains("at org.joda.time")|| line.contains("at com.hanan")) {
								if(line.contains(":")) {								
									String temp = (line.split(":")[1]);
		//							System.out.println(temp);
		//							if (temp.contains(")"))
		//								System.out.println(temp.indexOf(")"));
		//							System.out.println(line.substring(0, line.indexOf("(")));
									String temp2 = line.substring(0, line.indexOf("(")).split("at ")[1];
									sliceClass = temp2.substring(0, temp2.lastIndexOf("."));
									if (sliceClass.contains("$")) {
										String sclass = sliceClass.substring(0,sliceClass.lastIndexOf("$"));
										sliceClass=sclass;
									}
									sliceLine = temp.substring(0, temp.indexOf(")"));
									System.out.println(sliceClass+":"+sliceLine);
									break;
								}
							}
						}						
					}
				}					
			}
			reader.close();
//			if (!found) {
//				file = new File(failingFile);
//				 reader = new BufferedReader(new FileReader(file));
//				 testClass = "";
//				 testMethod = "";
//				 sliceLine = "";	
//				 line = null;
//				 testCounter = 0;
//				 found = false;
//				while ((line = reader.readLine()) != null) {
//					if (line.startsWith("---")) {
//						if(testCounter==0) {
//						 testCounter++;
//						 testClass = line.substring(line.indexOf(" ") + 1, line.indexOf("::"));
//						 testMethod = line.substring(line.indexOf("::") + 2, line.length());
//						}
//						else {
//							break;
//						}
//						 
//					}
//					else {
//						if (line.contains(testMethod)) {
//							found = true;
//							String temp = (line.split(":")[1]);
////							System.out.println(temp);
////							if (temp.contains(")"))
////								System.out.println(temp.indexOf(")"));
////							System.out.println(line.substring(0, line.indexOf("(")));
//							String temp2 = line.substring(0, line.indexOf("(")).split("at ")[1];
//							 testClass = temp2.substring(0, temp2.lastIndexOf("."));
//							sliceLine = temp.substring(0, temp.indexOf(")"));
////							System.out.println(sliceLine);
//							break;
//						}						    
//					}					
//				}
//				
//			}
	        /////////// /////////// /////////// /////////// /////////// /////////// ///////////
			/////////// /////////// /////////// /////////// /////////// /////////// ///////////
			long slice_start = System.currentTimeMillis();								
//		    Path Slicer4JResultsPath = Paths.get(proPath+"/results/new/Slicer4JResults");
	        Path instrumentedJar = Paths.get(proPath+"/results/new/Slicer4JResults/program_i.jar");
			if(!Files.exists(instrumentedJar)) {
				//1. copy the test classes
				File source = new File(buggyPath + testFolder);
				File dest = new File(buggyPath + classFolder);
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
//		        String cmd = "cp -R " + buggyPath + testFolder + "/* " + buggyPath + classFolder + "/";	  
//		        System.out.println(cmd);
//				Process p1 = Runtime.getRuntime().exec(cmd);
//				BufferedReader in = new BufferedReader(new InputStreamReader(p1.getInputStream()));
//				BufferedReader err = new BufferedReader(new InputStreamReader(p1.getErrorStream()));
//				String line1 = null;
//				String answer = in.readLine();
//				if(answer == null){
//					String error = err.readLine();
//					if (error != null)
//						System.out.println(error);
//				}
//				else 
//					while ((line1 = in.readLine()) != null) {
//						System.out.println(line1);
//					}	
//				in.close();
//				err.close();
//				p1.waitFor();
  
//				//2. create a jar 
				String cmd = "jar cvf " + proPath + "/results/new/program.jar" + " -C " + buggyPath + classFolder + " .";
				Process p1 = Runtime.getRuntime().exec(cmd);
				BufferedReader in = new BufferedReader(new InputStreamReader(p1.getInputStream()));
				BufferedReader err = new BufferedReader(new InputStreamReader(p1.getErrorStream()));
				String line1 = null;
				String answer = in.readLine();
				if(answer == null){
					String error = err.readLine();
					if (error != null)
						System.out.println(error);
				}
//				else 
//					while ((line1 = in.readLine()) != null) {
//						System.out.println(line1);
//					}				
				in.close();
				err.close();
				int c = p1.waitFor();
//				System.out.println("Process exitValue: " + c);
				System.out.println("Finish creating jar");
	        
//		        //3. slice 
		        String cmd2 = "python3 " + slicerFullPath +" -j " + proPath + "/results/new/program.jar" + " -o " + proPath + "/results/new/Slicer4JResults"+" -b " + sliceClass + ":" + sliceLine + " -tc " + testClass + " -tm " + testMethod + " -dep " + buggyPath + depPath;
		        System.out.println(cmd2);
       
	            String[] commads = {"python3", slicerFullPath, "-j", proPath + "/results/new/program.jar","-o",proPath + "/results/new/Slicer4JResults","-b",sliceClass + ":" + sliceLine,"-tc",testClass,"-tm",testMethod,"-dep", buggyPath + depPath};
				
	            Process p = new ProcessBuilder(commads)
	                    .redirectErrorStream(true)
	                    .start();
	            BufferedReader in2 = new BufferedReader(new InputStreamReader(p.getInputStream()));
	            BufferedReader err2 = new BufferedReader(new InputStreamReader(p.getErrorStream()));
				String line2 = null;
				String answer2 = in2.readLine();
				if(answer2 == null){
					String error = err2.readLine();
					if (error != null)
						System.out.println(error);
				}
				else 
					while ((line2 = in2.readLine()) != null) {
						System.out.println(line2);
					}				
				in2.close();
				err2.close();
				int rc = p.waitFor();
//				System.out.println("Process exitValue: " + rc);
				System.out.println("Finish creating slice");
//		        
			}
			long slice_finish = System.currentTimeMillis();					
			long traceTime = (int) (slice_finish - slice_start);
			
	        /////////// /////////// /////////// /////////// /////////// /////////// ///////////
			/////////// /////////// /////////// /////////// /////////// /////////// ///////////
//		    Path Slicer4JResultsPath = Paths.get(proPath+"/results/new/Slicer4JResults");
	        instrumentedJar = Paths.get(proPath+"/results/old/Slicer4JResults/program_i.jar");
			if(!Files.exists(instrumentedJar)) {
				//1. copy the test classes
				File source = new File(fixPath + testFolder);
				File dest = new File(fixPath + classFolder);
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
//		        String cmd = "cp -R " + buggyPath + testFolder + "/* " + buggyPath + classFolder + "/";	  
//		        System.out.println(cmd);
//				Process p1 = Runtime.getRuntime().exec(cmd);
//				BufferedReader in = new BufferedReader(new InputStreamReader(p1.getInputStream()));
//				BufferedReader err = new BufferedReader(new InputStreamReader(p1.getErrorStream()));
//				String line1 = null;
//				String answer = in.readLine();
//				if(answer == null){
//					String error = err.readLine();
//					if (error != null)
//						System.out.println(error);
//				}
//				else 
//					while ((line1 = in.readLine()) != null) {
//						System.out.println(line1);
//					}	
//				in.close();
//				err.close();
//				p1.waitFor();
  
//				//2. create a jar 
				String cmd = "jar cvf " + proPath + "/results/old/program.jar" + " -C " + fixPath + classFolder + " .";
				Process p1 = Runtime.getRuntime().exec(cmd);
				BufferedReader in = new BufferedReader(new InputStreamReader(p1.getInputStream()));
				BufferedReader err = new BufferedReader(new InputStreamReader(p1.getErrorStream()));
				String line1 = null;
				String answer = in.readLine();
				if(answer == null){
					String error = err.readLine();
					if (error != null)
						System.out.println(error);
				}
//				else 
//					while ((line1 = in.readLine()) != null) {
//						System.out.println(line1);
//					}				
				in.close();
				err.close();
				int c = p1.waitFor();
//				System.out.println("Process exitValue: " + c);
				System.out.println("Finish creating jar");
	        
//		        //3. slice 
		        String cmd2 = "python3 " + slicerFullPath +" -j " + proPath + "/results/old/program.jar" + " -o " + proPath + "/results/old/Slicer4JResults"+" -b " + sliceClass + ":" + sliceLine + " -tc " + testClass + " -tm " + testMethod + " -dep " + fixPath + depPath;
		        System.out.println(cmd2);
       
	            String[] commads = {"python3", slicerFullPath, "-j", proPath + "/results/old/program.jar","-o",proPath + "/results/old/Slicer4JResults","-b",sliceClass + ":" + sliceLine,"-tc",testClass,"-tm",testMethod,"-dep", fixPath + depPath};
				
	            Process p = new ProcessBuilder(commads)
	                    .redirectErrorStream(true)
	                    .start();
	            BufferedReader in2 = new BufferedReader(new InputStreamReader(p.getInputStream()));
	            BufferedReader err2 = new BufferedReader(new InputStreamReader(p.getErrorStream()));
				String line2 = null;
				String answer2 = in2.readLine();
				if(answer2 == null){
					String error = err2.readLine();
					if (error != null)
						System.out.println(error);
				}
				else 
					while ((line2 = in2.readLine()) != null) {
						System.out.println(line2);
					}				
				in2.close();
				err2.close();
				int rc = p.waitFor();
//				System.out.println("Process exitValue: " + rc);
				System.out.println("Finish creating slice");
//		        
			}
			
//			############################################################
	        Path rawSlice = Paths.get(proPath+"/results/old/Slicer4JResults/raw-slice.log");
//	        Path rawTrace = Paths.get(proPath+"/results/new/Slicer4JResults/trace.log_icdg.log");
			if(!Files.exists(rawSlice)) {
	            String[] commads = {"python3", slicerFullPath, "-j", proPath + "/results/old/program.jar","-o",proPath + "/results/old/Slicer4JResults","-b",sliceClass + ":" + sliceLine,"-tc",testClass,"-tm",testMethod,"-dep", fixPath + depPath};
				
	            Process p = new ProcessBuilder(commads)
	                    .redirectErrorStream(true)
	                    .start();
	            BufferedReader in2 = new BufferedReader(new InputStreamReader(p.getInputStream()));
	            BufferedReader err2 = new BufferedReader(new InputStreamReader(p.getErrorStream()));
				String line2 = null;
				String answer2 = in2.readLine();
				if(answer2 == null){
					String error = err2.readLine();
					if (error != null)
						System.out.println(error);
				}
				else 
					while ((line2 = in2.readLine()) != null) {
						System.out.println(line2);
					}				
				in2.close();
				err2.close();
				int rc = p.waitFor();
//				System.out.println("Process exitValue: " + rc);
				System.out.println("Finish Old slicing");
				
			}
//			############################################################
	        rawSlice = Paths.get(proPath+"/results/new/Slicer4JResults/raw-slice.log");
//	        Path rawTrace = Paths.get(proPath+"/results/new/Slicer4JResults/trace.log_icdg.log");
			if(!Files.exists(rawSlice)) {
	            String[] commads = {"python3", slicerFullPath, "-j", proPath + "/results/new/program.jar","-o",proPath + "/results/new/Slicer4JResults","-b",sliceClass + ":" + sliceLine,"-tc",testClass,"-tm",testMethod,"-dep", buggyPath + depPath};
				
	            Process p = new ProcessBuilder(commads)
	                    .redirectErrorStream(true)
	                    .start();
	            BufferedReader in2 = new BufferedReader(new InputStreamReader(p.getInputStream()));
	            BufferedReader err2 = new BufferedReader(new InputStreamReader(p.getErrorStream()));
				String line2 = null;
				String answer2 = in2.readLine();
				if(answer2 == null){
					String error = err2.readLine();
					if (error != null)
						System.out.println(error);
				}
				else 
					while ((line2 = in2.readLine()) != null) {
						System.out.println(line2);
					}				
				in2.close();
				err2.close();
				int rc = p.waitFor();
//				System.out.println("Process exitValue: " + rc);
				System.out.println("Finish New slicing");
				
			}
//			if(Files.exists(rawSlice)) {	
//				getSliceStats(baseProj,proPath,projectName,bugID,traceTime);
//			}
//			System.exit(0);
	}
	
	public static void getSliceStats(String baseProj, String proPath, String projectName,int bugID, long traceTime) {
		Stack<String> stack = new Stack<String>();
		
		 List<String> StmtsTraceList = new ArrayList<String>();
		 List<String> StmtsSliceList = new ArrayList<String>();
		 List<String> methodsTraceList = new ArrayList<String>();
		 List<String> methodsSliceList = new ArrayList<String>();
		 
		 List<String> UniqueStmtsTraceList = new ArrayList<String>();
		 List<String> UniqueStmtsSliceList = new ArrayList<String>();
		 List<String> UniquemethodsTraceList = new ArrayList<String>();
		 List<String> UniquemethodsSliceList = new ArrayList<String>();

		 
		 HashMap<String, List<String>> NodesMapping = new HashMap<>();
		 HashMap<String, String> StatmentIDMethodInstanceMapping = new HashMap<>();
		 HashMap<String, String> StatmentIDStatementInstanceMapping = new HashMap<>();
		
		File file = new File(proPath + "/results/new/Slicer4JResults/trace.log_icdg.log");
		BufferedReader br;
		
		try {
			PrintWriter writer;
			writer = new PrintWriter(proPath + "/results/new/Slicer4JResults/UniquTrace.txt", "UTF-8");
			br = new BufferedReader(new FileReader(file));
			String st = br.readLine();
			String CurrClassName = st.split(", ")[2].trim();
			String CurrLineNo = st.split("LINENO:")[1].split(":")[0];
			String CurrStatment = st;
			String PreMethodName = st.split(", ")[1].split(" ")[1].trim();	
			List<String> ByteCodeMappings = new ArrayList<String>();
			ByteCodeMappings.add(st);
			StatmentIDStatementInstanceMapping.put(st.split(", ")[0].trim(), st);
			StmtsTraceList.add(st);
			
			String PrevStatment = st;
			int counter =0;
			String CurrMethodName = st.split(", ")[1].split(" ")[1].trim();
			stack.push(CurrMethodName+"_"+String.valueOf(counter));
//			System.out.println(st.split(", ")[0].trim() + " : " +  CurrMethodName+"_"+String.valueOf(counter));
			StatmentIDMethodInstanceMapping.put(st.split(", ")[0].trim(),CurrMethodName+"_"+String.valueOf(counter));				
			boolean PrevStmIsInvoke = false;
			boolean PrevStmIsRet = false;
//			System.out.println("pre:" + PrevStmIsInvoke);
			boolean ThisStmtIsReturnStm = st.split(", ")[3].startsWith("return:");
//			System.out.println("ret:" + ThisStmtIsReturnStm);
			
			while ((st = br.readLine()) != null) {
				StatmentIDStatementInstanceMapping.put(st.split(", ")[0].trim(), st);
				if (!st.contains("LINENO"))
					continue;
				String clasName = st.split(", ")[2].trim();
				String Line = st.split("LINENO:")[1].split(":")[0];
				String method = st.split(", ")[1].split(" ")[1].trim();	

				if((!method.equals(PreMethodName)) && PrevStmIsRet) {	
					stack.pop();
				}
				if(stack.isEmpty() && PrevStmIsRet) {
					counter++;
				    stack.push(method+"_"+String.valueOf(counter));
				}
				
				if (clasName.equals(CurrClassName) && Line.equals(CurrLineNo) ) {
		
					ByteCodeMappings.add(st);
					if((!method.equals(PreMethodName)) && PrevStmIsInvoke){
						counter++;
					    stack.push(method+"_"+String.valueOf(counter));
						
					}
					

				} else {// add the previous and initilize
					if (PrevStmIsInvoke){
						counter++;
					    stack.push(method+"_"+String.valueOf(counter));					
					}
					StmtsTraceList.add(CurrStatment);
//					NodesMapping.put(statment, ByteCodeMappings);
					writer.println(CurrStatment);
					CurrClassName = clasName;
					CurrLineNo = Line;
					CurrStatment = st;					
					ByteCodeMappings = new ArrayList<String>();
					ByteCodeMappings.add(st);
				}
//				System.out.println(st.split(", ")[0].trim() + " : " +  stack.peek());
				StatmentIDMethodInstanceMapping.put(st.split(", ")[0].trim(),stack.peek());	
				
				
				PrevStmIsInvoke = st.split(", ")[3].split(":LINENO")[0].contains("invoke");
				PreMethodName = method;
				PrevStatment = st;
				PrevStmIsRet = st.split(", ")[3].trim().startsWith("return");
			}
			writer.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	
	     String previousMethod = "";
		 for(int i=0; i<StmtsTraceList.size(); i++) {				
			String clasName =  StmtsTraceList.get(i).split(", ")[2].trim();
			String Line =  StmtsTraceList.get(i).split("LINENO:")[1].split(":")[0];
			String stmt = clasName + " line " + Line;
			String methodName = StmtsTraceList.get(i).split(", ")[1].split(" ")[1].trim();
			
			if(!previousMethod.contains(methodName)) {//naiive solution
				previousMethod=methodName;
				methodsTraceList.add(methodName);
			}
//			if(!methodsTraceList.contains(StatmentIDMethodInstanceMapping.get(StmtsTraceList.get(i).split(", ")[0].trim()))) {
//				methodsTraceList.add(StatmentIDMethodInstanceMapping.get(StmtsTraceList.get(i).split(", ")[0].trim()));
//			}
//			
			if(!UniquemethodsTraceList.contains(methodName))//add unique methods
				UniquemethodsTraceList.add(methodName);
			
			if(!UniqueStmtsTraceList.contains(stmt))//add unique statements
				UniqueStmtsTraceList.add(stmt);	        
		 }
		 
		 
		 
		 file = new File(proPath + "/results/new/Slicer4JResults/raw-slice.log");
		 
			try {
				br = new BufferedReader(new FileReader(file));
				String st = br.readLine();
				String CurrClassName = st.split("    ")[0].split(":")[0].trim();
				String CurrLineNo = st.split("    ")[0].split(":")[1].trim();
				String CurrStatment = st;
				List<String> ByteCodeMappings = new ArrayList<String>();
				ByteCodeMappings.add(st);
				StmtsSliceList.add(st);
				
				while ((st = br.readLine()) != null) {
					String clasName = st.split("    ")[0].split(":")[0].trim();
					String Line = st.split("    ")[0].split(":")[1].trim();
					if (clasName.equals(CurrClassName) && Line.equals(CurrLineNo)) {
						ByteCodeMappings.add(st);
					} else {// add the previous and initilize
						StmtsSliceList.add(CurrStatment);
//						NodesMapping.put(statment, ByteCodeMappings);
						CurrClassName = clasName;
						CurrLineNo = Line;
						CurrStatment = st;
						ByteCodeMappings = new ArrayList<String>();
						ByteCodeMappings.add(st);
					}
				}
			} catch (FileNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (UnsupportedEncodingException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			file = new File(proPath + "/results/new/Slicer4JResults/slice-dependencies.log");
			int controls = 0;
			try {
				br = new BufferedReader(new FileReader(file));
				String st = br.readLine();
			
				while ((st = br.readLine()) != null) {
					if(st.contains("<--control--"))
						controls++;
				}
			} catch (FileNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (UnsupportedEncodingException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
		 

		     previousMethod = "";
			 for(int i=0; i<StmtsSliceList.size(); i++) {				
				String CurrClassName = StmtsSliceList.get(i).split("    ")[0].split(":")[0].trim();
				String CurrLineNo = StmtsSliceList.get(i).split("    ")[0].split(":")[1].trim();
				String stmt = CurrClassName + " line " + CurrLineNo;
				String stmtID = StmtsSliceList.get(i).split("    ")[2].split(":")[0].trim();
				String methodName = StatmentIDStatementInstanceMapping.get(stmtID).split(", ")[1].split(" ")[1].trim();
				
				if(!previousMethod.contains(methodName)) {//naiive solution
					previousMethod=methodName;
					methodsSliceList.add(methodName);
				}
//				if(!methodsSliceList.contains(StatmentIDMethodInstanceMapping.get(stmtID))) {
//					methodsSliceList.add(StatmentIDMethodInstanceMapping.get(stmtID));
//				}
				if(!UniquemethodsSliceList.contains(methodName))//add unique methods
					UniquemethodsSliceList.add(methodName);
				
				if(!UniqueStmtsSliceList.contains(stmt))//add unique statements
					UniqueStmtsSliceList.add(stmt);	        
			 }
		  
		 
			String results = baseProj+"/results/Slicer4JSliceStatsRegressionCheck.xlsx";
			File tempFile = new File(results);
			boolean FirstTime = false;
			if (!tempFile.exists()) {
			   FirstTime=true;
			   XSSFWorkbook workbook = new XSSFWorkbook();
			   XSSFSheet sheet = workbook.createSheet("stats");
			   try {
			       FileOutputStream outputStream = new FileOutputStream(results);
			       workbook.write(outputStream);
			       workbook.close();
			       outputStream.close();
			   } catch (Exception e) {
			   }
			 }		
			 if (FirstTime) {		    	
			     String[] header = {"project Name", "Bug ID", "# Unique Stmt instances in Trace", "# Unique Stmt instances in Slice","Unique Stmts Reduction", "# Stmts in Trace", "# Stmts in Slice", "Stmts Reduction", "# Stmts in Thin Slice", "# Unique Methods in Trace", "# Unique Methods in Slice"," Unique Methods Reduction", "# Methods in Trace", "# Methods in Slice","Methods Reduction","traceTime"};
			     WriteToExcel(results, header, "stats",false, true);
			 }
			 double UniqestmtReduc = ((Double.valueOf(UniqueStmtsTraceList.size())-Double.valueOf(UniqueStmtsSliceList.size()))/Double.valueOf(UniqueStmtsTraceList.size())) * 100.0;
			 double UniqemethodsReduc = ((Double.valueOf(UniquemethodsTraceList.size())-Double.valueOf(UniquemethodsSliceList.size()))/Double.valueOf(UniquemethodsTraceList.size())) * 100.0;
			 double stmtReduc = ((Double.valueOf(StmtsTraceList.size())-Double.valueOf(StmtsSliceList.size()))/Double.valueOf(StmtsTraceList.size())) * 100.0;
			 double methodsReduc = ((Double.valueOf(methodsTraceList.size())-Double.valueOf(methodsSliceList.size()))/Double.valueOf(methodsTraceList.size())) * 100.0;
			 
			 String[] data = {projectName, String.valueOf(bugID), 
					 String.valueOf(UniqueStmtsTraceList.size()),String.valueOf(UniqueStmtsSliceList.size()),String.valueOf(UniqestmtReduc),
					 String.valueOf(StmtsTraceList.size()),String.valueOf(StmtsSliceList.size()),String.valueOf(stmtReduc),String.valueOf(StmtsSliceList.size()-controls),
					 String.valueOf(UniquemethodsTraceList.size()),String.valueOf(UniquemethodsSliceList.size()),String.valueOf(UniqemethodsReduc),
					 String.valueOf(methodsTraceList.size()),String.valueOf(methodsSliceList.size()),String.valueOf(methodsReduc),String.valueOf(traceTime)};
			 WriteToExcel(results,data,"stats",false, false);			 
			 System.out.println("##############Finish##############");
				
	}
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
	public static List<TestCase> retrieveD4jFailingTestCase(String buggyVersionPath) throws IOException {
		String failingFile = buggyVersionPath + File.separator + "failing_tests";
		File file = new File(failingFile);

		BufferedReader reader = new BufferedReader(new FileReader(file));

		List<TestCase> list = new ArrayList<>();
		String line = null;
		while ((line = reader.readLine()) != null) {
			if (line.startsWith("---")) {
				String testClass = line.substring(line.indexOf(" ") + 1, line.indexOf("::"));
				String testMethod = line.substring(line.indexOf("::") + 2, line.length());

				TestCase tc = new TestCase(testClass, testMethod);
				list.add(tc);
			}
		}
		reader.close();

		return list;
	}

}
