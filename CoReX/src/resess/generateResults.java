package resess;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.apache.poi.ss.usermodel.Row;
import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;

import microbat.codeanalysis.runtime.StepLimitException;
import microbat.instrumentation.output.RunningInfo;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import resess.ChangeExtractor;
import resess.InPreSSE;
import resess.InPreSSS;
import tregression.SimulationFailException;
import tregression.empiricalstudy.Defects4jProjectConfig;
import tregression.empiricalstudy.RootCauseFinder;
import tregression.empiricalstudy.RootCauseNode;
import tregression.empiricalstudy.Simulator;
import tregression.empiricalstudy.TestCase;
import tregression.model.PairList;
import tregression.separatesnapshots.DiffMatcher;
import tregression.separatesnapshots.RunningResult;
import tregression.separatesnapshots.TraceCollector0;
import tregression.tracematch.ControlPathBasedTraceMatcher;

public class generateResults {
	public static final int NORMAL = 0;
	public static final int OVER_LONG = 1;
	public static final int MULTI_THREAD = 2;
	public static final int INSUFFICIENT_TRACE = 3;
	public static final int SAME_LENGTH = 4;
	public static final int OVER_LONG_INSTRUMENTATION_METHOD = 5;
	public static final int EXPECTED_STEP_NOT_MET = 6;
	public static final int UNDETERMINISTIC = 7;

	public void generateResult(String basePath, String projectName, String bugID, String proPath, String buggyPath, String fixPath, 
			boolean isReuse, boolean useSliceBreaker,
			boolean enableRandom, int breakLimit, boolean requireVisualization, 
			boolean allowMultiThread, int assertionLine, Defects4jProjectConfig config, String testcase, List<String> includedClassNames, List<String> excludedClassNames, String eraseorDual, boolean debug, String tool2Run, String save_slice_results) {
		List<TestCase> tcList;
		TestCase workingTC = null;
		try {
			tcList = retrieveD4jFailingTestCase(buggyPath);			
			if(testcase!=null){
				tcList = filterSpecificTestCase(testcase, tcList);
			}			
			for (TestCase tc : tcList) {
				System.out.println("#####working on test case " + tc.testClass + "#" + tc.testMethod);
				workingTC = tc;				 
				analyzeTestCaseResult(basePath, projectName, bugID, proPath, buggyPath, fixPath, isReuse, allowMultiThread,tc, assertionLine,
						config, requireVisualization, true, useSliceBreaker, enableRandom, breakLimit, 
						includedClassNames, excludedClassNames, eraseorDual,debug, tool2Run,save_slice_results);		
			    System.exit(0);
			}

		} catch (Exception e) {
			e.printStackTrace();
		}
	}
    //////////////////////////////////////////////////////////////////	
    private void analyzeTestCaseResult(String basePath, String projectName, String bugID, String proPath, String buggyPath, String fixPath, 
			boolean isReuse, boolean allowMultiThread, 
			TestCase tc, int assertionLine, Defects4jProjectConfig config, boolean requireVisualization, 
			boolean isRunInTestCaseMode, boolean useSliceBreaker, boolean enableRandom, int breakLimit, List<String> includedClassNames, 
			List<String> excludedClassNames, String eraseorDual,boolean debug, String tool2Run, String save_slice_results) throws Exception {
		TraceCollector0 newCollector = new TraceCollector0(true);
		TraceCollector0 oldCollector = new TraceCollector0(false);


		RunningResult newRS = null;
		RunningResult oldRs = null;

//		DiffMatcher diffMatcher = null;
		ChangeExtractor diffMatcher = null;
		PairList PairList = null;

		Long new_trace_start_time = System.currentTimeMillis();
		try {
			newRS = newCollector.run(buggyPath, tc, config, isRunInTestCaseMode, allowMultiThread, includedClassNames, excludedClassNames);
		} catch (StepLimitException e) {
			if(e.StepLenth == -100) {
				saveUndeterministicBugAndTerminate(basePath,projectName, bugID);
				System.exit(0);			
			}
			else if (e.StepLenth == -200) {
				saveMultiThreadBugAndTerminate(basePath,projectName, bugID);
				System.exit(0);			
			}
			else {
				saveBugAndTerminate(basePath,projectName, bugID,0,e.StepLenth);
				System.exit(0);			
			}
			
		}		
		if (newRS.getRunningType() != NORMAL) {
			System.out.println("Not normal");
		}
		Long new_trace_finish_time = System.currentTimeMillis();
		int newTraceTime = (int) (new_trace_finish_time - new_trace_start_time);
		
		Long old_trace_start_time = System.currentTimeMillis();
		try {
			oldRs = oldCollector.run(fixPath, tc, config, isRunInTestCaseMode, allowMultiThread, includedClassNames, excludedClassNames);			
		} catch (StepLimitException e) {
			if(e.StepLenth == -100) {
				saveUndeterministicBugAndTerminate(basePath,projectName, bugID);
				System.exit(0);			
			}
			else if (e.StepLenth == -200) {
				saveMultiThreadBugAndTerminate(basePath,projectName, bugID);
				System.exit(0);			
			}
			else {
				saveBugAndTerminate(basePath,projectName, bugID,oldRs.getRunningTrace().size(),newRS.getRunningTrace().size());	
				System.exit(0);
			}
				
		}
		if (oldRs.getRunningType() != NORMAL) {
			System.out.println("Not normal");
		}
		Long old_trace_finish_time = System.currentTimeMillis();
		int oldTraceTime = (int) (old_trace_finish_time - old_trace_start_time);
		
		int codeTime = 0;
		int traceTime = 0;
		/////////////////////code and trace comparison
		if (newRS != null && oldRs != null) {
					
			//#####################################################
			System.out.println("#################################");
			SaveTrace(newRS,oldRs,proPath);
			//#####################################################
           
			System.out.println("start matching trace..., new trace length: " + newRS.getRunningTrace().size() + ", old trace length: " + oldRs.getRunningTrace().size());		
			System.out.println("#################################");
			long code_match_start_time = System.currentTimeMillis();
			System.out.println("Code Alignement");
//			diffMatcher = new DiffMatcher(config.srcSourceFolder, config.srcTestFolder, buggyPath, fixPath);			
//			diffMatcher.matchCode();
			diffMatcher =  new ChangeExtractor(config.srcSourceFolder, config.srcTestFolder, buggyPath, fixPath);
			diffMatcher.matchCode();
			long code_match_finish_time = System.currentTimeMillis();
			codeTime = (int) (code_match_finish_time - code_match_start_time);
			
			
			System.out.println("#################################");
			System.out.println("Trace Alignement");
			long trace_match_start_time = System.currentTimeMillis();
			ControlPathBasedTraceMatcher traceMatcher = new ControlPathBasedTraceMatcher();
			if (projectName.contentEquals("InPreSS"))
				PairList = traceMatcher.matchTraceNodePair(newRS.getRunningTrace(), oldRs.getRunningTrace(), diffMatcher,"dual");
			else {
				PairList = traceMatcher.matchTraceNodePair(newRS.getRunningTrace(), oldRs.getRunningTrace(), diffMatcher,"inPreSS");
			}
			long trace_match_finish_time = System.currentTimeMillis();					
			traceTime = (int) (trace_match_finish_time - trace_match_start_time);
			System.out.println("finish matching trace, taking " + traceTime + "ms");

		}
				
		//////////////////////////dual slicing
		Trace newTrace = newRS.getRunningTrace();
		Trace oldTrace = oldRs.getRunningTrace();
				
		System.out.println("#################################");
		RootCauseFinder rootcauseFinder = new RootCauseFinder();
		rootcauseFinder.setRootCauseBasedOnDefects4J(PairList, diffMatcher, newTrace, oldTrace);
//		getRootCauseLocationInTrace(basePath, projectName, bugID, rootcauseFinder.getRealRootCaseList(),newTrace,oldTrace);
//		System.exit(0);
		//////////////////////////
		System.out.println("#################################");
		Simulator simulator = new Simulator(useSliceBreaker, enableRandom, breakLimit);
		simulator.prepare(newTrace, oldTrace, PairList, diffMatcher);//parents in getObservedFault
//		System.out.println(simulator.getObservedFault());
		TraceNode observedFaultNode = simulator.getObservedFault();
		
//		System.out.println(observedFaultNode);
		
		if(tool2Run.equals("dual") || tool2Run.equals("InPreSS") || tool2Run.equals("all")) {
			if (eraseorDual.equals("S")){
				InPreSSS configS = new InPreSSS();
				configS.dualSlicing(basePath,projectName, bugID,tc, true,proPath,observedFaultNode, newTrace, oldTrace, PairList, diffMatcher, oldTraceTime, newTraceTime, codeTime, traceTime,rootcauseFinder.getRealRootCaseList(),debug);	
			}
			else if (eraseorDual.equals("E")){
				InPreSSE configE = new InPreSSE();
				configE.dualSlicing(basePath,projectName, bugID,tc, false, proPath, observedFaultNode, newTrace, oldTrace, PairList, diffMatcher, oldTraceTime, newTraceTime, codeTime, traceTime,rootcauseFinder.getRealRootCaseList(),debug);
			}				
		}
		else if (tool2Run.equals("corex") || tool2Run.equals("all")){
			if (eraseorDual.equals("S")){
				CoReXS configS = new CoReXS();
				configS.corex(basePath,projectName, bugID,tc, assertionLine,true,proPath,observedFaultNode, newTrace, oldTrace, PairList, diffMatcher, oldTraceTime, newTraceTime, codeTime, traceTime,rootcauseFinder.getRealRootCaseList(),debug,tool2Run,save_slice_results);	
			}
		    else if (eraseorDual.equals("E")){
				CoReXE configE = new CoReXE();
				configE.corex(basePath,projectName, bugID,tc, assertionLine,false, proPath, observedFaultNode, newTrace, oldTrace, PairList, diffMatcher, oldTraceTime, newTraceTime, codeTime, traceTime,rootcauseFinder.getRealRootCaseList(),debug,tool2Run,save_slice_results);
		    }
		}
		
		return;
	}
	private void getRootCauseLocationInTrace(String basePath, String projectName, String bugID, List<RootCauseNode> realRootCaseList, Trace newTrace, Trace oldTrace) {
		
    	String results = basePath+"/results/BugPosition.xlsx";
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
		ArrayList<Integer> old_bugs = new ArrayList<Integer>();
		ArrayList<Integer> new_bugs = new ArrayList<Integer>();
		
		for (int i =0 ; i<realRootCaseList.size();i++) {
			if(realRootCaseList.get(i).isOnBefore()) {
//				System.out.println(realRootCaseList.get(i));
				new_bugs.add(Integer.valueOf(realRootCaseList.get(i).toString().split(": order ")[1].split("~")[0]));
			}
			else{
				old_bugs.add(Integer.valueOf(realRootCaseList.get(i).toString().split(": order ")[1].split("~")[0]));
			}
		}
		Collections.sort(old_bugs);
		Collections.sort(new_bugs);
		Integer old_first_bug_position = 0;
		Integer old_last_bug_position = 0;
		Integer new_first_bug_position = 0;
		Integer new_last_bug_position = 0;
		if(old_bugs.size()!=0) {
			 old_first_bug_position = old_bugs.get(0);
			 old_last_bug_position = old_bugs.get(old_bugs.size()-1);
		}
		if(new_bugs.size()!=0) {
			 new_first_bug_position = new_bugs.get(0);
			 new_last_bug_position = new_bugs.get(new_bugs.size()-1);
		}
		
		double old_first_bug_relative_position = (100.0*old_first_bug_position)/(double)(oldTrace.getExecutionList().size());
		double old_last_bug_relative_position = (100.0*old_last_bug_position)/(double)(oldTrace.getExecutionList().size());
		double new_first_bug_relative_position = (100.0*new_first_bug_position)/(double)(newTrace.getExecutionList().size());
		double new_last_bug_relative_position = (100.0*new_last_bug_position)/(double)(newTrace.getExecutionList().size());

        if (FirstTime) {		    	
	        String[] header = {"Project Name", "Bug ID", 
	        		"Old trace size (#T)", "position of the first bug", "relative position of the frirst bug", "position of the last bug", "relative position of the last bug", 
	        		"New trace size (#T)", "position of the first bug", "relative position of the frirst bug", "position of the last bug", "relative position of the last bug"};
	        WriteToExcel(results, header, "stats",false, true);
	    }
	    String[] data = {projectName, bugID, String.valueOf(oldTrace.getExecutionList().size()), String.valueOf(old_first_bug_position), String.valueOf(old_first_bug_relative_position), 
	    		 String.valueOf(old_last_bug_position), String.valueOf(old_last_bug_relative_position),
	    		String.valueOf(newTrace.getExecutionList().size()), String.valueOf(new_first_bug_position), String.valueOf(new_first_bug_relative_position), 
	    		 String.valueOf(new_last_bug_position), String.valueOf(new_last_bug_relative_position),};
	    WriteToExcel(results,data,"stats",false, false);
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
     private void saveBugAndTerminate(String basePath, String projectName, String bugID, int oldsize, int newSize) {
    	String results = basePath+"/results/"+projectName+"Long.xlsx";
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
	        String[] header = {"Bug ID", "Old trace size (#T)", "New trace size (#T)"};
	        WriteToExcel(results, header, "stats",false, true);
	    }
	    String[] data = {bugID, String.valueOf(oldsize), String.valueOf(newSize)};
	    WriteToExcel(results,data,"stats",false, false);		
	}
     private void saveUndeterministicBugAndTerminate(String basePath, String projectName, String bugID) {
     	String results = basePath+"/results/"+projectName+"Undeterministic.xlsx";
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
 	    String[] data = {bugID};
 	    WriteToExcel(results,data,"stats",false, false);		
 	}
     private void saveMultiThreadBugAndTerminate(String basePath, String projectName, String bugID) {
      	String results = basePath+"/results/"+projectName+"MultiThread.xlsx";
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
  	    String[] data = {bugID};
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
//	            XSSFSheet worksheet = ExcelWorkbook.getSheetAt(id);
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
	//////////////////////////////////////////////////////////////////
    private void SaveTrace(RunningResult buggyRS, RunningResult correctRs, String proPath) {
		PrintWriter writer;
		try {
			Path path = Paths.get(proPath+"/results");
			if(!Files.exists(path)) {
				new File(proPath+"/results").mkdirs();
				new File(proPath+"/results/new").mkdirs();
				new File(proPath+"/results/old").mkdirs();
			}
			writer = new PrintWriter(proPath+"/results/new/Trace.txt", "UTF-8");
			for(int i=0; i<buggyRS.getRunningTrace().size(); i++) {
				TraceNode buggyNode = buggyRS.getRunningTrace().getExecutionList().get(i);
				writer.println(buggyNode.toString());	
			}
			writer.close();
			writer = new PrintWriter(proPath+"/results/old/Trace.txt", "UTF-8");
			for(int i=0; i<correctRs.getRunningTrace().size(); i++) {
				TraceNode fixNode = correctRs.getRunningTrace().getExecutionList().get(i);
				writer.println(fixNode.toString());	
			}
			writer.close();
			
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	//////////////////////////////////////////////////////////////////	
	private List<TestCase> filterSpecificTestCase(String testcase, List<TestCase> tcList) {
		List<TestCase> filteredList = new ArrayList<>();
		for(TestCase tc: tcList){
			String tcName = tc.testClass + "#" + tc.testMethod;
			if(tcName.equals(testcase)){
				filteredList.add(tc);
			}
		}
		
		if(filteredList.isEmpty()){
			filteredList = tcList;
		}
		
		return filteredList;
	}
	//////////////////////////////////////////////////////////////////
	public List<TestCase> retrieveD4jFailingTestCase(String buggyVersionPath) throws IOException {
		return Defects4jProjectConfig.retrieveD4jFailingTestCase(buggyVersionPath);
	}

}
