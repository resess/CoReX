package resess;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.regex.Pattern;

import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;

import com.google.common.collect.BiMap;

import org.apache.poi.openxml4j.exceptions.InvalidFormatException;
import org.apache.poi.ss.usermodel.Row;
import ca.ubc.ece.resess.slicer.dynamic.slicer4j.Slicer;
import microbat.codeanalysis.bytecode.ByteCodeParser;
import microbat.codeanalysis.bytecode.MethodFinderByLine;
import microbat.model.BreakPoint;
import microbat.model.ClassLocation;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.trace.TraceNodeOrderComparator;
import microbat.model.value.VarValue;
import microbat.model.variable.Variable;
import resess.InPreSSE;
import sav.common.core.Pair;
import soot.ValueBox;
import tregression.StepChangeType;
import tregression.StepChangeTypeChecker;
import tregression.empiricalstudy.RootCauseNode;
import tregression.empiricalstudy.TestCase;
import tregression.model.PairList;
import tregression.model.TraceNodePair;
import tregression.separatesnapshots.DiffMatcher;

public class OldCoReXE {
	private boolean isMatchable(TraceNode invocationParent, PairList pairList, boolean isOnBefore) {
		if(isOnBefore){
			TraceNodePair pair = pairList.findByBeforeNode(invocationParent);
			if(pair!=null){
				if(pair.getAfterNode()!=null){
					return true;
				}
			}
		}
		else{
			TraceNodePair pair = pairList.findByAfterNode(invocationParent);
			if(pair!=null){
				if(pair.getBeforeNode()!=null){
					return true;
				}
			}
		}
		return false;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////	
	private TraceNode findLatestControlDifferent(TraceNode currentNode, TraceNode controlDom, 
			StepChangeTypeChecker checker, PairList pairList, DiffMatcher matcher,boolean isNew) {
		TraceNode n = currentNode.getStepInPrevious();
		StepChangeType t = checker.getType(n, isNew, pairList, matcher);
		while(t.getType()==StepChangeType.CTL && n.getOrder()>controlDom.getOrder()){
			TraceNode dom = n.getInvocationMethodOrDominator();
			if(dom.getMethodSign().equals(n.getMethodSign())){
				return n;
			}
			
			n = n.getStepInPrevious();
			t = checker.getType(n, isNew, pairList, matcher);
		}
		return controlDom;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void printDualSliceResults(List<TraceNode> visited, boolean isNew, String proPath, DiffMatcher matcher) {
		PrintWriter writer;
		try {
		String onNew = isNew ? "new" : "old";
		writer = new PrintWriter(proPath + "/results/" + onNew + "/DualSlice.txt", "UTF-8");
		Collections.sort(visited, new TraceNodeOrderComparator());
		for (int i = 0; i <= visited.size()-1; i++) {
//			System.out.println(visited.get(i));
		   writer.println(getSourceCode(visited.get(i),isNew,matcher));
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
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	public int findStartOrderInOtherTrace(TraceNode problematicStep, PairList pairList, boolean isOnBeforeTrace) {
		TraceNode node = problematicStep.getStepInPrevious();
		while(node != null) {
			TraceNode matchedNode = null;
			if(isOnBeforeTrace) {
				TraceNodePair pair = pairList.findByBeforeNode(node);
				if(pair != null) {
					matchedNode = pair.getAfterNode();
				}
			}
			else {
				TraceNodePair pair = pairList.findByAfterNode(node);
				if(pair != null) {
					matchedNode = pair.getBeforeNode();
				}
			}
			
			
			if(matchedNode != null) {
				return matchedNode.getOrder();
			}
			
			node = node.getStepInPrevious();
			
		}
		
		return 1;
	}
	public int findEndOrderInOtherTrace(TraceNode problematicStep, PairList pairList, boolean isOnBeforeTrace, Trace otherTrace) {
		TraceNode node = problematicStep.getStepInNext();
		while(node != null) {
			TraceNode matchedNode = null;
			if(isOnBeforeTrace) {
				TraceNodePair pair = pairList.findByBeforeNode(node);
				if(pair != null) {
					matchedNode = pair.getAfterNode();
				}
			}
			else {
				TraceNodePair pair = pairList.findByAfterNode(node);
				if(pair != null) {
					matchedNode = pair.getBeforeNode();
				}
			}
			
			
			if(matchedNode != null) {
				return matchedNode.getOrder();
			}
			
			node = node.getStepInNext();
		}
		
		/**
		 * Then, all the steps after problemStep cannot be matched in the other trace. 
		 */
		int order0 = findStartOrderInOtherTrace(problematicStep, pairList, isOnBeforeTrace);
		if(order0+1<=otherTrace.size()){
			TraceNode n = otherTrace.getExecutionList().get(order0);
			while(n!=null){
				if(n.isConditional()){
					if(n.getStepOverNext()!=null){
						return n.getStepOverNext().getOrder();
					}
					else{
						return n.getOrder();						
					}
				}
				else{
					if(n.getStepOverNext()!=null){
						n=n.getStepOverNext();						
					}
					else{
						n=n.getStepInNext();
					}
				}
			}
		}
		return otherTrace.size();
		
		/**
		 * The the length of the other trace.
		 */
//		TraceNode n = null;
//		int size = pairList.getPairList().size();
//		if(isOnBeforeTrace) {
//			n = pairList.getPairList().get(size-1).getAfterNode();
//		}
//		else {
//			n = pairList.getPairList().get(size-1).getBeforeNode();
//		}
//		int order = n.getOrder();
//		while(n!=null) {
//			n = n.getStepInNext();
//			if(n!=null) {
//				order = n.getOrder();
//			}
//		}
//		return order;
	}
	public TraceNode findControlMendingNodeOnOtherTrace(TraceNode problematicStep, PairList pairList,
			Trace otherTrace, boolean isOtherTraceTheBeforeTrace, ClassLocation correspondingLocation, DiffMatcher matcher) {
		
		int startOrder = findStartOrderInOtherTrace(problematicStep, pairList, !isOtherTraceTheBeforeTrace);
		int endOrder = findEndOrderInOtherTrace(problematicStep, pairList, !isOtherTraceTheBeforeTrace, otherTrace);
		System.currentTimeMillis();
		TraceNode bestNode = null;
		int value = -1;
		
		TraceNode temp = null;
		for(int i=endOrder; i>=startOrder; i--){
			if(i<=otherTrace.size()) {
				TraceNode node = otherTrace.getExecutionList().get(i-1);
				if(node.isConditional()){
					temp = node;
					if(node.getControlScope().containLocation(correspondingLocation)) {
						if(bestNode==null) {
							TraceNode programaticInvocationParent = problematicStep.getInvocationParent();
							TraceNode invocationParent = node.getInvocationParent();
							
							if(programaticInvocationParent==null && invocationParent==null) {
								bestNode = node;								
							}
							else if(programaticInvocationParent!=null && invocationParent!=null){
								if(pairList.isPair(programaticInvocationParent, 
										invocationParent, !isOtherTraceTheBeforeTrace)) {
									bestNode = node;
								}
							}
						}
					}
					else{
						List<TraceNode> allControlDominatees = node.findAllControlDominatees();
						for(TraceNode controlDominatee: allControlDominatees){
							if(controlDominatee.isException()){
								if(value==-1) {
									bestNode = node;
									value++;
								}
								else {
									List<TraceNode> allDominatees = bestNode.findAllControlDominatees();
									if(allDominatees.contains(node)) {
										bestNode = node;
									}
								}
							}
						}
					}
					
				}			
				else{
					BreakPoint correspondingPoint = new BreakPoint(correspondingLocation.getClassCanonicalName(), null, correspondingLocation.getLineNumber());
					MethodFinderByLine finder = new MethodFinderByLine(node.getBreakPoint());
					
					
					ByteCodeParser.parse(node.getClassCanonicalName(), finder, node.getTrace().getAppJavaClassPath());
					
					if(finder.getMethod()!=null){
						String methodSign = correspondingLocation.getClassCanonicalName() + "#" + finder.getMethod().getName() + finder.getMethod().getSignature();
						if(node.getMethodSign().equals(methodSign)){
							if(node.getLineNumber()<correspondingPoint.getLineNumber()){
								if(finder.isThrow() || finder.isReturn()){
									bestNode = node;
								}
							}
						}
					}
					
				}
			}
		}
		
		if(bestNode==null){
			bestNode = temp;
		}
		
		return bestNode;
	}
	public void dualSlicing(String basePath, String projectName, String bugID, TestCase tc,int assertionLine,
			boolean slicer4J, String proPath, TraceNode observedFaultNode, Trace newTrace, Trace oldTrace, PairList PairList, 
			DiffMatcher matcher, int oldTraceTime, int newTraceTime, int codeTime, int traceTime,  List<RootCauseNode> rootList,boolean debug ) throws IOException {

		List<TraceNode> new_workList = new ArrayList<>();
		List<TraceNode> new_visited = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> new_data_map = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> new_ctl_map = new HashMap<>();

		List<TraceNode> old_workList = new ArrayList<>();
		List<TraceNode> old_visited = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> old_data_map = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> old_ctl_map = new HashMap<>();
		

		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> old_CashDeps = new HashMap<>();
		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> new_CashDeps = new HashMap<>();
		
		StepChangeTypeChecker typeChecker = new StepChangeTypeChecker(newTrace, oldTrace);
		
		//to get statistics about slice 
//		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> slice_CashDeps = new HashMap<>();
//		getSliceStats(basePath, projectName,  bugID,PairList,slice_CashDeps, observedFaultNode, newTrace,typeChecker,matcher,proPath);
		
		new_visited.add(observedFaultNode);
		new_workList.add(observedFaultNode);
		System.out.println("#############################");
		System.out.println("Starting Working list");
		
		List<TraceNode> old_retained = new ArrayList<>();		
		List<TraceNode> new_retained = new ArrayList<>();
		
	
		new_retained.add(observedFaultNode);
		StepChangeType changeType = typeChecker.getType(observedFaultNode, true, PairList, matcher);
		TraceNode observedFaultNodeMapping = changeType.getMatchingStep();
		if(observedFaultNodeMapping!=null)
			old_retained.add(observedFaultNodeMapping);
		else
			old_retained.add(getAssertionStatement(oldTrace.getExecutionList(),tc,assertionLine));
		
		
		Long dual_start_time = System.currentTimeMillis();
		while(!new_workList.isEmpty() || !old_workList.isEmpty()){
			while(!new_workList.isEmpty()) {
//				System.out.println("#############################");
				TraceNode step = new_workList.remove(0);
			    updateWorklist(new_CashDeps, old_CashDeps, step, newTrace, oldTrace, new_visited, new_workList,old_visited,old_workList,true,typeChecker,
			    		PairList,matcher,new_data_map,new_ctl_map, proPath,new_retained,old_retained);				
			}
			////////////////////////////////////////////////////////////////////////////////////////
			while(!old_workList.isEmpty()) {
//				System.out.println("#############################");
				TraceNode step = old_workList.remove(0);
				updateWorklist(old_CashDeps, new_CashDeps, step, oldTrace, newTrace, old_visited,old_workList,new_visited, new_workList,false,typeChecker,
						PairList,matcher,old_data_map,old_ctl_map, proPath,old_retained,new_retained);
			}			
		}
		/// ################################################################
		/// ################################################################
		Long dual_finish_time = System.currentTimeMillis();				
		int dual_Time = (int) (dual_finish_time - dual_start_time);
		
		for(int i=old_visited.size()-1;i>=0; i--){
			TraceNode step = old_visited.get(i);
			if(step==null)
				old_visited.remove(i);
		}
		for(int i=new_visited.size()-1;i>=0; i--){
			TraceNode step = new_visited.get(i);
			if(step==null)
				new_visited.remove(i);
		}	
		System.out.println("##########Finish Dual Slciing###################");
		printDualSliceResults(old_visited, false, proPath, matcher);
		printDualSliceResults(new_visited,true, proPath,matcher);
		/// ################################################################
		/// ################################################################
		HashMap<Integer, Integer> oldChangeChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newChangeChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> oldTestCaseChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newTestCaseChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> oldCommonChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newCommonChunkInfo = new HashMap<>();
		getChangeChunks(typeChecker, matcher, old_visited,new_visited,oldChangeChunkInfo,newChangeChunkInfo);
//		getChangeChunks(typeChecker, inPreSSPairList, matcher, old_visited,new_visited,oldChangeChunkInfo,newChangeChunkInfo);
		getTestCaseChunks(tc,old_visited,new_visited,oldTestCaseChunkInfo,newTestCaseChunkInfo);
		getCommonBlocksChunks(typeChecker, matcher, tc,old_visited,new_visited,oldCommonChunkInfo,newCommonChunkInfo);
//		getCommonBlocksChunks(typeChecker, inPreSSPairList, matcher, tc,old_visited,new_visited,oldCommonChunkInfo,newCommonChunkInfo);
//		System.out.println("##############Printing Abstraction to Graph##############");
//		System.out.println(old_data_map);
		HashMap<TraceNode, List<Pair<TraceNode, String>>> both_new_data_map = new_data_map;
		HashMap<TraceNode, List<TraceNode>> both_new_ctl_map = new_ctl_map;
		HashMap<TraceNode, List<Pair<TraceNode, String>>> both_old_data_map = old_data_map;
		HashMap<TraceNode, List<TraceNode>> both_old_ctl_map = old_ctl_map;
		///################################################################
		///################################################################
		System.out.println("##############InPress ##############");	
		List<TraceNode> old_kept = new ArrayList<>();
		List<TraceNode> new_kept = new ArrayList<>();		
		List<String> old_kept_sourceCodeLevel = new ArrayList<>();		
		List<String> new_kept_sourceCodeLevel = new ArrayList<>();

//		addingClientTestNodes(tc, oldTrace.getExecutionList(), newTrace.getExecutionList(), old_kept, new_kept, old_retained, new_retained);
		//keep statements in the test that are kept in dual slice:
//		addingClientTestNodes(tc, old_visited, new_visited, old_kept, new_kept, old_retained, new_retained);
		int oldRetainedTestRemovedByDual = getRetainedTestRemovedByDual(tc, oldTrace.getExecutionList(),old_visited);
		int newRetainedTestRemovedByDual = getRetainedTestRemovedByDual(tc, newTrace.getExecutionList(),new_visited);
		
		HashMap<Integer, List<TraceNode>> oldDataBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newDataBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> oldCtlBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newCtlBlockNodes = new HashMap<>();
		long inPreSS_start_time = System.currentTimeMillis();	
		inPreSSAbstractionCircleOnlySameFunctionsCommonTrianlges(tc, proPath, old_visited,new_visited,typeChecker,PairList, 
				matcher,both_old_data_map,both_old_ctl_map,both_new_data_map,both_new_ctl_map,old_kept, new_kept, 
				oldDataBlockNodes, newDataBlockNodes, oldCtlBlockNodes, newCtlBlockNodes, old_retained, new_retained,old_kept_sourceCodeLevel,new_kept_sourceCodeLevel);
		long inPreSS_finish_time = System.currentTimeMillis();			
		int inPreSS_Time = (int) (inPreSS_finish_time - inPreSS_start_time);
		System.out.println("##############Saving Results##############");	
		if(debug)
			PrintFinalResultAll(tc,basePath, projectName, bugID, newTrace, oldTrace, new_visited, old_visited, new_kept, old_kept, new_retained, 
				old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
				traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,oldTestCaseChunkInfo,newTestCaseChunkInfo, oldCommonChunkInfo, newCommonChunkInfo,oldRetainedTestRemovedByDual,newRetainedTestRemovedByDual);	
		else {
			if(projectName.equals("Chart")||projectName.equals("Closure")||projectName.equals("Lang")||projectName.equals("Math")||projectName.equals("Mockito")||projectName.equals("Time")) {
				PrintD4JPaperResults(tc,basePath, projectName, bugID, newTrace, oldTrace, new_visited, old_visited, new_kept, old_kept, new_retained, 
						old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
						traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,oldTestCaseChunkInfo,newTestCaseChunkInfo,
						oldCommonChunkInfo, newCommonChunkInfo,
						oldRetainedTestRemovedByDual,newRetainedTestRemovedByDual,old_kept_sourceCodeLevel,new_kept_sourceCodeLevel);	
//				PrintFinalResultAll(tc,basePath, projectName, bugID, newTrace, oldTrace, new_visited, old_visited, new_kept, old_kept, new_retained, 
//						old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
//						traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,oldTestCaseChunkInfo,newTestCaseChunkInfo, oldCommonChunkInfo, newCommonChunkInfo,oldRetainedTestRemovedByDual,newRetainedTestRemovedByDual);	
			}		
			else 
				PrintPaperResults(tc,basePath, projectName, bugID, newTrace, oldTrace, new_visited, old_visited, new_kept, old_kept, new_retained, 
				old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
				traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,oldTestCaseChunkInfo,newTestCaseChunkInfo,
				oldCommonChunkInfo, newCommonChunkInfo,
				oldRetainedTestRemovedByDual,newRetainedTestRemovedByDual,old_kept_sourceCodeLevel,new_kept_sourceCodeLevel);	
			
		}
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void getSliceStats(String basePath, String projectName, String bugID, PairList dualPairList, HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> slice_CashDeps, TraceNode observedFaultNode, Trace newTrace, StepChangeTypeChecker typeChecker, DiffMatcher matcher, String proPath) {
		List<TraceNode> workList = new ArrayList<>();
		List<TraceNode> slice = new ArrayList<>();
		workList.add(observedFaultNode);
		slice.add(observedFaultNode);
		while(!workList.isEmpty()) {
			TraceNode step = workList.remove(0);
		    updateWorklistSlice(slice,workList,dualPairList,slice_CashDeps, step, newTrace,typeChecker,matcher);				
		}
		

		Path path = Paths.get(proPath+"/results/new");		
		if(!Files.exists(path)) {
			new File(proPath+"/results/new").mkdirs();		
		}
		PrintWriter writer = null;
		try {
			writer = new PrintWriter(proPath+"/results/new/Slice.txt", "UTF-8");
		} catch (FileNotFoundException | UnsupportedEncodingException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}


	    
		 List<String> UniqueStmtsTraceList = new ArrayList<String>();
		 List<String> UniqueStmtsSliceList = new ArrayList<String>();
		 List<String> UniquemethodsTraceList = new ArrayList<String>();
		 List<String> UniquemethodsSliceList = new ArrayList<String>();
		 List<String> StmtsTraceList = new ArrayList<String>();
		 List<String> StmtsSliceList = new ArrayList<String>();
		 List<String> methodsTraceList = new ArrayList<String>();
		 List<String> methodsSliceList = new ArrayList<String>();
	     String previousMethod = "";
		 for(int i=0; i<newTrace.size(); i++) {				
			String temp = newTrace.getExecutionList().get(i).getClassCanonicalName();
			String methodName = newTrace.getExecutionList().get(i).getMethodName();
			if(methodName != null){
				temp = temp + ":" + methodName;
			}
			
			if(!previousMethod.contains(temp)) {
				previousMethod=temp;
				methodsTraceList.add(temp);
			}
			if(!UniquemethodsTraceList.contains(temp))//add unique methods
				UniquemethodsTraceList.add(temp);
			
			temp = temp + ":" + newTrace.getExecutionList().get(i).getLineNumber();
			StmtsTraceList.add(temp);
			if(!UniqueStmtsTraceList.contains(temp))//add unique statements
				UniqueStmtsTraceList.add(temp);	        
		 }
		 previousMethod = "";
		 for(int i=0; i<slice.size(); i++) {	
			    writer.println(slice.get(i).toString());	
				
			    String temp = slice.get(i).getClassCanonicalName();
				String methodName = slice.get(i).getMethodName();
				if(methodName != null){
					temp = temp + ":" + methodName;
				}
				
				if(!previousMethod.contains(temp)) {
					previousMethod=temp;
					methodsSliceList.add(temp);
				}
				if(!UniquemethodsSliceList.contains(temp))
					UniquemethodsSliceList.add(temp);
				
				temp = temp + ":" + slice.get(i).getLineNumber();
				StmtsSliceList.add(temp);
				if(!UniqueStmtsSliceList.contains(temp))
					UniqueStmtsSliceList.add(temp);	        
		 }
		 writer.close();
			String results = basePath+"/results/SliceStatsERASE.xlsx";
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
			     String[] header = {"project Name", "Bug ID", "# Unique Stmt instances in Trace", "# Unique Stmt instances in Slice","Unique Stmts Reduction", "# Stmts in Trace", "# Stmts in Slice", "Stmts Reduction", "# Unique Methods in Trace", "# Unique Methods in Slice"," Unique Methods Reduction", "# Methods in Trace", "# Methods in Slice","Methods Reduction"};
			     WriteToExcel(results, header, "stats",false, true);
			 }
			 double UniqestmtReduc = ((Double.valueOf(UniqueStmtsTraceList.size())-Double.valueOf(UniqueStmtsSliceList.size()))/Double.valueOf(UniqueStmtsTraceList.size())) * 100.0;
			 double UniqemethodsReduc = ((Double.valueOf(UniquemethodsTraceList.size())-Double.valueOf(UniquemethodsSliceList.size()))/Double.valueOf(UniquemethodsTraceList.size())) * 100.0;
			 double stmtReduc = ((Double.valueOf(StmtsTraceList.size())-Double.valueOf(StmtsSliceList.size()))/Double.valueOf(StmtsTraceList.size())) * 100.0;
			 double methodsReduc = ((Double.valueOf(methodsTraceList.size())-Double.valueOf(methodsSliceList.size()))/Double.valueOf(methodsTraceList.size())) * 100.0;
			 
			 String[] data = {projectName, bugID, 
					 String.valueOf(UniqueStmtsTraceList.size()),String.valueOf(UniqueStmtsSliceList.size()),String.valueOf(UniqestmtReduc),
					 String.valueOf(StmtsTraceList.size()),String.valueOf(StmtsSliceList.size()),String.valueOf(stmtReduc),
					 String.valueOf(UniquemethodsTraceList.size()),String.valueOf(UniquemethodsSliceList.size()),String.valueOf(UniqemethodsReduc),
					 String.valueOf(methodsTraceList.size()),String.valueOf(methodsSliceList.size()),String.valueOf(methodsReduc)};
			 WriteToExcel(results,data,"stats",false, false);
			 System.exit(0);
	 }
	    	
	private void updateWorklistSlice(List<TraceNode> slice, List<TraceNode> workList, PairList dualPairList, HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> slice_CashDeps, TraceNode step, Trace newTrace,StepChangeTypeChecker typeChecker, DiffMatcher matcher) {
		StepChangeType changeType = typeChecker.getType(step, true, dualPairList, matcher);
		HashMap<Pair<TraceNode, String>, String> deps = new HashMap<>();//map the <dep node, the var> and data/control	
		deps = getDirectDependencies(slice_CashDeps, changeType, step, newTrace, true, typeChecker, dualPairList, matcher);
//		System.out.println("deps: " + deps);
		////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////
		for(Pair<TraceNode, String> d: deps.keySet()){
			if(!slice.contains(d.first())) {
				workList.add(d.first());
				slice.add(d.first());
			}
		}
		
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private int getRetainedTestRemovedByDual(TestCase tc, List<TraceNode> executionList, List<TraceNode> visited) {
		int res = 0;
		for (TraceNode node: executionList) {
			String ClassName = node.getClassCanonicalName();
			if (tc.testClass.equals(ClassName)) {			
				if(visited.contains(node)) {
				   //it is already kept by us.
			    }
				else {
				  res++;
			}			
		   }
		}
		return res;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void getCommonBlocksChunks(StepChangeTypeChecker typeChecker, DiffMatcher matcher, TestCase tc, List<TraceNode> old_visited, List<TraceNode> new_visited,
				HashMap<Integer, Integer> oldCommonChunkInfo, HashMap<Integer, Integer> newCommonChunkInfo) {
		int CurrentChunk=0;
		boolean PreviousStatementWasCommon = false;
		int NomberInJustFinishedChunk=0;
		for (int i = 0; i <= old_visited.size()-1; i++) {
			TraceNode step = old_visited.get(i);	
			boolean isSourceDiff = matcher.checkSourceDiff(step.getBreakPoint(), false);		
			if(isATestStatement(tc,step) || isSourceDiff) {		
				if(PreviousStatementWasCommon) {//finish the current block	
					if(NomberInJustFinishedChunk!=0)
					    oldCommonChunkInfo.put(CurrentChunk,NomberInJustFinishedChunk);
				}
				else {
					//nothing: the previous one was also retain
				}
				PreviousStatementWasCommon = false;
				
			}else { 
				if(PreviousStatementWasCommon) {
				   NomberInJustFinishedChunk++;//add to currentBlock
				}else {//start a new chunk
					CurrentChunk++;		
					NomberInJustFinishedChunk=1;
				}	    
		    PreviousStatementWasCommon=true;
			}		
		}
		 CurrentChunk=0;
		 PreviousStatementWasCommon = false;
		 NomberInJustFinishedChunk=0;
		for (int i = 0; i <= new_visited.size()-1; i++) {
			TraceNode step = new_visited.get(i);	
			boolean isSourceDiff = matcher.checkSourceDiff(step.getBreakPoint(), true);		
			if(isATestStatement(tc,step) || isSourceDiff) {		
				if(PreviousStatementWasCommon) {//finish the current block	
					if(NomberInJustFinishedChunk!=0)
					    newCommonChunkInfo.put(CurrentChunk,NomberInJustFinishedChunk);
				}
				else {
					//nothing: the previous one was also retain
				}
				PreviousStatementWasCommon = false;
				
			}else { 
				if(PreviousStatementWasCommon) {
				   NomberInJustFinishedChunk++;//add to currentBlock
				}else {//start a new chunk
					CurrentChunk++;		
					NomberInJustFinishedChunk=1;
				}	    
		    PreviousStatementWasCommon=true;
			}		
		}
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void addingClientTestNodes(TestCase tc, List<TraceNode> old_visited, List<TraceNode> new_visited, List<TraceNode> old_kept,
				List<TraceNode> new_kept, List<TraceNode> old_retained, List<TraceNode> new_retained) {
		for (TraceNode node: old_visited) {
			String ClassName = node.getClassCanonicalName();
			if (tc.testClass.equals(ClassName)) {
					if(!old_kept.contains(node)) {
						old_kept.add(node);
						old_retained.add(node);
					}			
			}
		}
		for (TraceNode node: new_visited) {
			String ClassName = node.getClassCanonicalName();
			if (tc.testClass.equals(ClassName)) {
					if(!new_kept.contains(node)) {
						new_kept.add(node);
						new_retained.add(node);
					}
				
			}
		}
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void getTestCaseChunks(TestCase tc, List<TraceNode> old_visited, List<TraceNode> new_visited,
			HashMap<Integer, Integer> oldTestChunkInfo, HashMap<Integer, Integer> newTestChunkInfo) {
	//Collections.sort(old_visited, new TraceNodePairOrderComparator());
	//Collections.sort(new_visited, new TraceNodePairOrderComparator());
	int CurrentChunk=0;
	boolean PreviousStatementWasTest = false;
	for (int i = 0; i <= old_visited.size()-1; i++) {
		TraceNode step = old_visited.get(i);	
		if(isATestStatement(tc,step)) {
			if(PreviousStatementWasTest) {
				//do nothing. We can add all changed statements to the arry for the chunck
			}
			else {
				CurrentChunk++;
				oldTestChunkInfo.put(CurrentChunk, step.getOrder());//this the first statement of this chunk just add it
			}
			PreviousStatementWasTest = true;
			
		}else {
			PreviousStatementWasTest=false;
		}
		
	}
	CurrentChunk = 0;
	PreviousStatementWasTest = false;
	for (int i = 0; i <= new_visited.size()-1; i++) {
		TraceNode step = new_visited.get(i);	
		if(isATestStatement(tc,step)) {
			if(PreviousStatementWasTest) {
				//do nothing. We can add all changed statements to the arry for the chunck
			}
			else {
				CurrentChunk++;
				newTestChunkInfo.put(CurrentChunk, step.getOrder());//this the first statement of this chunk just add it
			}
			PreviousStatementWasTest = true;
			
		}else {
			PreviousStatementWasTest=false;
		}
		
	  }
		
	}
	private void getChangeChunks(StepChangeTypeChecker typeChecker, DiffMatcher matcher, List<TraceNode> old_visited, List<TraceNode> new_visited,
				HashMap<Integer, Integer> oldChangeChunkInfo, HashMap<Integer, Integer> newChangeChunkInfo) {
		Collections.sort(old_visited, new TraceNodeOrderComparator());
		Collections.sort(new_visited, new TraceNodeOrderComparator());
		int CurrentChunk=0;
		boolean PreviousStatementWasChange = false;
		for (int i = 0; i <= old_visited.size()-1; i++) {
			TraceNode step = old_visited.get(i);
			boolean isSourceDiff = matcher.checkSourceDiff(step.getBreakPoint(), false);		
			if(isSourceDiff) {
				if(PreviousStatementWasChange) {
					//do nothing. We can add all changed statements to the arry for the chunck
				}
				else {
					CurrentChunk++;
					oldChangeChunkInfo.put(CurrentChunk, step.getOrder());//this the first statement of this chunk just add it
				}
				PreviousStatementWasChange = true;
				
			}else {
				PreviousStatementWasChange=false;
			}
			
		}
		CurrentChunk=0;
		PreviousStatementWasChange = false;
		for (int i = 0; i <= new_visited.size()-1; i++) {
			TraceNode step = new_visited.get(i);
			boolean isSourceDiff = matcher.checkSourceDiff(step.getBreakPoint(), true);		
			if(isSourceDiff) {
				if(PreviousStatementWasChange) {
					//do nothing. We can add all changed statements to the arry for the chunck
				}
				else {
					CurrentChunk++;
					newChangeChunkInfo.put(CurrentChunk, step.getOrder());
				}
				PreviousStatementWasChange = true;
				
			}else {
				PreviousStatementWasChange=false;
			}
			
		}
			
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void updateWorklist( HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> cashDeps, HashMap<TraceNode, 
			HashMap<Pair<TraceNode, String>, String>> OthercashDeps, TraceNode step, Trace trace, Trace otherTrace, List<TraceNode> visited, 
			List<TraceNode> workList, List<TraceNode> other_visited, List<TraceNode> other_workList, boolean isNew, 
			StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher, HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map, 
			HashMap<TraceNode, List<TraceNode>> ctl_map, String proPath,List<TraceNode> retained, List<TraceNode> OtherRetained) {
		if(step==null)
			return;
		StepChangeType changeType = typeChecker.getType(step, isNew, pairList, matcher);	
		String onNew = isNew?"new":"old";
//		System.out.println("On " + onNew + " trace," + step);
		////////////////////////////////////////////////////////////////////
		if(changeType.getType()==StepChangeType.SRC){
//			System.out.println("debug: node is src diff");
			TraceNode matchedStep = changeType.getMatchingStep();
//			if(!retained.contains(step))
//				retained.add(step);
			if(matchedStep!=null) {
				if(!other_visited.contains(matchedStep)) { 
					other_visited.add(matchedStep);
					other_workList.add(matchedStep);
//					if(!OtherRetained.contains(matchedStep))
//						OtherRetained.add(matchedStep);
				}
			}		
		}
		////////////////////////////////////////////////////////////////////
		//////////////////add corresponding node if it is data//////////////////
		if(changeType.getType()==StepChangeType.DAT){
//			System.out.println("debug: node is data diff");
			TraceNode matchedStep = changeType.getMatchingStep();
			if(!other_visited.contains(matchedStep)) { 
				other_visited.add(matchedStep);
				other_workList.add(matchedStep);					
			}
		}
		////////////////////////////////////////////////////////////////////
		//////////////////add control mending//////////////////
		if(changeType.getType()==StepChangeType.CTL){
//			System.out.println("debug: node is control diff");
			ClassLocation correspondingLocation = matcher.findCorrespondingLocation(step.getBreakPoint(), !isNew);	
			//System.out.println("debug: corresponding location:" + correspondingLocation.toString());
			TraceNode otherControlDom = findControlMendingNodeOnOtherTrace(step, pairList, otherTrace, !isNew, correspondingLocation, matcher);
			//System.out.println("debug: otherControlDom location:" + otherControlDom.toString());
			if(!other_visited.contains(otherControlDom)) { 
				other_visited.add(otherControlDom);
				other_workList.add(otherControlDom);
			}			
		}
		////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////
		
		HashMap<Pair<TraceNode, String>, String> deps = new HashMap<>();//map the <dep node, the var> and data/control		
		deps = getDirectDependencies(cashDeps, changeType, step, trace, isNew, typeChecker, pairList, matcher);
//		System.out.println("step:" + step + "deps: " + deps);
		////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////
		for(Pair<TraceNode, String> d: deps.keySet()){
//			System.out.println("dep node is " + d.first());						
			StepChangeType chgType = typeChecker.getType(d.first(), isNew, pairList, matcher);	
			if(chgType.getType()!=StepChangeType.IDT) {
				//System.out.println("not identical ");
				if(deps.get(d)=="data") {
					List<Pair<TraceNode, String>> dataDeps = data_map.get(step);
					if(dataDeps==null) {
						dataDeps = new ArrayList<>();
					}
					dataDeps.add(d);					
					data_map.put(step, dataDeps);
				}
				else if(deps.get(d)=="control") {
					List<TraceNode> ctlDeps = ctl_map.get(step);
					if(ctlDeps==null) {
						ctlDeps = new ArrayList<>();
					}
					ctlDeps.add(d.first());
					ctl_map.put(step, ctlDeps);
				}

				if(!visited.contains(d.first())) {
					workList.add(d.first());
					visited.add(d.first());						
				}
			}
			else {//if it is IDT
				//System.out.println("dep is identical ");
				if(changeType.getType()==StepChangeType.DAT){				
					TraceNode corresponding = changeType.getMatchingStep();//corresponding node of step in the other trace 
					//System.out.println("corresponding node:" + corresponding);
					if(corresponding!=null) {
						HashMap<Pair<TraceNode, String>, String> corresponding_deps = new HashMap<>();//the deps of corresponding nodes
						
						corresponding_deps = getDirectDependencies(OthercashDeps, changeType, corresponding, otherTrace, !isNew, typeChecker, pairList, matcher);
												
						boolean found = false;
						for(Pair<TraceNode, String> dd: corresponding_deps.keySet()){
							StepChangeType tepmType = typeChecker.getType(dd.first(), !isNew, pairList, matcher);		
							TraceNode correspondingDeps = tepmType.getMatchingStep();
							if(d.first().equals(correspondingDeps))//already in the slice
								found = true;
						}
						if(!found){
							//System.out.println("different def-use");
							if(deps.get(d)=="data") {
								List<Pair<TraceNode, String>> dataDeps = data_map.get(step);
								if(dataDeps==null) {
									dataDeps = new ArrayList<>();
								}
								dataDeps.add(d);
								data_map.put(step, dataDeps);
							}
							else if(deps.get(d)=="control") {
								List<TraceNode> ctlDeps = ctl_map.get(step);
								if(ctlDeps==null) {
									ctlDeps = new ArrayList<>();
								}
								ctlDeps.add(d.first());
								ctl_map.put(step, ctlDeps);
							}
							
//							April:24
//							if(!visited.contains(d.first())) { 								
//									visited.add(d.first());	//just add to visited not the worklist							
//							}
//							StepChangeType tepmType = typeChecker.getType(d.first(), !isNew, pairList, matcher);		
//							TraceNode correspondingDeps = tepmType.getMatchingStep();
//							if(!other_visited.contains(correspondingDeps)) { 								
//								other_visited.add(correspondingDeps);	//just add to visited not the worklist							
//							}
							
						}
						else {//April 10 Update: to also keep the identical dependencies if needed for context later
							if(deps.get(d)=="data") {
								List<Pair<TraceNode, String>> dataDeps = data_map.get(step);
								if(dataDeps==null) {
									dataDeps = new ArrayList<>();
								}
								dataDeps.add(d);
								data_map.put(step, dataDeps);
							}
							else if(deps.get(d)=="control") {
								List<TraceNode> ctlDeps = ctl_map.get(step);
								if(ctlDeps==null) {
									ctlDeps = new ArrayList<>();
								}
								ctlDeps.add(d.first());
								ctl_map.put(step, ctlDeps);
							}
						}
					}
				}
				else if (changeType.getType()==StepChangeType.CTL){//April 10 Update: to also keep the identical dependencies if needed for context later
					if(deps.get(d)=="data") {
						List<Pair<TraceNode, String>> dataDeps = data_map.get(step);
						if(dataDeps==null) {
							dataDeps = new ArrayList<>();
						}
						dataDeps.add(d);
						data_map.put(step, dataDeps);
					}
					else if(deps.get(d)=="control") {
						List<TraceNode> ctlDeps = ctl_map.get(step);
						if(ctlDeps==null) {
							ctlDeps = new ArrayList<>();
						}
						ctlDeps.add(d.first());
						ctl_map.put(step, ctlDeps);
					}
				}
				else if (changeType.getType()==StepChangeType.IDT){//April 10 Update: to also keep the identical dependencies if needed for context later
					if(deps.get(d)=="data") {
						List<Pair<TraceNode, String>> dataDeps = data_map.get(step);
						if(dataDeps==null) {
							dataDeps = new ArrayList<>();
						}
						dataDeps.add(d);
						data_map.put(step, dataDeps);
					}
					else if(deps.get(d)=="control") {
						List<TraceNode> ctlDeps = ctl_map.get(step);
						if(ctlDeps==null) {
							ctlDeps = new ArrayList<>();
						}
						ctlDeps.add(d.first());
						ctl_map.put(step, ctlDeps);
					}
				}
//				if(d.first().isException()){
//					TraceNode nextStep = d.first().getStepInPrevious();
//					//System.out.println("debug: prev step " + nextStep);
//					List<TraceNode> ctlDeps = ctl_map.get(step);
//					if(ctlDeps==null) {
//						ctlDeps = new ArrayList<>();
//					}
//					ctlDeps.add(nextStep);
//					ctl_map.put(step, ctlDeps);
//					if(!visited.contains(nextStep)) {
//						workList.add(nextStep);
//						visited.add(nextStep);							
//					}						
//				}
			}	
		}
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////	
	private HashMap<Pair<TraceNode, String>, String> getDirectDependencies(HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> cashDeps, 
			StepChangeType changeType, TraceNode step, Trace trace, boolean isNew, StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher) {
		if(cashDeps.containsKey(step))
			return cashDeps.get(step);
		HashMap<Pair<TraceNode, String>, String> deps = new HashMap<>();
		//////////////////add dependency nodes//////////////////
		//add all def-use
		for(VarValue readVar: step.getReadVariables()){
			TraceNode dataDom = trace.findDataDependency(step, readVar);
			//System.out.println("debug: data dependency node: " + dataDom);
			if(dataDom!=null) {
				Pair<TraceNode, String> keyPair = new Pair(dataDom, readVar.getVarName());				
				deps.put(keyPair,"data");			
			}
		}
		
		//////////////////add control node//////////////////
		TraceNode controlDom = step.getInvocationMethodOrDominator();
//		step.constructControlDomianceRelation();
//		System.out.println("debug: control dep node (dominator): " + controlDom);
		if(step.insideException() || getSourceCode(step, isNew, matcher).contains("throw")){
			controlDom = step.getStepInPrevious();
			//System.out.println("debug: control dep node (exception): " + controlDom);
		}
		else if(controlDom!=null && !controlDom.isConditional() && controlDom.isBranch() && !controlDom.equals(step.getInvocationParent())){
			StepChangeType t = typeChecker.getType(controlDom, isNew, pairList, matcher);
			if(t.getType()==StepChangeType.IDT){
				controlDom = findLatestControlDifferent(step, controlDom, typeChecker, pairList, matcher,isNew);						
			}
		}						
		if(controlDom==null){
			TraceNode invocationParent = step.getInvocationParent();
			//System.out.println("debug: control dep node (invocation): " + invocationParent);
			if(!isMatchable(invocationParent, pairList, isNew)){
				controlDom = invocationParent;
				//System.out.println("debug: control dep node (not matchable): " + controlDom);
			}
		}   
		//System.out.println("debug: control dependency node: " + controlDom);
		
		//the below if is a hack to fix the wrong control dependency in ERASE
		if(controlDom!=null) {
			if(changeType.getType()==StepChangeType.CTL) {
	//			System.out.println("step is control diff: " + step);
				if(controlDom.isConditional()||controlDom.isBranch()) {
	//				System.out.println("the step control is branch");
					TraceNode latestDataDiffCondition = findTheLatestDataDiffCondition(step,trace,typeChecker,isNew, pairList, matcher);
	//				System.out.println("latest diff"+latestDataDiffCondition);
					if(!controlDom.equals(latestDataDiffCondition))
						controlDom = latestDataDiffCondition;
				}
			}
		}
			
		if(controlDom!=null) {
			Pair<TraceNode, String> keyPair = new Pair(controlDom, "null");
			deps.put(keyPair, "control");
		}
		cashDeps.put(step, deps);
		return deps;
	}
	private TraceNode findTheLatestDataDiffCondition(TraceNode step, Trace trace, StepChangeTypeChecker typeChecker,
			boolean isNew, PairList pairList, DiffMatcher matcher) {
		List<TraceNode> nodes = trace.getExecutionList();
		Collections.sort(nodes, new TraceNodeOrderComparator());
		boolean passed = false;
		for(int i =nodes.size()-1;i>=0;i--) {
//			System.out.println("debug: step: " + nodes.get(i));
		    if(nodes.get(i).equals(step))
		    	passed = true;
		    if(passed) {
		    	StepChangeType t = typeChecker.getType(nodes.get(i), isNew, pairList, matcher);
				if((t.getType()==StepChangeType.DAT || t.getType()==StepChangeType.SRCDAT) && (nodes.get(i).isConditional() || nodes.get(i).isBranch())){
					return nodes.get(i);					
				}
		    }
		}
		return step.getControlDominator();
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	public String getJustSourceCode(TraceNode traceNode, boolean isOnNew, DiffMatcher matcher) {
		
		int lineNo = traceNode.getLineNumber();	
		String source = null;
        BreakPoint breakPoint = traceNode.getBreakPoint();
        String Path = breakPoint.getFullJavaFilePath();
		File file = new File(Path);
//		if(!file.exists()){
//			path = path.replace(matcher.getSourceFolderName(), matcher.getTestFolderName());
//			file = new File(path);
//		}
		
		if(file.exists()){
			InputStream stdin;
			try {
				stdin = new FileInputStream(file);
				InputStreamReader isr = new InputStreamReader(stdin);
				BufferedReader br = new BufferedReader(isr);

				String line = null;
				int index = 1;
				while ( (line = br.readLine()) != null){					
					if(index==lineNo) {
						source = line.trim();
						source= source.replace("\"", "'");
						return source;
					}
					index++;
				}				
			} catch (FileNotFoundException e1) {
				e1.printStackTrace();
			} catch (IOException e1) {
				e1.printStackTrace();
			}
		}
		return source;
		
		
		
	}
	public String getSourceCode(TraceNode traceNode, boolean isOnNew, DiffMatcher matcher) {
		
		int lineNo = traceNode.getLineNumber();	
		String source = null;
        BreakPoint breakPoint = traceNode.getBreakPoint();
        String Path = breakPoint.getFullJavaFilePath();
		File file = new File(Path);
//		if(!file.exists()){
//			path = path.replace(matcher.getSourceFolderName(), matcher.getTestFolderName());
//			file = new File(path);
//		}
		
		if(file.exists()){
			InputStream stdin;
			try {
				stdin = new FileInputStream(file);
				InputStreamReader isr = new InputStreamReader(stdin);
				BufferedReader br = new BufferedReader(isr);

				String line = null;
				int index = 1;
				while ( (line = br.readLine()) != null){					
					if(index==lineNo) {
						source = line.trim();
						source= source.replace("\"", "'");
					}
					index++;
				}				
			} catch (FileNotFoundException e1) {
				e1.printStackTrace();
			} catch (IOException e1) {
				e1.printStackTrace();
			}
		}
		
		String result = String.valueOf(traceNode.getOrder());
		result = traceNode.getClassCanonicalName();
		String methodName = traceNode.getMethodName();
		if(methodName != null){
			result = result + ":" + methodName;
		}
		result = result + ": LineNo@" + traceNode.getLineNumber() + "--->";
        result = result + source;
		return result;
		
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void inPreSSAbstractionCircleOnlySameFunctionsCommonTrianlges(TestCase tc,String proPath, List<TraceNode> old_visited, List<TraceNode> new_visited, 
			StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher, 
			HashMap<TraceNode, List<Pair<TraceNode, String>>> old_data_map, HashMap<TraceNode, List<TraceNode>> old_ctl_map, 
			HashMap<TraceNode, List<Pair<TraceNode, String>>> new_data_map, HashMap<TraceNode, List<TraceNode>> new_ctl_map, 
			List<TraceNode> old_kept, List<TraceNode> new_kept, HashMap<Integer, List<TraceNode>> oldDataBlockNodes, 
			HashMap<Integer, List<TraceNode>> newDataBlockNodes,HashMap<Integer, List<TraceNode>> oldCtlBlockNodes,
			HashMap<Integer, List<TraceNode>> newCtlBlockNodes, List<TraceNode> old_retained, List<TraceNode> new_retained,List<String> old_kept_sourceCodeLevel, List<String> new_kept_sourceCodeLevel) {
		/////////////////////////////////////////////////////////////
		Collections.sort(old_visited, new TraceNodeOrderComparator());
		Collections.sort(new_visited, new TraceNodeOrderComparator());                	
		/////////////////////extract blocks for old/////////////////////
		HashMap<Integer, List<TraceNode>> oldCtlBlockNodesTemp = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newCtlBlockNodesTemp = new HashMap<>();
		HashMap<TraceNode, Integer> oldBlocks = new HashMap<>();
		Integer BlockID = 0;
		Integer CTLBlockID = 0;
		boolean current_data_flag = false;
		boolean current_ctl_flag = false;
		boolean firstTime = true;
		boolean isDataBlock = false;
		boolean isCTLBlock = false;
		for(int i=old_visited.size()-1;i>=0; i--){
			TraceNode step = old_visited.get(i);	
//			System.out.println("step on old is: " + step);	
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
//			System.out.println("step type: " + changeType.getType());	
			//if ((changeType.getType()!=StepChangeType.DAT || i==old_visited.size()-1) && changeType.getType()!=StepChangeType.CTL) { //separate the blocks
//			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || (isATestStatement(tc, step) && isLastStatement(tc, step,old_visited))) { //it is retain	
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || (old_retained.contains(step))) { //it is retain	
				isDataBlock = false;
				isCTLBlock = false;
				if (current_data_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
					//firstTime = false;
				}
				if (current_ctl_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isDataBlock = false;
				isCTLBlock = true;
				if (!current_ctl_flag) {//if we are not currently in ctl block
					BlockID = BlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.DAT){ 
				isDataBlock = true;
				isCTLBlock = false;				
				if (!current_data_flag) {//if we are not currently in data block
					BlockID = BlockID + 1;
					current_data_flag = true;
					current_ctl_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
	//		if(firstTime) {
	//			firstTime = false;
	//			BlockID = BlockID + 1;
	//		}
			
	//		oldBlocks.put(step, BlockID);	
			
		}	
//		System.out.println("old blocks " + oldBlocks);	
		/////////////////////extract blocks for new/////////////////////
		HashMap<TraceNode, Integer> newBlocks = new HashMap<>();
		BlockID = 0;
		current_data_flag = false;
		current_ctl_flag = false;
		firstTime = true;
		isDataBlock = false;
		TraceNode previousData = null;
		for(int i=new_visited.size()-1;i>=0; i--){
			TraceNode step = new_visited.get(i);
			//System.out.println("step on new is: " + step);	
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
			//if ((changeType.getType()!=StepChangeType.DAT || i==new_visited.size()-1) && changeType.getType()!=StepChangeType.CTL) { //separate the blocks
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || (new_retained.contains(step))) { //separate the blocks				
				isDataBlock = false;
				isCTLBlock = false;
				if (current_data_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
					//firstTime = false;
				}
				if (current_ctl_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isDataBlock = false;
				isCTLBlock = true;
				if (!current_ctl_flag) {//coming from dat or other blocks
					CTLBlockID = CTLBlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
					//firstTime = false;
				}
				newBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.DAT){ 
				isDataBlock = true;
				isCTLBlock = false;	
				if (previousData!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousData, true, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();
					if(oldBlocks.get(matchedStep)!=oldBlocks.get(previousMatchedStep)) {//separate if it is separated in old 									
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						//firstTime = false;
					}					
					else {			
						if (!current_data_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = true;
							current_ctl_flag = false;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_data_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						//firstTime = false;
					}
					
				}
				previousData = step;
				newBlocks.put(step, BlockID);	
			}
	//		if (firstTime) {
	//			BlockID = BlockID + 1;
	//			firstTime = false;
	//		}
	//		newBlocks.put(step, BlockID);
		
			if (isDataBlock){
				if (newDataBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = newDataBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					newDataBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					newDataBlockNodes.put(BlockID, nodes);
				}
			}
			if (isCTLBlock){
				if (newCtlBlockNodesTemp.containsKey(CTLBlockID)){
					List<TraceNode> nodes = newCtlBlockNodesTemp.get(CTLBlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					newCtlBlockNodesTemp.put(CTLBlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					newCtlBlockNodesTemp.put(CTLBlockID, nodes);
				}
			}	
		}
//		System.out.println("new blocks " + newBlocks);
		/////////////////////extract blocks for old/////////////////////
		oldBlocks = new HashMap<>();
		BlockID = 0;
		CTLBlockID = 0;
		current_data_flag = false;
		current_ctl_flag = false;
		firstTime = true;
		isDataBlock = false;
		previousData = null;
		for(int i=old_visited.size()-1;i>=0; i--){
			TraceNode step = old_visited.get(i);
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || (old_retained.contains(step))) { //separate the blocks
				isDataBlock = false;
				isCTLBlock = false;
				if (current_data_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
					//firstTime = false;
				}
				if (current_ctl_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isDataBlock = false;
				isCTLBlock = true;
				if (!current_ctl_flag) {//coming from dat or other blocks
					CTLBlockID = CTLBlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.DAT){ 
				isDataBlock = true;
				isCTLBlock = false;	
				if (previousData!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousData, false, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();
					if(newBlocks.get(matchedStep)!=newBlocks.get(previousMatchedStep)) {//separate them 									
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						//firstTime = false;
					}					
					else {			
						if (!current_data_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = true;
							current_ctl_flag = false;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_data_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						//firstTime = false;
					}
				}
				previousData = step;
				oldBlocks.put(step, BlockID);
			}
	//		if (firstTime) {
	//			BlockID = BlockID + 1;
	//			firstTime = false;
	//		}
	//		oldBlocks.put(step, BlockID);
			if (isDataBlock){
				if (oldDataBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = oldDataBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					oldDataBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					oldDataBlockNodes.put(BlockID, nodes);
				}
			}
			if (isCTLBlock){
				if (oldCtlBlockNodesTemp.containsKey(CTLBlockID)){
					List<TraceNode> nodes = oldCtlBlockNodesTemp.get(CTLBlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					oldCtlBlockNodesTemp.put(CTLBlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					oldCtlBlockNodesTemp.put(CTLBlockID, nodes);
				}
			}
		}
		CTLBlockID = BlockID + 1;
		for(Integer ctlblockID:oldCtlBlockNodesTemp.keySet()) {
			oldCtlBlockNodes.put(CTLBlockID,oldCtlBlockNodesTemp.get(ctlblockID));
			for(TraceNode node:oldCtlBlockNodesTemp.get(ctlblockID))
				oldBlocks.put(node, CTLBlockID);
			CTLBlockID += 1;
		}
		for(Integer ctlblockID:newCtlBlockNodesTemp.keySet()) {
			newCtlBlockNodes.put(CTLBlockID,newCtlBlockNodesTemp.get(ctlblockID));	
			for(TraceNode node:newCtlBlockNodesTemp.get(ctlblockID))
				newBlocks.put(node, CTLBlockID);
			CTLBlockID += 1;
		}
//		System.out.println("#################after paralizing#################"); 
//		System.out.println("The # of data block in old " + oldDataBlockNodes);
//		System.out.println("The # of data block in new " + newDataBlockNodes);
//		System.out.println("The # of ctl block in old " + oldCtlBlockNodes);
//		System.out.println("The # of ctl block in new " + newCtlBlockNodes);
	
		////////////////////////////////////////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////////////////////////////	
		////////////////////////////////////////////////////////////////////////////////////////////////////////
		/////////////////////abstraction////////////////////////////////////////////////////////////////
//		PrintWriter writer;
		try {
			//should also the corresponding kept node from the other trace be add?
			
//			writer = new PrintWriter(proPath+"/results/Explainations.gv", "UTF-8");
//			writer.println("digraph dualGraph {");
//			writer.println("rankdir = BT;");
//			writer.println("splines=ortho;");
			
	//		Collections.sort(old_visited, new TraceNodeOrderComparator());
	//		Collections.sort(new_visited, new TraceNodeOrderComparator());
						
			List<TraceNode> new_dat_kept = new ArrayList<>();
			List<TraceNode> old_dat_kept = new ArrayList<>();
			
			HashMap<TraceNode, Integer> old_data_node_function = new HashMap<>();
			HashMap<TraceNode, Integer> new_data_node_function = new HashMap<>();
			HashMap<TraceNode, Integer> old_ctl_node_function = new HashMap<>();
			HashMap<TraceNode, Integer> new_ctl_node_function = new HashMap<>();
			Integer index = 0;
			////////////////////////////////////First Define what to keep////////////////////////////////////////////////
			for(int i=old_visited.size()-1;i>=0; i--){
				TraceNode step = old_visited.get(i);
//				System.out.println("this is step: " + step);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);				
				String Type;
//				if (changeType.getType() == StepChangeType.DAT && !isATestStatement(tc, step)) {
				if(changeType.getType()==StepChangeType.DAT && !old_retained.contains(step)) {				
					old_data_node_function.put(step, index);
					TraceNode matchedStep = changeType.getMatchingStep();	
					new_data_node_function.put(matchedStep, index);
					index = index + 1;
					if(old_kept.contains(step)) {//should be added but abstracted
						if(!new_dat_kept.contains(matchedStep))
							new_dat_kept.add(matchedStep);
					}					
				}
				//else if (changeType.getType()==StepChangeType.CTL && !isATestStatement(tc, step)) {
//				else if (changeType.getType()==StepChangeType.CTL && !isLastStatement(tc, step,old_visited)) {
				else if (changeType.getType()==StepChangeType.CTL && !old_retained.contains(step)) {
					old_ctl_node_function.put(step, index);
					index = index + 1;
				}
				else if(changeType.getType()!=0) {//not identical
					if(!old_retained.contains(step))
						old_retained.add(step);
					if(!old_kept.contains(step)) {
						old_kept.add(step);	
						if (!old_kept_sourceCodeLevel.contains(getSourceCode(step,false,matcher)))
							old_kept_sourceCodeLevel.add(getSourceCode(step,false,matcher));
					
					}
					TraceNode matchedStep = changeType.getMatchingStep();	
					if(matchedStep!=null) {
						if(!new_retained.contains(matchedStep))
							new_retained.add(matchedStep);
						if(!new_kept.contains(matchedStep))
							new_kept.add(matchedStep);
					}
				}
				List<Pair<TraceNode, String>> data_deps = old_data_map.get(step);	
//				System.out.println("deps: " + data_deps);
				if(data_deps!=null) 
					for(Pair<TraceNode, String> pair:data_deps) 
						if(old_visited.contains(pair.first()))
							if(oldBlocks.get(pair.first())!=oldBlocks.get(step))//keep the dep
								//April 10 update
								if(!old_kept.contains(pair.first())) {	
//									System.out.println(getJustSourceCode(pair.first(),false,matcher));
									if(getJustSourceCode(pair.first(),false,matcher).contains("return ")) {//if it is return statement, then add the defined variable					
//										System.out.println("this is return");
//										System.out.println(pair.first().getWrittenVariables().get(0));
//										VarValue temp = pair.first().getWrittenVariables().get(0);										
//										List<VarValue> writtenVar= new ArrayList<>();
//										temp.getVariable().setName("return_"+pair.first().getMethodName());
//										System.out.println(pair.first().getWrittenVariables());
//										writtenVar.add(temp);
//										pair.first().setWrittenVariables(writtenVar);
//										System.out.println(pair.first().getWrittenVariables());
//										System.out.println(pair.first().getReadVariables().get(0));
//										List<Pair<TraceNode, String>> return_data_deps = old_data_map.get(pair.first());										
//										if(return_data_deps!=null)
//											for(Pair<TraceNode, String> reutunr_pair:return_data_deps) 
//												if(old_visited.contains(reutunr_pair.first()))
//													if(!old_kept.contains(reutunr_pair.first())) {
////														System.out.println("this is step: " + step);
////														System.out.println("this is the kept dep of the return: " + reutunr_pair.first());
//														old_kept.add(reutunr_pair.first());
//														if (!old_kept_sourceCodeLevel.contains(getSourceCode(reutunr_pair.first(),false,matcher)))
//															old_kept_sourceCodeLevel.add(getSourceCode(reutunr_pair.first(),false,matcher));
//													}									
									}
//									else {
//										System.out.println("this is step: " + step);
//										System.out.println("this is the kept dep: " + pair.first());
										old_kept.add(pair.first());
										if (!old_kept_sourceCodeLevel.contains(getSourceCode(pair.first(),false,matcher)))
											old_kept_sourceCodeLevel.add(getSourceCode(pair.first(),false,matcher));
//									}
								}
				
	//			List<TraceNode> ctl_deps = old_ctl_map.get(step);
	//			if(ctl_deps!=null) 
	//				for(TraceNode node:ctl_deps) 
	//					if(old_visited.contains(node))
	//						if(oldBlocks.get(node)!=oldBlocks.get(step))//keep the dep
	//							if(!old_kept.contains(node))
	//								old_kept.add(node);		
			}
			/////////////////////////////////////First Define what to keep///////////////////////////////////////////////
			for(int i=new_visited.size()-1;i>=0; i--){
				TraceNode step = new_visited.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);				
				String Type;				
//				if (changeType.getType() == StepChangeType.DAT && !isATestStatement(tc, step)) {
				if (changeType.getType() == StepChangeType.DAT && !new_retained.contains(step)) {
					if (!new_data_node_function.keySet().contains(step)) {
						new_data_node_function.put(step, index);
						TraceNode matchedStep = changeType.getMatchingStep();	
						old_data_node_function.put(matchedStep, index);
						index = index + 1;
					}
					if (new_kept.contains(step)) {//should be added but abstracted
						TraceNode matchedStep = changeType.getMatchingStep();	
						if(!old_dat_kept.contains(matchedStep))
							old_dat_kept.add(matchedStep);
					}					
				}
//				 else if (changeType.getType() == StepChangeType.CTL && !isATestStatement(tc, step)) {
				else if (changeType.getType() == StepChangeType.CTL && !new_retained.contains(step)) {
					new_ctl_node_function.put(step, index);
					index = index + 1;
				}
				else if(changeType.getType()!=0) {//not identical				
					if(!new_retained.contains(step)) {				
						new_retained.add(step);
					}
					if(!new_kept.contains(step)) {
						new_kept.add(step);
						if (!new_kept_sourceCodeLevel.contains(getSourceCode(step,true,matcher)))
							new_kept_sourceCodeLevel.add(getSourceCode(step,true,matcher));					
					}
					TraceNode matchedStep = changeType.getMatchingStep();	
					if(matchedStep!=null) {
						if(!old_retained.contains(matchedStep))
							old_retained.add(matchedStep);
						if(!old_kept.contains(matchedStep))
							old_kept.add(matchedStep);
					}
				}
				List<Pair<TraceNode, String>> data_deps = new_data_map.get(step);				
				if(data_deps!=null) 
					for(Pair<TraceNode, String> pair:data_deps) 
						if(new_visited.contains(pair.first()))
							if(newBlocks.get(pair.first())!=newBlocks.get(step))//keep the dep
								//April 10 update
								if(!new_kept.contains(pair.first())) {
									if(getJustSourceCode(pair.first(),true,matcher).contains("return ")) {//if it is return statement, then add the defined variable
//										VarValue temp = pair.first().getReadVariables().get(0);										
//										List<VarValue> writtenVar= new ArrayList<>();
//										temp.getVariable().setName("return_"+pair.first().getMethodName());
//										System.out.println(pair.first().getWrittenVariables());
//										writtenVar.add(temp);
//										pair.first().setWrittenVariables(writtenVar);
//										System.out.println(pair.first().getReadVariables().get(0));
//										List<Pair<TraceNode, String>> return_data_deps = new_data_map.get(pair.first());
//										if(return_data_deps!=null)
//											for(Pair<TraceNode, String> reutunr_pair:return_data_deps) 
//												if(new_visited.contains(reutunr_pair.first()))
//													if(!new_kept.contains(reutunr_pair.first())) {
////														System.out.println("this is step: " + step);
////														System.out.println("this is the kept dep of the return: " + reutunr_pair.first());
//														new_kept.add(reutunr_pair.first());
//														if (!new_kept_sourceCodeLevel.contains(getSourceCode(reutunr_pair.first(),true,matcher)))
//															new_kept_sourceCodeLevel.add(getSourceCode(reutunr_pair.first(),true,matcher));
//													}									
									}
//									else {
//										System.out.println("this is step: " + step);
//										System.out.println("this is the kept dep: " + pair.first());
										new_kept.add(pair.first());
										if (!new_kept_sourceCodeLevel.contains(getSourceCode(pair.first(),true,matcher)))
											new_kept_sourceCodeLevel.add(getSourceCode(pair.first(),true,matcher));
//									}
								}
				
	//			List<TraceNode> ctl_deps = new_ctl_map.get(step);
	//			if(ctl_deps!=null) 
	//				for(TraceNode node:ctl_deps) 
	//					if(new_visited.contains(node))
	//						if(newBlocks.get(node)!=newBlocks.get(step))//keep the dep
	//							if(!new_kept.contains(node))
	//								new_kept.add(node);		
			}
			/////////////////////////////////////////////////////////////
	/////////////////////////////////////////////////////////////
	//Add test statements becasue they are in the dual slice//////
//			System.out.println(old_dat_kept);
//			System.out.println(new_dat_kept);
			for(TraceNode n: old_dat_kept) {
				if(!old_kept.contains(n)) {
				  old_kept.add(n);
				  if (!old_kept_sourceCodeLevel.contains(getSourceCode(n,false,matcher)))
						old_kept_sourceCodeLevel.add(getSourceCode(n,false,matcher));					
				
				  }
			}
			for(TraceNode n: new_dat_kept) {
				if(!new_kept.contains(n)) {
				  new_kept.add(n);
				  if (!new_kept_sourceCodeLevel.contains(getSourceCode(n,true,matcher)))
						new_kept_sourceCodeLevel.add(getSourceCode(n,true,matcher));
								
				}
			}
			if (old_kept.size()==0) {				
			    old_kept.add(old_visited.get(old_visited.size()-1));
			    if (!old_kept_sourceCodeLevel.contains(getSourceCode(old_visited.get(old_visited.size()-1),false,matcher)))
					old_kept_sourceCodeLevel.add(getSourceCode(old_visited.get(old_visited.size()-1),false,matcher));					
			
//			    if(!old_retained.contains(old_visited.get(old_visited.size()-1)))
//			    	old_retained.add(old_visited.get(old_visited.size()-1));
			}
			if (new_kept.size()==0) {		
			    new_kept.add(new_visited.get(new_visited.size()-1));
			    if (!new_kept_sourceCodeLevel.contains(getSourceCode(new_visited.get(new_visited.size()-1),true,matcher)))
					new_kept_sourceCodeLevel.add(getSourceCode(new_visited.get(new_visited.size()-1),true,matcher));
//			    
//			    if(!new_retained.contains(new_visited.get(new_visited.size()-1)))
//			    	new_retained.add(new_visited.get(new_visited.size()-1));
			}
				
			for (int i=0; i<old_kept.size(); i++) {
	        	if(old_kept.get(i)==null)
	        		old_kept.remove(old_kept.get(i));
			}
			for (int i=0; i<new_kept.size(); i++) {
	        	if(new_kept.get(i)==null)
	        		new_kept.remove(new_kept.get(i));
			}
	//		Collections.sort(old_visited, new TraceNodeOrderComparator());
	//		Collections.sort(new_visited, new TraceNodeOrderComparator());
			Collections.sort(old_kept, new TraceNodeOrderComparator());
			Collections.sort(new_kept, new TraceNodeOrderComparator());
//			System.out.println(old_kept);
			index = 0;
			////////////////////////add nodes of old with abstraction/////////////////////
			PrintWriter fileWriter = new PrintWriter(proPath + "/results/old/inPreSS.txt", "UTF-8");		
//			writer.println("subgraph cluster0 {");
//			writer.println("color=black;");
//			writer.println("label = \"old slice\";");
			List<String> tempInPreSS = new ArrayList<String>();
			for(int i=old_kept.size()-1;i>=0; i--){
				TraceNode step = old_kept.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
//				String Type;
//				if(changeType.getType()==StepChangeType.DAT && !isATestStatement(tc, step)) {
				if(changeType.getType()==StepChangeType.DAT && !old_retained.contains(step)) {
					//if (old_kept.contains(step) || old_dat_kept.contains(step)) {//should be added but abstracted					
//						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";
					old_data_node_function.put(step, index);
					TraceNode matchedStep = changeType.getMatchingStep();	
					new_data_node_function.put(matchedStep, index);
					index = index + 1;
						List<VarValue> written = step.getWrittenVariables();
						List<String> vars = new ArrayList<>(); 
						List<TraceNode> visited = new ArrayList<>();
						try {
							visited.add(step);
							List<Pair<TraceNode, String>> temp = addVariable(visited,step,vars,old_data_map,oldBlocks,old_kept, old_dat_kept);
						}
						catch (StackOverflowError e) {
					        System.err.println("oche!");
					    }
						String abstraction = "";
						if (written!=null && written.size()!=0 ) { //is an assignment
							abstraction = written.get(0).getVarName();
							abstraction = abstraction + "=Func_"+old_data_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
						}					
						else {
							abstraction = abstraction + "Func_"+old_data_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							
						}
//						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";					
//						String fixNode = step.toString();	
//						writer.println("\"OldNode: "+fixNode +"\""+ "["+Type+ " label=\""+abstraction+"\"];");										
						tempInPreSS.add(abstraction);
//						fileWriter.println(abstraction);
									
				}
//				else if (changeType.getType()==StepChangeType.CTL && !isATestStatement(tc, step)) {
				else if (changeType.getType()==StepChangeType.CTL && !isLastStatement(tc, step,old_visited)) {
					//if (old_kept.contains(step)) {//should be added but abstracted					
//						Type= "color=blue fillcolor=lightskyblue1 shape=box style=filled fontsize=10";
						old_ctl_node_function.put(step, index);					
						index = index + 1;
						List<VarValue> written = step.getWrittenVariables();					
						List<String> vars = new ArrayList<>(); 
						List<TraceNode> visited = new ArrayList<>();
						try {
							visited.add(step);
							List<Pair<TraceNode, String>> temp = addVariable(visited,step,vars,old_data_map,oldBlocks,old_kept, old_dat_kept);
						}
						catch (StackOverflowError e) {
					        System.err.println("oche!");
					    }
						String abstraction = "";
						if (written!=null && written.size()!=0) { //is an assignment
							abstraction = written.get(0).getVarName();
							abstraction = abstraction + "=Func_"+old_ctl_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							String fixNode = step.toString();	
//							writer.println("\"OldNode: "+fixNode +"\""+ "["+Type+ " label=\""+abstraction+"\"];");
						}
						else {
							abstraction = abstraction + "Func_"+old_ctl_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
//							String fixNode = step.toString();	
//							writer.println("\"OldNode: "+fixNode +"\""+ "["+Type+ " label=\""+abstraction+"\"];");
							//abstraction = getSourceCode(step, false, matcher, oldSlicer4J, oldSlicer4JBytecodeMapping);							
						}
//						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";
//						String fixNode = step.toString();	
//						writer.println("\"OldNode: "+fixNode +"\""+ "["+Type+ " label=\""+abstraction+"\"];");
						tempInPreSS.add(abstraction);
//						fileWriter.println(abstraction);										
					
				}
				else {//retained set 				
//					if (changeType.getType()==StepChangeType.SRCDAT || i==old_visited.size()-1) 
//						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";					 									
//					else if (changeType.getType()==StepChangeType.SRCCTL) 
//						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";					
//					else //(changeType.getType()==StepChangeType.IDT)
//						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";					
//					String fixNode = step.toString();			
//					writer.println("\"OldNode: "+fixNode +"\""+ "["+Type+ " label=\""+getSourceCode(step, false, matcher)+"\"];");										
					tempInPreSS.add(getSourceCode(step, false, matcher));
//					fileWriter.println(getSourceCode(step, false, matcher));//add the node itself
				}	
			}
//			writer.println("}");	
			for(int j=tempInPreSS.size()-1;j>=0;j--)
				fileWriter.println(tempInPreSS.get(j));
			fileWriter.close();
			/////////////////////////////////////////////////////////////
			////////////////////////add nodes of new/////////////////////
			fileWriter = new PrintWriter(proPath + "/results/new/inPreSS.txt", "UTF-8");
//			writer.println("subgraph cluster1 {");
//			writer.println("color=black;");
//			writer.println("label = \"newslice\";");
			tempInPreSS = new ArrayList<String>();
			for(int i=new_kept.size()-1;i>=0; i--){
				TraceNode step = new_kept.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
//				String Type;
//				if (changeType.getType()==StepChangeType.DAT && !isATestStatement(tc, step)) {
				if(changeType.getType()==StepChangeType.DAT && !isLastStatement(tc, step,new_visited)) {
					//if (new_kept.contains(step) || new_dat_kept.contains(step)) {//should be added but abstracted
						//ABSTRACTION 						
//						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";
						if (!new_data_node_function.keySet().contains(step)) {
							new_data_node_function.put(step, index);
							TraceNode matchedStep = changeType.getMatchingStep();	
							old_data_node_function.put(matchedStep, index);
							index = index + 1;
						}
						List<VarValue> written = step.getWrittenVariables();
						List<String> vars = new ArrayList<>(); 
						List<TraceNode> visited = new ArrayList<>();
						try {
							visited.add(step);
							List<Pair<TraceNode, String>> temp = addVariable(visited, step,vars,new_data_map,newBlocks,new_kept, new_dat_kept);
						}
						catch (StackOverflowError e) {
					        System.err.println("oche!");
					    }
						String abstraction = "";
						if (written!=null&& written.size()!=0) { //is an assignment
							abstraction = written.get(0).getVarName();
							abstraction = abstraction + "=Func_"+new_data_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
						}
						else {
							abstraction = abstraction + "Func_"+new_data_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							//abstraction = getSourceCode(step, true, matcher, newSlicer4J, newSlicer4JBytecodeMapping);
						}
//						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";					
//						String fixNode = step.toString();	
//						writer.println("\"NewNode: "+fixNode +"\""+ "["+Type+ " label=\""+abstraction+"\"];");										
						tempInPreSS.add(abstraction);
//						fileWriter.println(abstraction);
					
				}
//				else if (changeType.getType()==StepChangeType.CTL && !isATestStatement(tc, step)) {
				else if (changeType.getType()==StepChangeType.CTL && !isLastStatement(tc, step,new_visited)) {
					if (new_kept.contains(step)) {//should be added but abstracted					
//						Type= "color=blue fillcolor=lightskyblue1 shape=box style=filled fontsize=10";
						new_ctl_node_function.put(step, index);					
						index = index + 1;
						List<VarValue> written = step.getWrittenVariables();
						List<ValueBox> writtenSoot = new ArrayList<>();
						List<String> vars = new ArrayList<>(); 
						List<TraceNode> visited = new ArrayList<>();
						try {
							visited.add(step);
							List<Pair<TraceNode, String>> temp = addVariable(visited,step,vars,new_data_map,newBlocks,new_kept, new_dat_kept);
						}
						catch (StackOverflowError e) {
					        System.err.println("oche!");
					    }
						String abstraction = "";
						if (written!=null && written.size()!=0) { //is an assignment
							abstraction = written.get(0).getVarName();
							abstraction = abstraction + "=Func_"+new_ctl_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
						}
						else if (writtenSoot.size()!=0){
							abstraction = writtenSoot.get(0).getValue().toString();
							abstraction = abstraction + "=Func_"+new_ctl_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
						}
						else {
							abstraction = abstraction + "=Func_"+new_ctl_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							//abstraction = getSourceCode(step, true, matcher, newSlicer4J, newSlicer4JBytecodeMapping);
						}
//						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";
//						String fixNode = step.toString();	
//						writer.println("\"NewNode: "+fixNode +"\""+ "["+Type+ " label=\""+abstraction+"\"];");										
						tempInPreSS.add(abstraction);
//						fileWriter.println(abstraction);
					}
				}
				else {//retained set 
//					if (changeType.getType()==StepChangeType.SRCDAT || i==new_visited.size()-1) 
//						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";					 
//					else if (changeType.getType()==StepChangeType.SRCCTL) 
//						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";
//					else //(changeType.getType()==StepChangeType.IDT)
//						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";
//					String fixNode = step.toString();			
//					writer.println("\"NewNode: "+fixNode +"\""+ "["+Type+ " label=\""+getSourceCode(step, true, matcher)+"\"];");										
					tempInPreSS.add(getSourceCode(step, true, matcher));
//					fileWriter.println(getSourceCode(step, true, matcher));
				}
			}
//			writer.println("}");
			for(int j=tempInPreSS.size()-1;j>=0;j--)
				fileWriter.println(tempInPreSS.get(j));
			fileWriter.close();
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			/////////////////////////add control flow edges//////////////
	//		Collections.sort(old_kept, new TraceNodeOrderComparator());
	//		Collections.sort(new_kept, new TraceNodeOrderComparator());
			
//			for(int i=0;i<old_kept.size(); i++) {
//				if(i!=old_kept.size()-1) {
//					TraceNode step = old_kept.get(i);
//					TraceNode BeforeStep = old_kept.get(i+1);
////					writer.println("\"OldNode: "+BeforeStep +"\" " + "->" + "\"OldNode: "+step +"\" [color=gray55 style=dotted arrowhead=normal dir=back];");
//				}
//			}
//			for(int i=0;i<new_kept.size(); i++) {
//				if(i!=new_kept.size()-1) {
//					TraceNode step = new_kept.get(i);
//					TraceNode BeforeStep = new_kept.get(i+1);
////					writer.println("\"NewNode: "+BeforeStep +"\" " + "->" + "\"NewNode: "+step +"\" [color=gray55 style=dotted arrowhead=normal dir=back] ;");
//				}
//			}
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			/////////////////////////add alignment edges//////////////////////////////////////////////////////////////////////////////
//			for(int i=0;i<old_kept.size(); i++) {
//				TraceNode step = old_kept.get(i);
//				StepChangeType changeType = typeChecker.getType(step, false, pairList, matcher);
//				TraceNode matchedStep = changeType.getMatchingStep();
//				if(new_kept.contains(matchedStep)) {										
////					writer.println("\"OldNode: "+step +"\" " + "->" + "\"NewNode: "+matchedStep +"\" [color=grey55 style=dotted arrowhead=none constraint=false];");
//				}
//			}
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			/////////////////////////add dependency edges////////////////
	//		for(int i=0;i<old_kept.size(); i++) {
	//			TraceNode step = old_kept.get(i);
	//			if(old_data_map.keySet().contains(step)) 
	//				if(old_data_map.get(step)!=null)
	//					for(Pair<TraceNode, String> dep: old_data_map.get(step)) 
	//						if(old_kept.contains(dep.first())) 		
	//							//if (!dep.second().contains("stack"))
	//								writer.println("\"OldNode: "+step +"\" " + "-> " + "\"OldNode: "+dep.first() +"\" [color=black style=solid arrowhead=normal constraint=false xlabel=\" "+dep.second() +"   \" ];");//connect data nodes to east					
	//			if(old_ctl_map.keySet().contains(step)) 
	//				if(old_ctl_map.get(step)!=null)
	//					for(TraceNode dep: old_ctl_map.get(step)) 
	//						if(old_kept.contains(dep)) 						
	//							writer.println("\"OldNode: "+step +"\" " + "-> " + "\"OldNode: "+dep +"\" [color=black style=dashed arrowhead=normal constraint=false];");//connect data nodes to west	
	//		}
	//		
	//		for(int i=0;i<new_kept.size(); i++) {
	//			TraceNode step = new_kept.get(i);
	//			if(new_data_map.keySet().contains(step)) 
	//				if(new_data_map.get(step)!=null)
	//					for(Pair<TraceNode, String> dep: new_data_map.get(step)) 
	//						if(new_kept.contains(dep.first())) 
	//							//if (!dep.second().contains("stack"))
	//								writer.println("\"NewNode: "+step +"\" " + "-> " + "\"NewNode: "+dep.first() +"\" [color=black style=solid arrowhead=normal constraint=false xlabel=\" "+dep.second() +"   \" ];");
	//			if(new_ctl_map.keySet().contains(step)) 
	//				if(new_ctl_map.get(step)!=null)
	//					for(TraceNode dep: new_ctl_map.get(step)) 
	//						if(new_kept.contains(dep)) 
	//							writer.println("\"NewNode: "+step +"\" " + "-> " + "\"NewNode: "+dep +"\" [color=black style=dashed arrowhead=normal constraint=false];");
	//		}
	
			/////////////////////////////////////////////////////////////////////
//			writer.println("}");
//			writer.close();
			
		} catch (FileNotFoundException e) {                                        
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
	
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private boolean isATestStatement(TestCase tc, TraceNode step) {
		String ClassName = step.getClassCanonicalName();
		if (tc.testClass.equals(ClassName)) {
			return true;
		}
		return false;
	}
	private boolean isLastStatement(TestCase tc, TraceNode step, List<TraceNode> trace) {
		String ClassName = step.getClassCanonicalName();
		if (tc.testClass.equals(ClassName)) {
			if(trace.get(trace.size()-1).toString().contentEquals(step.toString())) {
				return true;
			}
		}
		return false;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private List<Pair<TraceNode, String>> addVariable(List<TraceNode> visited, TraceNode step, List<String> vars, HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map, HashMap<TraceNode, Integer> Blocks, List<TraceNode> kept, List<TraceNode> forced_kept) {
//		System.out.println("Node is " + step);
		List<Pair<TraceNode, String>> data_deps = data_map.get(step);	
//		System.out.println("the current is " + data_deps);
		List<Pair<TraceNode, String>> UpdatedDataDeps = new ArrayList<>();
		if(data_deps!=null) {
			for(Pair<TraceNode, String> pair:data_deps) {
//				System.out.println("The dep node is " + pair.first());
				if(kept.contains(pair.first()) || forced_kept.contains(pair.first())){//it is already kept in the trace just add it to vars
//					System.out.println("The dep node is kept => continue");
					if(!vars.contains(pair.second())) {
//						System.out.println("The var to be added from kept " + pair.second());
						vars.add(pair.second());
					}
					continue;
				}
				if(data_map.containsKey(pair.first())) {
					for(Pair<TraceNode, String> depDepsPair : data_map.get(pair.first())) {
						if (!UpdatedDataDeps.contains(depDepsPair))
							UpdatedDataDeps.add(depDepsPair);
					}
				}
				if(Blocks.get(pair.first()) == Blocks.get(step)){ //abstract pair.first()	
					try {
						if(!visited.contains(pair.first())){
							visited.add(pair.first());
							if(vars.size()<20) {
								List<Pair<TraceNode, String>> temp = addVariable(visited, pair.first(), vars, data_map, Blocks, kept, forced_kept);
								UpdatedDataDeps.addAll(temp);
							}
						}
					}
					catch (StackOverflowError e) {
				        System.err.println("oche!");
				    }
				}
				else {//it will be kept when analyzing deps of step 
					if(!vars.contains(pair.second()))
						vars.add(pair.second());
				}				
			}
		}
		if(UpdatedDataDeps.size()!=0 && UpdatedDataDeps!=null) {
			for(Pair<TraceNode, String> pair:UpdatedDataDeps )
				if((!data_deps.contains(pair)) && vars.contains(pair.second()))
					data_deps.add(pair);
		}
//		System.out.println("updated is " + data_deps);
		if (data_deps!=null)
			data_map.put(step, data_deps);
		return UpdatedDataDeps;		
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
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void PrintFinalResultAll(TestCase tc, String basePath, String projectName, String bugID, Trace newTrace, Trace oldTrace, 
			List<TraceNode> new_visited, List<TraceNode> old_visited, List<TraceNode> new_kept, List<TraceNode> old_kept, 
			List<TraceNode> new_retained, List<TraceNode> old_retained, HashMap<Integer, List<TraceNode>> newDataBlockNodes, 
			HashMap<Integer, List<TraceNode>> oldDataBlockNodes, HashMap<Integer, List<TraceNode>> newCtlBlockNodes, 
			HashMap<Integer, List<TraceNode>> oldCtlBlockNodes, int oldTraceTime, int newTraceTime, int codeTime, 
			int traceTime, int dualTime, int inPreSSTime, HashMap<Integer, Integer> oldChangeChunkInfo, 
			HashMap<Integer, Integer> newChangeChunkInfo,HashMap<Integer, Integer> oldTestCaseChunkInfo, HashMap<Integer, Integer> newTestCaseChunkInfo, 
			HashMap<Integer, Integer> oldCommonChunkInfo, HashMap<Integer, Integer> newCommonChunkInfo,
			int oldRetainedTestRemovedByDual, int newRetainedTestRemovedByDual) {
		
//		System.out.println("Old trace size is " + oldTrace.getExecutionList().size());
//		System.out.println("New trace size is " + newTrace.getExecutionList().size());
//		System.out.println("Old dual size is " + old_visited.size());
//		System.out.println("New dual size is " + new_visited.size());
//		System.out.println("Old retained size (removing test that are removed by DS) is " + old_retained.size());
//		System.out.println("New retained size (removing test that are removed by DS) is " + new_retained.size());
//		System.out.println("Old InPreSS size (removing test that are removed by DS) is " + old_kept.size());
//		System.out.println("New InPreSS size (removing test that are removed by DS) is " + new_kept.size());
		
//		int oldAllRetained = old_retained.size()-oldRetainedTestRemovedByDual;
//		int newAllRetained = new_retained.size()-newRetainedTestRemovedByDual;
//		int oldAllinPreSSRetained = old_kept.size() - oldRetainedTestRemovedByDual;
//		int newAllinPreSSRetained = new_kept.size() - newRetainedTestRemovedByDual;
		int oldAllRetained = old_retained.size();
		int newAllRetained = new_retained.size();
		int oldAllinPreSSRetained = old_kept.size();
		int newAllinPreSSRetained = new_kept.size();
//		System.out.println("Old retained size (removing test that are removed by DS) is " + oldAllRetained);
//		System.out.println("New retained size (removing test that are removed by DS) is " + newAllRetained);
//		System.out.println("Old inPreSS size (removing test that are removed by DS) is " + oldAllinPreSSRetained);
//		System.out.println("New inPreSS size (removing test that are removed by DS) is " + newAllinPreSSRetained);
		
	//	int OldTraceSourceSize = getTheSourceSize(oldTrace.getExecutionList());
	//	int NewTraceSourceSize = getTheSourceSize(newTrace.getExecutionList());
	//	int OldDualSourceSize = getTheSourceSize(old_visited);
	//	int NewDualSourceSize = getTheSourceSize(new_visited);
	//	int OldRetainedSourceSize = getTheSourceSize(old_retained);
	//	int NewRetainedSourceSize = getTheSourceSize(new_retained);
	//	int OldinPreSSSourceSize = getTheSourceSize(old_kept);
	//	int NewinPreSSSourceSize = getTheSourceSize(new_kept);
	//	
	//	System.out.println("Old trace size (source-level) is " + OldTraceSourceSize);
	//	System.out.println("New trace size (source-level) is " + NewTraceSourceSize);
	//	System.out.println("Old dual size (source-level) is " + OldDualSourceSize);
	//	System.out.println("New dual size (source-level) is " + NewDualSourceSize);
	//	System.out.println("Old retained size (source-level) is " + OldRetainedSourceSize);
	//	System.out.println("New retained size (source-level) is " + NewRetainedSourceSize);
	//	System.out.println("Old inPreSS size (source-level) is " + OldinPreSSSourceSize);
	//	System.out.println("New inPreSS size (source-level) is " + NewinPreSSSourceSize);
//		
//		System.out.println("Old #Data B is " + oldDataBlockNodes.keySet().size());
//		System.out.println("New #Data B is " + newDataBlockNodes.keySet().size());
//		System.out.println("Old #Control B is " + oldCtlBlockNodes.keySet().size());
//		System.out.println("New #Control B is " + newCtlBlockNodes.keySet().size());
//		System.out.println("old trace time is " + oldTraceTime);
//		System.out.println("new trace time is " + newTraceTime);
//		System.out.println("code diff " + codeTime);
//		System.out.println("trace diff " + traceTime);
//		System.out.println("dual time is " + dualTime);
//		System.out.println("inPreSS time is " + inPreSSTime);
	    
		String results = basePath+"/results/"+projectName+"Detailed.xlsx";
	    File tempFile = new File(results);
	    boolean FirstTime = false;
	    if (!tempFile.exists()) {//For the first time
	        FirstTime=true;
	        XSSFWorkbook workbook = new XSSFWorkbook();
	        XSSFSheet sheet = workbook.createSheet("stats");
	        try (FileOutputStream outputStream = new FileOutputStream(results)) {
	            workbook.write(outputStream);
	        } catch (Exception e) {
	        }
	    }
	
	    double sum = 0.0;
	    for(Integer loc:oldChangeChunkInfo.keySet()) {
	    	sum += oldChangeChunkInfo.get(loc);
	    }
	    double avg = sum/(double)oldChangeChunkInfo.keySet().size();
	    double oldLocation = avg/(double)oldTrace.getExecutionList().size();
	    int oldChangedStamts = getChanges(old_retained, tc);
	    
	    sum = 0.0;
	    for(Integer loc:newChangeChunkInfo.keySet()) {
	    	sum += newChangeChunkInfo.get(loc);
	    }
	    avg = sum/(double)newChangeChunkInfo.keySet().size();
	    double newLocation = avg/(double)newTrace.getExecutionList().size();
	    int newChangedStamts = getChanges(new_retained, tc);
	    	
	    double oldCommonBlockAvg = 0.0;
	    double oldCommonBlockMax = -1000000.0;
	    double oldCommonBlockMin = 100000.0;
	    double oldCommonBlockSum = 0.0;
		for (Integer blockID :oldCommonChunkInfo.keySet()) {
			Integer noOfStmts = oldCommonChunkInfo.get(blockID);
			if(noOfStmts!=null) {
				oldCommonBlockSum = oldCommonBlockSum + noOfStmts;
				if (oldCommonBlockMax<noOfStmts)
					oldCommonBlockMax = noOfStmts;
				if (oldCommonBlockMin>noOfStmts)
					oldCommonBlockMin = noOfStmts;
			}			
		}
		oldCommonBlockAvg = oldCommonBlockSum/oldCommonChunkInfo.keySet().size();
//		System.out.println("Old Common block size (sum): " + oldCommonBlockSum);
//		System.out.println("Old dCommon block size (avg) " + oldCommonBlockAvg);
//		System.out.println("Old Common block size (min): " + oldCommonBlockMin);
//		System.out.println("Old Common block size (max) " + oldCommonBlockMax);
		
	    double newCommonBlockAvg = 0.0;
	    double newCommonBlockMax = -1000000.0;
	    double newCommonBlockMin = 100000.0;
	    double newCommonBlockSum = 0.0;
		for (Integer blockID :newCommonChunkInfo.keySet()) {
			Integer noOfStmts = newCommonChunkInfo.get(blockID);
			if(noOfStmts!=null) {
				newCommonBlockSum = newCommonBlockSum + noOfStmts;
				if (newCommonBlockMax<noOfStmts)
					newCommonBlockMax = noOfStmts;
				if (newCommonBlockMin>noOfStmts)
					newCommonBlockMin = noOfStmts;
			}			
		}
		newCommonBlockAvg = newCommonBlockSum/newCommonChunkInfo.keySet().size();
//		System.out.println("New Common block size (sum): " + newCommonBlockSum);
//		System.out.println("New dCommon block size (avg) " + newCommonBlockAvg);
//		System.out.println("New Common block size (min): " + newCommonBlockMin);
//		System.out.println("New Common block size (max) " + newCommonBlockMax);
//		
		//calculating #B, avg, max of data blocks on dual slice
	    double oldDATDualAvg = 0.0;
	    double oldDATDualMax = -1000000.0;
	    double oldDATDualMin = 100000.0;
	    double oldDATDualSum = 0.0;
		for (Integer block :oldDataBlockNodes.keySet()) {
			List<TraceNode> nodes = oldDataBlockNodes.get(block);
			if(nodes!=null) {
				oldDATDualSum = oldDATDualSum + nodes.size();
				if (oldDATDualMax<nodes.size())
					oldDATDualMax = nodes.size();
				if (oldDATDualMin>nodes.size())
					oldDATDualMin = nodes.size();
			}			
		}
		oldDATDualAvg = oldDATDualSum/oldDataBlockNodes.keySet().size();
//		System.out.println("Old data dual block size (sum): " + oldDATDualSum);
//		System.out.println("Old data dual block size (avg) " + oldDATDualAvg);
//		System.out.println("Old data dual block size (min): " + oldDATDualMin);
//		System.out.println("Old data dual block size (max) " + oldDATDualMax);
		
		double newDATDualAvg = 0.0;
	    double newDATDualMax = -100000.0;
	    double newDATDualMin = 100000.0;
	    double newDATDualSum = 0.0;
		for (Integer block :newDataBlockNodes.keySet()) {
			List<TraceNode> nodes = newDataBlockNodes.get(block);
			if(nodes!=null) {
				newDATDualSum = newDATDualSum + nodes.size();
				if (newDATDualMax<nodes.size())
					newDATDualMax = nodes.size();
				if (newDATDualMin>nodes.size())
					newDATDualMin = nodes.size();
			}			
		}
		newDATDualAvg = newDATDualSum/newDataBlockNodes.keySet().size();
//		System.out.println("New data dual block size (sum): " + newDATDualSum);
//		System.out.println("New data dual block size (avg) " + newDATDualAvg);
//		System.out.println("New data dual block size (min): " + newDATDualMin);
//		System.out.println("New data dual block size (max) " + newDATDualMax);
		
		//calculating #B, avg, max of data blocks on dual slice
		double oldDATinPreSSAvg = 0.0;
		double oldDATinPreSSMax = -100000.0;
		double oldDATinPreSSMin = 100000.0;
		double oldDATinPreSSSum = 0.0;
		for (Integer block :oldDataBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = oldDataBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (old_kept.contains(node))
						size = size + 1;
				}
				oldDATinPreSSSum = oldDATinPreSSSum + size;
				if (oldDATinPreSSMax<size)
					oldDATinPreSSMax = size;
				if (oldDATinPreSSMin>size)
					oldDATinPreSSMin = size;
			}			
		}
		oldDATinPreSSAvg = oldDATinPreSSSum/oldDataBlockNodes.keySet().size();
//		System.out.println("Old data inPreSS block size (sum): " + oldDATinPreSSSum);
//		System.out.println("Old data inPreSS block size (avg) " + oldDATinPreSSAvg);
//		System.out.println("Old data inPreSS block size (min): " + oldDATinPreSSMin);
//		System.out.println("Old data inPreSS block size (max) " + oldDATinPreSSMax);
		
		double newDATinPreSSAvg = 0.0;
	    double newDATinPreSSMax = -100000.0;
	    double newDATinPreSSMin = 100000.0;
	    double newDATinPreSSSum = 0.0;
		for (Integer block :newDataBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = newDataBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (new_kept.contains(node))
						size = size + 1;
				}
				newDATinPreSSSum = newDATinPreSSSum + size;
				if (newDATinPreSSMax<size)
					newDATinPreSSMax = size;
				if (newDATinPreSSMin>size)
					newDATinPreSSMin = size;
			}			
		}
		newDATinPreSSAvg = newDATinPreSSSum/newDataBlockNodes.keySet().size();
//		System.out.println("New data inPreSS block size (sum): " + newDATinPreSSSum);
//		System.out.println("New data inPreSS block size (avg) " + newDATinPreSSAvg);
//		System.out.println("New data inPreSS block size (min): " + newDATinPreSSMin);
//		System.out.println("New datat inPreSS block size (max) " + newDATinPreSSMax);
		
		///////////////////////////////
		double oldCTLDualAvg = 0.0;
		double oldCTLDualMax = -1000000.0;
		double oldCTLDualMin = 100000.0;
		double oldCTLDualSum = 0.0;
		for (Integer block :oldCtlBlockNodes.keySet()) {
			List<TraceNode> nodes = oldCtlBlockNodes.get(block);
			if(nodes!=null) {
				oldCTLDualSum = oldCTLDualSum + nodes.size();
				if (oldCTLDualMax<nodes.size())
					oldCTLDualMax = nodes.size();
				if (oldCTLDualMin>nodes.size())
					oldCTLDualMin = nodes.size();
			}			
		}
		oldCTLDualAvg = oldCTLDualSum/oldCtlBlockNodes.keySet().size();
//		System.out.println("Old ctl dual block size (sum): " + oldCTLDualSum);
//		System.out.println("Old ctl dual block size (avg) " + oldCTLDualAvg);
//		System.out.println("Old ctl dual block size (min): " + oldCTLDualMin);
//		System.out.println("Old ctl dual block size (max) " + oldCTLDualMax);
		
		double newCTLDualAvg = 0.0;
		double newCTLDualMax = -100000.0;
		double newCTLDualMin = 100000.0;
		double newCTLDualSum = 0.0;
		for (Integer block :newCtlBlockNodes.keySet()) {
			List<TraceNode> nodes = newCtlBlockNodes.get(block);
			if(nodes!=null) {
				newCTLDualSum = newCTLDualSum + nodes.size();
				if (newCTLDualMax<nodes.size())
					newCTLDualMax = nodes.size();
				if (newCTLDualMin>nodes.size())
					newCTLDualMin = nodes.size();
			}			
		}
		newCTLDualAvg = newCTLDualSum/newCtlBlockNodes.keySet().size();
//		System.out.println("New ctl dual block size (sum): " + newCTLDualSum);
//		System.out.println("New ctl dual block size (avg) " + newCTLDualAvg);
//		System.out.println("New ctl dual block size (min): " + newCTLDualMin);
//		System.out.println("New ctl dual block size (max) " + newCTLDualMax);
		
		//calculating #B, avg, max of data blocks on dual slice
		double oldCTLinPreSSAvg = 0.0;
		double oldCTLinPreSSMax = -100000.0;
		double oldCTLinPreSSMin = 100000.0;
		double oldCTLinPreSSSum = 0.0;
		for (Integer block :oldCtlBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = oldCtlBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (old_kept.contains(node))
						size = size + 1;
				}
				oldCTLinPreSSSum = oldCTLinPreSSSum + size;
				if (oldCTLinPreSSMax<size)
					oldCTLinPreSSMax = size;
				if (oldCTLinPreSSMin>size)
					oldCTLinPreSSMin = size;
			}			
		}
		oldCTLinPreSSAvg = oldCTLinPreSSSum/oldCtlBlockNodes.keySet().size();
//		System.out.println("Old ctl inPreSS block size (sum): " + oldCTLinPreSSSum);
//		System.out.println("Old ctl inPreSS block size (avg) " + oldCTLinPreSSAvg);
//		System.out.println("Old ctl inPreSS block size (min): " + oldCTLinPreSSMin);
//		System.out.println("Old ctl inPreSS block size (max) " + oldCTLinPreSSMax);
		
		double newCTLinPreSSAvg = 0.0;
	    double newCTLinPreSSMax = -100000.0;
	    double newCTLinPreSSMin = 100000.0;
	    double newCTLinPreSSSum = 0.0;
		for (Integer block :newCtlBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = newCtlBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (new_kept.contains(node))
						size = size + 1;
				}
				newCTLinPreSSSum = newCTLinPreSSSum + size;
				if (newCTLinPreSSMax<size)
					newCTLinPreSSMax = size;
				if (newCTLinPreSSMin>size)
					newCTLinPreSSMin = size;
			}			
		}
		newCTLinPreSSAvg = newCTLinPreSSSum/newCtlBlockNodes.keySet().size();
//		System.out.println("New ctl inPreSS block size (sum): " + newCTLinPreSSSum);
//		System.out.println("New ctl inPreSS block size (avg) " + newCTLinPreSSAvg);
//		System.out.println("New ctl inPreSS block size (min): " + newCTLinPreSSMin);
//		System.out.println("New ctl inPreSS block size (max) " + newCTLinPreSSMax);
		
	    if (FirstTime) {
	    	
	        String[] header = {"Bug ID", 
	        		"Old trace size", "New trace size", "Old Dual size", "New Dual size", 
	        		"Old No. Change Chunks", "Old Avg. Location of changes chunks in Trace", "Old No Changed Stmts", 
	        		"Old No. Test Chunks", "Old No. Test Stmts","old all retained size", "old all retained size (keeping all tests even not kept by DS)",
	        		"New No. Change Chunks", "New Avg. Location of changes chunks in Trace", "New No Changed Stmts", 
	        		"New No. Test Chunks", "New No. Test Stmts","new all retained size", "new all retained size (keeping all tests even not kept by DS)",
	        		"Old # Common B", "New # Common B",
	        		"old Common block (sum)","old Common block (avg)","old Common block (min)","old Common block (max)",
	        		"new Common block (sum)","new Common block (avg)","new Common block (min)","new Common block (max)",
	        		"Old InPreSS size", "New InPreSS size", 
	        		"Old InPreSS size (keeping all tests even not kept by DS)", "New InPreSS size (keeping all tests even not kept by DS)", 
	        		"Old #Data B", "New #Data B", "Old #Control B", "New #Control B", 
	        		 "old data block Dual (sum)","old data block Dual (avg)","old data block Dual (min)","old data block Dual (max)",
	        		 "new data block Dual (sum)","new data block Dual (avg)","new data block Dual (min)","new data block Dual (max)",
	        		 "old ctl block Dual (sum)","old ctl block Dual (avg)","old ctl block Dual (min)","old ctl block Dual (max)",
	        		 "new ctl block Dual (sum)","new ctl block Dual (avg)","new ctl block Dual (min)","new ctl block Dual (max)",
	        		 "old data block inPreSS (sum)","old data block inPreSS (avg)","old data block inPreSS (min)","old data block inPreSS (max)",
	        		 "new data block inPreSS (sum)","new data block inPreSS (avg)","new data block inPreSS (min)","new data block inPreSS (max)",
	        		 "old ctl block inPreSS (sum)","old ctl block inPreSS (avg)","old ctl block inPreSS (min)","old ctl block inPreSS (max)",
	        		 "new ctl block inPreSS (sum)","new ctl block inPreSS (avg)","new ctl block inPreSS (min)","new ctl block inPreSS (max)",
	        		 "old trace time", "new trace time", 
	        		 "code diff time", "trace diff time", "dual time", "inPreSS time" 
	        		 };
	        WriteToExcel(results,header, "stats",false,true);
	    }
	    String[] data = {bugID, 
	    		String.valueOf(oldTrace.getExecutionList().size()), String.valueOf(newTrace.getExecutionList().size()), 
	    		String.valueOf(old_visited.size()), String.valueOf(new_visited.size()), 
	    		String.valueOf(oldChangeChunkInfo.keySet().size()), String.valueOf(oldLocation), String.valueOf(oldChangedStamts),
	    		String.valueOf(oldTestCaseChunkInfo.keySet().size()), String.valueOf(old_retained.size()-oldChangedStamts), 
	    		String.valueOf(oldAllRetained), String.valueOf(old_retained.size()),
	    		String.valueOf(newChangeChunkInfo.keySet().size()), String.valueOf(newLocation), String.valueOf(newChangedStamts),
	    		String.valueOf(newTestCaseChunkInfo.keySet().size()), String.valueOf(new_retained.size()-newChangedStamts), 
	    		String.valueOf(newAllRetained), String.valueOf(new_retained.size()),
	    		String.valueOf(oldCommonChunkInfo.keySet().size()), String.valueOf(newCommonChunkInfo.keySet().size()),
	    		String.valueOf(oldCommonBlockSum),String.valueOf(oldCommonBlockAvg),String.valueOf(oldCommonBlockMin),String.valueOf(oldCommonBlockMax),
	    		String.valueOf(newCommonBlockSum),String.valueOf(newCommonBlockAvg),String.valueOf(newCommonBlockMin),String.valueOf(newCommonBlockMax),
	    		String.valueOf(oldAllinPreSSRetained), String.valueOf(newAllinPreSSRetained),
	    		String.valueOf(old_kept.size()), String.valueOf(new_kept.size()), 		
	    		String.valueOf(oldDataBlockNodes.keySet().size()), String.valueOf(newDataBlockNodes.keySet().size()),
	    		String.valueOf(oldCtlBlockNodes.keySet().size()), String.valueOf(newCtlBlockNodes.keySet().size()),
	    		String.valueOf(oldDATDualSum),String.valueOf(oldDATDualAvg),String.valueOf(oldDATDualMin),String.valueOf(oldDATDualMax),
	    		String.valueOf(newDATDualSum),String.valueOf(newDATDualAvg),String.valueOf(newDATDualMin),String.valueOf(newDATDualMax),
	    		String.valueOf(oldCTLDualSum),String.valueOf(oldCTLDualAvg),String.valueOf(oldCTLDualMin),String.valueOf(oldCTLDualMax),
	    		String.valueOf(newCTLDualSum),String.valueOf(newCTLDualAvg),String.valueOf(newCTLDualMin),String.valueOf(newCTLDualMax),
	    		String.valueOf(oldDATinPreSSSum),String.valueOf(oldDATinPreSSAvg),String.valueOf(oldDATinPreSSMin),String.valueOf(oldDATinPreSSMax),
	    		String.valueOf(newDATinPreSSSum),String.valueOf(newDATinPreSSAvg),String.valueOf(newDATinPreSSMin),String.valueOf(newDATinPreSSMax),
	    		String.valueOf(oldCTLinPreSSSum),String.valueOf(oldCTLinPreSSAvg),String.valueOf(oldCTLinPreSSMin),String.valueOf(oldCTLinPreSSMax),
	    		String.valueOf(newCTLinPreSSSum),String.valueOf(newCTLinPreSSAvg),String.valueOf(newCTLinPreSSMin),String.valueOf(newCTLinPreSSMax),
	    		String.valueOf(oldTraceTime),String.valueOf(newTraceTime),
	    		String.valueOf(codeTime), String.valueOf(traceTime), String.valueOf(dualTime),String.valueOf(inPreSSTime)
	    		};
	    WriteToExcel(results,data, "stats",false,false);
		
		
		System.out.println("##############Final Results##############");
		
	}
	private void PrintPaperResults(TestCase tc, String basePath, String projectName, String bugID, Trace newTrace, Trace oldTrace, 
			List<TraceNode> new_visited, List<TraceNode> old_visited, List<TraceNode> new_kept, List<TraceNode> old_kept, 
			List<TraceNode> new_retained, List<TraceNode> old_retained, HashMap<Integer, List<TraceNode>> newDataBlockNodes, 
			HashMap<Integer, List<TraceNode>> oldDataBlockNodes, HashMap<Integer, List<TraceNode>> newCtlBlockNodes, 
			HashMap<Integer, List<TraceNode>> oldCtlBlockNodes, int oldTraceTime, int newTraceTime, int codeTime, 
			int traceTime, int dualTime, int InPreSSTime, HashMap<Integer, Integer> oldChangeChunkInfo, HashMap<Integer, Integer> newChangeChunkInfo, 
			HashMap<Integer, Integer> oldTestCaseChunkInfo, HashMap<Integer, Integer> newTestCaseChunkInfo, 
			HashMap<Integer, Integer> oldCommonChunkInfo, HashMap<Integer, Integer> newCommonChunkInfo,
			int oldRetainedTestRemovedByDual, int newRetainedTestRemovedByDual,List<String> old_kept_sourceCodeLevel, List<String> new_kept_sourceCodeLevel) throws IOException {
		  
			Path path = Paths.get(basePath+"/results");
			if(!Files.exists(path)) 
				new File(basePath+"/results").mkdirs();
			path = Paths.get(basePath+"/results/"+projectName);
			if(!Files.exists(path)) 
				new File(basePath+"/results/"+projectName).mkdirs();
			
			String results = basePath+"/results/"+projectName+"/"+bugID+".xlsx";
		    File tempFile = new File(results);
		    boolean FirstTime = false;
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
			double oldReduction = (Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(old_visited.size()))/(Double.valueOf(oldTrace.getExecutionList().size()))*100.0;
			double newReduction = (Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(new_visited.size()))/(Double.valueOf(newTrace.getExecutionList().size()))*100.0;
		    if (!tempFile.exists()) {
		        FirstTime=true;
		        XSSFWorkbook workbook = new XSSFWorkbook();
		        XSSFSheet sheet = workbook.createSheet("Table II");
		        try {
		        	FileOutputStream outputStream = new FileOutputStream(results);
		            workbook.write(outputStream);
		            workbook.close();
		        	outputStream.close();
		        } catch (Exception e) {
		        }
		    }		
	
            if (FirstTime) {		    	
		        String[] header = {"Bug ID", 
		        		"Old trace size (#T)","Old Dual size(#DSlice)", "%Reduction", "#Chg", 
		        		"New trace size (#T)","New Dual size(#DSlice)", "%Reduction", "#Chg", 	        		
		        		 };
		        WriteToExcel(results, header, "Table II",false, true);
		    }
		    String[] data = {bugID, 
		    		String.valueOf(oldTrace.getExecutionList().size()), String.valueOf(old_visited.size()), String.valueOf(oldReduction), String.valueOf(oldChangeChunkInfo.keySet().size()),
		    		String.valueOf(newTrace.getExecutionList().size()), String.valueOf(new_visited.size()), String.valueOf(newReduction), String.valueOf(newChangeChunkInfo.keySet().size())		    	   
		    		};
		    WriteToExcel(results,data,"Table II",false, false);
			
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
		    oldReduction = (Double.valueOf(old_visited.size())-Double.valueOf(old_kept.size()))/(Double.valueOf(old_visited.size()))*100.0;
			newReduction = (Double.valueOf(new_visited.size())-Double.valueOf(new_kept.size()))/(Double.valueOf(new_visited.size()))*100.0;
			
		    if (FirstTime) {		    	
		        String[] header = {"Bug ID", 
		        		"Old Dual size(#DSlice)", "Old InPreSS size(#InPreSS)", "%Reduction", 
		        		"New Dual size(#DSlice)", "New InPreSS size(#InPreSS)", "%Reduction",
		        		"DSlice Time (Min)", "InPreSS Time (Min)"};
		        WriteToExcel(results, header, "RQ1",true,true);
		    }
		    String[] detailedData = {bugID, 
		    		String.valueOf(old_visited.size()), String.valueOf(old_kept.size()), String.valueOf(oldReduction), 
		    		String.valueOf(new_visited.size()), String.valueOf(new_kept.size()), String.valueOf(newReduction), 
		    		String.valueOf((Double.valueOf(dualTime)/1000.0)/60.0), String.valueOf((Double.valueOf(InPreSSTime)/1000.0)/60.0)
		    		};
		       WriteToExcel(results,detailedData,"RQ1",true,false);
	
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######

		    
		    if (FirstTime) {		    	
		        String[] header = {"Bug ID", 
		        		"# Old mathched block", "Avg.", "Max", "%Reduction", 
		        		"# Old unmathched block", "Avg.", "Max", "%Reduction", 
		        		"# New mathched block", "Avg.", "Max", "%Reduction", 
		        		"# New unmathched block", "Avg.", "Max", "%Reduction", 
		        		};
		        WriteToExcel(results, header, "RQ2",true,true);
		    }
		    
		    
		 		       
		    double sum = 0.0;
		    for(Integer loc:oldChangeChunkInfo.keySet()) {
		    	sum += oldChangeChunkInfo.get(loc);
		    }
		    double avg = sum/(double)oldChangeChunkInfo.keySet().size();
		    double oldLocation = avg/(double)oldTrace.getExecutionList().size();
		    int oldChangedStamts = getChanges(old_retained, tc);
		    
		    sum = 0.0;
		    for(Integer loc:newChangeChunkInfo.keySet()) {
		    	sum += newChangeChunkInfo.get(loc);
		    }
		    avg = sum/(double)newChangeChunkInfo.keySet().size();
		    double newLocation = avg/(double)newTrace.getExecutionList().size();
		    int newChangedStamts = getChanges(new_retained, tc);
		    
		    double oldCommonBlockAvg = 0.0;
		    double oldCommonBlockMax = -1000000.0;
		    double oldCommonBlockMin = 100000.0;
		    double oldCommonBlockSum = 0.0;
			for (Integer blockID :oldCommonChunkInfo.keySet()) {
				Integer noOfStmts = oldCommonChunkInfo.get(blockID);
				if(noOfStmts!=null) {
					oldCommonBlockSum = oldCommonBlockSum + noOfStmts;
					if (oldCommonBlockMax<noOfStmts)
						oldCommonBlockMax = noOfStmts;
					if (oldCommonBlockMin>noOfStmts)
						oldCommonBlockMin = noOfStmts;
				}			
			}
			oldCommonBlockAvg = oldCommonBlockSum/oldCommonChunkInfo.keySet().size();

			
		    double newCommonBlockAvg = 0.0;
		    double newCommonBlockMax = -1000000.0;
		    double newCommonBlockMin = 100000.0;
		    double newCommonBlockSum = 0.0;
			for (Integer blockID :newCommonChunkInfo.keySet()) {
				Integer noOfStmts = newCommonChunkInfo.get(blockID);
				if(noOfStmts!=null) {
					newCommonBlockSum = newCommonBlockSum + noOfStmts;
					if (newCommonBlockMax<noOfStmts)
						newCommonBlockMax = noOfStmts;
					if (newCommonBlockMin>noOfStmts)
						newCommonBlockMin = noOfStmts;
				}			
			}
			newCommonBlockAvg = newCommonBlockSum/newCommonChunkInfo.keySet().size();

			
		    	
			//calculating #B, avg, max of data blocks on dual slice
		    double oldDATDualAvg = 0.0;
		    double oldDATDualMax = -1000000.0;
		    double oldDATDualMin = 100000.0;
		    double oldDATDualSum = 0.0;
			for (Integer block :oldDataBlockNodes.keySet()) {
				List<TraceNode> nodes = oldDataBlockNodes.get(block);
				if(nodes!=null) {
					oldDATDualSum = oldDATDualSum + nodes.size();
					if (oldDATDualMax<nodes.size())
						oldDATDualMax = nodes.size();
					if (oldDATDualMin>nodes.size())
						oldDATDualMin = nodes.size();
				}			
			}
			oldDATDualAvg = oldDATDualSum/oldDataBlockNodes.keySet().size();

			
			double newDATDualAvg = 0.0;
		    double newDATDualMax = -100000.0;
		    double newDATDualMin = 100000.0;
		    double newDATDualSum = 0.0;
			for (Integer block :newDataBlockNodes.keySet()) {
				List<TraceNode> nodes = newDataBlockNodes.get(block);
				if(nodes!=null) {
					newDATDualSum = newDATDualSum + nodes.size();
					if (newDATDualMax<nodes.size())
						newDATDualMax = nodes.size();
					if (newDATDualMin>nodes.size())
						newDATDualMin = nodes.size();
				}			
			}
			newDATDualAvg = newDATDualSum/newDataBlockNodes.keySet().size();

			
			//calculating #B, avg, max of data blocks on dual slice
			double oldDATInPreSSAvg = 0.0;
			double oldDATInPreSSMax = -100000.0;
			double oldDATInPreSSMin = 100000.0;
			double oldDATInPreSSSum = 0.0;
			for (Integer block :oldDataBlockNodes.keySet()) {
				int size = 0;
				List<TraceNode> nodes = oldDataBlockNodes.get(block);
				if(nodes!=null) {
					for (TraceNode node: nodes) {
						if (old_kept.contains(node))
							size = size + 1;
					}
					oldDATInPreSSSum = oldDATInPreSSSum + size;
					if (oldDATInPreSSMax<size)
						oldDATInPreSSMax = size;
					if (oldDATInPreSSMin>size)
						oldDATInPreSSMin = size;
				}			
			}
			oldDATInPreSSAvg = oldDATInPreSSSum/oldDataBlockNodes.keySet().size();

			
			double newDATInPreSSAvg = 0.0;
		    double newDATInPreSSMax = -100000.0;
		    double newDATInPreSSMin = 100000.0;
		    double newDATInPreSSSum = 0.0;
			for (Integer block :newDataBlockNodes.keySet()) {
				int size = 0;
				List<TraceNode> nodes = newDataBlockNodes.get(block);
				if(nodes!=null) {
					for (TraceNode node: nodes) {
						if (new_kept.contains(node))
							size = size + 1;
					}
					newDATInPreSSSum = newDATInPreSSSum + size;
					if (newDATInPreSSMax<size)
						newDATInPreSSMax = size;
					if (newDATInPreSSMin>size)
						newDATInPreSSMin = size;
				}			
			}
			newDATInPreSSAvg = newDATInPreSSSum/newDataBlockNodes.keySet().size();

			
			///////////////////////////////
			double oldCTLDualAvg = 0.0;
			double oldCTLDualMax = -1000000.0;
			double oldCTLDualMin = 100000.0;
			double oldCTLDualSum = 0.0;
			for (Integer block :oldCtlBlockNodes.keySet()) {
				List<TraceNode> nodes = oldCtlBlockNodes.get(block);
				if(nodes!=null) {
					oldCTLDualSum = oldCTLDualSum + nodes.size();
					if (oldCTLDualMax<nodes.size())
						oldCTLDualMax = nodes.size();
					if (oldCTLDualMin>nodes.size())
						oldCTLDualMin = nodes.size();
				}			
			}
			oldCTLDualAvg = oldCTLDualSum/oldCtlBlockNodes.keySet().size();

			
			double newCTLDualAvg = 0.0;
			double newCTLDualMax = -100000.0;
			double newCTLDualMin = 100000.0;
			double newCTLDualSum = 0.0;
			for (Integer block :newCtlBlockNodes.keySet()) {
				List<TraceNode> nodes = newCtlBlockNodes.get(block);
				if(nodes!=null) {
					newCTLDualSum = newCTLDualSum + nodes.size();
					if (newCTLDualMax<nodes.size())
						newCTLDualMax = nodes.size();
					if (newCTLDualMin>nodes.size())
						newCTLDualMin = nodes.size();
				}			
			}
			newCTLDualAvg = newCTLDualSum/newCtlBlockNodes.keySet().size();

			
			//calculating #B, avg, max of data blocks on dual slice
			double oldCTLInPreSSAvg = 0.0;
			double oldCTLInPreSSMax = -100000.0;
			double oldCTLInPreSSMin = 100000.0;
			double oldCTLInPreSSSum = 0.0;
			for (Integer block :oldCtlBlockNodes.keySet()) {
				int size = 0;
				List<TraceNode> nodes = oldCtlBlockNodes.get(block);
				if(nodes!=null) {
					for (TraceNode node: nodes) {
						if (old_kept.contains(node))
							size = size + 1;
					}
					oldCTLInPreSSSum = oldCTLInPreSSSum + size;
					if (oldCTLInPreSSMax<size)
						oldCTLInPreSSMax = size;
					if (oldCTLInPreSSMin>size)
						oldCTLInPreSSMin = size;
				}			
			}
			oldCTLInPreSSAvg = oldCTLInPreSSSum/oldCtlBlockNodes.keySet().size();

			
			double newCTLInPreSSAvg = 0.0;
		    double newCTLInPreSSMax = -100000.0;
		    double newCTLInPreSSMin = 100000.0;
		    double newCTLInPreSSSum = 0.0;
			for (Integer block :newCtlBlockNodes.keySet()) {
				int size = 0;
				List<TraceNode> nodes = newCtlBlockNodes.get(block);
				if(nodes!=null) {
					for (TraceNode node: nodes) {
						if (new_kept.contains(node))
							size = size + 1;
					}
					newCTLInPreSSSum = newCTLInPreSSSum + size;
					if (newCTLInPreSSMax<size)
						newCTLInPreSSMax = size;
					if (newCTLInPreSSMin>size)
						newCTLInPreSSMin = size;
				}			
			}
			newCTLInPreSSAvg = newCTLInPreSSSum/newCtlBlockNodes.keySet().size();		
		    
		    double reducOldData =  (Double.valueOf(old_visited.size())-(old_retained.size()+oldCTLDualSum+oldDATInPreSSSum))/(Double.valueOf(old_visited.size()))*100.0;
		    double reducOldCTL =  (Double.valueOf(old_visited.size())-(old_retained.size()+oldDATDualSum+oldCTLInPreSSSum))/(Double.valueOf(old_visited.size()))*100.0;
		    double reducNewData =  (Double.valueOf(new_visited.size())-(new_retained.size()+newCTLDualSum+newDATInPreSSSum))/(Double.valueOf(new_visited.size()))*100.0;
		    double reducNewCTL =  (Double.valueOf(new_visited.size())-(new_retained.size()+newDATDualSum+newCTLInPreSSSum))/(Double.valueOf(new_visited.size()))*100.0;
		    
		    String[] detailedDataRQ2 = {bugID, 
		    		String.valueOf(oldDataBlockNodes.keySet().size()), String.valueOf(oldDATDualAvg),String.valueOf(oldDATDualMax),String.valueOf(reducOldData),
		    		String.valueOf(oldCtlBlockNodes.keySet().size()), String.valueOf(oldCTLDualAvg),String.valueOf(oldCTLDualMax) ,String.valueOf(reducOldCTL),
		    		String.valueOf(oldDataBlockNodes.keySet().size()), String.valueOf(oldDATDualAvg),String.valueOf(oldDATDualMax) ,String.valueOf(reducNewData),
		    		String.valueOf(newCtlBlockNodes.keySet().size()),String.valueOf(newCTLDualAvg),String.valueOf(newCTLDualMax), String.valueOf(reducNewCTL),};
		       WriteToExcel(results,detailedDataRQ2,"RQ2",true,false);
		    
			
//				System.out.println("##############Source code statement##############");
//				System.out.println(old_kept_sourceCodeLevel.size());
//				System.out.println(new_kept_sourceCodeLevel.size());
				System.out.println("##############Finish##############");
						
	}	
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	/////////
	private void PrintD4JPaperResults(TestCase tc, String basePath, String projectName, String bugID, Trace newTrace, Trace oldTrace, 
			List<TraceNode> new_visited, List<TraceNode> old_visited, List<TraceNode> new_kept, List<TraceNode> old_kept, 
			List<TraceNode> new_retained, List<TraceNode> old_retained, HashMap<Integer, List<TraceNode>> newDataBlockNodes, 
			HashMap<Integer, List<TraceNode>> oldDataBlockNodes, HashMap<Integer, List<TraceNode>> newCtlBlockNodes, 
			HashMap<Integer, List<TraceNode>> oldCtlBlockNodes, int oldTraceTime, int newTraceTime, int codeTime, 
			int traceTime, int dualTime, int InPreSSTime, HashMap<Integer, Integer> oldChangeChunkInfo, HashMap<Integer, Integer> newChangeChunkInfo, 
			HashMap<Integer, Integer> oldTestCaseChunkInfo, HashMap<Integer, Integer> newTestCaseChunkInfo, 
			HashMap<Integer, Integer> oldCommonChunkInfo, HashMap<Integer, Integer> newCommonChunkInfo,
			int oldRetainedTestRemovedByDual, int newRetainedTestRemovedByDual,List<String> old_kept_sourceCodeLevel, List<String> new_kept_sourceCodeLevel ) throws IOException {
		  
			Path path = Paths.get(basePath+"/results");
			if(!Files.exists(path)) 
				new File(basePath+"/results").mkdirs();
			
			String results = basePath+"/results/"+projectName+".xlsx";
		    File tempFile = new File(results);
		    boolean FirstTime = false;
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
			double oldReduction = (Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(old_visited.size()))/(Double.valueOf(oldTrace.getExecutionList().size()))*100.0;
			double newReduction = (Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(new_visited.size()))/(Double.valueOf(newTrace.getExecutionList().size()))*100.0;
		    double InPreSSoldReduction = (Double.valueOf(old_visited.size())-Double.valueOf(old_kept.size()))/(Double.valueOf(old_visited.size()))*100.0;
		    double InPreSSnewReduction = (Double.valueOf(new_visited.size())-Double.valueOf(new_kept.size()))/(Double.valueOf(new_visited.size()))*100.0;
			
			if (!tempFile.exists()) {
		        FirstTime=true;
		        XSSFWorkbook workbook = new XSSFWorkbook();
		        XSSFSheet sheet = workbook.createSheet("Table II + RQ1");
		        try {
		        	FileOutputStream outputStream = new FileOutputStream(results);
		            workbook.write(outputStream);
		            workbook.close();
		        	outputStream.close();
		        } catch (Exception e) {
		        }
		    }		
	
            if (FirstTime) {		    	
		        String[] header = {"Bug ID", 
		        		"Old trace size (#T)","Old Dual size(#DSlice)", "%Old Reduction", "#Old Chg", "Old InPreSS size(#InPreSS)", "%Old InPreSS Reduction","Old InPreSS size(Source Code leve)",
		        		"New trace size (#T)","New Dual size(#DSlice)", "%New Reduction", "#New Chg", "New InPreSS size(#InPreSS)", "%New InPreSS Reduction","New InPreSS size(Source Code leve)",
		        		"DSlice Time (Min)", "InPreSS Time (Min)"
		        		};
		        WriteToExcel(results, header, "Table II + RQ1",false, true);
		    }
		    String[] data = {bugID, 
		    		String.valueOf(oldTrace.getExecutionList().size()), String.valueOf(old_visited.size()), String.valueOf(oldReduction), String.valueOf(oldChangeChunkInfo.keySet().size()), String.valueOf(old_kept.size()), String.valueOf(InPreSSoldReduction), String.valueOf(old_kept_sourceCodeLevel.size()),
		    		String.valueOf(newTrace.getExecutionList().size()), String.valueOf(new_visited.size()), String.valueOf(newReduction), String.valueOf(newChangeChunkInfo.keySet().size()), String.valueOf(new_kept.size()), String.valueOf(InPreSSnewReduction), String.valueOf(new_kept_sourceCodeLevel.size()),
		    		String.valueOf((Double.valueOf(dualTime)/1000.0)/60.0), String.valueOf((Double.valueOf(InPreSSTime)/1000.0)/60.0)
		    		};
		    WriteToExcel(results,data,"Table II + RQ1",false, false);
						
	
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######

		    
		    if (FirstTime) {		    	
		        String[] header = {"Bug ID", 
		        		"# Old mathched block", "Old Match Avg.", "Old Match Max", "%Old Match Reduction", 
		        		"# Old unmathched block", "Old UnMatch Avg.", "Old UnMatch Max", "%Old UnMatch Reduction", 
		        		"# New mathched block", "New Match Avg.", "New Match Max", "%New Match Reduction", 
		        		"# New unmathched block", "New UnMatch Avg.", "New UnMatch Max", "%New UnMatch Reduction", 
		        		};
		        WriteToExcel(results, header, "RQ2",true,true);
		    }
		       
		 		       
		    double sum = 0.0;
		    for(Integer loc:oldChangeChunkInfo.keySet()) {
		    	sum += oldChangeChunkInfo.get(loc);
		    }
		    double avg = sum/(double)oldChangeChunkInfo.keySet().size();
		    double oldLocation = avg/(double)oldTrace.getExecutionList().size();
		    int oldChangedStamts = getChanges(old_retained, tc);
		    
		    sum = 0.0;
		    for(Integer loc:newChangeChunkInfo.keySet()) {
		    	sum += newChangeChunkInfo.get(loc);
		    }
		    avg = sum/(double)newChangeChunkInfo.keySet().size();
		    double newLocation = avg/(double)newTrace.getExecutionList().size();
		    int newChangedStamts = getChanges(new_retained, tc);
		    
		    double oldCommonBlockAvg = 0.0;
		    double oldCommonBlockMax = -1000000.0;
		    double oldCommonBlockMin = 100000.0;
		    double oldCommonBlockSum = 0.0;
			for (Integer blockID :oldCommonChunkInfo.keySet()) {
				Integer noOfStmts = oldCommonChunkInfo.get(blockID);
				if(noOfStmts!=null) {
					oldCommonBlockSum = oldCommonBlockSum + noOfStmts;
					if (oldCommonBlockMax<noOfStmts)
						oldCommonBlockMax = noOfStmts;
					if (oldCommonBlockMin>noOfStmts)
						oldCommonBlockMin = noOfStmts;
				}			
			}
			oldCommonBlockAvg = oldCommonBlockSum/oldCommonChunkInfo.keySet().size();

			
		    double newCommonBlockAvg = 0.0;
		    double newCommonBlockMax = -1000000.0;
		    double newCommonBlockMin = 100000.0;
		    double newCommonBlockSum = 0.0;
			for (Integer blockID :newCommonChunkInfo.keySet()) {
				Integer noOfStmts = newCommonChunkInfo.get(blockID);
				if(noOfStmts!=null) {
					newCommonBlockSum = newCommonBlockSum + noOfStmts;
					if (newCommonBlockMax<noOfStmts)
						newCommonBlockMax = noOfStmts;
					if (newCommonBlockMin>noOfStmts)
						newCommonBlockMin = noOfStmts;
				}			
			}
			newCommonBlockAvg = newCommonBlockSum/newCommonChunkInfo.keySet().size();

			
		    	
			//calculating #B, avg, max of data blocks on dual slice
		    double oldDATDualAvg = 0.0;
		    double oldDATDualMax = -1000000.0;
		    double oldDATDualMin = 100000.0;
		    double oldDATDualSum = 0.0;
			for (Integer block :oldDataBlockNodes.keySet()) {
				List<TraceNode> nodes = oldDataBlockNodes.get(block);
				if(nodes!=null) {
					oldDATDualSum = oldDATDualSum + nodes.size();
					if (oldDATDualMax<nodes.size())
						oldDATDualMax = nodes.size();
					if (oldDATDualMin>nodes.size())
						oldDATDualMin = nodes.size();
				}			
			}
			oldDATDualAvg = oldDATDualSum/oldDataBlockNodes.keySet().size();

			
			double newDATDualAvg = 0.0;
		    double newDATDualMax = -100000.0;
		    double newDATDualMin = 100000.0;
		    double newDATDualSum = 0.0;
			for (Integer block :newDataBlockNodes.keySet()) {
				List<TraceNode> nodes = newDataBlockNodes.get(block);
				if(nodes!=null) {
					newDATDualSum = newDATDualSum + nodes.size();
					if (newDATDualMax<nodes.size())
						newDATDualMax = nodes.size();
					if (newDATDualMin>nodes.size())
						newDATDualMin = nodes.size();
				}			
			}
			newDATDualAvg = newDATDualSum/newDataBlockNodes.keySet().size();

			
			//calculating #B, avg, max of data blocks on dual slice
			double oldDATInPreSSAvg = 0.0;
			double oldDATInPreSSMax = -100000.0;
			double oldDATInPreSSMin = 100000.0;
			double oldDATInPreSSSum = 0.0;
			for (Integer block :oldDataBlockNodes.keySet()) {
				int size = 0;
				List<TraceNode> nodes = oldDataBlockNodes.get(block);
				if(nodes!=null) {
					for (TraceNode node: nodes) {
						if (old_kept.contains(node))
							size = size + 1;
					}
					oldDATInPreSSSum = oldDATInPreSSSum + size;
					if (oldDATInPreSSMax<size)
						oldDATInPreSSMax = size;
					if (oldDATInPreSSMin>size)
						oldDATInPreSSMin = size;
				}			
			}
			oldDATInPreSSAvg = oldDATInPreSSSum/oldDataBlockNodes.keySet().size();

			
			double newDATInPreSSAvg = 0.0;
		    double newDATInPreSSMax = -100000.0;
		    double newDATInPreSSMin = 100000.0;
		    double newDATInPreSSSum = 0.0;
			for (Integer block :newDataBlockNodes.keySet()) {
				int size = 0;
				List<TraceNode> nodes = newDataBlockNodes.get(block);
				if(nodes!=null) {
					for (TraceNode node: nodes) {
						if (new_kept.contains(node))
							size = size + 1;
					}
					newDATInPreSSSum = newDATInPreSSSum + size;
					if (newDATInPreSSMax<size)
						newDATInPreSSMax = size;
					if (newDATInPreSSMin>size)
						newDATInPreSSMin = size;
				}			
			}
			newDATInPreSSAvg = newDATInPreSSSum/newDataBlockNodes.keySet().size();

			
			///////////////////////////////
			double oldCTLDualAvg = 0.0;
			double oldCTLDualMax = -1000000.0;
			double oldCTLDualMin = 100000.0;
			double oldCTLDualSum = 0.0;
			for (Integer block :oldCtlBlockNodes.keySet()) {
				List<TraceNode> nodes = oldCtlBlockNodes.get(block);
				if(nodes!=null) {
					oldCTLDualSum = oldCTLDualSum + nodes.size();
					if (oldCTLDualMax<nodes.size())
						oldCTLDualMax = nodes.size();
					if (oldCTLDualMin>nodes.size())
						oldCTLDualMin = nodes.size();
				}			
			}
			oldCTLDualAvg = oldCTLDualSum/oldCtlBlockNodes.keySet().size();

			
			double newCTLDualAvg = 0.0;
			double newCTLDualMax = -100000.0;
			double newCTLDualMin = 100000.0;
			double newCTLDualSum = 0.0;
			for (Integer block :newCtlBlockNodes.keySet()) {
				List<TraceNode> nodes = newCtlBlockNodes.get(block);
				if(nodes!=null) {
					newCTLDualSum = newCTLDualSum + nodes.size();
					if (newCTLDualMax<nodes.size())
						newCTLDualMax = nodes.size();
					if (newCTLDualMin>nodes.size())
						newCTLDualMin = nodes.size();
				}			
			}
			newCTLDualAvg = newCTLDualSum/newCtlBlockNodes.keySet().size();

			
			//calculating #B, avg, max of data blocks on dual slice
			double oldCTLInPreSSAvg = 0.0;
			double oldCTLInPreSSMax = -100000.0;
			double oldCTLInPreSSMin = 100000.0;
			double oldCTLInPreSSSum = 0.0;
			for (Integer block :oldCtlBlockNodes.keySet()) {
				int size = 0;
				List<TraceNode> nodes = oldCtlBlockNodes.get(block);
				if(nodes!=null) {
					for (TraceNode node: nodes) {
						if (old_kept.contains(node))
							size = size + 1;
					}
					oldCTLInPreSSSum = oldCTLInPreSSSum + size;
					if (oldCTLInPreSSMax<size)
						oldCTLInPreSSMax = size;
					if (oldCTLInPreSSMin>size)
						oldCTLInPreSSMin = size;
				}			
			}
			oldCTLInPreSSAvg = oldCTLInPreSSSum/oldCtlBlockNodes.keySet().size();

			
			double newCTLInPreSSAvg = 0.0;
		    double newCTLInPreSSMax = -100000.0;
		    double newCTLInPreSSMin = 100000.0;
		    double newCTLInPreSSSum = 0.0;
			for (Integer block :newCtlBlockNodes.keySet()) {
				int size = 0;
				List<TraceNode> nodes = newCtlBlockNodes.get(block);
				if(nodes!=null) {
					for (TraceNode node: nodes) {
						if (new_kept.contains(node))
							size = size + 1;
					}
					newCTLInPreSSSum = newCTLInPreSSSum + size;
					if (newCTLInPreSSMax<size)
						newCTLInPreSSMax = size;
					if (newCTLInPreSSMin>size)
						newCTLInPreSSMin = size;
				}			
			}
			newCTLInPreSSAvg = newCTLInPreSSSum/newCtlBlockNodes.keySet().size();		
		    
		    double reducOldData =  (Double.valueOf(old_visited.size())-(old_retained.size()+oldCTLDualSum+oldDATInPreSSSum))/(Double.valueOf(old_visited.size()))*100.0;
		    double reducOldCTL =  (Double.valueOf(old_visited.size())-(old_retained.size()+oldDATDualSum+oldCTLInPreSSSum))/(Double.valueOf(old_visited.size()))*100.0;
		    double reducNewData =  (Double.valueOf(new_visited.size())-(new_retained.size()+newCTLDualSum+newDATInPreSSSum))/(Double.valueOf(new_visited.size()))*100.0;
		    double reducNewCTL =  (Double.valueOf(new_visited.size())-(new_retained.size()+newDATDualSum+newCTLInPreSSSum))/(Double.valueOf(new_visited.size()))*100.0;
		    
		    String[] detailedDataRQ2 = {bugID, 
		    		String.valueOf(oldDataBlockNodes.keySet().size()), String.valueOf(oldDATDualAvg),String.valueOf(oldDATDualMax),String.valueOf(reducOldData),
		    		String.valueOf(oldCtlBlockNodes.keySet().size()), String.valueOf(oldCTLDualAvg),String.valueOf(oldCTLDualMax) ,String.valueOf(reducOldCTL),
		    		String.valueOf(oldDataBlockNodes.keySet().size()), String.valueOf(newDATDualAvg),String.valueOf(newDATDualMax) ,String.valueOf(reducNewData),
		    		String.valueOf(newCtlBlockNodes.keySet().size()),String.valueOf(newCTLDualAvg),String.valueOf(newCTLDualMax), String.valueOf(reducNewCTL),};
		       WriteToExcel(results,detailedDataRQ2,"RQ2",true,false);
		    
			
			System.out.println("##############Finish##############");
						
	}	
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	/////////
	private int getChanges(List<TraceNode> retained, TestCase tc) {
		int no = 0;
		for (int i =0; i<=retained.size()-1; i++) {
			if (isATestStatement(tc,retained.get(i))) {
				//nothing
			}
			else {
				no++;
			}
		}
		return no;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	public Slicer setupSlicing(Path root, String jarPath, Path outDir, Path sliceLogger) {
		Slicer slicer = new Slicer();
		slicer.setPathJar(jarPath);
		slicer.setOutDir(outDir.toString());
		slicer.setLoggerJar(sliceLogger.toString());
	
		slicer.setFileToParse(outDir + File.separator + "trace.log");
		slicer.setStubDroidPath(
				root.getParent().toString() + File.separator + "models" + File.separator + "summariesManual");
		slicer.setTaintWrapperPath(root.getParent().toString() + File.separator + "models" + File.separator
				+ "EasyTaintWrapperSource.txt");
		return slicer;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	public void InPreSS(String basePath, String projectName, String bugID, TestCase tc,
			int assertionLine, boolean slicer4J, String proPath, TraceNode observedFaultNode, Trace newTrace, Trace oldTrace, PairList PairList, 
			DiffMatcher matcher, int oldTraceTime, int newTraceTime, int codeTime, int traceTime,  List<RootCauseNode> rootList,boolean debug, List<TraceNode> new_visited, List<TraceNode> old_visited, List<TraceNode> new_kept, List<TraceNode> old_kept, List<TraceNode> new_retained, List<TraceNode> old_retained ) throws IOException {

		List<TraceNode> new_workList = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> new_data_map = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> new_ctl_map = new HashMap<>();

		List<TraceNode> old_workList = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> old_data_map = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> old_ctl_map = new HashMap<>();
		

		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> old_CashDeps = new HashMap<>();
		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> new_CashDeps = new HashMap<>();
		
		StepChangeTypeChecker typeChecker = new StepChangeTypeChecker(newTrace, oldTrace);
		
		//to get statistics about slice 
//		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> slice_CashDeps = new HashMap<>();
//		getSliceStats(basePath, projectName,  bugID,PairList,slice_CashDeps, observedFaultNode, newTrace,typeChecker,matcher,proPath);
		
		System.out.println("#############################");
		System.out.println("Starting Working list on Dual and InPreSS");
		if(observedFaultNode!=null) {
			new_visited.add(observedFaultNode);
			new_workList.add(observedFaultNode);
			new_kept.add(observedFaultNode);
			new_retained.add(observedFaultNode);
			
			StepChangeType changeType = typeChecker.getType(observedFaultNode, true, PairList, matcher);
			TraceNode observedFaultNodeMapping = changeType.getMatchingStep();
			if(observedFaultNodeMapping!=null) {
				old_visited.add(observedFaultNodeMapping);
				old_workList.add(observedFaultNodeMapping);
				old_kept.add(observedFaultNodeMapping);
				old_retained.add(observedFaultNodeMapping);	
			}
			else {		
				TraceNode oldObservable = getAssertionStatement(oldTrace.getExecutionList(),tc,assertionLine);
				if(oldObservable!=null) {
					old_visited.add(oldObservable);
					old_workList.add(oldObservable);
					old_kept.add(oldObservable);
					old_retained.add(oldObservable);
					changeType = typeChecker.getType(oldObservable, false, PairList, matcher);
					TraceNode observedFaultNodeMappingonNew = changeType.getMatchingStep();
					if(observedFaultNodeMappingonNew!=null) {
						if(!new_visited.contains(observedFaultNodeMappingonNew)) {
							new_visited.add(observedFaultNodeMappingonNew);
							new_workList.add(observedFaultNodeMappingonNew);
							new_kept.add(observedFaultNodeMappingonNew);
							new_retained.add(observedFaultNodeMappingonNew);
						}
					}
					else {
						TraceNode newObservable = getAssertionStatement(newTrace.getExecutionList(),tc,assertionLine);
						if(newObservable!=null) {
							if(!new_visited.contains(newObservable)) {
								new_visited.add(newObservable);
								new_workList.add(newObservable);
								new_kept.add(newObservable);
								new_retained.add(newObservable);
							}
						}
						else {
							if(!new_visited.contains(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1))) {
								new_visited.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
								new_workList.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
								new_kept.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
								new_retained.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
						    }
						}				
					}
				}
				else {
					old_visited.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
					old_workList.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
					old_kept.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
					old_retained.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
					TraceNode newObservable = getAssertionStatement(newTrace.getExecutionList(),tc,assertionLine);
					if(newObservable!=null) {
						if(!new_visited.contains(newObservable)) {
							new_visited.add(newObservable);
							new_workList.add(newObservable);
							new_kept.add(newObservable);
							new_retained.add(newObservable);
						}
					}
					else {
						if(!new_visited.contains(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1))) {
							new_visited.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
							new_workList.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
							new_kept.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
							new_retained.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
					    }
					}
				}
							
			}
		}
		else {
			TraceNode oldObservable = getAssertionStatement(oldTrace.getExecutionList(),tc,assertionLine);
			if(oldObservable!=null) {
				old_visited.add(oldObservable);
				old_workList.add(oldObservable);
				old_kept.add(oldObservable);
				old_retained.add(oldObservable);
				StepChangeType changeType = typeChecker.getType(oldObservable, false, PairList, matcher);
				TraceNode observedFaultNodeMappingonNew = changeType.getMatchingStep();
				if(observedFaultNodeMappingonNew!=null) {
					if(!new_visited.contains(observedFaultNodeMappingonNew)) {
						new_visited.add(observedFaultNodeMappingonNew);
						new_workList.add(observedFaultNodeMappingonNew);
						new_kept.add(observedFaultNodeMappingonNew);
						new_retained.add(observedFaultNodeMappingonNew);
					}
				}
				else {
					TraceNode newObservable = getAssertionStatement(newTrace.getExecutionList(),tc,assertionLine);
					if(newObservable!=null) {
						if(!new_visited.contains(newObservable)) {
							new_visited.add(newObservable);
							new_workList.add(newObservable);
							new_kept.add(newObservable);
							new_retained.add(newObservable);
						}
					}
					else {
						if(!new_visited.contains(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1))) {
							new_visited.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
							new_workList.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
							new_kept.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
							new_retained.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
					    }
					}				
				}
			}
			else {
				old_visited.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
				old_workList.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
				old_kept.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
				old_retained.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
				TraceNode newObservable = getAssertionStatement(newTrace.getExecutionList(),tc,assertionLine);
				if(newObservable!=null) {
					if(!new_visited.contains(newObservable)) {
						new_visited.add(newObservable);
						new_workList.add(newObservable);
						new_kept.add(newObservable);
						new_retained.add(newObservable);
					}
				}
				else {
					if(!new_visited.contains(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1))) {
						new_visited.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
						new_workList.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
						new_kept.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
						new_retained.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
				    }
				}
			}
						
		}
		
		
		
		Long dual_start_time = System.currentTimeMillis();
		while(!new_workList.isEmpty() || !old_workList.isEmpty()){
			while(!new_workList.isEmpty()) {
//				System.out.println("#############################");
				TraceNode step = new_workList.remove(0);
			    updateWorklist(new_CashDeps, old_CashDeps, step, newTrace, oldTrace, new_visited, new_workList,old_visited,old_workList,true,typeChecker,
			    		PairList,matcher,new_data_map,new_ctl_map, proPath,new_retained,old_retained);				
			}
			////////////////////////////////////////////////////////////////////////////////////////
			while(!old_workList.isEmpty()) {
//				System.out.println("#############################");
				TraceNode step = old_workList.remove(0);
				updateWorklist(old_CashDeps, new_CashDeps, step, oldTrace, newTrace, old_visited,old_workList,new_visited, new_workList,false,typeChecker,
						PairList,matcher,old_data_map,old_ctl_map, proPath,old_retained,new_retained);
			}			
		}
		/// ################################################################
		/// ################################################################
		Long dual_finish_time = System.currentTimeMillis();				
		int dual_Time = (int) (dual_finish_time - dual_start_time);
		
		for(int i=old_visited.size()-1;i>=0; i--){
			TraceNode step = old_visited.get(i);
			if(step==null)
				old_visited.remove(i);
		}
		for(int i=new_visited.size()-1;i>=0; i--){
			TraceNode step = new_visited.get(i);
			if(step==null)
				new_visited.remove(i);
		}	
		System.out.println("##########Finish Dual Slciing###################");
		printDualSliceResults(old_visited, false, proPath, matcher);
		printDualSliceResults(new_visited,true, proPath,matcher);
		/// ################################################################
		/// ################################################################
		HashMap<Integer, Integer> oldChangeChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newChangeChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> oldTestCaseChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newTestCaseChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> oldCommonChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newCommonChunkInfo = new HashMap<>();
//		getChangeChunks(typeChecker, matcher, old_visited,new_visited,oldChangeChunkInfo,newChangeChunkInfo);
//		getChangeChunks(typeChecker, inPreSSPairList, matcher, old_visited,new_visited,oldChangeChunkInfo,newChangeChunkInfo);
//		getTestCaseChunks(tc,old_visited,new_visited,oldTestCaseChunkInfo,newTestCaseChunkInfo);
//		getCommonBlocksChunks(typeChecker, matcher, tc,old_visited,new_visited,oldCommonChunkInfo,newCommonChunkInfo);
//		getCommonBlocksChunks(typeChecker, inPreSSPairList, matcher, tc,old_visited,new_visited,oldCommonChunkInfo,newCommonChunkInfo);
//		System.out.println("##############Printing Abstraction to Graph##############");
//		System.out.println(old_data_map);
		HashMap<TraceNode, List<Pair<TraceNode, String>>> both_new_data_map = new_data_map;
		HashMap<TraceNode, List<TraceNode>> both_new_ctl_map = new_ctl_map;
		HashMap<TraceNode, List<Pair<TraceNode, String>>> both_old_data_map = old_data_map;
		HashMap<TraceNode, List<TraceNode>> both_old_ctl_map = old_ctl_map;
		///################################################################
		///################################################################
		System.out.println("##############InPress ##############");		
//		List<TraceNode> old_retained = new ArrayList<>();		
//		List<TraceNode> new_retained = new ArrayList<>();
		List<String> old_kept_sourceCodeLevel = new ArrayList<>();		
		List<String> new_kept_sourceCodeLevel = new ArrayList<>();

//		addingClientTestNodes(tc, oldTrace.getExecutionList(), newTrace.getExecutionList(), old_kept, new_kept, old_retained, new_retained);
		//keep statements in the test that are kept in dual slice:
//		addingClientTestNodes(tc, old_visited, new_visited, old_kept, new_kept, old_retained, new_retained);
		int oldRetainedTestRemovedByDual = 0;
//		oldRetainedTestRemovedByDual = getRetainedTestRemovedByDual(tc, oldTrace.getExecutionList(),old_visited);
		int newRetainedTestRemovedByDual = 0;
//		newRetainedTestRemovedByDual = getRetainedTestRemovedByDual(tc, newTrace.getExecutionList(),new_visited);
		
		HashMap<Integer, List<TraceNode>> oldDataBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newDataBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> oldCtlBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newCtlBlockNodes = new HashMap<>();
		long inPreSS_start_time = System.currentTimeMillis();	
		inPreSSAbstractionCircleOnlySameFunctionsCommonTrianlges(tc, proPath, old_visited,new_visited,typeChecker,PairList, 
				matcher,both_old_data_map,both_old_ctl_map,both_new_data_map,both_new_ctl_map,old_kept, new_kept, 
				oldDataBlockNodes, newDataBlockNodes, oldCtlBlockNodes, newCtlBlockNodes, old_retained, new_retained,old_kept_sourceCodeLevel,new_kept_sourceCodeLevel);
		long inPreSS_finish_time = System.currentTimeMillis();			
		int inPreSS_Time = (int) (inPreSS_finish_time - inPreSS_start_time);
		for(int i=old_kept.size()-1;i>=0; i--){
			TraceNode step = old_kept.get(i);
			if(step==null)
				old_kept.remove(i);
		}
		for(int i=new_kept.size()-1;i>=0; i--){
			TraceNode step = new_kept.get(i);
			if(step==null)
				new_kept.remove(i);
		}
		System.out.println("##############Saving Results##############");	
//		if(debug)
//			PrintFinalResultAll(tc,basePath, projectName, bugID, newTrace, oldTrace, new_visited, old_visited, new_kept, old_kept, new_retained, 
//				old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
//				traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,oldTestCaseChunkInfo,newTestCaseChunkInfo, oldCommonChunkInfo, newCommonChunkInfo,oldRetainedTestRemovedByDual,newRetainedTestRemovedByDual);	
//		else {
//			if(projectName.equals("Chart")||projectName.equals("Closure")||projectName.equals("Lang")||projectName.equals("Math")||projectName.equals("Mockito")||projectName.equals("Time")||projectName.equals("Toy")) {
//				PrintD4JPaperResults(tc,basePath, projectName, bugID, newTrace, oldTrace, new_visited, old_visited, new_kept, old_kept, new_retained, 
//						old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
//						traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,oldTestCaseChunkInfo,newTestCaseChunkInfo,
//						oldCommonChunkInfo, newCommonChunkInfo,
//						oldRetainedTestRemovedByDual,newRetainedTestRemovedByDual,old_kept_sourceCodeLevel,new_kept_sourceCodeLevel);	
////				PrintFinalResultAll(tc,basePath, projectName, bugID, newTrace, oldTrace, new_visited, old_visited, new_kept, old_kept, new_retained, 
////						old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
////						traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,oldTestCaseChunkInfo,newTestCaseChunkInfo, oldCommonChunkInfo, newCommonChunkInfo,oldRetainedTestRemovedByDual,newRetainedTestRemovedByDual);	
//			}		
//			else 
//				PrintPaperResults(tc,basePath, projectName, bugID, newTrace, oldTrace, new_visited, old_visited, new_kept, old_kept, new_retained, 
//				old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
//				traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,oldTestCaseChunkInfo,newTestCaseChunkInfo,
//				oldCommonChunkInfo, newCommonChunkInfo,
//				oldRetainedTestRemovedByDual,newRetainedTestRemovedByDual,old_kept_sourceCodeLevel,new_kept_sourceCodeLevel);	
//			
//		}
	}
private TraceNode getAssertionStatement(List<TraceNode> executionList, TestCase tc, int assertionLine) {
	Collections.sort(executionList,new TraceNodeOrderComparator());
	for(int i=executionList.size()-1;i>=0;i--) {
		TraceNode step =executionList.get(i); 
		String ClassName = step.getClassCanonicalName();		
		if (tc.testClass.equals(ClassName) && step.getLineNumber()==assertionLine) 
			return step;
	}
	return null;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
	public void corex(String basePath, String projectName, String bugID, TestCase tc, int assertionLine, boolean b, String proPath,
			TraceNode observedFaultNode, Trace newTrace, Trace oldTrace, PairList pairList, DiffMatcher diffMatcher,
			int oldTraceTime, int newTraceTime, int codeTime, int traceTime, List<RootCauseNode> realRootCaseList,
			boolean debug, String tool2Run) throws IOException {
		
		List<TraceNode> old_visited = new ArrayList<>();
		List<TraceNode> new_visited = new ArrayList<>();
		List<TraceNode> inpress_old_kept = new ArrayList<>();
		List<TraceNode> inpress_new_kept = new ArrayList<>();
		List<TraceNode> old_retained_dual = new ArrayList<>();		
		List<TraceNode> new_retained_dual = new ArrayList<>();
		if(tool2Run.equals("dual") || tool2Run.equals("all")) {
			InPreSSE configE = new InPreSSE();
//			TODO:if dual slice > necessary in printing results. then (necessary = dual slice) and for all cases, (unnecessary = dual - necessary) then the (sufficient = corex - (necessary + context)). 
//			configE.dualSlicing(basePath,projectName, bugID,tc, false, proPath, observedFaultNode, newTrace, oldTrace, PairList, diffMatcher, oldTraceTime, newTraceTime, codeTime, traceTime,rootcauseFinder.getRealRootCaseList(),debug,new_visited,old_visited,inpress_new_kept,inpress_old_kept,new_retained_dual,old_retained_dual);
//			InPreSS(basePath,projectName, bugID,tc, assertionLine,false, proPath, observedFaultNode, newTrace, oldTrace, pairList, diffMatcher, oldTraceTime, newTraceTime, codeTime, traceTime,realRootCaseList,debug,new_visited,old_visited,inpress_new_kept,inpress_old_kept,new_retained_dual,old_retained_dual);
		}
		
		List<TraceNode> new_workList = new ArrayList<>();
		List<TraceNode> dual_idt_new_visited = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> new_data_map = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> new_ctl_map = new HashMap<>();

		List<TraceNode> old_workList = new ArrayList<>();
		List<TraceNode> dual_idt_old_visited = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> old_data_map = new HashMap<>(); //(12, [(13,g), (14,f)])
		HashMap<TraceNode, List<TraceNode>> old_ctl_map = new HashMap<>();//(12, [13, 14])
		

		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> old_CashDeps = new HashMap<>();
		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> new_CashDeps = new HashMap<>();
		
		StepChangeTypeChecker typeChecker = new StepChangeTypeChecker(newTrace, oldTrace);
		

		List<TraceNode> old_retained = new ArrayList<>();		
		List<TraceNode> new_retained = new ArrayList<>();
		List<TraceNode> corex_old_kept = new ArrayList<>();//final kept after adding context of what we need
		List<TraceNode> corex_new_kept = new ArrayList<>();//final kept after adding context of what we need
		if(observedFaultNode!=null) {
			dual_idt_new_visited.add(observedFaultNode);
			new_workList.add(observedFaultNode);
			corex_new_kept.add(observedFaultNode);
			new_retained.add(observedFaultNode);		
			StepChangeType changeType = typeChecker.getType(observedFaultNode, true, pairList, diffMatcher);
			TraceNode observedFaultNodeMapping = changeType.getMatchingStep();
			if(observedFaultNodeMapping!=null) {
				dual_idt_old_visited.add(observedFaultNodeMapping);
				old_workList.add(observedFaultNodeMapping);
				corex_old_kept.add(observedFaultNodeMapping);
				old_retained.add(observedFaultNodeMapping);	
			}
			else {		
				TraceNode oldObservable = getAssertionStatement(oldTrace.getExecutionList(),tc,assertionLine);
				if(oldObservable!=null) {
					dual_idt_old_visited.add(oldObservable);
					old_workList.add(oldObservable);
					corex_old_kept.add(oldObservable);
					old_retained.add(oldObservable);
					changeType = typeChecker.getType(oldObservable, false, pairList, diffMatcher);
					TraceNode observedFaultNodeMappingonNew = changeType.getMatchingStep();
					if(observedFaultNodeMappingonNew!=null) {
						if(!dual_idt_new_visited.contains(observedFaultNodeMappingonNew)) {
							dual_idt_new_visited.add(observedFaultNodeMappingonNew);
							new_workList.add(observedFaultNodeMappingonNew);
							corex_new_kept.add(observedFaultNodeMappingonNew);
							new_retained.add(observedFaultNodeMappingonNew);
						}
					}
					else {
						TraceNode newObservable = getAssertionStatement(newTrace.getExecutionList(),tc,assertionLine);
						if(newObservable!=null) {
							if(!dual_idt_new_visited.contains(newObservable)) {
								dual_idt_new_visited.add(newObservable);
								new_workList.add(newObservable);
								corex_new_kept.add(newObservable);
								new_retained.add(newObservable);
							}
						}
						else {
							if(!dual_idt_new_visited.contains(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1))) {
								dual_idt_new_visited.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
								new_workList.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
								corex_new_kept.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
								new_retained.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
						    }
						}				
					}
				}
				else {
					dual_idt_old_visited.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
					old_workList.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
					corex_old_kept.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
					old_retained.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
					
					TraceNode newObservable = getAssertionStatement(newTrace.getExecutionList(),tc,assertionLine);
					if(newObservable!=null) {
						if(!dual_idt_new_visited.contains(newObservable)) {
							dual_idt_new_visited.add(newObservable);
							new_workList.add(newObservable);
							corex_new_kept.add(newObservable);
							new_retained.add(newObservable);
						}
					}
					else {
						if(!dual_idt_new_visited.contains(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1))) {
							dual_idt_new_visited.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
							new_workList.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
							corex_new_kept.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
							new_retained.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
					    }
					}
				}
							
			}
		}
		else {	
				TraceNode oldObservable = getAssertionStatement(oldTrace.getExecutionList(),tc,assertionLine);
				if(oldObservable!=null) {
					dual_idt_old_visited.add(oldObservable);
					old_workList.add(oldObservable);
					corex_old_kept.add(oldObservable);
					old_retained.add(oldObservable);
					StepChangeType changeType = typeChecker.getType(oldObservable, false, pairList, diffMatcher);
					TraceNode observedFaultNodeMappingonNew = changeType.getMatchingStep();
					if(observedFaultNodeMappingonNew!=null) {
						if(!dual_idt_new_visited.contains(observedFaultNodeMappingonNew)) {
							dual_idt_new_visited.add(observedFaultNodeMappingonNew);
							new_workList.add(observedFaultNodeMappingonNew);
							corex_new_kept.add(observedFaultNodeMappingonNew);
							new_retained.add(observedFaultNodeMappingonNew);
						}
					}
					else {
						TraceNode newObservable = getAssertionStatement(newTrace.getExecutionList(),tc,assertionLine);
						if(newObservable!=null) {
							if(!dual_idt_new_visited.contains(newObservable)) {
								dual_idt_new_visited.add(newObservable);
								new_workList.add(newObservable);
								corex_new_kept.add(newObservable);
								new_retained.add(newObservable);
							}
						}
						else {
							if(!dual_idt_new_visited.contains(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1))) {
								dual_idt_new_visited.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
								new_workList.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
								corex_new_kept.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
								new_retained.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
						    }
						}				
					}
				}
				else {
					dual_idt_old_visited.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
					old_workList.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
					corex_old_kept.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
					old_retained.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
					
					TraceNode newObservable = getAssertionStatement(newTrace.getExecutionList(),tc,assertionLine);
					if(newObservable!=null) {
						if(!dual_idt_new_visited.contains(newObservable)) {
							dual_idt_new_visited.add(newObservable);
							new_workList.add(newObservable);
							corex_new_kept.add(newObservable);
							new_retained.add(newObservable);
						}
					}
					else {
						if(!dual_idt_new_visited.contains(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1))) {
							dual_idt_new_visited.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
							new_workList.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
							corex_new_kept.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
							new_retained.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
					    }
					}
				}						
			}					
		System.out.println("#############################");
		System.out.println("Starting Working list on CoReX");
		

			List<TraceNode> old_retained_duall = new ArrayList<>();		
			List<TraceNode> new_retained_duall = new ArrayList<>();
	
			Long dual_start_time = System.currentTimeMillis();
			if(tool2Run.equals("corex") || tool2Run.equals("all")) {
				while(!new_workList.isEmpty() || !old_workList.isEmpty()){
					while(!new_workList.isEmpty()) {
		//				System.out.println("#############################");
						TraceNode step = new_workList.remove(0);
					    updateWorklistKeepingIdentical(new_CashDeps, old_CashDeps, step, newTrace, oldTrace, dual_idt_new_visited, new_workList,dual_idt_old_visited,old_workList,true,typeChecker,
					    		pairList,diffMatcher,new_data_map,new_ctl_map, proPath,new_retained_duall);				
					}
					////////////////////////////////////////////////////////////////////////////////////////
					while(!old_workList.isEmpty()) {
		//				System.out.println("#############################");
						TraceNode step = old_workList.remove(0);
						updateWorklistKeepingIdentical(old_CashDeps, new_CashDeps, step, oldTrace, newTrace, dual_idt_old_visited,old_workList,dual_idt_new_visited, new_workList,false,typeChecker,
								pairList,diffMatcher,old_data_map,old_ctl_map, proPath, old_retained_duall);
					}			
				}
		     }
		/// ################################################################
		/// ################################################################
		Long dual_finish_time = System.currentTimeMillis();				
		int dual_Time = (int) (dual_finish_time - dual_start_time);
			
		if(tool2Run.equals("corex") || tool2Run.equals("all")) {
			for(int i=dual_idt_old_visited.size()-1;i>=0; i--){
				TraceNode step = dual_idt_old_visited.get(i);
				if(step==null)
					dual_idt_old_visited.remove(i);
			}
			for(int i=dual_idt_new_visited.size()-1;i>=0; i--){
				TraceNode step = dual_idt_new_visited.get(i);
				if(step==null)
					dual_idt_new_visited.remove(i);
			}	
		}
		System.out.println("##########Finish Dual Slciing with keepint identical ###################");
//		printDualSliceResults(old_visited, false, proPath, diffMatcher);
//		printDualSliceResults(new_visited,true, proPath,diffMatcher);
		/// ################################################################
		/// ################################################################
		HashMap<Integer, Integer> oldChangeChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newChangeChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> oldCommonChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newCommonChunkInfo = new HashMap<>();
		getChangeChunks(typeChecker, diffMatcher, old_visited,new_visited,oldChangeChunkInfo,newChangeChunkInfo);
//		getCommonBlocksChunks(typeChecker, diffMatcher, tc,dual_idt_old_visited,dual_idt_new_visited,oldCommonChunkInfo,newCommonChunkInfo);
//		System.out.println("##############Printing Abstraction to Graph##############");
//		System.out.println(old_data_map);
		HashMap<TraceNode, List<Pair<TraceNode, String>>> both_new_data_map = new_data_map;
		HashMap<TraceNode, List<TraceNode>> both_new_ctl_map = new_ctl_map;
		HashMap<TraceNode, List<Pair<TraceNode, String>>> both_old_data_map = old_data_map;
		HashMap<TraceNode, List<TraceNode>> both_old_ctl_map = old_ctl_map;
		///################################################################
		///################################################################
		System.out.println("##############CoReX ##############");	
		List<TraceNode> inpress_keep_IDT_old_kept = new ArrayList<>();
		List<TraceNode> inpress_keep_IDT_new_kept = new ArrayList<>();
		List<TraceNode> corex_removing_DAT_IDT_old_kept = new ArrayList<>();
		List<TraceNode> corex_removing_DAT_IDT_new_kept = new ArrayList<>();
		
		List<String> old_kept_sourceCodeLevel = new ArrayList<>();		
		List<String> new_kept_sourceCodeLevel = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> new_corex_edges = new HashMap<>(); //<line 17, [(line 6, null), (line 7, f=Func_1(c,x)), (line 9, a)]>
		HashMap<TraceNode, List<Pair<TraceNode, String>>> old_corex_edges = new HashMap<>();

	
		HashMap<Integer, List<TraceNode>> oldDataBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newDataBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> oldCtlBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newCtlBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> oldIdtBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newIdtBlockNodes = new HashMap<>();
		long corex_start_time = System.currentTimeMillis();	
		

		if(tool2Run.equals("corex") || tool2Run.equals("all")) {
			corexAlgorithm(tc, proPath, dual_idt_old_visited,dual_idt_new_visited,typeChecker,pairList, 
				diffMatcher,both_old_data_map,both_old_ctl_map,both_new_data_map,both_new_ctl_map,corex_old_kept, corex_new_kept, inpress_keep_IDT_old_kept, inpress_keep_IDT_new_kept, 
				corex_removing_DAT_IDT_old_kept, corex_removing_DAT_IDT_new_kept, oldDataBlockNodes, newDataBlockNodes, oldCtlBlockNodes, newCtlBlockNodes, oldIdtBlockNodes, newIdtBlockNodes, old_retained, new_retained,old_kept_sourceCodeLevel,new_kept_sourceCodeLevel, new_corex_edges, old_corex_edges);
		}
		
		for(int i=corex_new_kept.size()-1;i>=0; i--){
			TraceNode step = corex_new_kept.get(i);
			if(step==null)
				corex_new_kept.remove(i);
		}
		for(int i=corex_old_kept.size()-1;i>=0; i--){
			TraceNode step = corex_old_kept.get(i);
			if(step==null)
				corex_old_kept.remove(i);
		}
		
//		corexAlgorithmOptimized(tc, proPath, dual_idt_old_visited,dual_idt_new_visited,typeChecker,pairList, 
//				diffMatcher,both_old_data_map,both_old_ctl_map,both_new_data_map,both_new_ctl_map,corex_old_kept, corex_new_kept, inpress_keep_IDT_old_kept, inpress_keep_IDT_new_kept, 
//				corex_removing_DAT_IDT_old_kept, corex_removing_DAT_IDT_new_kept, oldDataBlockNodes, newDataBlockNodes, oldCtlBlockNodes, newCtlBlockNodes, oldIdtBlockNodes, newIdtBlockNodes, old_retained, new_retained,old_kept_sourceCodeLevel,new_kept_sourceCodeLevel, new_corex_edges, old_corex_edges);
		
		
//		System.out.println("dual retained old" + old_retained_dual);
//		System.out.println("dual retained new" + new_retained_dual);
//		System.out.println("Corex retained old" + old_retained);
//		System.out.println("Corex retained new" + new_retained);
		
		long corex_finish_time = System.currentTimeMillis();			
		int corex_Time = (int) (corex_finish_time - corex_start_time);
		System.out.println("##############Saving Results##############");	
		if(tool2Run.equals("all") || tool2Run.equals("dual")) {
			PrintResults(tc,basePath, projectName, bugID, typeChecker,pairList, diffMatcher, newTrace, oldTrace,  new_visited, old_visited, inpress_new_kept,inpress_old_kept, dual_idt_new_visited, dual_idt_old_visited, corex_old_kept, corex_new_kept, inpress_keep_IDT_old_kept, inpress_keep_IDT_new_kept, 
				corex_removing_DAT_IDT_old_kept, corex_removing_DAT_IDT_new_kept, new_retained_dual, 
				old_retained_dual, newDataBlockNodes, oldDataBlockNodes, newIdtBlockNodes, oldIdtBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
								traceTime, dual_Time, corex_Time,oldChangeChunkInfo,newChangeChunkInfo,
								oldCommonChunkInfo, newCommonChunkInfo, old_kept_sourceCodeLevel,new_kept_sourceCodeLevel);									
		}
		else {
			PrintResults(tc,basePath, projectName, bugID, typeChecker,pairList, diffMatcher, newTrace, oldTrace,  new_visited, old_visited, inpress_new_kept,inpress_old_kept, dual_idt_new_visited, dual_idt_old_visited, corex_old_kept, corex_new_kept, inpress_keep_IDT_old_kept, inpress_keep_IDT_new_kept, 
					corex_removing_DAT_IDT_old_kept, corex_removing_DAT_IDT_new_kept, new_retained, 
									old_retained, newDataBlockNodes, oldDataBlockNodes, newIdtBlockNodes, oldIdtBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
									traceTime, dual_Time, corex_Time,oldChangeChunkInfo,newChangeChunkInfo,
									oldCommonChunkInfo, newCommonChunkInfo, old_kept_sourceCodeLevel,new_kept_sourceCodeLevel);	
			PrintCoReXResults(tc,basePath, projectName, bugID, typeChecker,pairList, diffMatcher, newTrace, oldTrace,  new_visited, old_visited, inpress_new_kept,inpress_old_kept, dual_idt_new_visited, dual_idt_old_visited, corex_old_kept, corex_new_kept, inpress_keep_IDT_old_kept, inpress_keep_IDT_new_kept, 
					corex_removing_DAT_IDT_old_kept, corex_removing_DAT_IDT_new_kept, new_retained, 
									old_retained, newDataBlockNodes, oldDataBlockNodes, newIdtBlockNodes, oldIdtBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
									traceTime, dual_Time, corex_Time,oldChangeChunkInfo,newChangeChunkInfo,
									oldCommonChunkInfo, newCommonChunkInfo, old_kept_sourceCodeLevel,new_kept_sourceCodeLevel);	
		}
		
	}
	private void PrintCoReXResults(TestCase tc, String basePath, String projectName, String bugID, StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher, 
			Trace newTrace,
			Trace oldTrace, List<TraceNode> new_visited, List<TraceNode> old_visited, List<TraceNode> inpress_new_kept,List<TraceNode> inpress_old_kept, List<TraceNode> dual_keep_IDT_new_visited, List<TraceNode> dual_keep_IDT_old_visited, List<TraceNode> old_kept, List<TraceNode> new_kept, 
			List<TraceNode> inpress_keep_IDT_old_kept, List<TraceNode> inpress_keep_IDT_new_kept,
			List<TraceNode> corex_removing_DAT_IDT_old_kept, List<TraceNode> corex_removing_DAT_IDT_new_kept, 
			List<TraceNode> new_retained, List<TraceNode> old_retained,
			HashMap<Integer, List<TraceNode>> newDataBlockNodes, HashMap<Integer, List<TraceNode>> oldDataBlockNodes,
			HashMap<Integer, List<TraceNode>> newIdtBlockNodes, HashMap<Integer, List<TraceNode>> oldIdtBlockNodes,
			HashMap<Integer, List<TraceNode>> newCtlBlockNodes, HashMap<Integer, List<TraceNode>> oldCtlBlockNodes,
			int oldTraceTime, int newTraceTime, int codeTime, int traceTime, int dual_Time, int corex_Time,
			HashMap<Integer, Integer> oldChangeChunkInfo, HashMap<Integer, Integer> newChangeChunkInfo,
			HashMap<Integer, Integer> oldCommonChunkInfo, HashMap<Integer, Integer> newCommonChunkInfo,
			List<String> old_kept_sourceCodeLevel,
			List<String> new_kept_sourceCodeLevel) {
		

		Path path = Paths.get(basePath+"/results");
		if(!Files.exists(path)) 
			new File(basePath+"/results").mkdirs();
		
		String results = basePath+"/results/"+projectName+"CoReX_Results.xlsx";
	    File tempFile = new File(results);
	    boolean FirstTime = false;
	    
	    if (!tempFile.exists()) {
	        FirstTime=true;
	        XSSFWorkbook workbook = new XSSFWorkbook();
	        try {
	        	FileOutputStream outputStream = new FileOutputStream(results);
	            workbook.write(outputStream);
	            workbook.close();
	        	outputStream.close();
	        } catch (Exception e) {
	        }
	    }
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######

	    int h2No_old = 0; 
	    for(TraceNode node: inpress_keep_IDT_old_kept) {
	    	StepChangeType changeType = typeChecker.getTypeForPrinting(node, false, pairList, matcher);
	    	if (changeType.getType()==StepChangeType.DAT && (!corex_removing_DAT_IDT_old_kept.contains(node)))//unnecessary data that is removed
	    		h2No_old++;	    		
	    }
	    int h2No_new = 0;
	    for(TraceNode node: inpress_keep_IDT_new_kept) {
	    	StepChangeType changeType = typeChecker.getTypeForPrinting(node, true, pairList, matcher);
	    	if (changeType.getType()==StepChangeType.DAT && (!corex_removing_DAT_IDT_new_kept.contains(node)))//unnecessary data that is removed
	    		h2No_new++;	    		
	    }
	    int h1No_old = 0;
	    int h1No_new = 0;
	    int h2No_old_nec = 0;	    
	    int h2No_new_nec = 0;	    
	    int h3No_old = 0;
	    for(TraceNode node: old_kept) {
	    	if (!corex_removing_DAT_IDT_old_kept.contains(node))
	    		h3No_old++;	
	    	else {
	    		StepChangeType changeType = typeChecker.getTypeForPrinting(node, false, pairList, matcher);
		    	if (changeType.getType()==StepChangeType.IDT)//sufficient identical that is kept
		    		h1No_old++;	
		    	else 
		    		h2No_old_nec++;
	    	}
	    }
	    int h3No_new = 0;
	    for(TraceNode node: new_kept) {
	    	if (!corex_removing_DAT_IDT_new_kept.contains(node))
	    		h3No_new++;	
	    	else {
	    		StepChangeType changeType = typeChecker.getTypeForPrinting(node, true, pairList, matcher);
		    	if (changeType.getType()==StepChangeType.IDT)//sufficient identical that is kept
		    		h1No_new++;	
		    	else 
		    		h2No_new_nec++;
	    	}
	    }
	    
	    if (FirstTime) {		    	
	        String[] header = {"Bug ID", 
	        		"Old CoReX size (#CoReX)", "H1: Old necessary size (#necessary)", "H1: Old unnecessary size (#Unnecessary)", "H2: Old relevant size (#Sufficiency)",  "H3: Old Contex size (#Context)", 
	        		"New CoReX size (#CoReX)", "H1: New necessary size (#necessary)", "H1: New unnecessary size (#Unnecessary)", "H2: New relevant size (#Sufficiency)",  "H3: New Contex size (#Context)"
	        		};
	        WriteToExcel(results, header, "RQ3-1",true,true);
	    }
	    
	    String[] detailedDataRQ2 = {bugID, 
	    		String.valueOf(old_kept.size()), String.valueOf(h2No_old_nec), String.valueOf(h2No_old), String.valueOf(h1No_old), String.valueOf(h3No_old),
	    		String.valueOf(new_kept.size()), String.valueOf(h2No_new_nec), String.valueOf(h2No_new), String.valueOf(h1No_new), String.valueOf(h3No_new)
	    		};
	    WriteToExcel(results,detailedDataRQ2,"RQ3-1",true, false);
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######
	    double CoReXoldReduction_orig = (Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(old_kept.size()))/(Double.valueOf(oldTrace.getExecutionList().size()))*100.0;
	    double CoReXnewReduction_orig = (Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(new_kept.size()))/(Double.valueOf(newTrace.getExecutionList().size()))*100.0;
		
        
        if (FirstTime) {		    	
	        String[] header = {"Bug ID", 
	        		"Old trace size (#T)", "Old CoReX size (#CoReX)", "%Old Trace vs CoReX Reduct.", 
	        		"New trace size (#T)", "New CoReX size (#CoReX)", "%New Trace vs CoReX Reduct.", 
	        		"TraceMatching and Initial Time (Min)", "CoReX Time (Min)"
	        		};
	        WriteToExcel(results, header, "RQ3-2",true, true);
	    }
        String[] detailedDataRQ3_2 = {bugID, 
	    		String.valueOf(oldTrace.getExecutionList().size()), 
	    		String.valueOf(old_kept.size()), String.valueOf(CoReXoldReduction_orig), 
	    		String.valueOf(newTrace.getExecutionList().size()), 
	    		String.valueOf(new_kept.size()), String.valueOf(CoReXnewReduction_orig),
	    		String.valueOf((Double.valueOf(dual_Time)/1000.0)/60.0), String.valueOf((Double.valueOf(corex_Time)/1000.0)/60.0)
	    		};
	    WriteToExcel(results,detailedDataRQ3_2,"RQ3-2",true, false);
					
		/////////////////#######////#######////#######////#######////#######////#######
		/////////////////#######////#######////#######////#######////#######////#######
	       /////////////////#######////#######////#######////#######////#######////#######
	       /////////////////#######////#######////#######////#######////#######////#######
	       
           boolean Einspect5_CoReX = CanFindTheBug(5, old_kept, new_kept,old_retained,new_retained);
	       
           boolean Einspect10_CoReX = CanFindTheBug(10, old_kept, new_kept,old_retained,new_retained);
	       
           boolean Einspect30_CoReX = CanFindTheBug(30, old_kept, new_kept,old_retained,new_retained);
	       
	       boolean Einspect50_CoReX = CanFindTheBug(50, old_kept, new_kept,old_retained,new_retained);
	  
	       boolean Einspect100_CoReX = CanFindTheBug(100, old_kept, new_kept,old_retained,new_retained);
	  
	       boolean Einspect200_CoReX = CanFindTheBug(200, old_kept, new_kept,old_retained,new_retained);
	       
	       int traversed_old_CoReX = CalculateWastedEffort(old_kept,old_retained);
	       int traversed_new_CoReX = CalculateWastedEffort(new_kept,new_retained);
	       
	       double wasted_effort_old_CoReX = ((double)traversed_old_CoReX/oldTrace.getExecutionList().size())*100.0;
	       double wasted_effort_new_CoRex = ((double)traversed_new_CoReX/newTrace.getExecutionList().size())*100.0;
	       
	       if (FirstTime) {		    	
		        String[] header = {"Bug ID", 
		        		"Einspect@5-CoReX", 
		        		"Einspect@10-CoReX", 
		        		"Einspect@30-CoReX",
		        		"Einspect@50-CoReX",
		        		"Einspect@100-CoReX",
		        		"Einspect@200-CoReX",
		        		"#Traversed Old Stmt-CoReX","#Traversed New Stmt-CoReX",
		        		"Exam% Old-CoReX","Exam% New-CoReX"
	        		
		        		};
		        WriteToExcel(results, header, "RQ3-3",true, true);
		    }
		    String[] detailedDataRQ4 = {bugID, 
		    		String.valueOf(Einspect5_CoReX),
		    		String.valueOf(Einspect10_CoReX),
		    		String.valueOf(Einspect30_CoReX),
		    		String.valueOf(Einspect50_CoReX),
		    		String.valueOf(Einspect100_CoReX),
		    		String.valueOf(Einspect200_CoReX),
		    		String.valueOf(traversed_old_CoReX),String.valueOf(traversed_new_CoReX),
		    		String.valueOf(wasted_effort_old_CoReX),String.valueOf(wasted_effort_new_CoRex)
		    };
		    WriteToExcel(results,detailedDataRQ4,"RQ3-3",true, false);
						

		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
		System.out.println("##############Finish##############");
		
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void PrintResults(TestCase tc, String basePath, String projectName, String bugID, StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher, 
			Trace newTrace,
			Trace oldTrace, List<TraceNode> new_visited, List<TraceNode> old_visited, List<TraceNode> inpress_new_kept,List<TraceNode> inpress_old_kept, List<TraceNode> dual_keep_IDT_new_visited, List<TraceNode> dual_keep_IDT_old_visited, List<TraceNode> old_kept, List<TraceNode> new_kept, 
			List<TraceNode> inpress_keep_IDT_old_kept, List<TraceNode> inpress_keep_IDT_new_kept,
			List<TraceNode> corex_removing_DAT_IDT_old_kept, List<TraceNode> corex_removing_DAT_IDT_new_kept, 
			List<TraceNode> new_retained, List<TraceNode> old_retained,
			HashMap<Integer, List<TraceNode>> newDataBlockNodes, HashMap<Integer, List<TraceNode>> oldDataBlockNodes,
			HashMap<Integer, List<TraceNode>> newIdtBlockNodes, HashMap<Integer, List<TraceNode>> oldIdtBlockNodes,
			HashMap<Integer, List<TraceNode>> newCtlBlockNodes, HashMap<Integer, List<TraceNode>> oldCtlBlockNodes,
			int oldTraceTime, int newTraceTime, int codeTime, int traceTime, int dual_Time, int corex_Time,
			HashMap<Integer, Integer> oldChangeChunkInfo, HashMap<Integer, Integer> newChangeChunkInfo,
			HashMap<Integer, Integer> oldCommonChunkInfo, HashMap<Integer, Integer> newCommonChunkInfo,
			List<String> old_kept_sourceCodeLevel,
			List<String> new_kept_sourceCodeLevel) {
		

		Path path = Paths.get(basePath+"/results");
		if(!Files.exists(path)) 
			new File(basePath+"/results").mkdirs();
		
		String results = basePath+"/results/"+projectName+"CoReX.xlsx";
	    File tempFile = new File(results);
	    boolean FirstTime = false;
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######
		double DualoldReduction = (Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(dual_keep_IDT_old_visited.size()))/(Double.valueOf(oldTrace.getExecutionList().size()))*100.0;
		double DualnewReduction = (Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(dual_keep_IDT_new_visited.size()))/(Double.valueOf(newTrace.getExecutionList().size()))*100.0;
	    double InPreSSoldReduction = (Double.valueOf(dual_keep_IDT_old_visited.size())-Double.valueOf(inpress_keep_IDT_old_kept.size()))/(Double.valueOf(dual_keep_IDT_old_visited.size()))*100.0;
	    double InPreSSnewReduction = (Double.valueOf(dual_keep_IDT_new_visited.size())-Double.valueOf(inpress_keep_IDT_new_kept.size()))/(Double.valueOf(dual_keep_IDT_new_visited.size()))*100.0;
		
		double DualoldReduction_orig = (Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(old_visited.size()))/(Double.valueOf(oldTrace.getExecutionList().size()))*100.0;
		double DualnewReduction_orig = (Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(new_visited.size()))/(Double.valueOf(newTrace.getExecutionList().size()))*100.0;
	    double InPreSSoldReduction_orig = (Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(inpress_old_kept.size()))/(Double.valueOf(oldTrace.getExecutionList().size()))*100.0;
	    double InPreSSnewReduction_orig = (Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(inpress_new_kept.size()))/(Double.valueOf(newTrace.getExecutionList().size()))*100.0;
	    double CoReXoldReduction_orig = (Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(old_kept.size()))/(Double.valueOf(oldTrace.getExecutionList().size()))*100.0;
	    double CoReXnewReduction_orig = (Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(new_kept.size()))/(Double.valueOf(newTrace.getExecutionList().size()))*100.0;
		
	    
	    double CoReXDualoldReduction_orig = (Double.valueOf(old_visited.size())-Double.valueOf(old_kept.size()))/(Double.valueOf(old_visited.size()))*100.0;
	    double CoReXDualnewReduction_orig = (Double.valueOf(new_visited.size())-Double.valueOf(new_kept.size()))/(Double.valueOf(new_visited.size()))*100.0;
	    double CoReXInPreSSoldReduction_orig = (Double.valueOf(inpress_old_kept.size())-Double.valueOf(old_kept.size()))/(Double.valueOf(inpress_old_kept.size()))*100.0;
	    double CoReXInPreSSnewReduction_orig = (Double.valueOf(inpress_new_kept.size())-Double.valueOf(new_kept.size()))/(Double.valueOf(inpress_new_kept.size()))*100.0;
	    
	    double CoReXDualoldReduction = (Double.valueOf(dual_keep_IDT_old_visited.size())-Double.valueOf(old_kept.size()))/(Double.valueOf(dual_keep_IDT_old_visited.size()))*100.0;
	    double CoReXDualnewReduction = (Double.valueOf(dual_keep_IDT_new_visited.size())-Double.valueOf(new_kept.size()))/(Double.valueOf(dual_keep_IDT_new_visited.size()))*100.0;
	    double CoReXInPreSSoldReduction = (Double.valueOf(inpress_keep_IDT_old_kept.size())-Double.valueOf(old_kept.size()))/(Double.valueOf(inpress_keep_IDT_old_kept.size()))*100.0;
	    double CoReXInPreSSnewReduction = (Double.valueOf(inpress_keep_IDT_new_kept.size())-Double.valueOf(new_kept.size()))/(Double.valueOf(inpress_keep_IDT_new_kept.size()))*100.0;
	    
		if (!tempFile.exists()) {
	        FirstTime=true;
	        XSSFWorkbook workbook = new XSSFWorkbook();
	        try {
	        	FileOutputStream outputStream = new FileOutputStream(results);
	            workbook.write(outputStream);
	            workbook.close();
	        	outputStream.close();
	        } catch (Exception e) {
	        }
	    }		

        if (FirstTime) {		    	
	        String[] header = {"Bug ID", 
	        		"Old trace size (#T)","Old Dual size + IDT(#DSlice+)", "%Old Trace vs Dual Reduct.", "#Old Chg", "Old InPreSS size + IDT(#InPreSS)", "%Old Dual vs InPreSS Reduct.", "Old CoReX size (#CoReX)", "%Old Dual vs CoReX Reduct.", "%Old InPreSS vs CoReX Reduct.", 
	        		"New trace size (#T)","New Dual size + IDT(#DSlice)", "%New Trace vs Dual Reduct.", "#New Chg", "New InPreSS size + IDT(#InPreSS)", "%New Dual vs InPreSS Reduct.", "New CoReX size (#CoReX)", "%New Dual vs CoReX Reduct.", "%New InPreSS vs CoReX Reduct.",
	        		"Old Dual size #DSlice+)", "%Old Trace vs Dual Reduct.", "#Old Chg", "Old InPreSS size(#InPreSS)", "%Old Dual vs InPreSS Reduct.", "Old CoReX size (#CoReX)", "%Old Dual vs CoReX Reduct.", "%Old InPreSS vs CoReX Reduct.", 
	        		"New Dual size (#DSlice)", "%New Trace vs Dual Reduct.", "#New Chg", "New InPreSS size(#InPreSS)", "%New Dual vs InPreSS Reduct.", "New CoReX size (#CoReX)", "%New Dual vs CoReX Reduct.", "%New InPreSS vs CoReX Reduct.",
	        		"DSlice Time (Min)", "CoReX Time (Min)"
	        		};
	        WriteToExcel(results, header, "RQ3-2-Extra",true, true);
	    }
	    String[] detailedDataRQ1 = {bugID, 
	    		String.valueOf(oldTrace.getExecutionList().size()), String.valueOf(dual_keep_IDT_old_visited.size()), String.valueOf(DualoldReduction), 
	    		String.valueOf(oldChangeChunkInfo.keySet().size()), String.valueOf(inpress_keep_IDT_old_kept.size()), String.valueOf(InPreSSoldReduction), 
	    		String.valueOf(old_kept.size()), String.valueOf(CoReXDualoldReduction), String.valueOf(CoReXInPreSSoldReduction),
	    		String.valueOf(newTrace.getExecutionList().size()), String.valueOf(dual_keep_IDT_new_visited.size()), String.valueOf(DualnewReduction), 
	    		String.valueOf(newChangeChunkInfo.keySet().size()), String.valueOf(inpress_keep_IDT_new_kept.size()), String.valueOf(InPreSSnewReduction), 
	    		String.valueOf(new_kept.size()), String.valueOf(CoReXDualnewReduction), String.valueOf(CoReXInPreSSnewReduction),
	    		String.valueOf(old_visited.size()), String.valueOf(DualoldReduction_orig), 
	    		String.valueOf(oldChangeChunkInfo.keySet().size()), String.valueOf(inpress_old_kept.size()), String.valueOf(InPreSSoldReduction_orig), 
	    		String.valueOf(old_kept.size()), String.valueOf(CoReXDualoldReduction_orig), String.valueOf(CoReXInPreSSoldReduction_orig),
	    		String.valueOf(new_visited.size()), String.valueOf(DualnewReduction_orig), 
	    		String.valueOf(newChangeChunkInfo.keySet().size()), String.valueOf(inpress_new_kept.size()), String.valueOf(InPreSSnewReduction_orig), 
	    		String.valueOf(new_kept.size()), String.valueOf(CoReXDualnewReduction_orig), String.valueOf(CoReXInPreSSnewReduction_orig),
	    		String.valueOf((Double.valueOf(dual_Time)/1000.0)/60.0), String.valueOf((Double.valueOf(corex_Time)/1000.0)/60.0)
	    		};
	    WriteToExcel(results,detailedDataRQ1,"RQ3-2-Extra",true, false);
					


        if (FirstTime) {		    	
	        String[] header = {"Bug ID", 
	        		"Old trace size (#T)","Old Dual size (#DSlice)", "%Old Trace vs Dual Reduct.", "#Old Chg", "Old InPreSS size", "%Old Trace vs InPreSS Reduct.", "Old CoReX size (#CoReX)", "%Old Trace vs CoReX Reduct.", 
	        		"New trace size (#T)","New Dual size (#DSlice)", "%New Trace vs Dual Reduct.", "#New Chg", "New InPreSS size", "%New Trace vs InPreSS Reduct.", "New CoReX size (#CoReX)", "%New Trace vs CoReX Reduct.", 
	        		"DSlice Time (Min)", "CoReX Time (Min)"
	        		};
	        WriteToExcel(results, header, "RQ3-2",true, true);
	    }
        String[] detailedDataRQ3_2 = {bugID, 
	    		String.valueOf(oldTrace.getExecutionList().size()), 
	    		String.valueOf(old_visited.size()), String.valueOf(DualoldReduction_orig), 
	    		String.valueOf(oldChangeChunkInfo.keySet().size()), 
	    		String.valueOf(inpress_old_kept.size()), String.valueOf(InPreSSoldReduction_orig), 
	    		String.valueOf(old_kept.size()), String.valueOf(CoReXoldReduction_orig), 
	    		String.valueOf(newTrace.getExecutionList().size()), 
	    		String.valueOf(new_visited.size()), String.valueOf(DualnewReduction_orig), 
	    		String.valueOf(newChangeChunkInfo.keySet().size()), 
	    		String.valueOf(inpress_new_kept.size()), String.valueOf(InPreSSnewReduction_orig), 
	    		String.valueOf(new_kept.size()), String.valueOf(CoReXnewReduction_orig),
	    		String.valueOf((Double.valueOf(dual_Time)/1000.0)/60.0), String.valueOf((Double.valueOf(corex_Time)/1000.0)/60.0)
	    		};
	    WriteToExcel(results,detailedDataRQ3_2,"RQ3-2",true, false);
					

	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######

	    int h2No_old = 0; 
	    for(TraceNode node: inpress_keep_IDT_old_kept) {
	    	StepChangeType changeType = typeChecker.getTypeForPrinting(node, false, pairList, matcher);
	    	if (changeType.getType()==StepChangeType.DAT && (!corex_removing_DAT_IDT_old_kept.contains(node)))//unnecessary data that is removed
	    		h2No_old++;	    		
	    }
	    int h2No_new = 0;
	    for(TraceNode node: inpress_keep_IDT_new_kept) {
	    	StepChangeType changeType = typeChecker.getTypeForPrinting(node, true, pairList, matcher);
	    	if (changeType.getType()==StepChangeType.DAT && (!corex_removing_DAT_IDT_new_kept.contains(node)))//unnecessary data that is removed
	    		h2No_new++;	    		
	    }
	    int h1No_old = 0;
	    int h1No_new = 0;
	    int h2No_old_nec = 0;	    
	    int h2No_new_nec = 0;	    
	    int h3No_old = 0;
	    for(TraceNode node: old_kept) {
	    	if (!corex_removing_DAT_IDT_old_kept.contains(node))
	    		h3No_old++;	
	    	else {
	    		StepChangeType changeType = typeChecker.getTypeForPrinting(node, false, pairList, matcher);
		    	if (changeType.getType()==StepChangeType.IDT)//sufficient identical that is kept
		    		h1No_old++;	
		    	else 
		    		h2No_old_nec++;
	    	}
	    }
	    int h3No_new = 0;
	    for(TraceNode node: new_kept) {
	    	if (!corex_removing_DAT_IDT_new_kept.contains(node))
	    		h3No_new++;	
	    	else {
	    		StepChangeType changeType = typeChecker.getTypeForPrinting(node, true, pairList, matcher);
		    	if (changeType.getType()==StepChangeType.IDT)//sufficient identical that is kept
		    		h1No_new++;	
		    	else 
		    		h2No_new_nec++;
	    	}
	    }
	    
	    if (FirstTime) {		    	
	        String[] header = {"Bug ID", 
	        		"Old CoReX size (#CoReX)", "H1: Old necessary size (#necessary)", "H1: Old unnecessary size (#Unnecessary)", "H2: Old relevant size (#Sufficiency)",  "H3: Old Contex size (#Context)", 
	        		"New CoReX size (#CoReX)", "H1: New necessary size (#necessary)", "H1: New unnecessary size (#Unnecessary)", "H2: New relevant size (#Sufficiency)",  "H3: New Contex size (#Context)"
	        		};
	        WriteToExcel(results, header, "RQ3-1",true,true);
	    }
	    
	    String[] detailedDataRQ2 = {bugID, 
	    		String.valueOf(old_kept.size()), String.valueOf(h2No_old_nec), String.valueOf(h2No_old), String.valueOf(h1No_old), String.valueOf(h3No_old),
	    		String.valueOf(new_kept.size()), String.valueOf(h2No_new_nec), String.valueOf(h2No_new), String.valueOf(h1No_new), String.valueOf(h3No_new)
	    		};
	    WriteToExcel(results,detailedDataRQ2,"RQ3-1",true, false);
		/////////////////#######////#######////#######////#######////#######////#######
		/////////////////#######////#######////#######////#######////#######////#######
	    		       
	    double sum = 0.0;
	    for(Integer loc:oldChangeChunkInfo.keySet()) {
	    	sum += oldChangeChunkInfo.get(loc);
	    }
	    double avg = sum/(double)oldChangeChunkInfo.keySet().size();
	    double oldLocation = avg/(double)oldTrace.getExecutionList().size();
//	    int oldChangedStamts = getChanges(old_retained, tc);
	    
	    sum = 0.0;
	    for(Integer loc:newChangeChunkInfo.keySet()) {
	    	sum += newChangeChunkInfo.get(loc);
	    }
	    avg = sum/(double)newChangeChunkInfo.keySet().size();
	    double newLocation = avg/(double)newTrace.getExecutionList().size();
//	    int newChangedStamts = getChanges(new_retained, tc);
	    
	    double oldCommonBlockAvg = 0.0;
	    double oldCommonBlockMax = -1000000.0;
	    double oldCommonBlockMin = 100000.0;
	    double oldCommonBlockSum = 0.0;
		for (Integer blockID :oldCommonChunkInfo.keySet()) {
			Integer noOfStmts = oldCommonChunkInfo.get(blockID);
			if(noOfStmts!=null) {
				oldCommonBlockSum = oldCommonBlockSum + noOfStmts;
				if (oldCommonBlockMax<noOfStmts)
					oldCommonBlockMax = noOfStmts;
				if (oldCommonBlockMin>noOfStmts)
					oldCommonBlockMin = noOfStmts;
			}			
		}
		oldCommonBlockAvg = oldCommonBlockSum/oldCommonChunkInfo.keySet().size();

		
	    double newCommonBlockAvg = 0.0;
	    double newCommonBlockMax = -1000000.0;
	    double newCommonBlockMin = 100000.0;
	    double newCommonBlockSum = 0.0;
		for (Integer blockID :newCommonChunkInfo.keySet()) {
			Integer noOfStmts = newCommonChunkInfo.get(blockID);
			if(noOfStmts!=null) {
				newCommonBlockSum = newCommonBlockSum + noOfStmts;
				if (newCommonBlockMax<noOfStmts)
					newCommonBlockMax = noOfStmts;
				if (newCommonBlockMin>noOfStmts)
					newCommonBlockMin = noOfStmts;
			}			
		}
		newCommonBlockAvg = newCommonBlockSum/newCommonChunkInfo.keySet().size();

		/////////////////#######////#######////#######////#######////#######////#######
		/////////////////#######////#######////#######////#######////#######////#######
	    	
		//calculating #B, avg, max of data blocks on dual slice
	    double oldDATDualAvg = 0.0;
	    double oldDATDualMax = -1000000.0;
	    double oldDATDualMin = 100000.0;
	    double oldDATDualSum = 0.0;
		for (Integer block :oldDataBlockNodes.keySet()) {
			List<TraceNode> nodes = oldDataBlockNodes.get(block);
			if(nodes!=null) {
				oldDATDualSum = oldDATDualSum + nodes.size();
				if (oldDATDualMax<nodes.size())
					oldDATDualMax = nodes.size();
				if (oldDATDualMin>nodes.size())
					oldDATDualMin = nodes.size();
			}			
		}
		oldDATDualAvg = oldDATDualSum/oldDataBlockNodes.keySet().size();

		
		double newDATDualAvg = 0.0;
	    double newDATDualMax = -100000.0;
	    double newDATDualMin = 100000.0;
	    double newDATDualSum = 0.0;
		for (Integer block :newDataBlockNodes.keySet()) {
			List<TraceNode> nodes = newDataBlockNodes.get(block);
			if(nodes!=null) {
				newDATDualSum = newDATDualSum + nodes.size();
				if (newDATDualMax<nodes.size())
					newDATDualMax = nodes.size();
				if (newDATDualMin>nodes.size())
					newDATDualMin = nodes.size();
			}			
		}
		newDATDualAvg = newDATDualSum/newDataBlockNodes.keySet().size();

		
		//calculating #B, avg, max of data blocks on InPReSS
		double oldDATInPreSSAvg = 0.0;
		double oldDATInPreSSMax = -100000.0;
		double oldDATInPreSSMin = 100000.0;
		double oldDATInPreSSSum = 0.0;
		for (Integer block :oldDataBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = oldDataBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (inpress_keep_IDT_old_kept.contains(node))
						size = size + 1;
				}
				oldDATInPreSSSum = oldDATInPreSSSum + size;
				if (oldDATInPreSSMax<size)
					oldDATInPreSSMax = size;
				if (oldDATInPreSSMin>size)
					oldDATInPreSSMin = size;
			}			
		}
		oldDATInPreSSAvg = oldDATInPreSSSum/oldDataBlockNodes.keySet().size();

		
		double newDATInPreSSAvg = 0.0;
	    double newDATInPreSSMax = -100000.0;
	    double newDATInPreSSMin = 100000.0;
	    double newDATInPreSSSum = 0.0;
		for (Integer block :newDataBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = newDataBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (inpress_keep_IDT_new_kept.contains(node))
						size = size + 1;
				}
				newDATInPreSSSum = newDATInPreSSSum + size;
				if (newDATInPreSSMax<size)
					newDATInPreSSMax = size;
				if (newDATInPreSSMin>size)
					newDATInPreSSMin = size;
			}			
		}
		newDATInPreSSAvg = newDATInPreSSSum/newDataBlockNodes.keySet().size();
         
		
		//calculating #B, avg, max of data blocks on CoReX
		double oldDATCoReXAvg = 0.0;
		double oldDATCoReXMax = -100000.0;
		double oldDATCoReXMin = 100000.0;
		double oldDATCoReXSum = 0.0;
		for (Integer block :oldDataBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = oldDataBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (old_kept.contains(node))
						size = size + 1;
				}
				oldDATCoReXSum = oldDATCoReXSum + size;
				if (oldDATCoReXMax<size)
					oldDATCoReXMax = size;
				if (oldDATCoReXMin>size)
					oldDATCoReXMin = size;
			}			
		}
		oldDATCoReXAvg = oldDATCoReXSum/oldDataBlockNodes.keySet().size();

		
		double newDATCoReXAvg = 0.0;
	    double newDATCoReXMax = -100000.0;
	    double newDATCoReXMin = 100000.0;
	    double newDATCoReXSum = 0.0;
		for (Integer block :newDataBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = newDataBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (new_kept.contains(node))
						size = size + 1;
				}
				newDATCoReXSum = newDATCoReXSum + size;
				if (newDATCoReXMax<size)
					newDATCoReXMax = size;
				if (newDATCoReXMin>size)
					newDATCoReXMin = size;
			}			
		}
		newDATCoReXAvg = newDATCoReXSum/newDataBlockNodes.keySet().size();
		
		/////////////////#######////#######////#######////#######////#######////#######
		/////////////////#######////#######////#######////#######////#######////#######
			
		//calculating #B, avg, max of idt blocks on dual slice
		double oldIDTDualAvg = 0.0;
		double oldIDTDualMax = -1000000.0;
		double oldIDTDualMin = 100000.0;
		double oldIDTDualSum = 0.0;
		for (Integer block :oldIdtBlockNodes.keySet()) {
			List<TraceNode> nodes = oldIdtBlockNodes.get(block);
			if(nodes!=null) {
				oldIDTDualSum = oldIDTDualSum + nodes.size();
				if (oldIDTDualMax<nodes.size())
					oldIDTDualMax = nodes.size();
				if (oldIDTDualMin>nodes.size())
					oldIDTDualMin = nodes.size();
			}			
		}
		oldIDTDualAvg = oldIDTDualSum/oldIdtBlockNodes.keySet().size();
		
		
		double newIDTDualAvg = 0.0;
		double newIDTDualMax = -100000.0;
		double newIDTDualMin = 100000.0;
		double newIDTDualSum = 0.0;
		for (Integer block :newIdtBlockNodes.keySet()) {
			List<TraceNode> nodes = newIdtBlockNodes.get(block);
			if(nodes!=null) {
				newIDTDualSum = newIDTDualSum + nodes.size();
				if (newIDTDualMax<nodes.size())
					newIDTDualMax = nodes.size();
				if (newIDTDualMin>nodes.size())
					newIDTDualMin = nodes.size();
			}			
		}
		newIDTDualAvg = newIDTDualSum/newIdtBlockNodes.keySet().size();
		
		
		//calculating #B, avg, max of idt blocks on inpress
		double oldIDTInPreSSAvg = 0.0;
		double oldIDTInPreSSMax = -100000.0;
		double oldIDTInPreSSMin = 100000.0;
		double oldIDTInPreSSSum = 0.0;
		for (Integer block :oldIdtBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = oldIdtBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (inpress_keep_IDT_old_kept.contains(node))
						size = size + 1;
				}
				oldIDTInPreSSSum = oldIDTInPreSSSum + size;
				if (oldIDTInPreSSMax<size)
					oldIDTInPreSSMax = size;
				if (oldIDTInPreSSMin>size)
					oldIDTInPreSSMin = size;
			}			
		}
		oldIDTInPreSSAvg = oldIDTInPreSSSum/oldIdtBlockNodes.keySet().size();
		
		
		double newIDTInPreSSAvg = 0.0;
		double newIDTInPreSSMax = -100000.0;
		double newIDTInPreSSMin = 100000.0;
		double newIDTInPreSSSum = 0.0;
		for (Integer block :newIdtBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = newIdtBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (inpress_keep_IDT_new_kept.contains(node))
						size = size + 1;
				}
				newIDTInPreSSSum = newIDTInPreSSSum + size;
				if (newIDTInPreSSMax<size)
					newIDTInPreSSMax = size;
				if (newIDTInPreSSMin>size)
					newIDTInPreSSMin = size;
			}			
		}
		newIDTInPreSSAvg = newIDTInPreSSSum/newIdtBlockNodes.keySet().size();
		 
		
		//calculating #B, avg, max of idt blocks on CoReX
		double oldIDTCoReXAvg = 0.0;
		double oldIDTCoReXMax = -100000.0;
		double oldIDTCoReXMin = 100000.0;
		double oldIDTCoReXSum = 0.0;
		for (Integer block :oldIdtBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = oldIdtBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (old_kept.contains(node))
						size = size + 1;
				}
				oldIDTCoReXSum = oldIDTCoReXSum + size;
				if (oldIDTCoReXMax<size)
					oldIDTCoReXMax = size;
				if (oldIDTCoReXMin>size)
					oldIDTCoReXMin = size;
			}			
		}
		oldIDTCoReXAvg = oldIDTCoReXSum/oldIdtBlockNodes.keySet().size();
		
		
		double newIDTCoReXAvg = 0.0;
		double newIDTCoReXMax = -100000.0;
		double newIDTCoReXMin = 100000.0;
		double newIDTCoReXSum = 0.0;
		for (Integer block :newIdtBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = newIdtBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (new_kept.contains(node))
						size = size + 1;
				}
				newIDTCoReXSum = newIDTCoReXSum + size;
				if (newIDTCoReXMax<size)
					newIDTCoReXMax = size;
				if (newIDTCoReXMin>size)
					newIDTCoReXMin = size;
			}			
		}
		newIDTCoReXAvg = newIDTCoReXSum/newIdtBlockNodes.keySet().size();

		/////////////////#######////#######////#######////#######////#######////#######
		/////////////////#######////#######////#######////#######////#######////#######
		//calculating #B, avg, max of control blocks on dual slice
		double oldCTLDualAvg = 0.0;
		double oldCTLDualMax = -1000000.0;
		double oldCTLDualMin = 100000.0;
		double oldCTLDualSum = 0.0;
		for (Integer block :oldCtlBlockNodes.keySet()) {
			List<TraceNode> nodes = oldCtlBlockNodes.get(block);
			if(nodes!=null) {
				oldCTLDualSum = oldCTLDualSum + nodes.size();
				if (oldCTLDualMax<nodes.size())
					oldCTLDualMax = nodes.size();
				if (oldCTLDualMin>nodes.size())
					oldCTLDualMin = nodes.size();
			}			
		}
		oldCTLDualAvg = oldCTLDualSum/oldCtlBlockNodes.keySet().size();

		
		double newCTLDualAvg = 0.0;
		double newCTLDualMax = -100000.0;
		double newCTLDualMin = 100000.0;
		double newCTLDualSum = 0.0;
		for (Integer block :newCtlBlockNodes.keySet()) {
			List<TraceNode> nodes = newCtlBlockNodes.get(block);
			if(nodes!=null) {
				newCTLDualSum = newCTLDualSum + nodes.size();
				if (newCTLDualMax<nodes.size())
					newCTLDualMax = nodes.size();
				if (newCTLDualMin>nodes.size())
					newCTLDualMin = nodes.size();
			}			
		}
		newCTLDualAvg = newCTLDualSum/newCtlBlockNodes.keySet().size();

		
		//calculating #B, avg, max of control blocks on inpress
		double oldCTLInPreSSAvg = 0.0;
		double oldCTLInPreSSMax = -100000.0;
		double oldCTLInPreSSMin = 100000.0;
		double oldCTLInPreSSSum = 0.0;
		for (Integer block :oldCtlBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = oldCtlBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (inpress_keep_IDT_old_kept.contains(node))
						size = size + 1;
				}
				oldCTLInPreSSSum = oldCTLInPreSSSum + size;
				if (oldCTLInPreSSMax<size)
					oldCTLInPreSSMax = size;
				if (oldCTLInPreSSMin>size)
					oldCTLInPreSSMin = size;
			}			
		}
		oldCTLInPreSSAvg = oldCTLInPreSSSum/oldCtlBlockNodes.keySet().size();

		
		double newCTLInPreSSAvg = 0.0;
	    double newCTLInPreSSMax = -100000.0;
	    double newCTLInPreSSMin = 100000.0;
	    double newCTLInPreSSSum = 0.0;
		for (Integer block :newCtlBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = newCtlBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (inpress_keep_IDT_new_kept.contains(node))
						size = size + 1;
				}
				newCTLInPreSSSum = newCTLInPreSSSum + size;
				if (newCTLInPreSSMax<size)
					newCTLInPreSSMax = size;
				if (newCTLInPreSSMin>size)
					newCTLInPreSSMin = size;
			}			
		}
		newCTLInPreSSAvg = newCTLInPreSSSum/newCtlBlockNodes.keySet().size();		
	    
		//calculating #B, avg, max of control blocks on corex
		double oldCTLCoReXAvg = 0.0;
		double oldCTLCoReXMax = -100000.0;
		double oldCTLCoReXMin = 100000.0;
		double oldCTLCoReXSum = 0.0;
		for (Integer block :oldCtlBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = oldCtlBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (old_kept.contains(node))
						size = size + 1;
				}
				oldCTLCoReXSum = oldCTLCoReXSum + size;
				if (oldCTLCoReXMax<size)
					oldCTLCoReXMax = size;
				if (oldCTLCoReXMin>size)
					oldCTLCoReXMin = size;
			}			
		}
		oldCTLCoReXAvg = oldCTLCoReXSum/oldCtlBlockNodes.keySet().size();

		
		double newCTLCoReXAvg = 0.0;
	    double newCTLCoReXMax = -100000.0;
	    double newCTLCoReXMin = 100000.0;
	    double newCTLCoReXSum = 0.0;
		for (Integer block :newCtlBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = newCtlBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (new_kept.contains(node))
						size = size + 1;
				}
				newCTLCoReXSum = newCTLCoReXSum + size;
				if (newCTLCoReXMax<size)
					newCTLCoReXMax = size;
				if (newCTLCoReXMin>size)
					newCTLCoReXMin = size;
			}			
		}
		newCTLCoReXAvg = newCTLCoReXSum/newCtlBlockNodes.keySet().size();		
	    
		
		
		/////////////////#######////#######////#######////#######////#######////#######
		/////////////////#######////#######////#######////#######////#######////#######
		
		
		
	    double Dual_reducOldData =  (Double.valueOf(dual_keep_IDT_old_visited.size())-(old_retained.size()+oldCTLDualSum+oldIDTDualSum+oldDATCoReXSum))/(Double.valueOf(dual_keep_IDT_old_visited.size()))*100.0;
	    double Dual_reducOldCTL =  (Double.valueOf(dual_keep_IDT_old_visited.size())-(old_retained.size()+oldDATDualSum+oldIDTDualSum+oldCTLCoReXSum))/(Double.valueOf(dual_keep_IDT_old_visited.size()))*100.0;
	    double Dual_reducOldIDT =  (Double.valueOf(dual_keep_IDT_old_visited.size())-(old_retained.size()+oldDATDualSum+oldCTLDualSum+oldIDTCoReXSum))/(Double.valueOf(dual_keep_IDT_old_visited.size()))*100.0;
	    double Dual_reducnewData =  (Double.valueOf(dual_keep_IDT_new_visited.size())-(new_retained.size()+newCTLDualSum+newIDTDualSum+newDATCoReXSum))/(Double.valueOf(dual_keep_IDT_new_visited.size()))*100.0;
	    double Dual_reducnewCTL =  (Double.valueOf(dual_keep_IDT_new_visited.size())-(new_retained.size()+newDATDualSum+newIDTDualSum+newCTLCoReXSum))/(Double.valueOf(dual_keep_IDT_new_visited.size()))*100.0;
	    double Dual_reducnewIDT =  (Double.valueOf(dual_keep_IDT_new_visited.size())-(new_retained.size()+newDATDualSum+newCTLDualSum+newIDTCoReXSum))/(Double.valueOf(dual_keep_IDT_new_visited.size()))*100.0;
	    
	    double InPreSS_reducOldData =  (Double.valueOf(inpress_keep_IDT_old_kept.size())-(old_retained.size()+oldCTLInPreSSSum+oldIDTInPreSSSum+oldDATCoReXSum))/(Double.valueOf(inpress_keep_IDT_old_kept.size()))*100.0;
	    double InPreSS_reducOldCTL =  (Double.valueOf(inpress_keep_IDT_old_kept.size())-(old_retained.size()+oldDATInPreSSSum+oldIDTInPreSSSum+oldCTLCoReXSum))/(Double.valueOf(inpress_keep_IDT_old_kept.size()))*100.0;
	    double InPreSS_reducOldIDT =  (Double.valueOf(inpress_keep_IDT_old_kept.size())-(old_retained.size()+oldDATInPreSSSum+oldCTLInPreSSSum+oldIDTCoReXSum))/(Double.valueOf(inpress_keep_IDT_old_kept.size()))*100.0;
	    double InPreSS_reducnewData =  (Double.valueOf(inpress_keep_IDT_new_kept.size())-(new_retained.size()+newCTLInPreSSSum+newIDTInPreSSSum+newDATCoReXSum))/(Double.valueOf(inpress_keep_IDT_new_kept.size()))*100.0;
	    double InPreSS_reducnewCTL =  (Double.valueOf(inpress_keep_IDT_new_kept.size())-(new_retained.size()+newDATInPreSSSum+newIDTInPreSSSum+newCTLCoReXSum))/(Double.valueOf(inpress_keep_IDT_new_kept.size()))*100.0;
	    double InPreSS_reducnewIDT =  (Double.valueOf(inpress_keep_IDT_new_kept.size())-(new_retained.size()+newDATInPreSSSum+newCTLInPreSSSum+newIDTCoReXSum))/(Double.valueOf(inpress_keep_IDT_new_kept.size()))*100.0;
	    
	    if (FirstTime) {		    	
	        String[] header = {"Bug ID", 	        		
	        		"# Old mathched block", "Old Match Avg.", "Old Match Max", "%Old Match Reduction (vs Dual)", "%Old Match Reduction (vs InPreSS)",
	        		"# Old identical block", "Old Identical Avg.", "Old Identical Max", "%Old Identical Reduction (vs Dual)", "%Old Identical Reduction (vs InPreSS)",
	        		"# Old unmathched block", "Old UnMatch Avg.", "Old UnMatch Max", "%Old UnMatch Reduction", "%Old UnMatch Reduction (vs Dual)", "%Old UnMatch Reduction (vs InPreSS)",
	        		"# New mathched block", "New Match Avg.", "New Match Max", "%New Match Reduction", "%New Match Reduction (vs Dual)", "%New Match Reduction (vs InPreSS)",
	        		"# New identical block", "New Identical Avg.", "New Identical Max", "%New Identical Reduction", "%New Identical Reduction (vs Dual)", "%New Identical Reduction (vs InPreSS)",
	        		"# New unmathched block", "New UnMatch Avg.", "New UnMatch Max", "%New UnMatch Reduction", "%New UnMatch Reduction (vs Dual)", "%New UnMatch Reduction (vs InPreSS)"
	        		};
	        WriteToExcel(results, header, "RQ3-4",true,true);
	    }
	    
	    String[] detailedDataRQ3 = {bugID, 
	    		String.valueOf(oldDataBlockNodes.keySet().size()), String.valueOf(oldDATCoReXAvg),String.valueOf(oldDATCoReXMax),String.valueOf(Dual_reducOldData),String.valueOf(InPreSS_reducOldData),
	    		String.valueOf(oldIdtBlockNodes.keySet().size()), String.valueOf(oldIDTCoReXAvg),String.valueOf(oldIDTCoReXMax),String.valueOf(Dual_reducOldIDT),String.valueOf(InPreSS_reducOldIDT),
	    		String.valueOf(oldCtlBlockNodes.keySet().size()), String.valueOf(oldCTLCoReXAvg),String.valueOf(oldCTLCoReXMax),String.valueOf(Dual_reducOldCTL),String.valueOf(InPreSS_reducOldCTL),
	    		String.valueOf(newDataBlockNodes.keySet().size()), String.valueOf(newDATCoReXAvg),String.valueOf(newDATCoReXMax),String.valueOf(Dual_reducnewData),String.valueOf(InPreSS_reducnewData),
	    		String.valueOf(newIdtBlockNodes.keySet().size()), String.valueOf(newIDTCoReXAvg),String.valueOf(newIDTCoReXMax),String.valueOf(Dual_reducnewIDT),String.valueOf(InPreSS_reducnewIDT),
	    		String.valueOf(newCtlBlockNodes.keySet().size()), String.valueOf(newCTLCoReXAvg),String.valueOf(newCTLCoReXMax),String.valueOf(Dual_reducnewCTL),String.valueOf(InPreSS_reducnewCTL),
	    		};
	       WriteToExcel(results,detailedDataRQ3,"RQ3-4",true,false);
	    
	       /////////////////#######////#######////#######////#######////#######////#######
	       /////////////////#######////#######////#######////#######////#######////#######
	       
	       boolean Einspect5_Dual = CanFindTheBug(5, old_visited, new_visited,old_retained,new_retained);
	       boolean Einspect5_InPreSS = CanFindTheBug(5, inpress_old_kept, inpress_new_kept,old_retained,new_retained);
	       boolean Einspect5_CoReX = CanFindTheBug(5, old_kept, new_kept,old_retained,new_retained);
	       
	       boolean Einspect10_Dual = CanFindTheBug(10, old_visited, new_visited,old_retained,new_retained);
	       boolean Einspect10_InPreSS = CanFindTheBug(10, inpress_old_kept, inpress_new_kept,old_retained,new_retained);
	       boolean Einspect10_CoReX = CanFindTheBug(10, old_kept, new_kept,old_retained,new_retained);
	       
	       boolean Einspect30_Dual = CanFindTheBug(30, old_visited, new_visited,old_retained,new_retained);
	       boolean Einspect30_InPreSS = CanFindTheBug(30, inpress_old_kept, inpress_new_kept,old_retained,new_retained);
	       boolean Einspect30_CoReX = CanFindTheBug(30, old_kept, new_kept,old_retained,new_retained);
	       
	       boolean Einspect50_Dual = CanFindTheBug(50, old_visited, new_visited,old_retained,new_retained);
	       boolean Einspect50_InPreSS = CanFindTheBug(50, inpress_old_kept, inpress_new_kept,old_retained,new_retained);
	       boolean Einspect50_CoReX = CanFindTheBug(50, old_kept, new_kept,old_retained,new_retained);
	  
	       boolean Einspect100_Dual = CanFindTheBug(100, old_visited, new_visited,old_retained,new_retained);
	       boolean Einspect100_InPreSS = CanFindTheBug(100, inpress_old_kept, inpress_new_kept,old_retained,new_retained);
	       boolean Einspect100_CoReX = CanFindTheBug(100, old_kept, new_kept,old_retained,new_retained);
	  
	       boolean Einspect200_Dual = CanFindTheBug(200, old_visited, new_visited,old_retained,new_retained);
	       boolean Einspect200_InPreSS = CanFindTheBug(200, inpress_old_kept, inpress_new_kept,old_retained,new_retained);
	       boolean Einspect200_CoReX = CanFindTheBug(200, old_kept, new_kept,old_retained,new_retained);
	       
	       int traversed_old_Dual = CalculateWastedEffort(old_visited,old_retained);
	       int traversed_new_Dual = CalculateWastedEffort(new_visited,new_retained);
	       int traversed_old_InPreSS = CalculateWastedEffort(inpress_old_kept,old_retained);
	       int traversed_new_InPreSS = CalculateWastedEffort(inpress_new_kept,new_retained);
	       int traversed_old_CoReX = CalculateWastedEffort(old_kept,old_retained);
	       int traversed_new_CoReX = CalculateWastedEffort(new_kept,new_retained);
	       
	       double wasted_effort_old_Dual = (double)traversed_old_Dual/oldTrace.getExecutionList().size();
	       double wasted_effort_new_Dual = (double)traversed_new_Dual/newTrace.getExecutionList().size();
	       double wasted_effort_old_InPreSS = (double)traversed_old_InPreSS/oldTrace.getExecutionList().size();
	       double wasted_effort_new_InPreSS = (double)traversed_new_InPreSS/newTrace.getExecutionList().size();
	       double wasted_effort_old_CoReX = (double)traversed_old_CoReX/oldTrace.getExecutionList().size();
	       double wasted_effort_new_CoRex = (double)traversed_new_CoReX/newTrace.getExecutionList().size();
	       
	       if (FirstTime) {		    	
		        String[] header = {"Bug ID", 
		        		"Einspect@5-Dual", "Einspect@5-InPreSS", "Einspect@5-CoReX", 
		        		"Einspect@10-Dual", "Einspect@10-InPreSS", "Einspect@10-CoReX", 
		        		"Einspect@30-Dual", "Einspect@30-InPreSS", "Einspect@30-CoReX",
		        		"Einspect@50-Dual", "Einspect@50-InPreSS", "Einspect@50-CoReX",
		        		"Einspect@100-Dual", "Einspect@100-InPreSS", "Einspect@100-CoReX",
		        		"Einspect@200-Dual", "Einspect@200-InPreSS", "Einspect@200-CoReX",
		        		"#Traversed Old Stmt-Dual", "#Traversed New Stmt-Dual", "#Traversed Old Stmt-InPreSS", "#Traversed New Stmt-InPreSS", "#Traversed Old Stmt-CoReX","#Traversed New Stmt-CoReX",
		        		"Exam% Old-Dual", "Exam% New-Dual", "Exam% Old-InPreSS", "Exam% New-InPreSS", "Exam% Old-CoReX","Exam% New-CoReX",
		        		
		        		};
		        WriteToExcel(results, header, "RQ3-3",true, true);
		    }
		    String[] detailedDataRQ4 = {bugID, 
		    		String.valueOf(Einspect5_Dual),String.valueOf(Einspect5_InPreSS),String.valueOf(Einspect5_CoReX),
		    		String.valueOf(Einspect10_Dual),String.valueOf(Einspect10_InPreSS),String.valueOf(Einspect10_CoReX),
		    		String.valueOf(Einspect30_Dual),String.valueOf(Einspect30_InPreSS),String.valueOf(Einspect30_CoReX),
		    		String.valueOf(Einspect50_Dual),String.valueOf(Einspect50_InPreSS),String.valueOf(Einspect50_CoReX),
		    		String.valueOf(Einspect100_Dual),String.valueOf(Einspect100_InPreSS),String.valueOf(Einspect100_CoReX),
		    		String.valueOf(Einspect200_Dual),String.valueOf(Einspect200_InPreSS),String.valueOf(Einspect200_CoReX),
		    		String.valueOf(traversed_old_Dual),String.valueOf(traversed_new_Dual),String.valueOf(traversed_old_InPreSS),String.valueOf(traversed_new_InPreSS),String.valueOf(traversed_old_CoReX),String.valueOf(traversed_new_CoReX),
		    		String.valueOf(wasted_effort_old_Dual),String.valueOf(wasted_effort_new_Dual),String.valueOf(wasted_effort_old_InPreSS),String.valueOf(wasted_effort_new_InPreSS),String.valueOf(wasted_effort_old_CoReX),String.valueOf(wasted_effort_new_CoRex)
		    };
		    WriteToExcel(results,detailedDataRQ4,"RQ3-3",true, false);
						

		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
		System.out.println("##############Finish##############");
		
		
	}
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
private int CalculateWastedEffort(List<TraceNode> visited, List<TraceNode> retained) {
		int NoStmt = 0;
		int traversed = 0;
		Collections.sort(visited, new TraceNodeOrderComparator());
		for(int i=visited.size()-1;i>=0;i--) {
			traversed++;
			if(retained.contains(visited.get(i)))
				NoStmt ++;
			if(NoStmt==retained.size())
				return traversed;
		}
		return traversed;
}
	////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
	private boolean CanFindTheBug(int EInsp, List<TraceNode> old_visited, List<TraceNode> new_visited,List<TraceNode> old_retained, List<TraceNode> new_retained) {
		boolean found = false;
		int count_old = 0;
		int count_new = 0;
		Collections.sort(old_visited, new TraceNodeOrderComparator());
		Collections.sort(new_visited, new TraceNodeOrderComparator());
		if(old_visited.size()-EInsp>=0)
			for(int i=old_visited.size()-1;i>=old_visited.size()-EInsp;i--) {
				if(old_retained.contains(old_visited.get(i)))
					count_old ++;
			}
		else
			for(int i=old_visited.size()-1;i>=0;i--) {
				if(old_retained.contains(old_visited.get(i)))
					count_old ++;
			}
		if(new_visited.size()-EInsp>=0)
			for(int i=new_visited.size()-1;i>=new_visited.size()-EInsp;i--) {
				if(new_retained.contains(new_visited.get(i)))
					count_new ++;
			}
		else
			for(int i=new_visited.size()-1;i>=0;i--) {
				if(new_retained.contains(new_visited.get(i)))
					count_new ++;
			}
		if(count_old==old_retained.size() && count_new==new_retained.size())
			found = true;
		return found;		
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void corexAlgorithmOptimized(TestCase tc,String proPath, List<TraceNode> old_visited, List<TraceNode> new_visited, 
			StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher, 
			HashMap<TraceNode, List<Pair<TraceNode, String>>> old_data_map, HashMap<TraceNode, List<TraceNode>> old_ctl_map, 
			HashMap<TraceNode, List<Pair<TraceNode, String>>> new_data_map, HashMap<TraceNode, List<TraceNode>> new_ctl_map, 
			List<TraceNode> old_kept, List<TraceNode> new_kept, List<TraceNode> inpress_keep_IDT_old_kept, List<TraceNode> inpress_keep_IDT_new_kept,
			List<TraceNode> corex_removing_DAT_IDT_old_kept, List<TraceNode> corex_removing_DAT_IDT_new_kept,
			HashMap<Integer, List<TraceNode>> oldDataBlockNodes, 
			HashMap<Integer, List<TraceNode>> newDataBlockNodes,HashMap<Integer, List<TraceNode>> oldCtlBlockNodes,
			HashMap<Integer, List<TraceNode>> newCtlBlockNodes, HashMap<Integer, List<TraceNode>> oldIdtBlockNodes,HashMap<Integer, List<TraceNode>> newIdtBlockNodes, 
			List<TraceNode> old_retained, List<TraceNode> new_retained,List<String> old_kept_sourceCodeLevel, List<String> new_kept_sourceCodeLevel, HashMap<TraceNode, List<Pair<TraceNode, String>>> new_corex_edges, HashMap<TraceNode, List<Pair<TraceNode, String>>> old_corex_edges) {
		
		/////////////////////////////////////////////////////////////
		Collections.sort(old_visited, new TraceNodeOrderComparator());
		Collections.sort(new_visited, new TraceNodeOrderComparator());                	
		/////////////////////extract blocks for old/////////////////////
		HashMap<Integer, List<TraceNode>> oldCtlBlockNodesTemp = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newCtlBlockNodesTemp = new HashMap<>();
		HashMap<TraceNode, Integer> oldBlocks = new HashMap<>();
		Integer BlockID = 0;
		boolean current_data_flag = false;
		boolean current_ctl_flag = false;
		boolean current_idt_flag = false;
		boolean firstTime = true;
		boolean isDataBlock = false;
		boolean isCTLBlock = false;
		boolean isIDTBlock = false;
		for(int i=old_visited.size()-1;i>=0; i--){
			TraceNode step = old_visited.get(i);	
//			System.out.println("step on old is: " + step);	
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
//			System.out.println("step type: " + changeType.getType());	
			//if ((changeType.getType()!=StepChangeType.DAT || i==old_visited.size()-1) && changeType.getType()!=StepChangeType.CTL) { //separate the blocks
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || (isATestStatement(tc, step) && isLastStatement(tc, step,old_visited))) { //it is retain		
				isDataBlock = false;
				isCTLBlock = false;
				isIDTBlock = false;
				if (current_data_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
					//firstTime = false;
				}
				if (current_idt_flag) {//coming from an identical block
					//BlockID = BlockID + 1;
					current_idt_flag = false;
					//firstTime = false;
				}
				if (current_ctl_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isDataBlock = false;
				isCTLBlock = true;
				isIDTBlock = false;
				if (!current_ctl_flag) {//if we are not currently in ctl block
					BlockID = BlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
					current_idt_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.DAT){ 
				isDataBlock = true;
				isCTLBlock = false;		
				isIDTBlock = false;
				if (!current_data_flag) {//if we are not currently in data block
					BlockID = BlockID + 1;
					current_data_flag = true;
					current_ctl_flag = false;
					current_idt_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.IDT){ 
				isIDTBlock = true;
				isDataBlock = false;
				isCTLBlock = false;				
				if (!current_idt_flag) {//if we are not currently in idt block
					BlockID = BlockID + 1;
					current_idt_flag = true;
					current_data_flag = false;
					current_ctl_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
	//		if(firstTime) {
	//			firstTime = false;
	//			BlockID = BlockID + 1;
	//		}
			
	//		oldBlocks.put(step, BlockID);	
			
		}	
//		System.out.println("old blocks " + oldBlocks);	
		/////////////////////extract blocks for new/////////////////////
		HashMap<TraceNode, Integer> newBlocks = new HashMap<>();
		BlockID = 0;
		int CTLBlockID = 0;
		current_data_flag = false;
		current_ctl_flag = false;
		current_idt_flag = false;
		firstTime = true;
		isDataBlock = false;
		isCTLBlock = false;
		isIDTBlock = false;
		TraceNode previousData = null;
		TraceNode previousIDT = null;
		for(int i=new_visited.size()-1;i>=0; i--){
			TraceNode step = new_visited.get(i);
			//System.out.println("step on new is: " + step);	
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
			//if ((changeType.getType()!=StepChangeType.DAT || i==new_visited.size()-1) && changeType.getType()!=StepChangeType.CTL) { //separate the blocks
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || (isATestStatement(tc, step) && isLastStatement(tc, step,new_visited))) { //separate the blocks				
				isDataBlock = false;
				isCTLBlock = false;
				isIDTBlock = false;
				if (current_data_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
					//firstTime = false;
				}
				if (current_ctl_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
					//firstTime = false;
				}
				if (current_idt_flag) {//coming from an identical block
					//BlockID = BlockID + 1;
					current_idt_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isDataBlock = false;
				isIDTBlock = false;
				isCTLBlock = true;
				if (!current_ctl_flag) {//coming from dat or other blocks
					CTLBlockID = CTLBlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
					current_idt_flag = false;
					//firstTime = false;
				}
				newBlocks.put(step, CTLBlockID);//will be updated later once we know the number of all data blocks
			}
			else if (changeType.getType()==StepChangeType.DAT){ 
				isDataBlock = true;
				isCTLBlock = false;	
				isIDTBlock = false;
				if (previousData!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousData, true, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();					
					if(oldBlocks.get(matchedStep)!=oldBlocks.get(previousMatchedStep)) {//separate if it is separated in old 									
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						current_idt_flag = false;
						//firstTime = false;
					}					
					else {			
						if (!current_data_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = true;
							current_ctl_flag = false;
							current_idt_flag = false;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_data_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						current_idt_flag = false;
						//firstTime = false;
					}
					
				}
				previousData = step;
				newBlocks.put(step, BlockID);	
			}
			else if (changeType.getType()==StepChangeType.IDT){ 
				isDataBlock = false;
				isCTLBlock = false;	
				isIDTBlock = true;
				if (previousIDT!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousIDT, true, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();
					if(oldBlocks.get(matchedStep)!=oldBlocks.get(previousMatchedStep)) {//separate if it is separated in old 									
						BlockID = BlockID + 1;
						current_data_flag = false;
						current_ctl_flag = false;
						current_idt_flag = true;
						//firstTime = false;
					}					
					else {			
						if (!current_idt_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = false;
							current_ctl_flag = false;
							current_idt_flag = true;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_idt_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = false;
						current_ctl_flag = false;
						current_idt_flag = true;
						//firstTime = false;
					}
					
				}
				previousIDT = step;
				newBlocks.put(step, BlockID);	
			}
	//		if (firstTime) {
	//			BlockID = BlockID + 1;
	//			firstTime = false;
	//		}
	//		newBlocks.put(step, BlockID);
		
			if (isDataBlock){
				if (newDataBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = newDataBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					newDataBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					newDataBlockNodes.put(BlockID, nodes);
				}
			}
			if (isCTLBlock){
				if (newCtlBlockNodesTemp.containsKey(CTLBlockID)){
					List<TraceNode> nodes = newCtlBlockNodesTemp.get(CTLBlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					newCtlBlockNodesTemp.put(CTLBlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					newCtlBlockNodesTemp.put(CTLBlockID, nodes);
				}
			}
			if (isIDTBlock){
				if (newIdtBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = newIdtBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					newIdtBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					newIdtBlockNodes.put(BlockID, nodes);
				}
			}
		}
//		System.out.println("new blocks " + newBlocks);
		/////////////////////extract blocks for old/////////////////////
		oldBlocks = new HashMap<>();
		BlockID = 0;
		CTLBlockID = 0;
		current_data_flag = false;
		current_ctl_flag = false;
		current_idt_flag = false;
		firstTime = true;
		isDataBlock = false;
		isCTLBlock = false;
		isIDTBlock = false;
		previousData = null;
		previousIDT = null;
		for(int i=old_visited.size()-1;i>=0; i--){
			TraceNode step = old_visited.get(i);
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || (isATestStatement(tc, step) && isLastStatement(tc, step,old_visited))) { //separate the blocks
				isDataBlock = false;
				isCTLBlock = false;
				isIDTBlock = false;
				if (current_data_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
					//firstTime = false;
				}
				if (current_ctl_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
					//firstTime = false;
				}
				if (current_idt_flag) {//coming from an identical block
					//BlockID = BlockID + 1;
					current_idt_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isDataBlock = false;
				isCTLBlock = true;
				isIDTBlock = false;
				if (!current_ctl_flag) {//coming from dat or other blocks
					CTLBlockID = CTLBlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
					current_idt_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, CTLBlockID);//will be updated later
			}
			else if (changeType.getType()==StepChangeType.DAT){ 
				isDataBlock = true;
				isCTLBlock = false;	
				isIDTBlock = false;
				if (previousData!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousData, false, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();
					if(newBlocks.get(matchedStep)!=newBlocks.get(previousMatchedStep)) {//separate them 									
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						current_idt_flag = false;
						//firstTime = false;
					}					
					else {			
						if (!current_data_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = true;
							current_ctl_flag = false;
							current_idt_flag = false;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_data_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						current_idt_flag = false;
						//firstTime = false;
					}
				}
				previousData = step;
				oldBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.IDT){ 
				isDataBlock = false;
				isCTLBlock = false;	
				isIDTBlock = true;
				if (previousIDT!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousIDT, false, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();
					if(newBlocks.get(matchedStep)!=newBlocks.get(previousMatchedStep)) {//separate them 									
						BlockID = BlockID + 1;
						current_data_flag = false;
						current_ctl_flag = false;
						current_idt_flag = true;
						//firstTime = false;
					}					
					else {			
						if (!current_idt_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = false;
							current_ctl_flag = false;
							current_idt_flag = true;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_idt_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = false;
						current_ctl_flag = false;
						current_idt_flag = true;
						//firstTime = false;
					}
				}
				previousIDT = step;
				oldBlocks.put(step, BlockID);
			}
	//		if (firstTime) {
	//			BlockID = BlockID + 1;
	//			firstTime = false;
	//		}
	//		oldBlocks.put(step, BlockID);
			if (isDataBlock){
				if (oldDataBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = oldDataBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					oldDataBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					oldDataBlockNodes.put(BlockID, nodes);
				}
			}
			if (isCTLBlock){
				if (oldCtlBlockNodesTemp.containsKey(CTLBlockID)){
					List<TraceNode> nodes = oldCtlBlockNodesTemp.get(CTLBlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					oldCtlBlockNodesTemp.put(CTLBlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					oldCtlBlockNodesTemp.put(CTLBlockID, nodes);
				}
			}
			if (isIDTBlock){
				if (oldIdtBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = oldIdtBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					oldIdtBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					oldIdtBlockNodes.put(BlockID, nodes);
				}
			}
		}
		///////////////////////////////////////////////////////////////////////////////////////////////////
		//update the control blocksID: 
		CTLBlockID = BlockID + 1;
		for(Integer ctlblockID:oldCtlBlockNodesTemp.keySet()) {
			oldCtlBlockNodes.put(CTLBlockID,oldCtlBlockNodesTemp.get(ctlblockID));
			for(TraceNode node:oldCtlBlockNodesTemp.get(ctlblockID))
				oldBlocks.put(node, CTLBlockID);
			CTLBlockID += 1;
		}
		for(Integer ctlblockID:newCtlBlockNodesTemp.keySet()) {
			newCtlBlockNodes.put(CTLBlockID,newCtlBlockNodesTemp.get(ctlblockID));	
			for(TraceNode node:newCtlBlockNodesTemp.get(ctlblockID))
				newBlocks.put(node, CTLBlockID);
			CTLBlockID += 1;
		}
//		System.out.println("#################after paralizing#################"); 
//		System.out.println("The # of data block in old " + oldDataBlockNodes);
//		System.out.println("The # of data block in new " + newDataBlockNodes);
//		System.out.println("The # of ctl block in old " + oldCtlBlockNodes);
//		System.out.println("The # of ctl block in new " + newCtlBlockNodes);
//		System.out.println("The # of idt block in old " + oldIdtBlockNodes);
//		System.out.println("The # of idt block in new " + newIdtBlockNodes);
//		////////////////////////////////////////////////////////////////////////////////////////////////////////
//		////////////////////////////////////////////////////////////////////////////////////////////////////////
//		////////////////////////////////////////////////////////////////////////////////////////////////////////	
//		////////////////////////////////////////////////////////////////////////////////////////////////////////
//		/////////////////////abstraction////////////////////////////////////////////////////////////////
			//should also the corresponding kept node from the other trace be add?
		
			Collections.sort(old_visited, new TraceNodeOrderComparator());
			Collections.sort(new_visited, new TraceNodeOrderComparator());
			
			List<TraceNode> new_dat_kept = new ArrayList<>();
			List<TraceNode> old_dat_kept = new ArrayList<>();
			
			inpress_keep_IDT_old_kept.add(old_visited.get(old_visited.size()-1));
			inpress_keep_IDT_new_kept.add(new_visited.get(new_visited.size()-1));
											
			HashMap<TraceNode, List<Pair<Integer,String>>> old_data_node_function = new HashMap<>();
			HashMap<TraceNode, List<Pair<Integer,String>>> new_data_node_function = new HashMap<>();
			HashMap<TraceNode, List<Pair<Integer,String>>> old_ctl_node_function = new HashMap<>();
			HashMap<TraceNode, List<Pair<Integer,String>>> new_ctl_node_function = new HashMap<>();
//			HashMap<TraceNode, Integer> old_idt_node_function = new HashMap<>();
//			HashMap<TraceNode, Integer> new_idt_node_function = new HashMap<>();
			Integer index = 0;
			
			
			
			List<TraceNode> new_workList = new ArrayList<>();
			List<TraceNode> old_workList = new ArrayList<>();
			new_workList.add(new_visited.get(new_visited.size()-1));
			old_workList.add(old_visited.get(old_visited.size()-1));
			
			while(!new_workList.isEmpty() || !old_workList.isEmpty()){
				while(!new_workList.isEmpty()) {
//					System.out.println("#############################");
					TraceNode step = new_workList.remove(0);
				    updateKept(tc,step, new_visited, new_workList,old_visited,old_workList,true,typeChecker,
				    		pairList,matcher,new_data_map,new_ctl_map, proPath,new_retained,old_retained,new_kept,old_kept,newBlocks);				
				}
				////////////////////////////////////////////////////////////////////////////////////////
				while(!old_workList.isEmpty()) {
//					System.out.println("#############################");
					TraceNode step = old_workList.remove(0);
					updateKept(tc,step, old_visited, old_workList,new_visited,new_workList,false,typeChecker,
				    		pairList,matcher,old_data_map,old_ctl_map, proPath,old_retained,new_retained,old_kept,new_kept,oldBlocks);
				}			
			}	
			System.out.println("The initial nodes in old after removing unnecessary matched and identical " + old_kept);
			System.out.println("The initial nodes in new after removing unnecessary matched and identical  " + new_kept);
			Collections.sort(old_kept, new TraceNodeOrderComparator());
			Collections.sort(new_kept, new TraceNodeOrderComparator());
			
	/////////////////////////////////////Now 2) add the context of variables we decided to keep  ///////////////////////////////////////////////
			for(int i=old_kept.size()-1;i>=0; i--){
				TraceNode step = old_kept.get(i);
				old_corex_edges.put(step,null);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
				getContext(step,old_kept,old_corex_edges,old_data_map,old_ctl_map,old_data_node_function,old_ctl_node_function,changeType);					
			}
			for(int i=new_kept.size()-1;i>=0; i--){
				TraceNode step = new_kept.get(i);
				new_corex_edges.put(step,null);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
				getContext(step,new_kept,new_corex_edges,new_data_map,new_ctl_map,new_data_node_function,new_ctl_node_function,changeType);					
			}
			System.out.println("Final nodes in old " + old_kept);
			System.out.println("Final nodes in new " + new_kept);
	}
	private void updateKept(TestCase tc,TraceNode step, List<TraceNode> visited, List<TraceNode> workList,
			List<TraceNode> other_visited, List<TraceNode> other_workList, boolean isNew, StepChangeTypeChecker typeChecker,
			PairList pairList, DiffMatcher matcher, HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map,
			HashMap<TraceNode, List<TraceNode>> ctl_map, String proPath, List<TraceNode> retained,List<TraceNode> other_retained, List<TraceNode> kept, List<TraceNode> other_kept,HashMap<TraceNode, Integer> Blocks) {
				    
//			System.out.println("this is step on old: " + step);
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, isNew, pairList, matcher);											
			
			if(changeType.getType()==StepChangeType.SRCCTL || changeType.getType()==StepChangeType.SRCDAT || isLastStatement(tc, step,visited)) {//retain statement
				if(changeType.getType()==StepChangeType.SRCDAT || isLastStatement(tc, step,visited)) {	
					TraceNode matchedStep = changeType.getMatchingStep();
					if(matchedStep!=null) {
						if(!other_retained.contains(matchedStep))
							other_retained.add(matchedStep);
						if(!other_kept.contains(matchedStep)) {
							other_kept.add(matchedStep);
							other_workList.add(matchedStep);
						}
						
						
					}
				}
				if(!retained.contains(step))
					retained.add(step);
				if(!kept.contains(step))
					kept.add(step);										
			}
			
			else if (changeType.getType()==StepChangeType.CTL && !isLastStatement(tc, step,visited)) {
				if(!kept.contains(step)) 
					kept.add(step);										
			}
			
			else if ((changeType.getType()==StepChangeType.DAT && !isLastStatement(tc, step,visited))||(changeType.getType()==StepChangeType.IDT && !isLastStatement(tc, step,visited))) {									
				TraceNode matchedStep = changeType.getMatchingStep();	
				if(!other_visited.contains(matchedStep)) { //only in one trace/slice => keep
					if(!kept.contains(step)) {
						kept.add(step);	
						if(matchedStep!=null) {
							if(!other_kept.contains(matchedStep)) { //add the symmetric data and identical to other trace
								other_kept.add(matchedStep);
								other_workList.add(matchedStep);
						     }
						}
					}
				}
				else {//if the other trace contains but for different reason: from different dependency
//					System.out.println("step is " + step);
					boolean found = false;
					for(TraceNode dominatee:step.getDataDominatee().keySet()) {
						StepChangeType t = typeChecker.getTypeForPrinting(dominatee, false, pairList, matcher);
						TraceNode matchedDominatee = t.getMatchingStep();	
						if(matchedStep.getDataDominatee().keySet().contains(matchedDominatee)) {
//							System.out.println("it is found in the other trace");
							found = true;
						}
					}
					if(!found) {
						if(!kept.contains(step)) {
							kept.add(step);			
							if(matchedStep!=null) {
								if(!other_kept.contains(matchedStep)) {//add the symmetric data and identical to other trace
									other_kept.add(matchedStep);
									other_workList.add(matchedStep);								
								}
							}
						}
					}
				}
				if(step.getReadVariables().size()==0) {//it is reaching definition =>keep
					if(!kept.contains(step)) {
						kept.add(step);			
						if(matchedStep!=null) {
							if(!other_kept.contains(matchedStep)) {//add the symmetric data and identical to other trace
								other_kept.add(matchedStep);	
								other_workList.add(matchedStep);
							}
						}
					}
				}
				if(step.isBranch()||step.isLoopCondition() || step.isConditional()) {// it is the control condition that makes control block => keep
					if(!kept.contains(step)) {
						kept.add(step);	
						if(matchedStep!=null) {
							if(!other_kept.contains(matchedStep)) {//add the symmetric data and identical to other trace
								other_kept.add(matchedStep);	
								other_workList.add(matchedStep);
							}
						}
					}
				}
				
			}
						
			List<Pair<TraceNode, String>> data_deps = data_map.get(step);	
//			System.out.println("data deps: " + data_deps);
			if(data_deps!=null) 
				for(Pair<TraceNode, String> pair:data_deps) 
					if(visited.contains(pair.first()))
						if(Blocks.get(pair.first())!=Blocks.get(step))								
							if(!workList.contains(pair.first())) {										
								workList.add(pair.first());
							}
			
			List<TraceNode> ctl_deps = ctl_map.get(step);
//			System.out.println("control deps: " + ctl_deps);
			if(changeType.getType()==StepChangeType.CTL)//if the node is control diff we also want to keep the if statement 
				if(ctl_deps!=null) 
					for(TraceNode node:ctl_deps) {
						StepChangeType changeTypes = typeChecker.getTypeForPrinting(node, false, pairList, matcher);				
						if(changeTypes.getType()==StepChangeType.DAT || changeTypes.getType()==StepChangeType.SRCDAT){//keep the control condition causing the control block
//							System.out.println("control dep which is DAT");
							if(visited.contains(node))
								if(!kept.contains(node)) {
									kept.add(node);	
									workList.add(node);
								}	
						}
					}				
}
		
//##############################################//##############################################//##############################################
//##############################################//##############################################//##############################################
//##############################################//##############################################//##############################################
   
	private void corexAlgorithm(TestCase tc,String proPath, List<TraceNode> old_visited, List<TraceNode> new_visited, 
			StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher, 
			HashMap<TraceNode, List<Pair<TraceNode, String>>> old_data_map, HashMap<TraceNode, List<TraceNode>> old_ctl_map, 
			HashMap<TraceNode, List<Pair<TraceNode, String>>> new_data_map, HashMap<TraceNode, List<TraceNode>> new_ctl_map, 
			List<TraceNode> old_kept, List<TraceNode> new_kept, List<TraceNode> inpress_keep_IDT_old_kept, List<TraceNode> inpress_keep_IDT_new_kept,
			List<TraceNode> corex_removing_DAT_IDT_old_kept, List<TraceNode> corex_removing_DAT_IDT_new_kept,
			HashMap<Integer, List<TraceNode>> oldDataBlockNodes, 
			HashMap<Integer, List<TraceNode>> newDataBlockNodes,HashMap<Integer, List<TraceNode>> oldCtlBlockNodes,
			HashMap<Integer, List<TraceNode>> newCtlBlockNodes, HashMap<Integer, List<TraceNode>> oldIdtBlockNodes,HashMap<Integer, List<TraceNode>> newIdtBlockNodes, 
			List<TraceNode> old_retained, List<TraceNode> new_retained,List<String> old_kept_sourceCodeLevel, List<String> new_kept_sourceCodeLevel, HashMap<TraceNode, List<Pair<TraceNode, String>>> new_corex_edges, HashMap<TraceNode, List<Pair<TraceNode, String>>> old_corex_edges) {
		
		/////////////////////////////////////////////////////////////
		Collections.sort(old_visited, new TraceNodeOrderComparator());
		Collections.sort(new_visited, new TraceNodeOrderComparator());                	
		/////////////////////extract blocks for old/////////////////////
		HashMap<Integer, List<TraceNode>> oldCtlBlockNodesTemp = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newCtlBlockNodesTemp = new HashMap<>();
		HashMap<TraceNode, Integer> oldBlocks = new HashMap<>();
		Integer BlockID = 0;
		boolean current_data_flag = false;
		boolean current_ctl_flag = false;
		boolean current_idt_flag = false;
		boolean firstTime = true;
		boolean isDataBlock = false;
		boolean isCTLBlock = false;
		boolean isIDTBlock = false;
		for(int i=old_visited.size()-1;i>=0; i--){
			TraceNode step = old_visited.get(i);	
//			System.out.println("step on old is: " + step);	
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
//			System.out.println("step type: " + changeType.getType());	
			//if ((changeType.getType()!=StepChangeType.DAT || i==old_visited.size()-1) && changeType.getType()!=StepChangeType.CTL) { //separate the blocks
//			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || (isATestStatement(tc, step) && isLastStatement(tc, step,old_visited))) { //it is retain		
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || old_retained.contains(step)) { //it is retain		
					
				isDataBlock = false;
				isCTLBlock = false;
				isIDTBlock = false;
				if (current_data_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
					//firstTime = false;
				}
				if (current_idt_flag) {//coming from an identical block
					//BlockID = BlockID + 1;
					current_idt_flag = false;
					//firstTime = false;
				}
				if (current_ctl_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isDataBlock = false;
				isCTLBlock = true;
				isIDTBlock = false;
				if (!current_ctl_flag) {//if we are not currently in ctl block
					BlockID = BlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
					current_idt_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.DAT){ 
				isDataBlock = true;
				isCTLBlock = false;		
				isIDTBlock = false;
				if (!current_data_flag) {//if we are not currently in data block
					BlockID = BlockID + 1;
					current_data_flag = true;
					current_ctl_flag = false;
					current_idt_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.IDT){ 
				isIDTBlock = true;
				isDataBlock = false;
				isCTLBlock = false;				
				if (!current_idt_flag) {//if we are not currently in idt block
					BlockID = BlockID + 1;
					current_idt_flag = true;
					current_data_flag = false;
					current_ctl_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
	//		if(firstTime) {
	//			firstTime = false;
	//			BlockID = BlockID + 1;
	//		}
			
	//		oldBlocks.put(step, BlockID);	
			
		}	
//		System.out.println("old blocks " + oldBlocks);	
		/////////////////////extract blocks for new/////////////////////
		HashMap<TraceNode, Integer> newBlocks = new HashMap<>();
		BlockID = 0;
		int CTLBlockID = 0;
		current_data_flag = false;
		current_ctl_flag = false;
		current_idt_flag = false;
		firstTime = true;
		isDataBlock = false;
		isCTLBlock = false;
		isIDTBlock = false;
		TraceNode previousData = null;
		TraceNode previousIDT = null;
		for(int i=new_visited.size()-1;i>=0; i--){
			TraceNode step = new_visited.get(i);
			//System.out.println("step on new is: " + step);	
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
			//if ((changeType.getType()!=StepChangeType.DAT || i==new_visited.size()-1) && changeType.getType()!=StepChangeType.CTL) { //separate the blocks
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || new_retained.contains(step)) { //separate the blocks				
				isDataBlock = false;
				isCTLBlock = false;
				isIDTBlock = false;
				if (current_data_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
					//firstTime = false;
				}
				if (current_ctl_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
					//firstTime = false;
				}
				if (current_idt_flag) {//coming from an identical block
					//BlockID = BlockID + 1;
					current_idt_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isDataBlock = false;
				isIDTBlock = false;
				isCTLBlock = true;
				if (!current_ctl_flag) {//coming from dat or other blocks
					CTLBlockID = CTLBlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
					current_idt_flag = false;
					//firstTime = false;
				}
				newBlocks.put(step, CTLBlockID);//will be updated later once we know the number of all data blocks
			}
			else if (changeType.getType()==StepChangeType.DAT){ 
				isDataBlock = true;
				isCTLBlock = false;	
				isIDTBlock = false;
				if (previousData!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousData, true, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();					
					if(oldBlocks.get(matchedStep)!=oldBlocks.get(previousMatchedStep)) {//separate if it is separated in old 									
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						current_idt_flag = false;
						//firstTime = false;
					}					
					else {			
						if (!current_data_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = true;
							current_ctl_flag = false;
							current_idt_flag = false;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_data_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						current_idt_flag = false;
						//firstTime = false;
					}
					
				}
				previousData = step;
				newBlocks.put(step, BlockID);	
			}
			else if (changeType.getType()==StepChangeType.IDT){ 
				isDataBlock = false;
				isCTLBlock = false;	
				isIDTBlock = true;
				if (previousIDT!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousIDT, true, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();
					if(oldBlocks.get(matchedStep)!=oldBlocks.get(previousMatchedStep)) {//separate if it is separated in old 									
						BlockID = BlockID + 1;
						current_data_flag = false;
						current_ctl_flag = false;
						current_idt_flag = true;
						//firstTime = false;
					}					
					else {			
						if (!current_idt_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = false;
							current_ctl_flag = false;
							current_idt_flag = true;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_idt_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = false;
						current_ctl_flag = false;
						current_idt_flag = true;
						//firstTime = false;
					}
					
				}
				previousIDT = step;
				newBlocks.put(step, BlockID);	
			}
	//		if (firstTime) {
	//			BlockID = BlockID + 1;
	//			firstTime = false;
	//		}
	//		newBlocks.put(step, BlockID);
		
			if (isDataBlock){
				if (newDataBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = newDataBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					newDataBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					newDataBlockNodes.put(BlockID, nodes);
				}
			}
			if (isCTLBlock){
				if (newCtlBlockNodesTemp.containsKey(CTLBlockID)){
					List<TraceNode> nodes = newCtlBlockNodesTemp.get(CTLBlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					newCtlBlockNodesTemp.put(CTLBlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					newCtlBlockNodesTemp.put(CTLBlockID, nodes);
				}
			}
			if (isIDTBlock){
				if (newIdtBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = newIdtBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					newIdtBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					newIdtBlockNodes.put(BlockID, nodes);
				}
			}
		}
//		System.out.println("new blocks " + newBlocks);
		/////////////////////extract blocks for old/////////////////////
		oldBlocks = new HashMap<>();
		BlockID = 0;
		CTLBlockID = 0;
		current_data_flag = false;
		current_ctl_flag = false;
		current_idt_flag = false;
		firstTime = true;
		isDataBlock = false;
		isCTLBlock = false;
		isIDTBlock = false;
		previousData = null;
		previousIDT = null;
		for(int i=old_visited.size()-1;i>=0; i--){
			TraceNode step = old_visited.get(i);
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || old_retained.contains(step)) { //separate the blocks
				isDataBlock = false;
				isCTLBlock = false;
				isIDTBlock = false;
				if (current_data_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
					//firstTime = false;
				}
				if (current_ctl_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
					//firstTime = false;
				}
				if (current_idt_flag) {//coming from an identical block
					//BlockID = BlockID + 1;
					current_idt_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isDataBlock = false;
				isCTLBlock = true;
				isIDTBlock = false;
				if (!current_ctl_flag) {//coming from dat or other blocks
					CTLBlockID = CTLBlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
					current_idt_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, CTLBlockID);//will be updated later
			}
			else if (changeType.getType()==StepChangeType.DAT){ 
				isDataBlock = true;
				isCTLBlock = false;	
				isIDTBlock = false;
				if (previousData!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousData, false, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();
					if(newBlocks.get(matchedStep)!=newBlocks.get(previousMatchedStep)) {//separate them 									
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						current_idt_flag = false;
						//firstTime = false;
					}					
					else {			
						if (!current_data_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = true;
							current_ctl_flag = false;
							current_idt_flag = false;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_data_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						current_idt_flag = false;
						//firstTime = false;
					}
				}
				previousData = step;
				oldBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.IDT){ 
				isDataBlock = false;
				isCTLBlock = false;	
				isIDTBlock = true;
				if (previousIDT!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousIDT, false, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();
					if(newBlocks.get(matchedStep)!=newBlocks.get(previousMatchedStep)) {//separate them 									
						BlockID = BlockID + 1;
						current_data_flag = false;
						current_ctl_flag = false;
						current_idt_flag = true;
						//firstTime = false;
					}					
					else {			
						if (!current_idt_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = false;
							current_ctl_flag = false;
							current_idt_flag = true;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_idt_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = false;
						current_ctl_flag = false;
						current_idt_flag = true;
						//firstTime = false;
					}
				}
				previousIDT = step;
				oldBlocks.put(step, BlockID);
			}
	//		if (firstTime) {
	//			BlockID = BlockID + 1;
	//			firstTime = false;
	//		}
	//		oldBlocks.put(step, BlockID);
			if (isDataBlock){
				if (oldDataBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = oldDataBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					oldDataBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					oldDataBlockNodes.put(BlockID, nodes);
				}
			}
			if (isCTLBlock){
				if (oldCtlBlockNodesTemp.containsKey(CTLBlockID)){
					List<TraceNode> nodes = oldCtlBlockNodesTemp.get(CTLBlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					oldCtlBlockNodesTemp.put(CTLBlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					oldCtlBlockNodesTemp.put(CTLBlockID, nodes);
				}
			}
			if (isIDTBlock){
				if (oldIdtBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = oldIdtBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					oldIdtBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					oldIdtBlockNodes.put(BlockID, nodes);
				}
			}
		}
		///////////////////////////////////////////////////////////////////////////////////////////////////
		//update the control blocksID: 
		CTLBlockID = BlockID + 1;
		for(Integer ctlblockID:oldCtlBlockNodesTemp.keySet()) {
			oldCtlBlockNodes.put(CTLBlockID,oldCtlBlockNodesTemp.get(ctlblockID));
			for(TraceNode node:oldCtlBlockNodesTemp.get(ctlblockID))
				oldBlocks.put(node, CTLBlockID);
			CTLBlockID += 1;
		}
		for(Integer ctlblockID:newCtlBlockNodesTemp.keySet()) {
			newCtlBlockNodes.put(CTLBlockID,newCtlBlockNodesTemp.get(ctlblockID));	
			for(TraceNode node:newCtlBlockNodesTemp.get(ctlblockID))
				newBlocks.put(node, CTLBlockID);
			CTLBlockID += 1;
		}
//		System.out.println("#################after paralizing#################"); 
//		System.out.println("The # of data block in old " + oldDataBlockNodes);
//		System.out.println("The # of data block in new " + newDataBlockNodes);
//		System.out.println("The # of ctl block in old " + oldCtlBlockNodes);
//		System.out.println("The # of ctl block in new " + newCtlBlockNodes);
//		System.out.println("The # of idt block in old " + oldIdtBlockNodes);
//		System.out.println("The # of idt block in new " + newIdtBlockNodes);
//		////////////////////////////////////////////////////////////////////////////////////////////////////////
//		////////////////////////////////////////////////////////////////////////////////////////////////////////
//		////////////////////////////////////////////////////////////////////////////////////////////////////////	
//		////////////////////////////////////////////////////////////////////////////////////////////////////////
//		/////////////////////abstraction////////////////////////////////////////////////////////////////
			//should also the corresponding kept node from the other trace be add?
		
			Collections.sort(old_visited, new TraceNodeOrderComparator());
			Collections.sort(new_visited, new TraceNodeOrderComparator());
			
			List<TraceNode> new_dat_kept = new ArrayList<>();
			List<TraceNode> old_dat_kept = new ArrayList<>();
			
			inpress_keep_IDT_old_kept.add(old_visited.get(old_visited.size()-1));
			inpress_keep_IDT_new_kept.add(new_visited.get(new_visited.size()-1));
											
			HashMap<TraceNode, List<Pair<Integer,String>>> old_data_node_function = new HashMap<>();
			HashMap<TraceNode, List<Pair<Integer,String>>> new_data_node_function = new HashMap<>();
			HashMap<TraceNode, List<Pair<Integer,String>>> old_ctl_node_function = new HashMap<>();
			HashMap<TraceNode, List<Pair<Integer,String>>> new_ctl_node_function = new HashMap<>();
//			HashMap<TraceNode, Integer> old_idt_node_function = new HashMap<>();
//			HashMap<TraceNode, Integer> new_idt_node_function = new HashMap<>();
			Integer index = 0;
			
////////////////////////////////////First Define what to keep (like inpress but just keep the identical too)////////////////////////////////////////////////
			for(int i=old_visited.size()-1;i>=0; i--){
				TraceNode step = old_visited.get(i);
//				System.out.println("this is step on old: " + step);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);				
									
				/////////keep the dependencies in different block

				List<Pair<TraceNode, String>> data_deps = old_data_map.get(step);	
//				System.out.println("data deps: " + data_deps);
				if(data_deps!=null) 
					for(Pair<TraceNode, String> pair:data_deps) 
						if(old_visited.contains(pair.first()))
							if(oldBlocks.get(pair.first())!=oldBlocks.get(step))								
								if(!inpress_keep_IDT_old_kept.contains(pair.first())) {										
									inpress_keep_IDT_old_kept.add(pair.first());
								}
				
				List<TraceNode> ctl_deps = old_ctl_map.get(step);
//				System.out.println("control deps: " + ctl_deps);
				if(changeType.getType()==StepChangeType.CTL)//if the node is control diff we also want to keep the if statement 
					if(ctl_deps!=null) 
						for(TraceNode node:ctl_deps) {
							StepChangeType changeTypes = typeChecker.getTypeForPrinting(node, false, pairList, matcher);				
							if(changeTypes.getType()==StepChangeType.DAT || changeTypes.getType()==StepChangeType.SRCDAT){//keep the control condition causing the control block
//								System.out.println("control dep which is DAT");
								if(old_visited.contains(node))
									if(!inpress_keep_IDT_old_kept.contains(node)) {
										inpress_keep_IDT_old_kept.add(node);	
									}	
							}
						}				
			}
			
			for(int i=new_visited.size()-1;i>=0; i--){
				TraceNode step = new_visited.get(i);
//				System.out.println("this is step on new: " + step);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);				
				
				/////////keep the dependencies

				List<Pair<TraceNode, String>> data_deps = new_data_map.get(step);	
//				System.out.println("data deps: " + data_deps);
				if(data_deps!=null) 
					for(Pair<TraceNode, String> pair:data_deps) 
						if(new_visited.contains(pair.first()))
							if(newBlocks.get(pair.first())!=newBlocks.get(step)) {
								if(!inpress_keep_IDT_new_kept.contains(pair.first())) {										
									inpress_keep_IDT_new_kept.add(pair.first());
								}
							}
				
				List<TraceNode> ctl_deps = new_ctl_map.get(step);
//				System.out.println("control deps: " + ctl_deps);
				if(changeType.getType()==StepChangeType.CTL)//if the node is control diff we also want to keep the if statement 
					if(ctl_deps!=null) 
						for(TraceNode node:ctl_deps) {
							StepChangeType changeTypes = typeChecker.getTypeForPrinting(node, true, pairList, matcher);	
							if(changeTypes.getType()==StepChangeType.DAT || changeTypes.getType()==StepChangeType.SRCDAT)//keep the control condition causing the control block
								if(new_visited.contains(node))
									if(!inpress_keep_IDT_new_kept.contains(node)) {
										inpress_keep_IDT_new_kept.add(node);	
									}							
						}				
			}
			
//			System.out.println("#################after paralizing#################"); 
//			System.out.println("The initial nodes in old " + inpress_keep_IDT_old_kept);
//			System.out.println("The initial nodes in new " + inpress_keep_IDT_new_kept);
			Collections.sort(inpress_keep_IDT_old_kept, new TraceNodeOrderComparator());
			Collections.sort(inpress_keep_IDT_new_kept, new TraceNodeOrderComparator());
			
/////////////////////////////////////Now 1) remove those matched and identical that have the same dep in both old and new and also are not reaching definition. ///////////////////////////////////////////////
			System.out.println("steps size in old " + inpress_keep_IDT_old_kept.size());
			for(int i=inpress_keep_IDT_old_kept.size()-1;i>=0; i--){
				TraceNode step = inpress_keep_IDT_old_kept.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
//				System.out.println("step in old " + step);
				if(changeType.getType()==StepChangeType.SRCCTL || changeType.getType()==StepChangeType.SRCDAT || old_retained.contains(step)) {//retain statement
					if(changeType.getType()==StepChangeType.SRCCTL) {
//						for (VarValue var: step.getReadVariables()) {
//							List<Pair<Integer, String>> vars = old_ctl_node_function.get(step);
//							if (vars==null)
//								vars = new ArrayList<>();
//							Pair<Integer, String> pair = new Pair(index,var.getVarName());
//							vars.add(pair);
//							old_ctl_node_function.put(step, vars);
//							index = index + 1;
//						}
					}
					else if(changeType.getType()==StepChangeType.SRCDAT || old_retained.contains(step)) {	
						TraceNode matchedStep = changeType.getMatchingStep();
//						for (VarValue var: step.getReadVariables()) {
//							List<Pair<Integer, String>> vars = old_data_node_function.get(step);
//							if (vars==null)
//								vars = new ArrayList<>();
//							Pair<Integer, String> pair = new Pair(index,var.getVarName());
//							vars.add(pair);
//							old_data_node_function.put(step, vars);
//							new_data_node_function.put(matchedStep, vars);
//							index = index + 1;
//						}																
						if(matchedStep!=null) {
							if(!inpress_keep_IDT_new_kept.contains(matchedStep))
								new_dat_kept.add(matchedStep);
							if(!new_retained.contains(matchedStep))
								new_retained.add(matchedStep);
							if(!new_kept.contains(matchedStep))
								new_kept.add(matchedStep);	
						}
					}
					if(!old_retained.contains(step))//TODO:check and get it back
						old_retained.add(step);
					if(!old_kept.contains(step)) {
						old_kept.add(step);	
//						if (!old_kept_sourceCodeLevel.contains(getSourceCode(step,false,matcher)))
//							old_kept_sourceCodeLevel.add(getSourceCode(step,false,matcher));					
					}
				}
				
				else if (changeType.getType()==StepChangeType.CTL && !old_retained.contains(step)) {
//					for (VarValue var: step.getReadVariables()) {
//						List<Pair<Integer, String>> vars = old_ctl_node_function.get(step);
//						if (vars==null)
//							vars = new ArrayList<>();
//						Pair<Integer, String> pair = new Pair(index,var.getVarName());
//						vars.add(pair);
//						old_ctl_node_function.put(step, vars);
//						index = index + 1;
//					}
					if(!old_kept.contains(step)) {
						old_kept.add(step);	
//						if (!old_kept_sourceCodeLevel.contains(getSourceCode(step,false,matcher)))
//							old_kept_sourceCodeLevel.add(getSourceCode(step,false,matcher));					
					}
				}
				
				else if ((changeType.getType()==StepChangeType.DAT && !old_retained.contains(step))||(changeType.getType()==StepChangeType.IDT && !old_retained.contains(step))) {									
					TraceNode matchedStep = changeType.getMatchingStep();	
					if(!inpress_keep_IDT_new_kept.contains(matchedStep)) { //only in one trace/slice => keep
						if(!old_kept.contains(step)) {
							old_kept.add(step);	
//							if (!old_kept_sourceCodeLevel.contains(getSourceCode(step,false,matcher)))
//								old_kept_sourceCodeLevel.add(getSourceCode(step,false,matcher));
//							for (VarValue var: step.getReadVariables()) {
//								List<Pair<Integer, String>> vars = old_data_node_function.get(step);
//								if (vars==null)
//									vars = new ArrayList<>();
//								Pair<Integer, String> pair = new Pair(index,var.getVarName());
//								vars.add(pair);
//								old_data_node_function.put(step, vars);
//								new_data_node_function.put(matchedStep, vars);
//								index = index + 1;
//							}
							if(matchedStep!=null) {
								if(!inpress_keep_IDT_new_kept.contains(matchedStep))
									new_dat_kept.add(matchedStep);
								if(!new_kept.contains(matchedStep)) {//add the symmetric data and identical to other trace
									new_kept.add(matchedStep);
//							        if (!new_kept_sourceCodeLevel.contains(getSourceCode(matchedStep,true,matcher)))
//										new_kept_sourceCodeLevel.add(getSourceCode(matchedStep,true,matcher));									
								}	
							}
						}
					}
//					else {//if the other trace contains but for different reason: from different dependency
////						System.out.println("step is " + step);
//						boolean found = false;
//						for(TraceNode dominatee:step.getDataDominatee().keySet()) {
//							StepChangeType t = typeChecker.getTypeForPrinting(dominatee, false, pairList, matcher);
//							TraceNode matchedDominatee = t.getMatchingStep();	
//							if(matchedStep.getDataDominatee().keySet().contains(matchedDominatee)) {
////								System.out.println("it is found in the other trace");
//								found = true;
//							}
//						}
//						if(!found) {
//							if(!old_kept.contains(step)) {
//								old_kept.add(step);	
//								if (!old_kept_sourceCodeLevel.contains(getSourceCode(step,false,matcher)))
//									old_kept_sourceCodeLevel.add(getSourceCode(step,false,matcher));	
//								for (VarValue var: step.getReadVariables()) {
//									List<Pair<Integer, String>> vars = old_data_node_function.get(step);
//									if (vars==null)
//										vars = new ArrayList<>();
//									Pair<Integer, String> pair = new Pair(index,var.getVarName());
//									vars.add(pair);
//									old_data_node_function.put(step, vars);
//									new_data_node_function.put(matchedStep, vars);
//									index = index + 1;
//								}
////								old_data_node_function.put(step, index);	
////								new_data_node_function.put(matchedStep, index);
////								index = index + 1;	
//								if(matchedStep!=null) {
//									if(!inpress_keep_IDT_new_kept.contains(matchedStep))
//										new_dat_kept.add(matchedStep);
//									if(!new_kept.contains(matchedStep)) {//add the symmetric data and identical to other trace
//										new_kept.add(matchedStep);
//								        if (!new_kept_sourceCodeLevel.contains(getSourceCode(matchedStep,true,matcher)))
//											new_kept_sourceCodeLevel.add(getSourceCode(matchedStep,true,matcher));									
//									}
//								}
//							}
//						}
//					}
					if(step.getReadVariables().size()==0) {//it is reaching definition =>keep
						if(!old_kept.contains(step)) {
							old_kept.add(step);	
//							if (!old_kept_sourceCodeLevel.contains(getSourceCode(step,false,matcher)))
//								old_kept_sourceCodeLevel.add(getSourceCode(step,false,matcher));
//							for (VarValue var: step.getReadVariables()) {
//								List<Pair<Integer, String>> vars = old_data_node_function.get(step);
//								if (vars==null)
//									vars = new ArrayList<>();
//								Pair<Integer, String> pair = new Pair(index,var.getVarName());
//								vars.add(pair);
//								old_data_node_function.put(step, vars);
//								new_data_node_function.put(matchedStep, vars);
//								index = index + 1;
//							}	
							if(matchedStep!=null) {
								if(!new_kept.contains(matchedStep)) {//add the symmetric data and identical to other trace
									new_kept.add(matchedStep);
//							        if (!new_kept_sourceCodeLevel.contains(getSourceCode(matchedStep,true,matcher)))
//										new_kept_sourceCodeLevel.add(getSourceCode(matchedStep,true,matcher));									
								}	
								if(!inpress_keep_IDT_new_kept.contains(matchedStep))
									new_dat_kept.add(matchedStep);
							}
						}
					}
					if(step.isBranch()||step.isLoopCondition() || step.isConditional()) {// it is the control condition that makes control block => keep
						if(!old_kept.contains(step)) {
							old_kept.add(step);	
//							if (!old_kept_sourceCodeLevel.contains(getSourceCode(step,false,matcher)))
//								old_kept_sourceCodeLevel.add(getSourceCode(step,false,matcher));
//							for (VarValue var: step.getReadVariables()) {
//								List<Pair<Integer, String>> vars = old_data_node_function.get(step);
//								if (vars==null)
//									vars = new ArrayList<>();
//								Pair<Integer, String> pair = new Pair(index,var.getVarName());
//								vars.add(pair);
//								old_data_node_function.put(step, vars);
//								new_data_node_function.put(matchedStep, vars);
//								index = index + 1;
//							}

							if(matchedStep!=null) {
								if(!new_kept.contains(matchedStep)) {//add the symmetric data and identical to other trace
									new_kept.add(matchedStep);
//							        if (!new_kept_sourceCodeLevel.contains(getSourceCode(matchedStep,true,matcher)))
//										new_kept_sourceCodeLevel.add(getSourceCode(matchedStep,true,matcher));									
								}
								if(!inpress_keep_IDT_new_kept.contains(matchedStep))
									new_dat_kept.add(matchedStep);
							}
						}
					}
					
				}
				
			}
			System.out.println("steps size in new " + inpress_keep_IDT_new_kept.size());
			for(int i=inpress_keep_IDT_new_kept.size()-1;i>=0; i--){
				TraceNode step = inpress_keep_IDT_new_kept.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
//				System.out.println("step in new " + step);
				if(changeType.getType()==StepChangeType.SRCCTL || changeType.getType()==StepChangeType.SRCDAT || new_retained.contains(step)) {//retain statement
					if(changeType.getType()==StepChangeType.SRCCTL) {
//						for (VarValue var: step.getReadVariables()) {
//							List<Pair<Integer, String>> vars = new_ctl_node_function.get(step);
//							if (vars==null)
//								vars = new ArrayList<>();
//							Pair<Integer, String> pair = new Pair(index,var.getVarName());
//							vars.add(pair);
//							new_ctl_node_function.put(step, vars);
//							index = index + 1;
//						}						
					}
					else if(changeType.getType()==StepChangeType.SRCDAT || new_retained.contains(step)) {
						TraceNode matchedStep = changeType.getMatchingStep();	
//						if (!new_data_node_function.containsKey(step)) {
//							for (VarValue var: step.getReadVariables()) {
//								List<Pair<Integer, String>> vars = new_data_node_function.get(step);
//								if (vars==null)
//									vars = new ArrayList<>();
//								Pair<Integer, String> pair = new Pair(index,var.getVarName());
//								vars.add(pair);
//								new_data_node_function.put(step, vars);
//								old_data_node_function.put(matchedStep, vars);
//								index = index + 1;
//							}
//						}
						if(matchedStep!=null) {
							if(!inpress_keep_IDT_old_kept.contains(matchedStep))
								old_dat_kept.add(matchedStep);
							if(!old_retained.contains(matchedStep))
								old_retained.add(matchedStep);
							if(!old_kept.contains(matchedStep))
								old_kept.add(matchedStep);
						}
					}
					
					if(!new_retained.contains(step))//TODO: check get it back
						new_retained.add(step);
					if(!new_kept.contains(step)) {
						new_kept.add(step);	
//						if (!new_kept_sourceCodeLevel.contains(getSourceCode(step,true,matcher)))
//							new_kept_sourceCodeLevel.add(getSourceCode(step,true,matcher));					
					}
				}
				
				else if (changeType.getType()==StepChangeType.CTL && !new_retained.contains(step)) {
//					for (VarValue var: step.getReadVariables()) {
//						List<Pair<Integer, String>> vars = new_ctl_node_function.get(step);
//						if (vars==null)
//							vars = new ArrayList<>();
//						Pair<Integer, String> pair = new Pair(index,var.getVarName());
//						vars.add(pair);
//						new_ctl_node_function.put(step, vars);
//						index = index + 1;
//					}
					if(!new_kept.contains(step)) {
						new_kept.add(step);	
//						if (!new_kept_sourceCodeLevel.contains(getSourceCode(step,true,matcher)))
//							new_kept_sourceCodeLevel.add(getSourceCode(step,true,matcher));					
					}
				}
				
				else if ((changeType.getType()==StepChangeType.DAT && !new_retained.contains(step))||(changeType.getType()==StepChangeType.IDT && !new_retained.contains(step))) {
					TraceNode matchedStep = changeType.getMatchingStep();	
					if(!inpress_keep_IDT_old_kept.contains(matchedStep)) { //only in one trace/slice => keep
						if(!new_kept.contains(step)) {
							new_kept.add(step);	
//							if (!new_kept_sourceCodeLevel.contains(getSourceCode(step,true,matcher)))
//								new_kept_sourceCodeLevel.add(getSourceCode(step,true,matcher));	
//							if (!new_data_node_function.containsKey(step)) {
//								for (VarValue var: step.getReadVariables()) {
//									List<Pair<Integer, String>> vars = new_data_node_function.get(step);
//									if (vars==null)
//										vars = new ArrayList<>();
//									Pair<Integer, String> pair = new Pair(index,var.getVarName());
//									vars.add(pair);
//									new_data_node_function.put(step, vars);
//									old_data_node_function.put(matchedStep, vars);
//									index = index + 1;
//								}									
//							}
							if(matchedStep!=null) {
								if(!inpress_keep_IDT_old_kept.contains(matchedStep))
									old_dat_kept.add(matchedStep);
								if(!old_kept.contains(matchedStep)) {//add the symmetric data and identical to other trace
									old_kept.add(matchedStep);
//							        if (!old_kept_sourceCodeLevel.contains(getSourceCode(matchedStep,false,matcher)))
//										old_kept_sourceCodeLevel.add(getSourceCode(matchedStep,false,matcher));									
								}		
							}
						}
					}
//					else {//if the other trace contains but for different reason: from different dependency
////						System.out.println("step is " + step);
//						boolean found = false;
//						for(TraceNode dominatee:step.getDataDominatee().keySet()) {
//							StepChangeType t = typeChecker.getTypeForPrinting(dominatee, true, pairList, matcher);
//							TraceNode matchedDominatee = t.getMatchingStep();	
//							if(matchedStep.getDataDominatee().keySet().contains(matchedDominatee))
//								found = true;
//						}
//						if(!found) {
//							if(!new_kept.contains(step)) {
//								new_kept.add(step);	
//								if (!new_kept_sourceCodeLevel.contains(getSourceCode(step,true,matcher)))
//									new_kept_sourceCodeLevel.add(getSourceCode(step,true,matcher));	
//								if (!new_data_node_function.containsKey(step)) {
//									for (VarValue var: step.getReadVariables()) {
//										List<Pair<Integer, String>> vars = new_data_node_function.get(step);
//										if (vars==null)
//											vars = new ArrayList<>();
//										Pair<Integer, String> pair = new Pair(index,var.getVarName());
//										vars.add(pair);
//										new_data_node_function.put(step, vars);
//										old_data_node_function.put(matchedStep, vars);
//										index = index + 1;
//									}
////									new_data_node_function.put(step, index);	
////									old_data_node_function.put(matchedStep, index);
////									index = index + 1;	
//								}
//								if(matchedStep!=null) {
//									if(!inpress_keep_IDT_old_kept.contains(matchedStep))
//										old_dat_kept.add(matchedStep);
//									if(!old_kept.contains(matchedStep)) {//add the symmetric data and identical to other trace
//										old_kept.add(matchedStep);
//								        if (!old_kept_sourceCodeLevel.contains(getSourceCode(matchedStep,false,matcher)))
//											old_kept_sourceCodeLevel.add(getSourceCode(matchedStep,false,matcher));									
//									}
//								}
//							}
//						}
//					}
					if(step.getReadVariables().size()==0) {//it is reaching definition =>keep
						if(!new_kept.contains(step)) {
							new_kept.add(step);	
//							if (!new_kept_sourceCodeLevel.contains(getSourceCode(step,true,matcher)))
//								new_kept_sourceCodeLevel.add(getSourceCode(step,true,matcher));	
//							if (!new_data_node_function.containsKey(step)) {
//								for (VarValue var: step.getReadVariables()) {
//									List<Pair<Integer, String>> vars = new_data_node_function.get(step);
//									if (vars==null)
//										vars = new ArrayList<>();
//									Pair<Integer, String> pair = new Pair(index,var.getVarName());
//									vars.add(pair);
//									new_data_node_function.put(step, vars);
//									old_data_node_function.put(matchedStep, vars);
//									index = index + 1;
//								}	
//							}
							if(matchedStep!=null) {
								if(!inpress_keep_IDT_old_kept.contains(matchedStep))
									old_dat_kept.add(matchedStep);
								if(!old_kept.contains(matchedStep)) {//add the symmetric data and identical to other trace
									old_kept.add(matchedStep);
//							        if (!old_kept_sourceCodeLevel.contains(getSourceCode(matchedStep,false,matcher)))
//										old_kept_sourceCodeLevel.add(getSourceCode(matchedStep,false,matcher));	
								}
							}
						}
					}
					if(step.isBranch()||step.isLoopCondition() || step.isConditional()) {// it is the control condition that makes control block => keep
						if(!new_kept.contains(step)) {
							new_kept.add(step);	
//							if (!new_kept_sourceCodeLevel.contains(getSourceCode(step,true,matcher)))
//								new_kept_sourceCodeLevel.add(getSourceCode(step,true,matcher));		
//							if (!new_data_node_function.containsKey(step)) {
//								for (VarValue var: step.getReadVariables()) {
//									List<Pair<Integer, String>> vars = new_data_node_function.get(step);
//									if (vars==null)
//										vars = new ArrayList<>();
//									Pair<Integer, String> pair = new Pair(index,var.getVarName());
//									vars.add(pair);
//									new_data_node_function.put(step, vars);
//									old_data_node_function.put(matchedStep, vars);
//									index = index + 1;
//								}
//							}
							if(matchedStep!=null) {
								if(!inpress_keep_IDT_old_kept.contains(matchedStep))
									old_dat_kept.add(matchedStep);
								if(!old_kept.contains(matchedStep)) {//add the symmetric data and identical to other trace
									old_kept.add(matchedStep);
//							        if (!old_kept_sourceCodeLevel.contains(getSourceCode(matchedStep,false,matcher)))
//										old_kept_sourceCodeLevel.add(getSourceCode(matchedStep,false,matcher));									
								}
							}
						}
					}
					
				}
				
			}
			
//			System.out.println("#################after paralizing#################"); 

	        for (int i=0; i<old_kept.size(); i++) {
	        	if(old_kept.get(i)==null)
	        		old_kept.remove(old_kept.get(i));
	        	else {
	        		corex_removing_DAT_IDT_old_kept.add(old_kept.get(i));
	        	}
	        }
	        for (int i=0; i<new_kept.size(); i++) {
	        	if(new_kept.get(i)==null)
	        		new_kept.remove(new_kept.get(i));
	        	else {	        
	        	corex_removing_DAT_IDT_new_kept.add(new_kept.get(i));
	        	}
	        }
	        
	        inpress_keep_IDT_old_kept.addAll(old_dat_kept);//adding the symmetric ones to the initial list to compare to original inpress
	        inpress_keep_IDT_new_kept.addAll(new_dat_kept);//adding the symmetric ones to the initial list to compare to original inpress
	        
			System.out.println("The initial nodes in old after removing unnecessary matched and identical " + old_kept);
			System.out.println("The initial nodes in new after removing unnecessary matched and identical  " + new_kept);
		
			Collections.sort(old_kept, new TraceNodeOrderComparator());
			Collections.sort(new_kept, new TraceNodeOrderComparator());
			
/////////////////////////////////////Now 2) add the context of variables we decided to keep  ///////////////////////////////////////////////
			for(int i=old_kept.size()-1;i>=0; i--){
				TraceNode step = old_kept.get(i);
				old_corex_edges.put(step,null);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
				getContext(step,old_kept,old_corex_edges,old_data_map,old_ctl_map,old_data_node_function,old_ctl_node_function,changeType);					
			}
			for(int i=new_kept.size()-1;i>=0; i--){
				TraceNode step = new_kept.get(i);
				new_corex_edges.put(step,null);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
				getContext(step,new_kept,new_corex_edges,new_data_map,new_ctl_map,new_data_node_function,new_ctl_node_function,changeType);					
			}
			System.out.println("Final nodes in old " + old_kept);
			System.out.println("Final nodes in new " + new_kept);
/////////////////////////////////////Now 3)add edges  ///////////////////////////////////////////////
			boolean save_result = false;
			if(save_result) {
				HashMap<String, List<String>> old_functionsVars = new HashMap<>();//keep the mapping between the _Func(vars) and list of vars
				HashMap<String, List<String>> new_functionsVars = new HashMap<>();
				HashMap<String, String> old_functionsDef = new HashMap<>();//keep the mapping between the Var = _Func(vars) and Var
				HashMap<String, String> new_functionsDef = new HashMap<>();
				for(int i=old_kept.size()-1;i>=0; i--){
					TraceNode step = old_kept.get(i);
					old_corex_edges.put(step,null);
					StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
	//				System.out.println("Step on old is: " + step + "the type is" + changeType.getType());
					if(changeType.getType()==StepChangeType.DAT||changeType.getType()==StepChangeType.IDT || changeType.getType()==StepChangeType.SRCDAT) {
						if(!old_data_node_function.containsKey(step)) {
							TraceNode matchedStep = changeType.getMatchingStep();	
							for (VarValue var: step.getReadVariables()) {
								List<Pair<Integer, String>> vars = old_data_node_function.get(step);
								if (vars==null)
									vars = new ArrayList<>();
								Pair<Integer, String> pair = new Pair(index,var.getVarName());
								vars.add(pair);
								old_data_node_function.put(step, vars);
								new_data_node_function.put(matchedStep, vars);
								index = index + 1;
							}
	//						old_data_node_function.put(step, index);	
	//						new_data_node_function.put(matchedStep, index);
	//						index = index + 1;									
						}
					}
					else if (changeType.getType()==StepChangeType.CTL || changeType.getType()==StepChangeType.SRCCTL){
						if(!old_ctl_node_function.containsKey(step)) {
							for (VarValue var: step.getReadVariables()) {
								List<Pair<Integer, String>> vars = old_ctl_node_function.get(step);
								if (vars==null)
									vars = new ArrayList<>();
								Pair<Integer, String> pair = new Pair(index,var.getVarName());
								vars.add(pair);
								old_ctl_node_function.put(step, vars);
								index = index + 1;
							}
	//						old_ctl_node_function.put(step, index);	
	//						index = index + 1;			
						}
					}			
					getEdges(step,old_kept,old_corex_edges,old_data_map,old_ctl_map,old_data_node_function,old_ctl_node_function,changeType,old_functionsVars,old_functionsDef);					
				}
				for(int i=new_kept.size()-1;i>=0; i--){
					TraceNode step = new_kept.get(i);
					new_corex_edges.put(step,null);
					StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
	//				System.out.println("Step on new is: " + step + "the type is" + changeType.getType());
					if(changeType.getType()==StepChangeType.DAT||changeType.getType()==StepChangeType.IDT || changeType.getType()==StepChangeType.SRCDAT) {
						if(!new_data_node_function.containsKey(step)) {
							TraceNode matchedStep = changeType.getMatchingStep();	
							for (VarValue var: step.getReadVariables()) {
								List<Pair<Integer, String>> vars = new_data_node_function.get(step);
								if (vars==null)
									vars = new ArrayList<>();
								Pair<Integer, String> pair = new Pair(index,var.getVarName());
								vars.add(pair);
								new_data_node_function.put(step, vars);
								old_data_node_function.put(matchedStep, vars);
								index = index + 1;
							}
	//						new_data_node_function.put(step, index);	
	//						old_data_node_function.put(matchedStep, index);
	//						index = index + 1;									
						}
					}
					else if (changeType.getType()==StepChangeType.CTL || changeType.getType()==StepChangeType.SRCCTL){
						if(!new_ctl_node_function.containsKey(step)) {
							for (VarValue var: step.getReadVariables()) {
								List<Pair<Integer, String>> vars = new_ctl_node_function.get(step);
								if (vars==null)
									vars = new ArrayList<>();
								Pair<Integer, String> pair = new Pair(index,var.getVarName());
								vars.add(pair);
								new_ctl_node_function.put(step, vars);
								index = index + 1;
							}
	//						new_ctl_node_function.put(step, index);	
	//						index = index + 1;			
						}
					}
					getEdges(step,new_kept,new_corex_edges,new_data_map,new_ctl_map,new_data_node_function,new_ctl_node_function,changeType,new_functionsVars,new_functionsDef);					
				}
	
				System.out.println("Final edges in old are " + old_corex_edges);
				System.out.println("Final edges in new are  " + new_corex_edges);
	////////////////////////saving/////////////////////
				Collections.sort(old_kept, new TraceNodeOrderComparator());
				Collections.sort(new_kept, new TraceNodeOrderComparator());
						
				try {
				PrintWriter fileWriter = new PrintWriter(proPath + "/results/old/CoReX.txt", "UTF-8");
				PrintWriter writer = new PrintWriter(proPath+"/results/Explainations.gv", "UTF-8");
				writer.println("digraph dualGraph {");
				writer.println("rankdir = BT;");
				writer.println("splines=ortho;");
				writer.println("subgraph cluster0 {");
				writer.println("color=black;");
				writer.println("label = \"old slice\";");
				for(int i=0;i<=old_kept.size()-1;i++){
					TraceNode step = old_kept.get(i);
					boolean NotAssignemnt = false;
	//				System.out.println("step is " + step + "written is " + step.getWrittenVariables());
					if (step.getWrittenVariables().size()!=0) {
						if(!Pattern.compile(step.getWrittenVariables().get(0).getVarName()+ ".*=").matcher(getSourceCode(step, false, matcher)).find()) {
	//						System.out.println("is not an assignement");
							NotAssignemnt= true;
						}
					}
					if(NotAssignemnt)
						fileWriter.println(getSourceCode(step, false, matcher) + " " + step.getWrittenVariables().toString());
					else
						fileWriter.println(getSourceCode(step, false, matcher));
					String fixNode = step.toString();
					String Type = "";
					StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);		
					if(changeType.getType()==StepChangeType.DAT && !isLastStatement(tc, step,old_visited)) {					
						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";																			
					}	
					else if (changeType.getType()==StepChangeType.IDT) {					
						Type= "color=green fillcolor=green shape=box style=filled fontsize=10";																			
					}					
					else if (changeType.getType()==StepChangeType.CTL && !isLastStatement(tc, step,old_visited)) {					
						Type= "color=blue fillcolor=lightskyblue1 shape=box style=filled fontsize=10";																																						
					}
					else {//retained set 				
						if (changeType.getType()==StepChangeType.SRCDAT || isLastStatement(tc, step,old_visited)) 
							Type = "color=red fillcolor=white shape=box style=filled fontsize=10";					 									
						else 
							Type = "color=red fillcolor=white shape=box style=filled fontsize=10";									
					}	
					if(NotAssignemnt)
						writer.println("\"OldNode: "+fixNode +"\""+ "["+Type+ " label=\""+getSourceCode(step, false, matcher)+ " " +step.getWrittenVariables().toString()+"\"];");	
					else
						writer.println("\"OldNode: "+fixNode +"\""+ "["+Type+ " label=\""+getSourceCode(step, false, matcher)+"\"];");	
				}
				writer.println("}");	
				fileWriter.close();
				/////////////////////////////////////////////////////////////
				////////////////////////add nodes of new/////////////////////
				fileWriter = new PrintWriter(proPath + "/results/new/CoReX.txt", "UTF-8");		
				writer.println("subgraph cluster1 {");
				writer.println("color=black;");
				writer.println("label = \"new slice\";");
				for(int i=0;i<=new_kept.size()-1;i++){
					TraceNode step = new_kept.get(i);
					boolean NotAssignemnt = false;
	//				System.out.println("step is " + step + "written is " + step.getWrittenVariables());
					if (step.getWrittenVariables().size()!=0) {
						if(!Pattern.compile(step.getWrittenVariables().get(0).getVarName()+ ".*=").matcher(getSourceCode(step, true, matcher)).find()) {
	//						System.out.println("is not an assignement");
							NotAssignemnt= true;
						}
					}
					if(NotAssignemnt)
						fileWriter.println(getSourceCode(step, true, matcher) + " " + step.getWrittenVariables().toString());
					else
						fileWriter.println(getSourceCode(step, true, matcher));
					String fixNode = step.toString();
					String Type = "";
					StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);		
					if(changeType.getType()==StepChangeType.DAT && !isLastStatement(tc, step,new_visited)) {					
						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";																			
					}	
					else if (changeType.getType()==StepChangeType.IDT) {					
						Type= "color=green fillcolor=green shape=box style=filled fontsize=10";																			
					}	
					else if (changeType.getType()==StepChangeType.CTL && !isLastStatement(tc, step,new_visited)) {					
						Type= "color=blue fillcolor=lightskyblue1 shape=box style=filled fontsize=10";																																						
					}
					else {//retained set 				
						if (changeType.getType()==StepChangeType.SRCDAT || isLastStatement(tc, step,new_visited)) 
							Type = "color=red fillcolor=white shape=box style=filled fontsize=10";					 									
						else 
							Type = "color=red fillcolor=white shape=box style=filled fontsize=10";									
					}	
					if(NotAssignemnt)
						writer.println("\"NewNode: "+fixNode +"\""+ "["+Type+ " label=\""+getSourceCode(step, true, matcher)+ " " +step.getWrittenVariables().toString()+"\"];");	
					else
						writer.println("\"NewNode: "+fixNode +"\""+ "["+Type+ " label=\""+getSourceCode(step, true, matcher)+"\"];");	
				}
				writer.println("}");	
				fileWriter.close();
				//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				//////////////////////////////add control flow edges////////////////////////////////////////////////////////////////////////////////////////////				
				for(int i=0;i<old_kept.size(); i++) {
					if(i!=old_kept.size()-1) {
						String step = old_kept.get(i).toString();
						String BeforeStep = old_kept.get(i+1).toString();
						writer.println("\"OldNode: "+BeforeStep +"\" " + "->" + "\"OldNode: "+step +"\" [style=invis];");
					}
				} 
				for(int i=0;i<new_kept.size(); i++) {
					if(i!=new_kept.size()-1) {
						String step = new_kept.get(i).toString();
						String BeforeStep = new_kept.get(i+1).toString();
						writer.println("\"NewNode: "+BeforeStep +"\" " + "->" + "\"NewNode: "+step +"\" [style=invis] ;");
					} 
				}
				//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				/////////////////////////add alignment edges between two traces//////////////////////////////////////////////////////////////////////////////
	//			for(int i=0;i<old_kept.size(); i++) {
	//				TraceNode step = old_kept.get(i);				
	//				StepChangeType changeType = typeChecker.getType(step, false, pairList, matcher);
	//				TraceNode matchedStep = changeType.getMatchingStep();
	//				if(new_kept.contains(matchedStep)) {										
	//					writer.println("\"OldNode: "+step.toString() +"\" " + "->" + "\"NewNode: "+matchedStep.toString() +"\" [color=grey55 style=dotted arrowhead=none constraint=true];");
	//				}
	//			}
				//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				/////////////////////////add dependency edges////////////////
				for(int i=0;i<old_kept.size(); i++) {
					TraceNode step = old_kept.get(i);
					if(old_corex_edges.keySet().contains(step)) 
						if(old_corex_edges.get(step)!=null)
							for(Pair<TraceNode, String> dep: old_corex_edges.get(step)) 
								if(old_kept.contains(dep.first())) 		
									if (dep.second().contains("CONTROL")) {
										StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
										if(changeType.getType()==StepChangeType.CTL)//only these ctl edges are important
											writer.println("\"OldNode: "+step.toString() +"\" " + "-> " + "\"OldNode: "+dep.first().toString() +"\" [color=black style=dashed arrowhead=normal constraint=false];");//connect control nodes to west	
									}
									else
										writer.println("\"OldNode: "+step.toString() +"\" " + "-> " + "\"OldNode: "+dep.first().toString() +"\" [color=black style=solid arrowhead=normal constraint=false xlabel=\" "+dep.second() +"   \" ];");//connect data nodes to east																		
				}
				
				for(int i=0;i<new_kept.size(); i++) {
					TraceNode step = new_kept.get(i);
					if(new_corex_edges.keySet().contains(step)) 
						if(new_corex_edges.get(step)!=null)
							for(Pair<TraceNode, String> dep: new_corex_edges.get(step)) 
								if(new_kept.contains(dep.first())) 		
									if (dep.second().contains("CONTROL")) {
										StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
										if(changeType.getType()==StepChangeType.CTL)//only these ctl edges are important
										writer.println("\"NewNode: "+step +"\" " + "-> " + "\"NewNode: "+dep.first().toString() +"\" [color=black style=dashed arrowhead=normal constraint=false];");//connect control nodes to west	
									}
									else
										writer.println("\"NewNode: "+step +"\" " + "-> " + "\"NewNode: "+dep.first().toString() +"\" [color=black style=solid arrowhead=normal constraint=false xlabel=\" "+dep.second() +"   \" ];");//connect data nodes to east																		
				}
				/////////////////////////////////////////////////////////////////////
				writer.println("}");
				writer.close();
				
			} catch (FileNotFoundException e) {                                        
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (UnsupportedEncodingException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} 
		}// end of save_result
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void getEdges(TraceNode step, List<TraceNode> kept, HashMap<TraceNode, List<Pair<TraceNode, String>>> corex_edges, HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map, HashMap<TraceNode, List<TraceNode>> ctl_map, HashMap<TraceNode, List<Pair<Integer, String>>> data_node_function, HashMap<TraceNode, List<Pair<Integer, String>>> ctl_node_function, StepChangeType changeType, HashMap<String, List<String>> functionsVars, HashMap<String, String>functionsDef) {
//		System.out.println("Node is " + step);
		List<Pair<TraceNode, String>> data_deps = data_map.get(step);	
//		System.out.println("the current data dep is " + data_deps);
		if(data_deps!=null) {
			for(Pair<TraceNode, String> pair:data_deps) {
//				System.out.println("The dep node is " + pair.first());
				String variable = "";
				if (pair.second().contains("#")) {
					String[] temp = pair.second().split("#");//for those return statement
					variable = temp[temp.length-1].split("\\(")[0] + " Return";
				}
				else
					variable = pair.second();
				if(kept.contains(pair.first())){//it is already kept in the trace, simple edge
//					System.out.println("it is already kept");
					List<Pair<TraceNode, String>> dataDeps = corex_edges.get(step);
					if(dataDeps==null) {
						dataDeps = new ArrayList<>();
					}	
					Pair<TraceNode, String> keyPair = new Pair(pair.first(), variable);						
					dataDeps.add(keyPair);					
					corex_edges.put(step, dataDeps);		
				}
				else {//transitive keep => compound edge => _Func
					getTransitiveEdges(step, pair.first(), variable, kept, corex_edges,data_map,ctl_map,data_node_function,ctl_node_function,changeType,functionsVars,functionsDef);							
				}							
			}
		}
		List<TraceNode> control_deps = ctl_map.get(step);	
		if(control_deps!=null) {
			for(TraceNode ctlNode:control_deps) {
				if(kept.contains(ctlNode)){//it is already kept in the trace => control edge
					List<Pair<TraceNode, String>> Deps = corex_edges.get(step);
					if(Deps==null) {
						Deps = new ArrayList<>();
					}			
					Deps.add(new Pair(ctlNode, "CONTROL"));					
					corex_edges.put(step, Deps);
				}							
			}
		}
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void getTransitiveEdges(TraceNode step, TraceNode first, String variable2Look, List<TraceNode> kept,
			HashMap<TraceNode, List<Pair<TraceNode, String>>> corex_edges,
			HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map, HashMap<TraceNode, List<TraceNode>> ctl_map, HashMap<TraceNode, List<Pair<Integer, String>>> data_node_function, HashMap<TraceNode, List<Pair<Integer, String>>> ctl_node_function, StepChangeType changeType, HashMap<String, List<String>> functionsVars, HashMap<String, String> functionsDef) {
//		System.out.println("head Node is " + step);
//		System.out.println("Node is " + first);
		List<Pair<TraceNode, String>> data_deps = data_map.get(first);	
//		System.out.println("the current data dep is " + data_deps);
		if(data_deps!=null) {
			for(Pair<TraceNode, String> pair:data_deps) {
//				System.out.println("The dep node is " + pair.first());
				if(kept.contains(pair.first())){//it is already kept in the trace 
					List<Pair<TraceNode, String>> dataDeps = corex_edges.get(step);
					if(dataDeps==null) {
						dataDeps = new ArrayList<>();
					}		
					if(changeType.getType()==StepChangeType.DAT||changeType.getType()==StepChangeType.IDT||changeType.getType()==StepChangeType.SRCDAT) {
				    	boolean fully_found = false;
				    	boolean node_found = false;
				    	String previous_function = "";
				    	Pair<TraceNode, String> found_node = null;
					    for(Pair<TraceNode, String> dep: dataDeps) {
					    	if(pair.first().equals(dep.first())) {//the node is already added between step and pair.first
//					    		System.out.println("already kept");
					    		if(functionsDef.containsKey(dep.second())) {
						    		if(functionsDef.get(dep.second()).equals(variable2Look) && functionsVars.containsKey(dep.second())) {//there is compound transitive edge between these two nodes
							    		if(functionsVars.get(dep.second()).contains(pair.second())) {//the variable pair.second was already visited and in the list 
//							    			System.out.println("already kept " + pair.second());
							    			fully_found = true;		
							    		}
						    		    else {
							    			node_found = true;
								    		previous_function = dep.second();
								    		found_node = dep;
						    		    }
						    	    }
					    	    }	
					        }
					    }
					    if (!fully_found) {//if fully found do nothing, it is repetitive
					    	String function = "";
				    		if(node_found && previous_function.contains("Func")) {//merge different compound data edges to the same node
//				    		   System.out.println("found node");
//				    		   System.out.println(dataDeps);
				    		   dataDeps.remove(found_node);//remove previous edge		
//				    		   System.out.println(dataDeps);
				    		   List<String> previous_vars = functionsVars.get(previous_function);//get list of vars of previous function
				    		   previous_vars.add(pair.second());
				    		   int index = 0;
				    		   for(Pair<Integer, String> variableIndex:data_node_function.get(step))
				    			   if (variableIndex.second().equals(variable2Look))
				    				   index = variableIndex.first();
				    		   function = variable2Look+"=Func_" + index + "(";
								for(int j=0; j<previous_vars.size();j++) {
									if(j!=previous_vars.size()-1)
										function = function + previous_vars.get(j) + ", ";
									else
										function = function + previous_vars.get(j);
								}
							   function = function + ")";
				    		   functionsVars.put(function, previous_vars);//update the function with the previous
				    		}
				    		else {//the first compound data edge between these two nodes
				    			int index = 0;
					    		for(Pair<Integer, String> variableIndex:data_node_function.get(step))
					    			if (variableIndex.second().equals(variable2Look))
					    				index = variableIndex.first();
				    			 function = variable2Look+"=Func_" + index + "(" + pair.second() + ")";
				    			 List<String> vars = new ArrayList();
					    		 vars.add(pair.second());
					    		 functionsVars.put(function, vars);
					    		 functionsDef.put(function, variable2Look);
				    		}
			    			Pair<TraceNode, String> keyPair = new Pair(pair.first(), function);						
							dataDeps.add(keyPair);					
							corex_edges.put(step, dataDeps);				    		
				    	}						
					}
					else if(changeType.getType()==StepChangeType.CTL||changeType.getType()==StepChangeType.SRCCTL) {
				    	boolean fully_found = false;
				    	boolean node_found = false;
				    	String previous_function = "";
				    	Pair<TraceNode, String> found_node = null;
					    for(Pair<TraceNode, String> dep: dataDeps) {
					    	if(pair.first().equals(dep.first())) {//the node is already added between step and pair.first
					    		if(functionsDef.containsKey(dep.second())) {
						    		if(functionsDef.get(dep.second()).equals(variable2Look) && functionsVars.containsKey(dep.second())) {//there is compound transitive edge between these two nodes
							    		if(functionsVars.get(dep.second()).contains(pair.second())) {//the variable pair.second was already visited and in the list 
							    			fully_found = true;		
							    		}
						    		    else {
							    			node_found = true;
								    		previous_function = dep.second();
								    		found_node = dep;
						    		    }
						    	    }
					    	    }	
					        }
					    }
					    if (!fully_found) {//if fully found do nothing, it is repetitive
					    	String function = "";
				    		if(node_found && previous_function.contains("Func")) {//merge different compound data edges to the same node
				    		   dataDeps.remove(found_node);//remove previous edge			    		   
				    		   List<String> previous_vars = functionsVars.get(previous_function);//get list of vars of previous function
				    		   previous_vars.add(pair.second());
				    		   int index = 0;
					    	   for(Pair<Integer, String> variableIndex:ctl_node_function.get(step))
					    			if (variableIndex.second().equals(variable2Look))
					    				index = variableIndex.first();
				    		   function = variable2Look+"=Func_" + index + "(";
								for(int j=0; j<previous_vars.size();j++) {
									if(j!=previous_vars.size()-1)
										function = function + previous_vars.get(j) + ", ";
									else
										function = function + previous_vars.get(j);
								}
							   function = function + ")";
				    		   functionsVars.put(function, previous_vars);//update the function with the previous
				    		}
				    		else {//the first compound data edge between these two nodes
				    			int index = 0;
				    			for(Pair<Integer, String> variableIndex:ctl_node_function.get(step))
					    			if (variableIndex.second().equals(variable2Look))
					    				index = variableIndex.first();
				    			 function = variable2Look+"=Func_" + index + "(" + pair.second() + ")";
				    			 List<String> vars = new ArrayList();
					    		 vars.add(pair.second());
					    		 functionsVars.put(function, vars);
					    		 functionsDef.put(function, variable2Look);
				    		}
			    			Pair<TraceNode, String> keyPair = new Pair(pair.first(), function);						
							dataDeps.add(keyPair);					
							corex_edges.put(step, dataDeps);				    		
				    	}						
					}
				}
				else {//transitive keep
					getTransitiveEdges(step, pair.first(), variable2Look, kept, corex_edges,data_map,ctl_map, data_node_function, ctl_node_function, changeType,functionsVars,functionsDef);
				}												
			}
		}

	}
    ////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void getContext(TraceNode step, List<TraceNode> kept, HashMap<TraceNode, List<Pair<TraceNode, String>>> corex_edges, HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map, HashMap<TraceNode, List<TraceNode>> ctl_map, HashMap<TraceNode, List<Pair<Integer, String>>> old_data_node_function, HashMap<TraceNode, List<Pair<Integer, String>>> old_ctl_node_function, StepChangeType changeType) {
//		System.out.println("Node is " + step);
		List<Pair<TraceNode, String>> data_deps = data_map.get(step);	
//		System.out.println("the current data dep is " + data_deps);
		if(data_deps!=null) {
			for(Pair<TraceNode, String> pair:data_deps) {
//				System.out.println("The dep node is " + pair.first());
				if(pair.first().getReadVariables().size()==0) {//it is reaching definition and need to be kept
					if(!kept.contains(pair.first())) {
						kept.add(pair.first());
					}
				}
				if(step.getInvocationParent()!=null) {
					if(!step.getInvocationParent().equals(pair.first().getInvocationParent())){//pair.first() is a method invocation => keep it
						if(!kept.contains(pair.first())) {
							kept.add(pair.first());
						}
					}
				}
				if(!kept.contains(pair.first())){//it is not already kept in the trace 
					getContext(pair.first(), kept, corex_edges,data_map,ctl_map,old_data_node_function,old_ctl_node_function,changeType);							
				}							
			}
		}
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void getTransitiveContext(TraceNode step, TraceNode first, List<TraceNode> kept,
			HashMap<TraceNode, List<Pair<TraceNode, String>>> corex_edges,
			HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map, HashMap<TraceNode, List<TraceNode>> ctl_map, HashMap<TraceNode, Integer> data_node_function, HashMap<TraceNode, Integer> ctl_node_function, StepChangeType changeType) {
//		System.out.println("Node is " + first);
		List<Pair<TraceNode, String>> data_deps = data_map.get(first);	
//		System.out.println("the current data dep is " + data_deps);
		if(data_deps!=null) {
			for(Pair<TraceNode, String> pair:data_deps) {
//				System.out.println("The dep node is " + pair.first());
				if(pair.first().getReadVariables().size()==0) {//it is reaching definition and need to be kept
					if(!kept.contains(pair.first())) {
						kept.add(pair.first());
					}
				}
				if(first.getInvocationParent()!=null) {
					if(!first.getInvocationParent().equals(pair.first().getInvocationParent())){//pair.first() is a method invocation => keep it
						if(!kept.contains(pair.first())) {
							kept.add(pair.first());							
						}
					}
				}
				if(!kept.contains(pair.first())){//it is already kept in the trace 
					getTransitiveContext(step, pair.first(), kept, corex_edges,data_map,ctl_map, data_node_function, ctl_node_function, changeType);
				}												
			}
		}
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void updateWorklistKeepingIdentical( HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> cashDeps, HashMap<TraceNode, 
			HashMap<Pair<TraceNode, String>, String>> OthercashDeps, TraceNode step, Trace trace, Trace otherTrace, List<TraceNode> visited, 
			List<TraceNode> workList, List<TraceNode> other_visited, List<TraceNode> other_workList, boolean isNew, 
			StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher, HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map, 
			HashMap<TraceNode, List<TraceNode>> ctl_map, String proPath,List<TraceNode> retained) {
		if(step==null)
			return;
		StepChangeType changeType = typeChecker.getType(step, isNew, pairList, matcher);	
		String onNew = isNew?"new":"old";
//		System.out.println("On " + onNew + " trace," + step);
		////////////////////////////////////////////////////////////////////
		if(changeType.getType()==StepChangeType.SRC){
//			System.out.println("debug: node is src diff");
			TraceNode matchedStep = changeType.getMatchingStep();	
			if(matchedStep!=null) {
				if(!other_visited.contains(matchedStep)) { 
					other_visited.add(matchedStep);
					other_workList.add(matchedStep);					
				}				
			}		
		}
		////////////////////////////////////////////////////////////////////
		//////////////////add corresponding node if it is data//////////////////
		if(changeType.getType()==StepChangeType.DAT){
//			System.out.println("debug: node is data diff");
			TraceNode matchedStep = changeType.getMatchingStep();
			if(!other_visited.contains(matchedStep)) { 
				other_visited.add(matchedStep);
				other_workList.add(matchedStep);					
			}
		}
		////////////////////////////////////////////////////////////////////
		//////////////////add control mending//////////////////
		if(changeType.getType()==StepChangeType.CTL){
//			System.out.println("debug: node is control diff");
			ClassLocation correspondingLocation = matcher.findCorrespondingLocation(step.getBreakPoint(), !isNew);	
			//System.out.println("debug: corresponding location:" + correspondingLocation.toString());
			TraceNode otherControlDom = findControlMendingNodeOnOtherTrace(step, pairList, otherTrace, !isNew, correspondingLocation, matcher);
			//System.out.println("debug: otherControlDom location:" + otherControlDom.toString());
			if(!other_visited.contains(otherControlDom)) { 
				other_visited.add(otherControlDom);
				other_workList.add(otherControlDom);
			}			
		}
		////////////////////////////////////////////////////////////////////
		//////////////////add identical for context//////////////////
		if(changeType.getType()==StepChangeType.IDT){
//			System.out.println("debug: node is identical");
			TraceNode matchedStep = changeType.getMatchingStep();
			if(!other_visited.contains(matchedStep)) { 
				other_visited.add(matchedStep);
				other_workList.add(matchedStep);
			}			
		}
		////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////
		
		HashMap<Pair<TraceNode, String>, String> deps = new HashMap<>();//map the <dep node, the var> and data/control		
		deps = getDirectDependencies(cashDeps, changeType, step, trace, isNew, typeChecker, pairList, matcher);
//		System.out.println("step:" + step + "deps: " + deps);
		////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////
		for(Pair<TraceNode, String> d: deps.keySet()){
//			System.out.println("dep node is " + d.first());						
			StepChangeType chgType = typeChecker.getType(d.first(), isNew, pairList, matcher);	
//			if(chgType.getType()!=StepChangeType.IDT) { //we want to keep any kind of dependencies
				if(deps.get(d)=="data") {
					List<Pair<TraceNode, String>> dataDeps = data_map.get(step);
					if(dataDeps==null) {
						dataDeps = new ArrayList<>();
					}
					dataDeps.add(d);					
					data_map.put(step, dataDeps);
				}
				else if(deps.get(d)=="control") {
					List<TraceNode> ctlDeps = ctl_map.get(step);
					if(ctlDeps==null) {
						ctlDeps = new ArrayList<>();
					}
					ctlDeps.add(d.first());
					ctl_map.put(step, ctlDeps);
				}

				if(!visited.contains(d.first())) {
					workList.add(d.first());
					visited.add(d.first());						
				}
//				if(chgType.getType()==StepChangeType.SRC) {
//					if(!retained.contains(d.first()))
//						retained.add(d.first());
//				}
				
//			}
			
//			if(d.first().isException()){
//				TraceNode nextStep = d.first().getStepInPrevious();
//				//System.out.println("debug: prev step " + nextStep);
//				List<TraceNode> ctlDeps = ctl_map.get(step);
//				if(ctlDeps==null) {
//					ctlDeps = new ArrayList<>();
//				}
//					ctlDeps.add(nextStep);
//					ctl_map.put(step, ctlDeps);
//				if(!visited.contains(nextStep)) {
//					workList.add(nextStep);
//					visited.add(nextStep);							
//				}						
//			}
         }	
	}
}
