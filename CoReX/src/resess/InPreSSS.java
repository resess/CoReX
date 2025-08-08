package resess;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
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
import java.util.Map;

import org.apache.poi.openxml4j.exceptions.InvalidFormatException;
import org.apache.poi.ss.usermodel.Row;
import org.apache.poi.ss.usermodel.Sheet;
import org.apache.poi.ss.usermodel.Workbook;
import org.apache.poi.ss.usermodel.WorkbookFactory;
import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;

import ca.ubc.ece.resess.slicer.dynamic.core.graph.DynamicControlFlowGraph;
import ca.ubc.ece.resess.slicer.dynamic.core.slicer.DynamicSlice;
import ca.ubc.ece.resess.slicer.dynamic.core.statements.StatementInstance;
import ca.ubc.ece.resess.slicer.dynamic.slicer4j.Slicer;

import microbat.codeanalysis.bytecode.ByteCodeParser;
import microbat.codeanalysis.bytecode.MethodFinderByLine;
import microbat.model.BreakPoint;
import microbat.model.ClassLocation;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.trace.TraceNodeOrderComparator;
import microbat.model.value.VarValue;
import sav.common.core.Pair;
import soot.ValueBox;
import tregression.StepChangeType;
import tregression.StepChangeTypeChecker;
import tregression.empiricalstudy.RootCauseNode;
import tregression.empiricalstudy.TestCase;
import tregression.model.PairList;
import tregression.model.TraceNodePair;
import tregression.separatesnapshots.DiffMatcher;

public class InPreSSS {
	public int findStartOrderInOtherTrace(TraceNode problematicStep, PairList pairList, boolean isOnBeforeTrace) {
		TraceNode node = problematicStep.getStepInPrevious();
		while (node != null) {
			TraceNode matchedNode = null;
			if (isOnBeforeTrace) {
				TraceNodePair pair = pairList.findByBeforeNode(node);
				if (pair != null) {
					matchedNode = pair.getAfterNode();
				}
			} else {
				TraceNodePair pair = pairList.findByAfterNode(node);
				if (pair != null) {
					matchedNode = pair.getBeforeNode();
				}
			}

			if (matchedNode != null) {
				return matchedNode.getOrder();
			}

			node = node.getStepInPrevious();

		}

		return 1;
	}

	public int findEndOrderInOtherTrace(TraceNode problematicStep, PairList pairList, boolean isOnBeforeTrace,
			Trace otherTrace) {
		TraceNode node = problematicStep.getStepInNext();
		while (node != null) {
			TraceNode matchedNode = null;
			if (isOnBeforeTrace) {
				TraceNodePair pair = pairList.findByBeforeNode(node);
				if (pair != null) {
					matchedNode = pair.getAfterNode();
				}
			} else {
				TraceNodePair pair = pairList.findByAfterNode(node);
				if (pair != null) {
					matchedNode = pair.getBeforeNode();
				}
			}

			if (matchedNode != null) {
				return matchedNode.getOrder();
			}

			node = node.getStepInNext();
		}

		/**
		 * Then, all the steps after problemStep cannot be matched in the other trace.
		 */
		int order0 = findStartOrderInOtherTrace(problematicStep, pairList, isOnBeforeTrace);
		if (order0 + 1 <= otherTrace.size()) {
			TraceNode n = otherTrace.getExecutionList().get(order0);
			while (n != null) {
				if (n.isConditional()) {
					if (n.getStepOverNext() != null) {
						return n.getStepOverNext().getOrder();
					} else {
						return n.getOrder();
					}
				} else {
					if (n.getStepOverNext() != null) {
						n = n.getStepOverNext();
					} else {
						n = n.getStepInNext();
					}
				}
			}
		}
		return otherTrace.size();

		/**
		 * The the length of the other trace.
		 */
	}

	public TraceNode findControlMendingNodeOnOtherTrace(TraceNode problematicStep, PairList pairList, Trace otherTrace,
			boolean isOtherTraceTheBeforeTrace, ClassLocation correspondingLocation, DiffMatcher matcher) {

		int startOrder = findStartOrderInOtherTrace(problematicStep, pairList, !isOtherTraceTheBeforeTrace);
		int endOrder = findEndOrderInOtherTrace(problematicStep, pairList, !isOtherTraceTheBeforeTrace, otherTrace);
		System.currentTimeMillis();
		TraceNode bestNode = null;
		int value = -1;

		TraceNode temp = null;
		for (int i = endOrder; i >= startOrder; i--) {
			if (i <= otherTrace.size()) {
				TraceNode node = otherTrace.getExecutionList().get(i - 1);
				if (node.isConditional()) {
					temp = node;
					if (node.getControlScope().containLocation(correspondingLocation)) {
						if (bestNode == null) {
							TraceNode programaticInvocationParent = problematicStep.getInvocationParent();
							TraceNode invocationParent = node.getInvocationParent();

							if (programaticInvocationParent == null && invocationParent == null) {
								bestNode = node;
							} else if (programaticInvocationParent != null && invocationParent != null) {
								if (pairList.isPair(programaticInvocationParent, invocationParent,
										!isOtherTraceTheBeforeTrace)) {
									bestNode = node;
								}
							}
						}
					} else {
						List<TraceNode> allControlDominatees = node.findAllControlDominatees();
						for (TraceNode controlDominatee : allControlDominatees) {
							if (controlDominatee.isException()) {
								if (value == -1) {
									bestNode = node;
									value++;
								} else {
									List<TraceNode> allDominatees = bestNode.findAllControlDominatees();
									if (allDominatees.contains(node)) {
										bestNode = node;
									}
								}
							}
						}
					}

				} else {
					BreakPoint correspondingPoint = new BreakPoint(correspondingLocation.getClassCanonicalName(), null,
							correspondingLocation.getLineNumber());
					MethodFinderByLine finder = new MethodFinderByLine(node.getBreakPoint());

					ByteCodeParser.parse(node.getClassCanonicalName(), finder, node.getTrace().getAppJavaClassPath());

					if (finder.getMethod() != null) {
						String methodSign = correspondingLocation.getClassCanonicalName() + "#"
								+ finder.getMethod().getName() + finder.getMethod().getSignature();
						if (node.getMethodSign().equals(methodSign)) {
							if (node.getLineNumber() < correspondingPoint.getLineNumber()) {
								if (finder.isThrow() || finder.isReturn()) {
									bestNode = node;
								}
							}
						}
					}

				}
			}
		}

		if (bestNode == null) {
			bestNode = temp;
		}

		return bestNode;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////

	public void dualSlicing(String basePath, String projectName, String bugID, TestCase tc, boolean slicer4J, String proPath, TraceNode observedFaultNode, Trace newTrace,
			Trace oldTrace, PairList PairList, DiffMatcher matcher, int oldTraceTime, int newTraceTime, int codeTime, int traceTime, List<RootCauseNode> rootList,boolean debug) throws IOException {
	
		List<TraceNode> new_workList = new ArrayList<>();
		List<TraceNode> new_visited = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> new_data_map = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> new_ctl_map = new HashMap<>();

		List<TraceNode> old_workList = new ArrayList<>();
		List<TraceNode> old_visited = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> old_data_map = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> old_ctl_map = new HashMap<>();

		HashMap<TraceNode, String> oldTheReasonToBeInResult = new HashMap<>();
		HashMap<TraceNode, String> newTheReasonToBeInResult = new HashMap<>();

		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> old_CashDeps = new HashMap<>();
		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> new_CashDeps = new HashMap<>();

		new_visited.add(observedFaultNode);
		new_workList.add(observedFaultNode);
		newTheReasonToBeInResult.put(observedFaultNode, "the failed assertion");
				
		System.out.println("#############################");
		System.out.println("Starting Working list");

		BiMap<TraceNode, String> newSlicer4J = HashBiMap.create();
		BiMap<TraceNode, String> oldSlicer4J = HashBiMap.create();
		HashMap<String, List<String>> newSlicer4JBytecodeMapping = new HashMap<>();
		HashMap<String, List<String>> oldSlicer4JBytecodeMapping = new HashMap<>();

//		Path currRelativePath = Paths.get("");
		String relativepath = System.getProperty("user.dir")+"/deps/Slicer4J/Slicer4J";
        Path slicer_root = Paths.get(relativepath);
		 

		Path old_sliceLogger = Paths.get(slicer_root.getParent().getParent().toString(), "DynamicSlicingCore"
				+ File.separator + "DynamicSlicingLoggingClasses" + File.separator + "DynamicSlicingLogger.jar");
		String old_jarPath = proPath + "/results/old/program.jar";
		Path old_outDir = Paths.get(proPath + "/results/old/Slicer4JResults");
		Slicer old_slicer = setupSlicing(slicer_root, old_jarPath, old_outDir, old_sliceLogger);
		DynamicControlFlowGraph old_dcfg = old_slicer.prepareGraph();


		Path new_sliceLogger = Paths.get(slicer_root.getParent().getParent().toString(), "DynamicSlicingCore"
				+ File.separator + "DynamicSlicingLoggingClasses" + File.separator + "DynamicSlicingLogger.jar");
		String new_jarPath = proPath + "/results/new/program.jar";
		Path new_outDir = Paths.get(proPath + "/results/new/Slicer4JResults");
		Slicer new_slicer = setupSlicing(slicer_root, new_jarPath, new_outDir, new_sliceLogger);
		DynamicControlFlowGraph new_dcfg = new_slicer.prepareGraph();

		if (slicer4J) {
			getMappingOfTraces(proPath, true, newTrace, newSlicer4J, newSlicer4JBytecodeMapping);
			getMappingOfTraces(proPath, false, oldTrace, oldSlicer4J, oldSlicer4JBytecodeMapping);
		}
		
		StepChangeTypeChecker typeChecker = new StepChangeTypeChecker(newTrace, oldTrace);
		
		Long dual_start_time = System.currentTimeMillis();
		while (!new_workList.isEmpty() || !old_workList.isEmpty()) {
			while (!new_workList.isEmpty()) {
//				System.out.println("#############################");
				TraceNode step = new_workList.remove(0);
				updateWorklist(newTheReasonToBeInResult, oldTheReasonToBeInResult, new_dcfg, new_slicer, old_dcfg,
						old_slicer, new_CashDeps, old_CashDeps, newSlicer4J, oldSlicer4J, newSlicer4JBytecodeMapping,
						oldSlicer4JBytecodeMapping, slicer4J, step, newTrace, oldTrace, new_visited, new_workList,
						old_visited, old_workList, true, typeChecker, PairList, matcher, new_data_map, new_ctl_map,
						proPath, bugID);
			}
			////////////////////////////////////////////////////////////////////////////////////////
			while (!old_workList.isEmpty()) {
//				System.out.println("#############################");
				TraceNode step = old_workList.remove(0);
				updateWorklist(oldTheReasonToBeInResult, newTheReasonToBeInResult, new_dcfg, new_slicer, old_dcfg,
						old_slicer, old_CashDeps, new_CashDeps, oldSlicer4J, newSlicer4J, oldSlicer4JBytecodeMapping,
						newSlicer4JBytecodeMapping, slicer4J, step, oldTrace, newTrace, old_visited, old_workList,
						new_visited, new_workList, false, typeChecker, PairList, matcher, old_data_map, old_ctl_map,
						proPath, bugID);
			}
		}
		/// ################################################################
		/// ################################################################
		Long dual_finish_time = System.currentTimeMillis();
		int dual_Time = (int) (dual_finish_time - dual_start_time);
		printDualSliceResults(old_visited, false, proPath, matcher,oldSlicer4J, oldSlicer4JBytecodeMapping);
		printDualSliceResults(new_visited,true, proPath,matcher,newSlicer4J, newSlicer4JBytecodeMapping);
		/// ################################################################
		/// ################################################################
		HashMap<Integer, Integer> oldChangeChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newChangeChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> oldCommonChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newCommonChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> oldTestCaseChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newTestCaseChunkInfo = new HashMap<>();
		Collections.sort(old_visited, new TraceNodePairOrderComparator(oldSlicer4J, oldSlicer4JBytecodeMapping));
		Collections.sort(new_visited, new TraceNodePairOrderComparator(newSlicer4J, newSlicer4JBytecodeMapping));
		getChangeChunks(typeChecker, matcher, old_visited,new_visited,oldChangeChunkInfo,newChangeChunkInfo);
//		getChangeChunks(typeChecker, InPreSSPairList, matcher, old_visited,new_visited,oldChangeChunkInfo,newChangeChunkInfo);
		getTestCaseChunks(tc,old_visited,new_visited,oldTestCaseChunkInfo,newTestCaseChunkInfo);
		getCommonBlocksChunks(typeChecker, matcher, tc,old_visited,new_visited,oldCommonChunkInfo,newCommonChunkInfo);
//		getCommonBlocksChunks(typeChecker, InPreSSPairList, matcher, tc,old_visited,new_visited,oldCommonChunkInfo,newCommonChunkInfo);
		//System.out.println("##############Printing Abstraction to Graph##############");

		HashMap<TraceNode, List<Pair<TraceNode, String>>> both_new_data_map = new_data_map;
		HashMap<TraceNode, List<TraceNode>> both_new_ctl_map = new_ctl_map;
		HashMap<TraceNode, List<Pair<TraceNode, String>>> both_old_data_map = old_data_map;
		HashMap<TraceNode, List<TraceNode>> both_old_ctl_map = old_ctl_map;
		
		System.out.println("##############InPress##############");
		List<TraceNode> old_kept = new ArrayList<>();
		List<TraceNode> new_kept = new ArrayList<>();		
		List<TraceNode> old_retained = new ArrayList<>();		
		List<TraceNode> new_retained = new ArrayList<>();	
		List<String> old_kept_sourceCodeLevel = new ArrayList<>();		
		List<String> new_kept_sourceCodeLevel = new ArrayList<>();	
		
		//keep all statements in the test even if they remove by dual slice:
		//addingClientTestNodes(tc, oldTrace.getExecutionList(), newTrace.getExecutionList(), old_kept, new_kept, old_retained, new_retained, oldSlicer4J, newSlicer4J, oldSlicer4JBytecodeMapping, newSlicer4JBytecodeMapping);		
		
		//keep statements in the test that are kept in dual slice:
//		addingClientTestNodes(tc, old_visited, new_visited, old_kept, new_kept, old_retained, new_retained, oldSlicer4J, newSlicer4J, oldSlicer4JBytecodeMapping, newSlicer4JBytecodeMapping);
		int oldRetainedTestRemovedByDual = getRetainedTestRemovedByDual(tc, oldTrace.getExecutionList(),old_visited,oldSlicer4J,oldSlicer4JBytecodeMapping);
		int newRetainedTestRemovedByDual = getRetainedTestRemovedByDual(tc, newTrace.getExecutionList(),new_visited,newSlicer4J,newSlicer4JBytecodeMapping);
		

		HashMap<Integer, List<TraceNode>> oldCtlBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newCtlBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> oldDataBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newDataBlockNodes = new HashMap<>();
		long inPreSS_start_time = System.currentTimeMillis();
		InPreSSAbstractionCircleOnlySameFunctionsCommonTrianlges(tc, proPath, old_visited, new_visited, typeChecker,
				PairList, matcher, both_old_data_map, both_old_ctl_map, both_new_data_map,
				both_new_ctl_map, oldSlicer4J, newSlicer4J, oldSlicer4JBytecodeMapping, newSlicer4JBytecodeMapping,
				new_dcfg, new_slicer, old_dcfg, old_slicer, old_kept, new_kept, oldDataBlockNodes, newDataBlockNodes,
				oldCtlBlockNodes, newCtlBlockNodes, old_retained, new_retained,old_kept_sourceCodeLevel,new_kept_sourceCodeLevel);
		long inPreSS_finish_time = System.currentTimeMillis();
		int inPreSS_Time = (int) (inPreSS_finish_time - inPreSS_start_time);
		if(debug)
			PrintFinalResultAll(tc,basePath, projectName, bugID, newTrace, oldTrace, new_visited, old_visited, new_kept, old_kept, new_retained, 
				old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
				traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,oldTestCaseChunkInfo,newTestCaseChunkInfo,
				oldCommonChunkInfo, newCommonChunkInfo,
				oldRetainedTestRemovedByDual,newRetainedTestRemovedByDual);	
		else {
			if(projectName.equals("Chart")||projectName.equals("Closure")||projectName.equals("Lang")||projectName.equals("Math")||projectName.equals("Mockito")||projectName.equals("Time")) {
				PrintD4JPaperResults(tc,basePath, projectName, bugID, newTrace, oldTrace, new_visited, old_visited, new_kept, old_kept, new_retained, 
						old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
						traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,oldTestCaseChunkInfo,newTestCaseChunkInfo,
						oldCommonChunkInfo, newCommonChunkInfo,
						oldRetainedTestRemovedByDual,newRetainedTestRemovedByDual,old_kept_sourceCodeLevel,new_kept_sourceCodeLevel);
			}
			else
				PrintPaperResults(tc,basePath, projectName, bugID, newTrace, oldTrace, new_visited, old_visited, new_kept, old_kept, new_retained, 
				old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
				traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,oldTestCaseChunkInfo,newTestCaseChunkInfo,
				oldCommonChunkInfo, newCommonChunkInfo,
				oldRetainedTestRemovedByDual,newRetainedTestRemovedByDual,old_kept_sourceCodeLevel,new_kept_sourceCodeLevel);	
			
			PrintResults(tc,basePath, projectName, bugID, typeChecker,PairList, matcher, newTrace, oldTrace,  new_visited, old_visited, new_kept,old_kept,
					new_retained, old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
									traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,
									oldCommonChunkInfo, newCommonChunkInfo, old_kept_sourceCodeLevel,new_kept_sourceCodeLevel,newSlicer4J, oldSlicer4J, newSlicer4JBytecodeMapping,
									oldSlicer4JBytecodeMapping);
		}
            		   
	}
	private void PrintResults(TestCase tc, String basePath, String projectName, String bugID, StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher, 
			Trace newTrace,
			Trace oldTrace, List<TraceNode> new_visited, List<TraceNode> old_visited, List<TraceNode> inpress_new_kept,List<TraceNode> inpress_old_kept, 
			List<TraceNode> new_retained, List<TraceNode> old_retained,
			HashMap<Integer, List<TraceNode>> newDataBlockNodes, HashMap<Integer, List<TraceNode>> oldDataBlockNodes,
			HashMap<Integer, List<TraceNode>> newCtlBlockNodes, HashMap<Integer, List<TraceNode>> oldCtlBlockNodes,
			int oldTraceTime, int newTraceTime, int codeTime, int traceTime, int dual_Time, int inpress_time,
			HashMap<Integer, Integer> oldChangeChunkInfo, HashMap<Integer, Integer> newChangeChunkInfo,
			HashMap<Integer, Integer> oldCommonChunkInfo, HashMap<Integer, Integer> newCommonChunkInfo,
			List<String> old_kept_sourceCodeLevel,
			List<String> new_kept_sourceCodeLevel,BiMap<TraceNode, String> NewSlicer4JMapping, BiMap<TraceNode, String> OldSlicer4JMapping,
			HashMap<String, List<String>> NewSlicer4JBytecodeMapping,
			HashMap<String, List<String>> OldSlicer4JBytecodeMapping) {
		

		Path path = Paths.get(basePath+"/results");
		if(!Files.exists(path)) 
			new File(basePath+"/results").mkdirs();
		
		String results = basePath+"/results/"+projectName+"Dual_InPreSS_Results.xlsx";
	    File tempFile = new File(results);
	    boolean FirstTime = false;
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######

		double DualoldReduction_orig = (Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(old_visited.size()))/(Double.valueOf(oldTrace.getExecutionList().size()))*100.0;
		double DualnewReduction_orig = (Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(new_visited.size()))/(Double.valueOf(newTrace.getExecutionList().size()))*100.0;
	    double InPreSSoldReduction_orig = (Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(inpress_old_kept.size()))/(Double.valueOf(oldTrace.getExecutionList().size()))*100.0;
	    double InPreSSnewReduction_orig = (Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(inpress_new_kept.size()))/(Double.valueOf(newTrace.getExecutionList().size()))*100.0;

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
	        		"Old trace size (#T)","Old Dual size (#DSlice)", "%Old Trace vs Dual Reduct.", "Old InPreSS size", "%Old Trace vs InPreSS Reduct.", 
	        		"New trace size (#T)","New Dual size (#DSlice)", "%New Trace vs Dual Reduct.", "New InPreSS size", "%New Trace vs InPreSS Reduct.", 
	        		"DSlice Time (Min)", "InPreSS Time (Min)"
	        		};
	        WriteToExcel(results, header, "RQ3-2",true, true);
	    }
        String[] detailedDataRQ3_2 = {bugID, 
	    		String.valueOf(oldTrace.getExecutionList().size()), 
	    		String.valueOf(old_visited.size()), String.valueOf(DualoldReduction_orig), 
	    		String.valueOf(inpress_old_kept.size()), String.valueOf(InPreSSoldReduction_orig), 
	    		String.valueOf(newTrace.getExecutionList().size()), 
	    		String.valueOf(new_visited.size()), String.valueOf(DualnewReduction_orig), 
	    		String.valueOf(inpress_new_kept.size()), String.valueOf(InPreSSnewReduction_orig), 
	    		String.valueOf((Double.valueOf(dual_Time)/1000.0)/60.0), String.valueOf((Double.valueOf(inpress_time)/1000.0)/60.0)
	    		};
	    WriteToExcel(results,detailedDataRQ3_2,"RQ3-2",true, false);
					

	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######

	       /////////////////#######////#######////#######////#######////#######////#######
	       /////////////////#######////#######////#######////#######////#######////#######
	       
	       boolean Einspect5_Dual = CanFindTheBug(5, old_visited, new_visited,old_retained,new_retained,NewSlicer4JMapping,OldSlicer4JMapping,NewSlicer4JBytecodeMapping,OldSlicer4JBytecodeMapping);
	       boolean Einspect5_InPreSS = CanFindTheBug(5, inpress_old_kept, inpress_new_kept,old_retained,new_retained,NewSlicer4JMapping,OldSlicer4JMapping,NewSlicer4JBytecodeMapping,OldSlicer4JBytecodeMapping);
	      
	       boolean Einspect10_Dual = CanFindTheBug(10, old_visited, new_visited,old_retained,new_retained,NewSlicer4JMapping,OldSlicer4JMapping,NewSlicer4JBytecodeMapping,OldSlicer4JBytecodeMapping);
	       boolean Einspect10_InPreSS = CanFindTheBug(10, inpress_old_kept, inpress_new_kept,old_retained,new_retained,NewSlicer4JMapping,OldSlicer4JMapping,NewSlicer4JBytecodeMapping,OldSlicer4JBytecodeMapping);
	       
	       boolean Einspect30_Dual = CanFindTheBug(30, old_visited, new_visited,old_retained,new_retained,NewSlicer4JMapping,OldSlicer4JMapping,NewSlicer4JBytecodeMapping,OldSlicer4JBytecodeMapping);
	       boolean Einspect30_InPreSS = CanFindTheBug(30, inpress_old_kept, inpress_new_kept,old_retained,new_retained,NewSlicer4JMapping,OldSlicer4JMapping,NewSlicer4JBytecodeMapping,OldSlicer4JBytecodeMapping);
	       
	       boolean Einspect50_Dual = CanFindTheBug(50, old_visited, new_visited,old_retained,new_retained,NewSlicer4JMapping,OldSlicer4JMapping,NewSlicer4JBytecodeMapping,OldSlicer4JBytecodeMapping);
	       boolean Einspect50_InPreSS = CanFindTheBug(50, inpress_old_kept, inpress_new_kept,old_retained,new_retained,NewSlicer4JMapping,OldSlicer4JMapping,NewSlicer4JBytecodeMapping,OldSlicer4JBytecodeMapping);
	       
	       boolean Einspect100_Dual = CanFindTheBug(100, old_visited, new_visited,old_retained,new_retained,NewSlicer4JMapping,OldSlicer4JMapping,NewSlicer4JBytecodeMapping,OldSlicer4JBytecodeMapping);
	       boolean Einspect100_InPreSS = CanFindTheBug(100, inpress_old_kept, inpress_new_kept,old_retained,new_retained,NewSlicer4JMapping,OldSlicer4JMapping,NewSlicer4JBytecodeMapping,OldSlicer4JBytecodeMapping);
	       
	       boolean Einspect200_Dual = CanFindTheBug(200, old_visited, new_visited,old_retained,new_retained,NewSlicer4JMapping,OldSlicer4JMapping,NewSlicer4JBytecodeMapping,OldSlicer4JBytecodeMapping);
	       boolean Einspect200_InPreSS = CanFindTheBug(200, inpress_old_kept, inpress_new_kept,old_retained,new_retained,NewSlicer4JMapping,OldSlicer4JMapping,NewSlicer4JBytecodeMapping,OldSlicer4JBytecodeMapping);
	       
	       int traversed_old_Dual = CalculateWastedEffort(old_visited,old_retained,OldSlicer4JMapping,OldSlicer4JBytecodeMapping);
	       int traversed_new_Dual = CalculateWastedEffort(new_visited,new_retained,NewSlicer4JMapping,NewSlicer4JBytecodeMapping);
	       int traversed_old_InPreSS = CalculateWastedEffort(inpress_old_kept,old_retained,OldSlicer4JMapping,OldSlicer4JBytecodeMapping);
	       int traversed_new_InPreSS = CalculateWastedEffort(inpress_new_kept,new_retained,NewSlicer4JMapping,NewSlicer4JBytecodeMapping);
	       
	       double wasted_effort_old_Dual = ((double)traversed_old_Dual/oldTrace.getExecutionList().size())*100.0;
	       double wasted_effort_new_Dual = ((double)traversed_new_Dual/newTrace.getExecutionList().size())*100.0;
	       double wasted_effort_old_InPreSS = ((double)traversed_old_InPreSS/oldTrace.getExecutionList().size())*100.0;
	       double wasted_effort_new_InPreSS = ((double)traversed_new_InPreSS/newTrace.getExecutionList().size())*100.0;
	      
	       if (FirstTime) {		    	
		        String[] header = {"Bug ID", 
		        		"Einspect@5-Dual", "Einspect@5-InPreSS", 
		        		"Einspect@10-Dual", "Einspect@10-InPreSS", 
		        		"Einspect@30-Dual", "Einspect@30-InPreSS",
		        		"Einspect@50-Dual", "Einspect@50-InPreSS",
		        		"Einspect@100-Dual", "Einspect@100-InPreSS",
		        		"Einspect@200-Dual", "Einspect@200-InPreSS", 
		        		"#Traversed Old Stmt-Dual", "#Traversed New Stmt-Dual", "#Traversed Old Stmt-InPreSS", "#Traversed New Stmt-InPreSS",
		        		"Exam% Old-Dual", "Exam% New-Dual", "Exam% Old-InPreSS", "Exam% New-InPreSS"     		
		        		};
		        WriteToExcel(results, header, "RQ3-3",true, true);
		    }
		    String[] detailedDataRQ4 = {bugID, 
		    		String.valueOf(Einspect5_Dual),String.valueOf(Einspect5_InPreSS),
		    		String.valueOf(Einspect10_Dual),String.valueOf(Einspect10_InPreSS),
		    		String.valueOf(Einspect30_Dual),String.valueOf(Einspect30_InPreSS),
		    		String.valueOf(Einspect50_Dual),String.valueOf(Einspect50_InPreSS),
		    		String.valueOf(Einspect100_Dual),String.valueOf(Einspect100_InPreSS),
		    		String.valueOf(Einspect200_Dual),String.valueOf(Einspect200_InPreSS),
		    		String.valueOf(traversed_old_Dual),String.valueOf(traversed_new_Dual),String.valueOf(traversed_old_InPreSS),String.valueOf(traversed_new_InPreSS),
		    		String.valueOf(wasted_effort_old_Dual),String.valueOf(wasted_effort_new_Dual),String.valueOf(wasted_effort_old_InPreSS),String.valueOf(wasted_effort_new_InPreSS)
		    };
		    WriteToExcel(results,detailedDataRQ4,"RQ3-3",true, false);
						

		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
		System.out.println("##############Finish##############");
		
	}
	private int CalculateWastedEffort(List<TraceNode> visited, List<TraceNode> retained,BiMap<TraceNode, String> Slicer4JMapping,
			HashMap<String, List<String>> Slicer4JBytecodeMapping) {
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
	private boolean CanFindTheBug(int EInsp, List<TraceNode> old_visited, List<TraceNode> new_visited,List<TraceNode> old_retained, List<TraceNode> new_retained,
			BiMap<TraceNode, String> NewSlicer4JMapping, BiMap<TraceNode, String> OldSlicer4JMapping,
			HashMap<String, List<String>> NewSlicer4JBytecodeMapping,
			HashMap<String, List<String>> OldSlicer4JBytecodeMapping) {
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
	////////////////////////////////////////////////////////////////////////////////////////////////////s

	private void PrintD4JPaperResults(TestCase tc, String basePath, String projectName, String bugID, Trace newTrace,
			Trace oldTrace, List<TraceNode> new_visited, List<TraceNode> old_visited, List<TraceNode> new_kept,
			List<TraceNode> old_kept, List<TraceNode> new_retained, List<TraceNode> old_retained,
			HashMap<Integer, List<TraceNode>> newDataBlockNodes, HashMap<Integer, List<TraceNode>> oldDataBlockNodes,
			HashMap<Integer, List<TraceNode>> newCtlBlockNodes, HashMap<Integer, List<TraceNode>> oldCtlBlockNodes,
			int oldTraceTime, int newTraceTime, int codeTime, int traceTime, int dual_Time, int inPreSS_Time,
			HashMap<Integer, Integer> oldChangeChunkInfo, HashMap<Integer, Integer> newChangeChunkInfo,
			HashMap<Integer, Integer> oldTestCaseChunkInfo, HashMap<Integer, Integer> newTestCaseChunkInfo,
			HashMap<Integer, Integer> oldCommonChunkInfo, HashMap<Integer, Integer> newCommonChunkInfo,
			int oldRetainedTestRemovedByDual, int newRetainedTestRemovedByDual, List<String> old_kept_sourceCodeLevel,
			List<String> new_kept_sourceCodeLevel) {
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
	    		String.valueOf((Double.valueOf(dual_Time)/1000.0)/60.0), String.valueOf((Double.valueOf(inPreSS_Time)/1000.0)/60.0)
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

	private int getRetainedTestRemovedByDual(TestCase tc, List<TraceNode> executionList, List<TraceNode> visited,
			BiMap<TraceNode, String> oldSlicer4J, HashMap<String, List<String>> oldSlicer4JBytecodeMapping) {
		int res = 0;
		for (TraceNode node: executionList) {
			String ClassName = node.getClassCanonicalName();
			if (tc.testClass.equals(ClassName)) {
				List<Integer> positions = getSlicer4JMappedNode(node,oldSlicer4J,oldSlicer4JBytecodeMapping);
				if (positions !=null && positions.size()!=0) {
					if(visited.contains(node)) {
						//it is already kept by us.
					}
					else {
						res++;
					}
				}
			}
		}
		return res;
	}

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

		int CurrentChunk=0;
		boolean PreviousStatementWasChange = false;
		for (int i = 0; i <= old_visited.size()-1; i++) {
			TraceNode step = old_visited.get(i);
			boolean isSourceDiff = matcher.checkSourceDiff(step.getBreakPoint(), false);		
			if(isSourceDiff) {
				//System.out.println("Yes, I'm changed in OLD!");
				if(PreviousStatementWasChange) {
					//do nothing. we are already in this chunk. We can later add all changed statements to the arry for the chunck
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
				//System.out.println("Yes, I'm changed in NEW!");
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
	////////////////////////////////////////////////////////////////////////////////////////////////////s
	private void addingClientTestNodes(TestCase tc, List<TraceNode> old_visited, List<TraceNode> new_visited, List<TraceNode> old_kept,
			List<TraceNode> new_kept, List<TraceNode> old_retained, List<TraceNode> new_retained, BiMap<TraceNode, String> oldSlicer4J, BiMap<TraceNode, String> newSlicer4J, HashMap<String, List<String>> oldSlicer4JBytecodeMapping, HashMap<String, List<String>> newSlicer4JBytecodeMapping) {
	for (TraceNode node: old_visited) {
		String ClassName = node.getClassCanonicalName();
		if (tc.testClass.equals(ClassName)) {
			List<Integer> positions = getSlicer4JMappedNode(node,oldSlicer4J,oldSlicer4JBytecodeMapping);
			if (positions !=null && positions.size()!=0) {
				if(!old_kept.contains(node)) {
					old_kept.add(node);
					old_retained.add(node);
				}
			}
		}
	}
	for (TraceNode node: new_visited) {
		String ClassName = node.getClassCanonicalName();
		if (tc.testClass.equals(ClassName)) {
			List<Integer> positions = getSlicer4JMappedNode(node,newSlicer4J,newSlicer4JBytecodeMapping);
			if (positions !=null && positions.size()!=0) {
				if(!new_kept.contains(node)) {
					new_kept.add(node);
					new_retained.add(node);
				}
			}
		}
	}
			
}

	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	public static void getMappingOfTraces(String proPath, boolean isNew, Trace Trace, BiMap<TraceNode, String> Slicer4J,
			HashMap<String, List<String>> NodesMapping) {

		String path = (isNew) ? "new" : "old";
		File file = new File(proPath + "/results/" + path + "/Slicer4JResults/trace.log_icdg.log");
		BufferedReader br;
		List<String> Slicer4Jnodes = new ArrayList<String>();
		try {
			PrintWriter writer;
			writer = new PrintWriter(proPath + "/results/" + path + "/Slicer4JResults/Slicer4JTrace.txt", "UTF-8");
			br = new BufferedReader(new FileReader(file));
			String st = br.readLine();
			String CurrClassName = st.split(", ")[2].trim();
			String CurrLineNo = st.split("LINENO:")[1].split(":")[0];
			String CurrMethodName = st.split(", ")[1].split(" ")[1];
			List<String> ByteCodeMappings = new ArrayList<String>();
			String statment = "";
			ByteCodeMappings.add(st);

			int order = 1;
			while ((st = br.readLine()) != null) {

				if (!st.contains("LINENO"))
					continue;
				String clasName = st.split(", ")[2].trim();
				String Line = st.split("LINENO:")[1].split(":")[0];
				String MethodName = st.split(", ")[1].split(" ")[1];
				if (clasName.equals(CurrClassName) && Line.equals(CurrLineNo)) {
					ByteCodeMappings.add(st);
				} else {// add the previous and initilize
					statment = "order " + String.valueOf(order) + "~" + CurrClassName + ": line " + CurrLineNo + " in "
							+ CurrMethodName;
					Slicer4Jnodes.add(statment);
					NodesMapping.put(statment, ByteCodeMappings);
					writer.println(statment);
					order = order + 1;
					CurrClassName = clasName;
					CurrLineNo = Line;
					CurrMethodName = MethodName;
					ByteCodeMappings = new ArrayList<String>();
					ByteCodeMappings.add(st);
				}
			}
			statment = "order " + String.valueOf(order) + "~" + CurrClassName + ": line " + CurrLineNo + " in "
					+ CurrMethodName;
			Slicer4Jnodes.add(statment);
			NodesMapping.put(statment, ByteCodeMappings);
			writer.println(statment);
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
		////////////////////////////////////////////////////////
		List<TraceNode> nodes = Trace.getExecutionList();
		PrintWriter writer;
		try {
			writer = new PrintWriter(proPath + "/results/" + path + "/Slicer4JResults/Slicer4JTraceMapping.txt",
					"UTF-8");
			for (int i = 0; i < nodes.size(); i++) {
				// System.out.println("From trace");
				// System.out.println(nodes.get(i));
				String ClassName = nodes.get(i).toString().split("~")[1].split(":")[0];
				String LineNo = nodes.get(i).toString().split("line ")[1].split(" ")[0];
				for (int j = 0; j < Slicer4Jnodes.size(); j++) {
					// System.out.println("From Slicer4J");
					// System.out.println(Slicer4Jnodes.get(j));
					String sClassName = Slicer4Jnodes.get(j).toString().split("~")[1].split(":")[0];
					String sLineNo = Slicer4Jnodes.get(j).toString().split("line ")[1].split(" ")[0];
					if (ClassName.equals(sClassName) && LineNo.equals(sLineNo)) {
						// System.out.println(nodes.get(i) + " ---> " + Slicer4Jnodes.get(j));
						writer.println(nodes.get(i) + " ---> " + Slicer4Jnodes.get(j));
						Slicer4J.put(nodes.get(i), Slicer4Jnodes.get(j));
						Slicer4Jnodes.remove(j);
						break;
					}
				}
			}
			writer.close();
		} catch (FileNotFoundException | UnsupportedEncodingException e) {
			e.printStackTrace();
		}
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void updateWorklist(HashMap<TraceNode, String> reasons, HashMap<TraceNode, String> other_reasons,
			DynamicControlFlowGraph new_dcfg, Slicer new_slicer, DynamicControlFlowGraph old_dcfg, Slicer old_slicer,
			HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> cashDeps,
			HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> OthercashDeps,
			BiMap<TraceNode, String> Slicer4JMapping, BiMap<TraceNode, String> OtherSlicer4JMapping,
			HashMap<String, List<String>> Slicer4JBytecodeMapping,
			HashMap<String, List<String>> otherSlicer4JBytecodeMapping, boolean slicer4J, TraceNode step, Trace trace,
			Trace otherTrace, List<TraceNode> visited, List<TraceNode> workList, List<TraceNode> other_visited,
			List<TraceNode> other_workList, boolean isNew, StepChangeTypeChecker typeChecker, PairList pairList,
			DiffMatcher matcher, HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map,
			HashMap<TraceNode, List<TraceNode>> ctl_map, String proPath, String bugID) {

		StepChangeType changeType = typeChecker.getType(step, isNew, pairList, matcher);
		String onNew = isNew ? "new" : "old";
//		System.out.println("On " + onNew + " trace," + step);
		////////////////////////////////////////////////////////////////////
		if (changeType.getType() == StepChangeType.SRC) {
//			System.out.println("debug: node is src diff");
			TraceNode matchedStep = changeType.getMatchingStep();	
			List<Integer> matchPositions = getSlicer4JMappedNode(matchedStep, OtherSlicer4JMapping, otherSlicer4JBytecodeMapping);
			if (matchPositions != null) {
				if(!other_visited.contains(matchedStep)) { 
					other_visited.add(matchedStep);
					other_workList.add(matchedStep);					
				}
			}
		}
		////////////////////////////////////////////////////////////////////
		////////////////// add corresponding node if it is data//////////////////
		if (changeType.getType() == StepChangeType.DAT) {
//			System.out.println("debug: node is data diff");
			TraceNode matchedStep = changeType.getMatchingStep();
			// System.out.println("debug: matched step: " + matchedStep);
			List<Integer> matchPositions = getSlicer4JMappedNode(matchedStep, OtherSlicer4JMapping,
					otherSlicer4JBytecodeMapping);
			if (matchPositions != null) {
				if (!other_visited.contains(matchedStep)) {
					other_visited.add(matchedStep);
					other_workList.add(matchedStep);
					List<Integer> positions = getSlicer4JMappedNode(step, Slicer4JMapping, Slicer4JBytecodeMapping);
					if (positions != null && positions.size() != 0) {
						String result = String.valueOf(positions.get(0));// the first byte code trace order in slicer4J
						other_reasons.put(matchedStep, "data diff node ~ to node " + result);
						// System.out.println("debug: list: " + other_workList);
					}
				}
			}
		}
		////////////////////////////////////////////////////////////////////
		////////////////// add control mending//////////////////
		if (changeType.getType() == StepChangeType.CTL) {
//			System.out.println("debug: node is control diff");
			ClassLocation correspondingLocation = matcher.findCorrespondingLocation(step.getBreakPoint(), !isNew);
			// System.out.println("debug: control corresponding Location " +
			// correspondingLocation);
			TraceNode otherControlDom = findControlMendingNodeOnOtherTrace(step, pairList, otherTrace, !isNew,
					correspondingLocation, matcher);
			// System.out.println("debug: control dep node of mending " + otherControlDom);
			List<Integer> matchPositions = getSlicer4JMappedNode(otherControlDom, OtherSlicer4JMapping,
					otherSlicer4JBytecodeMapping);
			if (matchPositions != null) {
				if (!other_visited.contains(otherControlDom)) {
					other_visited.add(otherControlDom);
					other_workList.add(otherControlDom);
					List<Integer> positions = getSlicer4JMappedNode(step, Slicer4JMapping, Slicer4JBytecodeMapping);
					if (positions != null && positions.size() != 0) {
						String result = String.valueOf(positions.get(0));// the first byte code trace order in slicer4J
						other_reasons.put(otherControlDom, "control mending node which stops node ~ to node " + result);
						// System.out.println("debug: list: " + other_workList);
					}
				}
			}
		}
		////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////
		// get deps of node step
//		if (step.toString().equals(
//				"order 2262~com.fasterxml.jackson.core.json.ReaderBasedJsonParser: line 2861 in _reportInvalidToken(...)")) {
//			return;
//		}
		HashMap<Pair<TraceNode, String>, String> deps = new HashMap<>();// map the <dep node, the var> and data/control
		if (slicer4J) {
			if (isNew) {
				deps = getSlicer4JDirectDependencies(cashDeps, Slicer4JMapping, Slicer4JBytecodeMapping, step, isNew,
						new_dcfg, new_slicer);
			} else {
				deps = getSlicer4JDirectDependencies(cashDeps, Slicer4JMapping, Slicer4JBytecodeMapping, step, isNew,
						old_dcfg, old_slicer);
			}
		}
		////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////
		for (Pair<TraceNode, String> d : deps.keySet()) {
			// System.out.println("debug: dep node: " + d.first());
			StepChangeType chgType = typeChecker.getType(d.first(), isNew, pairList, matcher);
			if (chgType.getType() != StepChangeType.IDT) {
				if (deps.get(d) == "data") {
					List<Pair<TraceNode, String>> dataDeps = data_map.get(step);
					if (dataDeps == null) {
						dataDeps = new ArrayList<>();
					}
					dataDeps.add(d);
					// System.out.println("update the data list of step " + step + " with "+
					// dataDeps);
					data_map.put(step, dataDeps);
				} else if (deps.get(d) == "control") {
					List<TraceNode> ctlDeps = ctl_map.get(step);
					if (ctlDeps == null) {
						ctlDeps = new ArrayList<>();
					}
					ctlDeps.add(d.first());
					// System.out.println("update the control list of step " + step + " with "+
					// ctlDeps);
					ctl_map.put(step, ctlDeps);
				}
				List<Integer> matchPositions = getSlicer4JMappedNode(d.first(), Slicer4JMapping,
						Slicer4JBytecodeMapping);
				if (matchPositions != null) {
					if (!visited.contains(d.first())) {
						workList.add(d.first());
						visited.add(d.first());
						List<Integer> positions = getSlicer4JMappedNode(step, Slicer4JMapping, Slicer4JBytecodeMapping);
						if (positions != null) {
							String result = String.valueOf(positions.get(0));// the first byte code trace order in
																				// slicer4J
							if (deps.get(d) == "data") {
								reasons.put(d.first(), "node data effect on node " + result);
							} else if (deps.get(d) == "control") {
								reasons.put(d.first(), "node control effect on node " + result);
							}
						}
					}
				}
			}
	
			else { 
//			  System.out.println("debug: dep is identical"); 
			  //in case that d is identical in both traces but the other trace def-use is something else => int x =2; y=x;=> int x=2; x=1; y=x; 
			  if(changeType.getType()==StepChangeType.DAT)
			  {	
			       TraceNode corresponding = changeType.getMatchingStep();//corresponding node of step in the other trace 
			         //System.out.println("corresponding node:" + corresponding); 
			       if(corresponding!=null) 
			       { 
//			    	   System.out.println("corresponding " + corresponding.getOrder() + corresponding.toString());
			    	   HashMap<Pair<TraceNode, String>, String> corresponding_deps = new HashMap<>();//the deps of corresponding nodes 			       

			    		   if(isNew) { 
//			    			   if(bugID.contentEquals("1"))
//			    			      corresponding_deps = getSlicer4JDirectDependencies(OthercashDeps, Slicer4JMapping, Slicer4JBytecodeMapping, corresponding, !isNew, old_dcfg, old_slicer); 
//			    			   else
			    				  corresponding_deps = getSlicer4JDirectDependencies(OthercashDeps, OtherSlicer4JMapping, otherSlicer4JBytecodeMapping, corresponding, !isNew, old_dcfg, old_slicer);			    			   
			    		   }else {
			    				 corresponding_deps = getSlicer4JDirectDependencies(OthercashDeps, OtherSlicer4JMapping, otherSlicer4JBytecodeMapping, corresponding, !isNew, new_dcfg, new_slicer);			    			   
			    		   }
			    	   boolean found = false; 
			    	   for(Pair<TraceNode, String> dd: corresponding_deps.keySet()){
			    		   StepChangeType tepmType = typeChecker.getType(dd.first(), !isNew, pairList, matcher); 
			    		   TraceNode correspondingDeps = tepmType.getMatchingStep();
			    		   if(d.first().equals(correspondingDeps))//already in the slice 
			    			   found = true; 
			    	   }
			    	   if(!found){ 
//			    		   System.out.println("different def-use");
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
			    		   List<Integer> matchPositions = getSlicer4JMappedNode(d.first(),Slicer4JMapping,Slicer4JBytecodeMapping);
			    		   if(matchPositions!=null) {
//			    			   System.out.println("to be added");
			    			   if(!visited.contains(d.first())) { 
//			    				   System.out.println("Not in the list");
			    				   List<Integer> positions = getSlicer4JMappedNode(corresponding,OtherSlicer4JMapping, otherSlicer4JBytecodeMapping); 
			    				   String result = String.valueOf(positions.get(0));//the first byte code trace order in slicer4J
			    				   List<Integer> StepPositions = getSlicer4JMappedNode(step,Slicer4JMapping,Slicer4JBytecodeMapping); 
			    				   String StepResult = String.valueOf(StepPositions.get(0));//the first byte code trace order in slicer4J 
			    				   if(deps.get(d)=="data") {
			    					   reasons.put(d.first(), "identical dep for node " +StepResult + " but corresponds to no matching dep of node " + result); 
			    				   }else if(deps.get(d)=="control") {
			    					   reasons.put(d.first(), "identical dep for node " +StepResult + " but corresponds to no matching dep of node " + result); 
			    				   }
//			    				   System.out.println("added added");
			    				   visited.add(d.first()); //just add to visited not the worklist 
			                   } 
			    		   }
			          }
			      } 
			   }
			}
			  if(d.first().isException())
			  { 
				  TraceNode nextStep = d.first().getStepInPrevious(); 
				  //System.out.println("debug: prev step " + nextStep); 
				  List<TraceNode> ctlDeps = ctl_map.get(step); 
				  if(ctlDeps==null) {
					  ctlDeps = new ArrayList<>(); 
				   } 
				  ctlDeps.add(nextStep); 
				  ctl_map.put(step, ctlDeps); 
				  List<Integer> matchPositions = getSlicer4JMappedNode(nextStep,Slicer4JMapping,Slicer4JBytecodeMapping);
				  if(matchPositions!=null) { 
					  if(!visited.contains(nextStep)) {
						  workList.add(nextStep); 
						  visited.add(nextStep); 
						  List<Integer> StepPositions = getSlicer4JMappedNode(step,Slicer4JMapping,Slicer4JBytecodeMapping); 
						  String StepResult = String.valueOf(StepPositions.get(0));//the first byte code trace order in slicer4J 
						  reasons.put(nextStep, "exception node controling " + StepResult); 
						} 
				  } 
			  } 
			 
		}
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////	
	private HashMap<Pair<TraceNode, String>, String> getSlicer4JDirectDependencies(
			HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> cashDeps,
			BiMap<TraceNode, String> Slicer4JNodeMapping, HashMap<String, List<String>> Slicer4JBytecodeMapping,
			TraceNode step, boolean isNew, DynamicControlFlowGraph dcfg, Slicer slicer) {
		// 1. given a traceNode step => find the equivalent file:lineNo
		// 2. runJslicer
		// 3. Read slice-dependencies
		// 4. Finds the corresponding traceNode
		// then if it is control add it as deps.put(dep,"control"); if it is data add it
		// as deps.put(dep,"data");

		if (cashDeps.containsKey(step)) {
//			System.out.println("already cached: " + step);
//			System.out.println("cached: " + cashDeps.get(step));
			return cashDeps.get(step);
		}
//		System.out.println("Not cached");
		HashMap<Pair<TraceNode, String>, String> deps = new HashMap<>();

		////////////////// add dependency nodes//////////////////
		List<Integer> positions = getSlicer4JMappedNode(step, Slicer4JNodeMapping, Slicer4JBytecodeMapping);
		if (positions != null) {

			//// Maybe just got with the last position

			for (Integer tracePositionToSliceFrom : positions) {
				// System.out.println(tracePositionToSliceFrom);
				StatementInstance stmt = dcfg.mapNoUnits(tracePositionToSliceFrom);
				// System.out.println(stmt);
				try {
					DynamicSlice dynamicSlice = slicer.directStatementDependency(stmt, false, false);
					Map<StatementInstance, String> sliceDeps = dynamicSlice.getSliceDependenciesAsMap();
					for (StatementInstance statement : sliceDeps.keySet()) {
//						System.out.println("##############");
//						System.out.println("The dep statement is:" + statement);
//						System.out.println("The dep type statement is:" + sliceDeps.get(statement));
						TraceNode key = getTraceNodeMapping(statement, Slicer4JNodeMapping, Slicer4JBytecodeMapping);
//						System.out.println("The dep node is:" + key);
						if (key != null && !key.toString().equals(step.toString())) {
							if (sliceDeps.get(statement).split(",")[0].contains("data")) {
								String depVar = sliceDeps.get(statement).split("varaible:")[1].split(",")[0];
								Pair<TraceNode, String> pair = new Pair(key, depVar);
								deps.put(pair, "data");
							} else if (sliceDeps.get(statement).split(",")[0].contains("control")) {
								Pair<TraceNode, String> pair = new Pair(key, "null");
								deps.put(pair, "control");
							}
						}
					}
				} catch (StackOverflowError e) {
					System.err.println("oche!");
				}

			}
		}
		cashDeps.put(step, deps);
		return deps;
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////	
	public static TraceNode getTraceNodeMapping(StatementInstance statement, BiMap<TraceNode, String> slicer4jNodeMapping,
			HashMap<String, List<String>> slicer4jBytecodeMapping) {
		String id = statement.toString().split(", ")[0];
		for (String slicerNode : slicer4jBytecodeMapping.keySet()) {
			for (String bytecode : slicer4jBytecodeMapping.get(slicerNode)) {
				String byteID = bytecode.split(", ")[0];
				if (id.trim().equals(byteID.trim())) {
					return slicer4jNodeMapping.inverse().get(slicerNode);
				}
			}
		}
		return null;
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	public static List<Integer> getSlicer4JMappedNode(TraceNode step, BiMap<TraceNode, String> slicer4jNodeMapping,
			HashMap<String, List<String>> slicer4jBytecodeMapping) {
		// System.out.println(slicer4jNodeMapping);
		// System.out.println("The step is:" + step);
		String Slicer4JStmt = slicer4jNodeMapping.get(step);// order 2, int foo
		// System.out.println("The statement is:" + Slicer4JStmt);
		if (slicer4jBytecodeMapping.containsKey(Slicer4JStmt)) {
			List<String> bytecodes = slicer4jBytecodeMapping.get(Slicer4JStmt);
			List<Integer> integers = new ArrayList<>();
			for (String bytecode : bytecodes) {
				Integer id = Integer.valueOf(bytecode.split(", ")[0]);
				integers.add(id);
			}
			return integers;
		}
		return null;
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

	public String getSourceCode(TraceNode traceNode, boolean isOnNew, DiffMatcher matcher,
			BiMap<TraceNode, String> Slicer4JNodeMapping, HashMap<String, List<String>> Slicer4JBytecodeMapping) {

		int lineNo = traceNode.getLineNumber();
		String source = null;
		BreakPoint breakPoint = traceNode.getBreakPoint();
		String Path = breakPoint.getFullJavaFilePath();
		File file = new File(Path);
//		if(!file.exists()){
//			path = path.replace(matcher.getSourceFolderName(), matcher.getTestFolderName());
//			file = new File(path);
//		}

		if (file.exists()) {
			InputStream stdin;
			try {
				stdin = new FileInputStream(file);
				InputStreamReader isr = new InputStreamReader(stdin);
				BufferedReader br = new BufferedReader(isr);

				String line = null;
				int index = 1;
				while ((line = br.readLine()) != null) {
					if (index == lineNo) {
						source = line.trim();
						source = source.replace("\"", "'");
					}
					index++;
				}
			} catch (FileNotFoundException e1) {
				e1.printStackTrace();
			} catch (IOException e1) {
				e1.printStackTrace();
			}
		}
		/*
		 * String result = String.valueOf(node.getOrder()); result =
		 * node.getClassCanonicalName(); String methodName = node.getMethodName();
		 * if(methodName != null){ result = result + ":" + methodName; } result = result
		 * + ": LineNo@" + node.getLineNumber() + "--->"; result = result + source;
		 * return result;
		 */
//		List<Integer> positions = getSlicer4JMappedNode(traceNode, Slicer4JNodeMapping, Slicer4JBytecodeMapping);
//		String result = String.valueOf(positions.get(0));// the first byte code trace order in slicer4J
//		result = result + "#" + traceNode.getClassCanonicalName();
//		String methodName = traceNode.getMethodName();
//		if (methodName != null) {
//			result = result + "#" + methodName;
//		}
//		result = result + "#LineNo@" + traceNode.getLineNumber() + " ----> ";
//		result = result + source;
		String result = "Line " + traceNode.getLineNumber() + " ";
		String methodName = traceNode.getMethodName();
		if (methodName != null) {
			result = result + traceNode.getClassCanonicalName() + ":" + methodName + " ---> " + source;
		}else {
			result = result + traceNode.getClassCanonicalName() + " ---> " + source;
		}
		return result;
	}
	
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void printDualSliceResults(List<TraceNode> visited, boolean isNew, String proPath, DiffMatcher matcher, BiMap<TraceNode, String> oldSlicer4J, HashMap<String, List<String>> oldSlicer4JBytecodeMapping) {
		PrintWriter writer;
		try {
			String onNew = isNew ? "new" : "old";
			writer = new PrintWriter(proPath + "/results/" + onNew + "/DualSlice.txt", "UTF-8");
			for (int i = visited.size() - 1; i >= 0; i--) {

				writer.println(getSourceCode(visited.get(i),isNew,matcher, oldSlicer4J, oldSlicer4JBytecodeMapping));
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
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////

	private void InPreSSAbstractionCircleOnlySameFunctionsCommonTrianlges(TestCase tc, String proPath, List<TraceNode> old_visited,
			List<TraceNode> new_visited, StepChangeTypeChecker typeChecker,
			PairList pairList, DiffMatcher matcher, HashMap<TraceNode, List<Pair<TraceNode, String>>> old_data_map,
			HashMap<TraceNode, List<TraceNode>> old_ctl_map,
			HashMap<TraceNode, List<Pair<TraceNode, String>>> new_data_map,
			HashMap<TraceNode, List<TraceNode>> new_ctl_map, BiMap<TraceNode, String> oldSlicer4J,
			BiMap<TraceNode, String> newSlicer4J, HashMap<String, List<String>> oldSlicer4JBytecodeMapping,
			HashMap<String, List<String>> newSlicer4JBytecodeMapping, DynamicControlFlowGraph new_dcfg,
			Slicer new_slicer, DynamicControlFlowGraph old_dcfg, Slicer old_slicer, List<TraceNode> old_kept,
			List<TraceNode> new_kept, HashMap<Integer, List<TraceNode>> oldDataBlockNodes,
			HashMap<Integer, List<TraceNode>> newDataBlockNodes, HashMap<Integer, List<TraceNode>> oldCtlBlockNodes,
			HashMap<Integer, List<TraceNode>> newCtlBlockNodes, List<TraceNode> old_retained,
			List<TraceNode> new_retained, List<String> old_kept_sourceCodeLevel, List<String> new_kept_sourceCodeLevel) {
		/////////////////////////////////////////////////////////////
//		Collections.sort(old_visited, new TraceNodePairOrderComparator(oldSlicer4J, oldSlicer4JBytecodeMapping));
//		Collections.sort(new_visited, new TraceNodePairOrderComparator(newSlicer4J, newSlicer4JBytecodeMapping));
//		System.out.println(old_visited.size());
//		System.out.println(new_visited.size());
		///////////////////// extract blocks for old/////////////////////
		HashMap<TraceNode, Integer> oldBlocks = new HashMap<>();
		Integer BlockID = 0;
		boolean current_data_flag = false;
		boolean current_ctl_flag = false;
		boolean firstTime = true;
		boolean isDataBlock = false;
		boolean isCTLBlock = false;
		for (int i = old_visited.size() - 1; i >= 0; i--) {
			TraceNode step = old_visited.get(i);
			//System.out.println("step on old is: " + step);
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL) || (isATestStatement(tc, step) && isLastStatement(tc, step,old_visited))) { // separate the blocks
				isDataBlock = false;
				isCTLBlock = false;
				if (current_data_flag) {// coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
				}
				if (current_ctl_flag) {// coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
				}
			} else if (changeType.getType() == StepChangeType.CTL) {
				isDataBlock = false;
				isCTLBlock = true;
				if (!current_ctl_flag) {// coming from dat or other blocks
					BlockID = BlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
				}
				oldBlocks.put(step, BlockID);//added now
			} else if (changeType.getType() == StepChangeType.DAT) {
				isDataBlock = true;
				isCTLBlock = false;
				if (!current_data_flag) {// coming from ctl or other blocks
					BlockID = BlockID + 1;
					current_data_flag = true;
					current_ctl_flag = false;
				}
				oldBlocks.put(step, BlockID);//added now
			}
			//added now the following
//			if (firstTime) {
//				firstTime = false;
//				BlockID = BlockID + 1;
//			}
//			oldBlocks.put(step, BlockID);
		}
//		System.out.println("old blocks " + oldBlocks);	
		///////////////////// extract blocks for new/////////////////////
		HashMap<TraceNode, Integer> newBlocks = new HashMap<>();
		BlockID = 0;
		current_data_flag = false;
		current_ctl_flag = false;
		firstTime = true;
		isDataBlock = false;
		TraceNode previousData = null;
		for (int i = new_visited.size() - 1; i >= 0; i--) {
			TraceNode step = new_visited.get(i);
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL) || (isATestStatement(tc, step) && isLastStatement(tc, step,new_visited))) { // separate the blocks
				isDataBlock = false;
				isCTLBlock = false;
				if (current_data_flag) {// coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
				}
				if (current_ctl_flag) {// coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
				}
			} else if (changeType.getType() == StepChangeType.CTL) {
				isDataBlock = false;
				isCTLBlock = true;
				if (!current_ctl_flag) {// coming from dat or other blocks
					BlockID = BlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
				}
				newBlocks.put(step, BlockID);
			} else if (changeType.getType() == StepChangeType.DAT) {
				isDataBlock = true;
				isCTLBlock = false;
				if (previousData != null) {
					StepChangeType previousChangeType = typeChecker.getType(previousData, true, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep = previousChangeType.getMatchingStep();
					if (oldBlocks.get(matchedStep) != oldBlocks.get(previousMatchedStep)) {//separate if it is separated in old 		
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
					} else {
						if (!current_data_flag) {// coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = true;
							current_ctl_flag = false;
						}
					}
				} else {
					if (!current_data_flag) {// coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
					}
				}
				previousData = step;
				newBlocks.put(step, BlockID);	

			}
//			if (firstTime) {
//				BlockID = BlockID + 1;
//				firstTime = false;
//			}
//			newBlocks.put(step, BlockID);
			if (isDataBlock) {
				if (newDataBlockNodes.containsKey(BlockID)) {
					List<TraceNode> nodes = newDataBlockNodes.get(BlockID);
					if (nodes == null)
						nodes = new ArrayList<>();
					nodes.add(step);
					newDataBlockNodes.put(BlockID, nodes);
				} else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					newDataBlockNodes.put(BlockID, nodes);
				}
			}
			if (isCTLBlock) {
				if (newCtlBlockNodes.containsKey(BlockID)) {
					List<TraceNode> nodes = newCtlBlockNodes.get(BlockID);
					if (nodes == null)
						nodes = new ArrayList<>();
					nodes.add(step);
					newCtlBlockNodes.put(BlockID, nodes);
				} else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					newCtlBlockNodes.put(BlockID, nodes);
				}
			}
		}
//		System.out.println("new blocks " + newBlocks);
		///////////////////// extract blocks for old/////////////////////
		oldBlocks = new HashMap<>();
		BlockID = 0;
		current_data_flag = false;
		current_ctl_flag = false;
		firstTime = true;
		isDataBlock = false;
		previousData = null;
		for (int i = old_visited.size() - 1; i >= 0; i--) {
			TraceNode step = old_visited.get(i);
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL) || (isATestStatement(tc, step) && isLastStatement(tc, step,old_visited))) { // separate the blocks
				isDataBlock = false;
				isCTLBlock = false;
				if (current_data_flag) {// coming from a data block
//					BlockID = BlockID + 1;
					current_data_flag = false;
				}
				if (current_ctl_flag) {// coming from a ctl block
//					BlockID = BlockID + 1;
					current_ctl_flag = false;
				}
			} else if (changeType.getType() == StepChangeType.CTL) {
				isDataBlock = false;
				isCTLBlock = true;
				if (!current_ctl_flag) {// coming from dat or other blocks
					BlockID = BlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
				}
				oldBlocks.put(step, BlockID);
			} else if (changeType.getType() == StepChangeType.DAT) {
				isDataBlock = true;
				isCTLBlock = false;
				if (previousData != null) {
					StepChangeType previousChangeType = typeChecker.getType(previousData, false, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep = previousChangeType.getMatchingStep();
					if (newBlocks.get(matchedStep) != newBlocks.get(previousMatchedStep)) {// separate them
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
					} else {
						if (!current_data_flag) {// coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = true;
							current_ctl_flag = false;
						}
					}
				} else {
					if (!current_data_flag) {// coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
					}
				}
				previousData = step;
				oldBlocks.put(step, BlockID);

			}
//			if (firstTime) {
//				BlockID = BlockID + 1;
//				firstTime = false;
//			}
//			oldBlocks.put(step, BlockID);
			if (isDataBlock) {
				if (oldDataBlockNodes.containsKey(BlockID)) {
					List<TraceNode> nodes = oldDataBlockNodes.get(BlockID);
					if (nodes == null)
						nodes = new ArrayList<>();
					nodes.add(step);
					oldDataBlockNodes.put(BlockID, nodes);
				} else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					oldDataBlockNodes.put(BlockID, nodes);
				}
			}
			if (isCTLBlock) {
				if (oldCtlBlockNodes.containsKey(BlockID)) {
					List<TraceNode> nodes = oldCtlBlockNodes.get(BlockID);
					if (nodes == null)
						nodes = new ArrayList<>();
					nodes.add(step);
					oldCtlBlockNodes.put(BlockID, nodes);
				} else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					oldCtlBlockNodes.put(BlockID, nodes);
				}
			}
		}
//		System.out.println("#################after paralizing#################");
//		System.out.println("The data block size in old " + oldDataBlockNodes.keySet().size());
//		System.out.println("The data block size in new " + newDataBlockNodes.keySet().size());
//		System.out.println("The ctl block size in old " + oldCtlBlockNodes.keySet().size());
//		System.out.println("The ctl block size in new " + newCtlBlockNodes.keySet().size());

		////////////////////////////////////////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////////////////////////////
		///////////////////// abstraction////////////////////////////////////////////////////////////////		

		try {
			// should also the corresponding kept node from the other trace be add?
						
//			Collections.sort(old_visited, new TraceNodePairOrderComparator(oldSlicer4J, oldSlicer4JBytecodeMapping));
//			Collections.sort(new_visited, new TraceNodePairOrderComparator(newSlicer4J, newSlicer4JBytecodeMapping));

			List<TraceNode> new_dat_kept = new ArrayList<>();
			List<TraceNode> old_dat_kept = new ArrayList<>();

			HashMap<TraceNode, Integer> old_data_node_function = new HashMap<>();
			HashMap<TraceNode, Integer> new_data_node_function = new HashMap<>();
			HashMap<TraceNode, Integer> old_ctl_node_function = new HashMap<>();
			HashMap<TraceNode, Integer> new_ctl_node_function = new HashMap<>();
			Integer index = 0;
			//////////////////////////////////// First Define what to
			//////////////////////////////////// keep////////////////////////////////////////////////
			for (int i = old_visited.size() - 1; i >= 0; i--) {
				TraceNode step = old_visited.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
				String Type;
//				if (changeType.getType() == StepChangeType.DAT && !isATestStatement(tc, step)) {
				if (changeType.getType() == StepChangeType.DAT && !isLastStatement(tc, step,old_visited)) {
					old_data_node_function.put(step, index);
					TraceNode matchedStep = changeType.getMatchingStep();
					new_data_node_function.put(matchedStep, index);
					index = index + 1;
					if (old_kept.contains(step)) {// should be added but abstracted
						if (!new_dat_kept.contains(matchedStep))
							new_dat_kept.add(matchedStep);
					}
				}
				//else if (changeType.getType() == StepChangeType.CTL && !isATestStatement(tc, step)) {
				else if (changeType.getType() == StepChangeType.CTL && !isLastStatement(tc, step,old_visited)) {
					old_ctl_node_function.put(step, index);
					index = index + 1;
				} else {
					if (!old_retained.contains(step))
						old_retained.add(step);
					if (!old_kept.contains(step)) {
						old_kept.add(step);
						if (!old_kept_sourceCodeLevel.contains(getSourceCode(step,false,matcher, oldSlicer4J, oldSlicer4JBytecodeMapping)))
							old_kept_sourceCodeLevel.add(getSourceCode(step,false,matcher, oldSlicer4J, oldSlicer4JBytecodeMapping));
					}
				}
				List<Pair<TraceNode, String>> data_deps = old_data_map.get(step);
				if (data_deps != null)
					for (Pair<TraceNode, String> pair : data_deps)
						if (old_visited.contains(pair.first()))
							if (oldBlocks.get(pair.first()) != oldBlocks.get(step))// keep the dep
								if (!old_kept.contains(pair.first())) {
									old_kept.add(pair.first());
									if (!old_kept_sourceCodeLevel.contains(getSourceCode(pair.first(),false,matcher, oldSlicer4J, oldSlicer4JBytecodeMapping)))
										old_kept_sourceCodeLevel.add(getSourceCode(pair.first(),false,matcher, oldSlicer4J, oldSlicer4JBytecodeMapping));
								}

//				List<TraceNode> ctl_deps = old_ctl_map.get(step);
//				if(ctl_deps!=null) 
//					for(TraceNode node:ctl_deps) 
//						if(old_visited.contains(node))
//							if(oldBlocks.get(node)!=oldBlocks.get(step))//keep the dep
//								if(!old_kept.contains(node))
//									old_kept.add(node);		
			}
			///////////////////////////////////// First Define what to
			///////////////////////////////////// keep///////////////////////////////////////////////
			for (int i = new_visited.size() - 1; i >= 0; i--) {
				TraceNode step = new_visited.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
				String Type;
//				if (changeType.getType() == StepChangeType.DAT && !isATestStatement(tc, step)) {
				if (changeType.getType() == StepChangeType.DAT && !isLastStatement(tc, step, new_visited)) {
					if (!new_data_node_function.keySet().contains(step)) {
						new_data_node_function.put(step, index);
						TraceNode matchedStep = changeType.getMatchingStep();
						old_data_node_function.put(matchedStep, index);
						index = index + 1;
					}
					if (new_kept.contains(step)) {// should be added but abstracted
						TraceNode matchedStep = changeType.getMatchingStep();
						if (!old_dat_kept.contains(matchedStep))
							old_dat_kept.add(matchedStep);
					}
				}
//				 else if (changeType.getType() == StepChangeType.CTL && !isATestStatement(tc, step)) {
				else if (changeType.getType() == StepChangeType.CTL && !isLastStatement(tc, step, new_visited)) {
					new_ctl_node_function.put(step, index);
					index = index + 1;
				} else {
					if (!new_retained.contains(step))
						new_retained.add(step);
					if (!new_kept.contains(step)) {
						new_kept.add(step);
						if (!new_kept_sourceCodeLevel.contains(getSourceCode(step,true,matcher, newSlicer4J, newSlicer4JBytecodeMapping)))
							new_kept_sourceCodeLevel.add(getSourceCode(step,true,matcher, newSlicer4J, newSlicer4JBytecodeMapping));
					}
				}
				List<Pair<TraceNode, String>> data_deps = new_data_map.get(step);
				if (data_deps != null)
					for (Pair<TraceNode, String> pair : data_deps)
						if (new_visited.contains(pair.first()))
							if (newBlocks.get(pair.first()) != newBlocks.get(step))// keep the dep
								if (!new_kept.contains(pair.first())) {
									new_kept.add(pair.first());
									if (!new_kept_sourceCodeLevel.contains(getSourceCode(pair.first(),true,matcher, newSlicer4J, newSlicer4JBytecodeMapping)))
										new_kept_sourceCodeLevel.add(getSourceCode(pair.first(),true,matcher, newSlicer4J, newSlicer4JBytecodeMapping));
								}

//				List<TraceNode> ctl_deps = new_ctl_map.get(step);
//				if(ctl_deps!=null) 
//					for(TraceNode node:ctl_deps) 
//						if(new_visited.contains(node))
//							if(newBlocks.get(node)!=newBlocks.get(step))//keep the dep
//								if(!new_kept.contains(node))
//									new_kept.add(node);		
			}
			/////////////////////////////////////////////////////////////
			//Add test statements becasue they are in the dual slice//////
			for(TraceNode n: old_dat_kept) {
				List<Integer> positions = getSlicer4JMappedNode(n,oldSlicer4J,oldSlicer4JBytecodeMapping);
				if (positions !=null && positions.size()!=0) {
					if(!old_kept.contains(n)) {
						old_kept.add(n);
						if (!old_kept_sourceCodeLevel.contains(getSourceCode(n,false,matcher, oldSlicer4J, oldSlicer4JBytecodeMapping)))
							old_kept_sourceCodeLevel.add(getSourceCode(n,false,matcher, oldSlicer4J, oldSlicer4JBytecodeMapping));					
					}
				}
			}
			for(TraceNode n: new_dat_kept) {
				List<Integer> positions = getSlicer4JMappedNode(n,newSlicer4J,newSlicer4JBytecodeMapping);
				if (positions !=null && positions.size()!=0) {
					if(!new_kept.contains(n)) {
						new_kept.add(n);
						if (!new_kept_sourceCodeLevel.contains(getSourceCode(n,true,matcher, newSlicer4J, newSlicer4JBytecodeMapping)))
							new_kept_sourceCodeLevel.add(getSourceCode(n,true,matcher, newSlicer4J, newSlicer4JBytecodeMapping));
					
					}
				}
			}
			if (old_kept.size()==0) {				
			    old_kept.add(old_visited.get(old_visited.size()-1));
			    if (!old_kept_sourceCodeLevel.contains(getSourceCode(old_visited.get(old_visited.size()-1),false,matcher, oldSlicer4J, oldSlicer4JBytecodeMapping)))
					old_kept_sourceCodeLevel.add(getSourceCode(old_visited.get(old_visited.size()-1),false,matcher, oldSlicer4J, oldSlicer4JBytecodeMapping));					
			
//			    if(!old_retained.contains(old_visited.get(old_visited.size()-1)))
//			    	old_retained.add(old_visited.get(old_visited.size()-1));
			}
			if (new_kept.size()==0) {		
			    new_kept.add(new_visited.get(new_visited.size()-1));
				if (!new_kept_sourceCodeLevel.contains(getSourceCode(new_visited.get(new_visited.size()-1),true,matcher, newSlicer4J, newSlicer4JBytecodeMapping)))
					new_kept_sourceCodeLevel.add(getSourceCode(new_visited.get(new_visited.size()-1),true,matcher, newSlicer4J, newSlicer4JBytecodeMapping));
//			    if(!new_retained.contains(new_visited.get(new_visited.size()-1)))
//			    	new_retained.add(new_visited.get(new_visited.size()-1));
			}
//			Collections.sort(old_visited, new TraceNodePairOrderComparator(oldSlicer4J, oldSlicer4JBytecodeMapping));
//			Collections.sort(new_visited, new TraceNodePairOrderComparator(newSlicer4J, newSlicer4JBytecodeMapping));
			Collections.sort(old_kept, new TraceNodePairOrderComparator(oldSlicer4J, oldSlicer4JBytecodeMapping));
			Collections.sort(new_kept, new TraceNodePairOrderComparator(newSlicer4J, newSlicer4JBytecodeMapping));
			//////////////////////// add nodes of old with abstraction/////////////////////
			PrintWriter fileWriter = new PrintWriter(proPath + "/results/old/inPreSS.txt", "UTF-8");
//			PrintWriter writer = new PrintWriter(proPath + "/results/inPreSSExplaination.gv", "UTF-8");
//			writer.println("digraph dualGraph {");
//			writer.println("rankdir = BT;");
//			writer.println("splines=ortho;");
//			
//			writer.println("subgraph cluster0 {");
//			writer.println("color=black;");
//			writer.println("label = \"old slice\";");
			for (int i = old_kept.size() - 1; i >= 0; i--) {
				TraceNode step = old_kept.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
//				String Type;
				if (changeType.getType() == StepChangeType.DAT && !isATestStatement(tc, step)) {
					
//						Type = "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";
						List<VarValue> written = step.getWrittenVariables();
						List<ValueBox> writtenSoot = new ArrayList<>();
						List<Integer> positions = getSlicer4JMappedNode(step, oldSlicer4J, oldSlicer4JBytecodeMapping);
						if (positions != null) {
							for (Integer tracePositionToSliceFrom : positions) {
								StatementInstance stmt = old_dcfg.mapNoUnits(tracePositionToSliceFrom);
								writtenSoot.addAll(stmt.getUnit().getDefBoxes());
							}
						}
						List<String> vars = new ArrayList<>();
						List<TraceNode> visited = new ArrayList<>();
						try {
							visited.add(step);
							List<Pair<TraceNode, String>> temp = addVariable(visited, step, vars, old_data_map,
									oldBlocks, old_kept, old_dat_kept);
						} catch (StackOverflowError e) {
							System.err.println("oche!");
						}
						String abstraction = "";
						if (written != null && written.size() != 0) { // is an assignment
							boolean found = false;							
							for (int kk=0; kk<written.size();kk++) {
								abstraction = written.get(kk).getVarName();
								if ((!abstraction.isEmpty()) && abstraction!=null) {							
									abstraction = abstraction + "=Func" + old_data_node_function.get(step) + "(";
									for (int j = 0; j < vars.size(); j++) {
										if (j != vars.size() - 1)
											abstraction = abstraction + vars.get(j) + ", ";
										else
											abstraction = abstraction + vars.get(j);
									}
									abstraction = abstraction + ");";
									found = true;
									break;
								}
							}
							if(!found) {
								abstraction = "Func" + old_data_node_function.get(step) + "(";
								for (int j = 0; j < vars.size(); j++) {
									if (j != vars.size() - 1)
										abstraction = abstraction + vars.get(j) + ", ";
									else
										abstraction = abstraction + vars.get(j);
								}
								abstraction = abstraction + ");";
							}
						} else if (writtenSoot.size() != 0) {
							boolean found = false;
							for (int kk=0; kk<writtenSoot.size();kk++) {							
								abstraction = writtenSoot.get(kk).getValue().toString();
								if ((!abstraction.isEmpty()) && abstraction!=null) {
									abstraction = abstraction + "=Func" + old_data_node_function.get(step) + "(";
									for (int j = 0; j < vars.size(); j++) {
										if (j != vars.size() - 1)
											abstraction = abstraction + vars.get(j) + ", ";
										else
											abstraction = abstraction + vars.get(j);
									}
									abstraction = abstraction + ");";
									found = true;
									break;
								}
							}
							if(!found) {
								abstraction = "Func" + old_data_node_function.get(step) + "(";
								for (int j = 0; j < vars.size(); j++) {
									if (j != vars.size() - 1)
										abstraction = abstraction + vars.get(j) + ", ";
									else
										abstraction = abstraction + vars.get(j);
								}
								abstraction = abstraction + ");";
							}
						} else {//not an assignment
							abstraction = abstraction + "Func" + old_data_node_function.get(step) + "(";
							for (int j = 0; j < vars.size(); j++) {
								if (j != vars.size() - 1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							// abstraction = getSourceCode(step, false, matcher, oldSlicer4J,oldSlicer4JBytecodeMapping);
						}
//						String fixNode = step.toString();
//						writer.println("\"OldNode: " + fixNode + "\"" + "[" + Type + " label=\"" + abstraction + "\"];");
						fileWriter.println(abstraction);

					
				} else if (changeType.getType() == StepChangeType.CTL && !isATestStatement(tc, step)) {
					//if (old_kept.contains(step)) {// should be added but abstracted
//						Type = "color=blue fillcolor=lightskyblue1 shape=box style=filled fontsize=10";
						List<VarValue> written = step.getWrittenVariables();
						List<ValueBox> writtenSoot = new ArrayList<>();
						List<Integer> positions = getSlicer4JMappedNode(step, oldSlicer4J, oldSlicer4JBytecodeMapping);
						if (positions != null) {
							for (Integer tracePositionToSliceFrom : positions) {
								StatementInstance stmt = old_dcfg.mapNoUnits(tracePositionToSliceFrom);
								writtenSoot.addAll(stmt.getUnit().getDefBoxes());
							}
						}
						List<String> vars = new ArrayList<>();
						List<TraceNode> visited = new ArrayList<>();
						try {
							visited.add(step);
							List<Pair<TraceNode, String>> temp = addVariable(visited, step, vars, old_data_map,
									oldBlocks, old_kept, old_dat_kept);
						} catch (StackOverflowError e) {
							System.err.println("oche!");
						}
						String abstraction = "";
						if (written != null && written.size() != 0) { // is an assignment
							boolean found = false;
							for (int kk=0; kk<written.size();kk++) {
								abstraction = written.get(kk).getVarName();
								if ((!abstraction.isEmpty()) && abstraction!=null) {
									abstraction = abstraction + "=Func" + old_ctl_node_function.get(step) + "(";
									for (int j = 0; j < vars.size(); j++) {
										if (j != vars.size() - 1)
											abstraction = abstraction + vars.get(j) + ", ";
										else
											abstraction = abstraction + vars.get(j);
									}
									abstraction = abstraction + ");";	
									found = true;
									break;
								}						
							}
							if(!found) {
								abstraction = "Func" + old_ctl_node_function.get(step) + "(";
								for (int j = 0; j < vars.size(); j++) {
									if (j != vars.size() - 1)
										abstraction = abstraction + vars.get(j) + ", ";
									else
										abstraction = abstraction + vars.get(j);
								}
								abstraction = abstraction + ");";
							}
						} else if (writtenSoot.size() != 0) {
							boolean found = false;
							for (int kk=0; kk<writtenSoot.size();kk++) {
								abstraction = writtenSoot.get(kk).getValue().toString();
								if ((!abstraction.isEmpty()) && abstraction!=null) {
									abstraction = abstraction + "=Func" + old_ctl_node_function.get(step) + "(";
									for (int j = 0; j < vars.size(); j++) {
										if (j != vars.size() - 1)
											abstraction = abstraction + vars.get(j) + ", ";
										else
											abstraction = abstraction + vars.get(j);
									}
									abstraction = abstraction + ");";
									found = true;
									break;
								}
							}
							if(!found) {
								abstraction = "Func" + old_ctl_node_function.get(step) + "(";
								for (int j = 0; j < vars.size(); j++) {
									if (j != vars.size() - 1)
										abstraction = abstraction + vars.get(j) + ", ";
									else
										abstraction = abstraction + vars.get(j);
								}
								abstraction = abstraction + ");";
							}
						} else {
							abstraction = abstraction + "Func" + old_ctl_node_function.get(step) + "(";
							for (int j = 0; j < vars.size(); j++) {
								if (j != vars.size() - 1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							// abstraction = getSourceCode(step, false, matcher, oldSlicer4J, oldSlicer4JBytecodeMapping);
						}
//						String fixNode = step.toString();
//						writer.println("\"OldNode: " + fixNode + "\"" + "[" + Type + " label=\"" + abstraction + "\"];");
						fileWriter.println(abstraction);

					
				} else {// retained set
//					if (changeType.getType() == StepChangeType.SRCDAT || i == old_visited.size() - 1)
//						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";
//					else if (changeType.getType() == StepChangeType.SRCCTL)
//						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";
//					else // (changeType.getType()==StepChangeType.IDT)
//					Type = "color=red fillcolor=white shape=box style=filled fontsize=10";
//					String fixNode = step.toString();
//					writer.println("\"OldNode: " + fixNode + "\"" + "[" + Type + " label=\""+ getSourceCode(step, false, matcher, oldSlicer4J, oldSlicer4JBytecodeMapping) + "\"];");
					fileWriter.println(getSourceCode(step, false, matcher, oldSlicer4J, oldSlicer4JBytecodeMapping));
				}
			}
//			writer.println("}");
			fileWriter.close();
			/////////////////////////////////////////////////////////////
			//////////////////////// add nodes of new/////////////////////
			fileWriter = new PrintWriter(proPath + "/results/new/inPreSS.txt", "UTF-8");
//			writer.println("subgraph cluster1 {");
//			writer.println("color=black;");
//			writer.println("label = \"newslice\";");
			for (int i = new_kept.size() - 1; i >= 0; i--) {
				TraceNode step = new_kept.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
//				String Type;
				if (changeType.getType() == StepChangeType.DAT && !isATestStatement(tc, step)) {
					//if (new_kept.contains(step) || new_dat_kept.contains(step)) {// should be added but abstracted
//						Type = "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";
						List<VarValue> written = step.getWrittenVariables();
						List<ValueBox> writtenSoot = new ArrayList<>();
						List<Integer> positions = getSlicer4JMappedNode(step, oldSlicer4J, oldSlicer4JBytecodeMapping);
						if (positions != null) {
							for (Integer tracePositionToSliceFrom : positions) {
								StatementInstance stmt = old_dcfg.mapNoUnits(tracePositionToSliceFrom);
								writtenSoot.addAll(stmt.getUnit().getDefBoxes());
							}
						}
						List<String> vars = new ArrayList<>();
						List<TraceNode> visited = new ArrayList<>();
						try {
							visited.add(step);
							List<Pair<TraceNode, String>> temp = addVariable(visited, step, vars, new_data_map,
									newBlocks, new_kept, new_dat_kept);
						} catch (StackOverflowError e) {
							System.err.println("oche!");
						}
						String abstraction = "";
						if (written != null && written.size() != 0) { // is an assignment
							boolean found = false;
							for (int kk=0; kk<written.size();kk++) {
								abstraction = written.get(kk).getVarName();
								if ((!abstraction.isEmpty()) && abstraction!=null) {	
									abstraction = abstraction + "=Func" + new_data_node_function.get(step) + "(";
									for (int j = 0; j < vars.size(); j++) {
										if (j != vars.size() - 1)
											abstraction = abstraction + vars.get(j) + ", ";
										else
											abstraction = abstraction + vars.get(j);
									}
									abstraction = abstraction + ");";
									found = true;
									break;
								}
							}
							if(!found) {
								abstraction = "Func" + new_data_node_function.get(step) + "(";
								for (int j = 0; j < vars.size(); j++) {
									if (j != vars.size() - 1)
										abstraction = abstraction + vars.get(j) + ", ";
									else
										abstraction = abstraction + vars.get(j);
								}
								abstraction = abstraction + ");";
							}
						} else if (writtenSoot.size() != 0) {
							boolean found = false;
							for (int kk=0; kk<writtenSoot.size();kk++) {
								abstraction = writtenSoot.get(kk).getValue().toString();
								if ((!abstraction.isEmpty()) && abstraction!=null) {
									abstraction = abstraction + "=Func" + new_data_node_function.get(step) + "(";
									for (int j = 0; j < vars.size(); j++) {
										if (j != vars.size() - 1)
											abstraction = abstraction + vars.get(j) + ", ";
										else
											abstraction = abstraction + vars.get(j);
									}
									abstraction = abstraction + ");";
									found = true;
									break;
								}
							}	
							if(!found) {
								abstraction = "Func" + new_data_node_function.get(step) + "(";
								for (int j = 0; j < vars.size(); j++) {
									if (j != vars.size() - 1)
										abstraction = abstraction + vars.get(j) + ", ";
									else
										abstraction = abstraction + vars.get(j);
								}
								abstraction = abstraction + ");";
							}
						} else {
							abstraction = abstraction + "Func" + new_data_node_function.get(step) + "(";
							for (int j = 0; j < vars.size(); j++) {
								if (j != vars.size() - 1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							// abstraction = getSourceCode(step, true, matcher, newSlicer4J,newSlicer4JBytecodeMapping);
						}
//						String fixNode = step.toString();
//						writer.println("\"NewNode: " + fixNode + "\"" + "[" + Type + " label=\"" + abstraction + "\"];");
						fileWriter.println(abstraction);
					
				} else if (changeType.getType() == StepChangeType.CTL && !isATestStatement(tc, step)) {
					if (new_kept.contains(step)) {// should be added but abstracted
//						Type = "color=blue fillcolor=lightskyblue1 shape=box style=filled fontsize=10";
						List<VarValue> written = step.getWrittenVariables();
						List<ValueBox> writtenSoot = new ArrayList<>();
						List<Integer> positions = getSlicer4JMappedNode(step, oldSlicer4J, oldSlicer4JBytecodeMapping);
						if (positions != null) {
							for (Integer tracePositionToSliceFrom : positions) {
								StatementInstance stmt = old_dcfg.mapNoUnits(tracePositionToSliceFrom);
								writtenSoot.addAll(stmt.getUnit().getDefBoxes());
							}
						}
						List<String> vars = new ArrayList<>();
						List<TraceNode> visited = new ArrayList<>();
						try {
							visited.add(step);
							List<Pair<TraceNode, String>> temp = addVariable(visited, step, vars, new_data_map,
									newBlocks, new_kept, new_dat_kept);
						} catch (StackOverflowError e) {
							System.err.println("oche!");
						}
						String abstraction = "";
						if (written != null && written.size() != 0) { // is an assignment
							boolean found = false;
							for (int kk=0; kk<written.size();kk++) {
								abstraction = written.get(kk).getVarName();
								if ((!abstraction.isEmpty()) && abstraction!=null) {	
									abstraction = abstraction + "=Func" + new_ctl_node_function.get(step) + "(";
									for (int j = 0; j < vars.size(); j++) {
										if (j != vars.size() - 1)
											abstraction = abstraction + vars.get(j) + ", ";
										else
											abstraction = abstraction + vars.get(j);
									}
									abstraction = abstraction + ");";
									found = true;
									break;								
								}
							}
							if(!found) {
								abstraction = "Func" + new_ctl_node_function.get(step) + "(";
								for (int j = 0; j < vars.size(); j++) {
									if (j != vars.size() - 1)
										abstraction = abstraction + vars.get(j) + ", ";
									else
										abstraction = abstraction + vars.get(j);
								}
								abstraction = abstraction + ");";
							}
						} else if (writtenSoot.size() != 0) {
							boolean found = false;
							for (int kk=0; kk<writtenSoot.size();kk++) {
								abstraction = writtenSoot.get(kk).getValue().toString();
								if ((!abstraction.isEmpty()) && abstraction!=null) {
									abstraction = abstraction + "=Func" + new_ctl_node_function.get(step) + "(";
									for (int j = 0; j < vars.size(); j++) {
										if (j != vars.size() - 1)
											abstraction = abstraction + vars.get(j) + ", ";
										else
											abstraction = abstraction + vars.get(j);
									}
									abstraction = abstraction + ");";
									found = true;									
									break;
								}
							}
							if(!found) {
								abstraction = "Func" + new_ctl_node_function.get(step) + "(";
								for (int j = 0; j < vars.size(); j++) {
									if (j != vars.size() - 1)
										abstraction = abstraction + vars.get(j) + ", ";
									else
										abstraction = abstraction + vars.get(j);
								}
								abstraction = abstraction + ");";
							}
						} else {
							abstraction = abstraction + "Func" + new_ctl_node_function.get(step) + "(";
							for (int j = 0; j < vars.size(); j++) {
								if (j != vars.size() - 1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							// abstraction = getSourceCode(step, true, matcher, newSlicer4J, newSlicer4JBytecodeMapping);
						}
//						String fixNode = step.toString();
//						writer.println("\"NewNode: " + fixNode + "\"" + "[" + Type + " label=\"" + abstraction + "\"];");
						fileWriter.println(abstraction);
					}
				} else {// retained set
//					if (changeType.getType() == StepChangeType.SRCDAT || i == new_visited.size() - 1)
//						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";
//					else if (changeType.getType() == StepChangeType.SRCCTL)
//						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";
//					else // (changeType.getType()==StepChangeType.IDT)
//					Type = "color=red fillcolor=white shape=box style=filled fontsize=10";
//					String fixNode = step.toString();
//					writer.println("\"NewNode: " + fixNode + "\"" + "[" + Type + " label=\""+ getSourceCode(step, true, matcher, newSlicer4J, newSlicer4JBytecodeMapping) + "\"];");
					fileWriter.println(getSourceCode(step, true, matcher, newSlicer4J, newSlicer4JBytecodeMapping));
				}
			}
//			writer.println("}");
			fileWriter.close();
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			///////////////////////// add control flow edges//////////////
			
//			Collections.sort(old_kept, new TraceNodePairOrderComparator(oldSlicer4J, oldSlicer4JBytecodeMapping));
//			Collections.sort(new_kept, new TraceNodePairOrderComparator(newSlicer4J, newSlicer4JBytecodeMapping));

//			for (int i = 0; i < old_kept.size(); i++) {
//				if (i != old_kept.size() - 1) {
//					TraceNode step = old_kept.get(i);
//					TraceNode BeforeStep = old_kept.get(i + 1);					
////					writer.println("\"OldNode: " + BeforeStep + "\" " + "->" + "\"OldNode: " + step
////							+ "\" [color=gray55 style=dotted arrowhead=normal dir=back];");
//				}
//			}
//			for (int i = 0; i < new_kept.size(); i++) {
//				if (i != new_kept.size() - 1) {
//					TraceNode step = new_kept.get(i);
//					TraceNode BeforeStep = new_kept.get(i + 1);
////					writer.println("\"NewNode: " + BeforeStep + "\" " + "->" + "\"NewNode: " + step
////							+ "\" [color=gray55 style=dotted arrowhead=normal dir=back] ;");
//				}
//			}
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			///////////////////////// add alignment
			////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////// edges//////////////////////////////////////////////////////////////////////////////
//			for (int i = 0; i < old_kept.size(); i++) {
//				TraceNode step = old_kept.get(i);
//				StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
//				TraceNode matchedStep = changeType.getMatchingStep();
////				if (new_kept.contains(matchedStep)) {
//////					writer.println("\"OldNode: " + step + "\" " + "->" + "\"NewNode: " + matchedStep
//////							+ "\" [color=grey55 style=dotted arrowhead=none constraint=false];");
////				}
//			}
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			///////////////////////// add dependency edges////////////////
			/*for (int i = 0; i < old_kept.size(); i++) {
				TraceNode step = old_kept.get(i);
				if (old_data_map.keySet().contains(step))
					if (old_data_map.get(step) != null)
						for (Pair<TraceNode, String> dep : old_data_map.get(step))
							if (old_kept.contains(dep.first()))
								// if (!dep.second().contains("stack"))
								writer.println("\"OldNode: " + step + "\" " + "-> " + "\"OldNode: " + dep.first()
										+ "\" [color=black style=solid arrowhead=normal constraint=false xlabel=\" "
										+ dep.second() + "   \" ];");// connect data nodes to east
				if (old_ctl_map.keySet().contains(step))
					if (old_ctl_map.get(step) != null)
						for (TraceNode dep : old_ctl_map.get(step))
							if (old_kept.contains(dep))
								writer.println("\"OldNode: " + step + "\" " + "-> " + "\"OldNode: " + dep
										+ "\" [color=black style=dashed arrowhead=normal constraint=false];");// connect
																												// data
																												// nodes
																												// to
																												// west
			}

			for (int i = 0; i < new_kept.size(); i++) {
				TraceNode step = new_kept.get(i);
				if (new_data_map.keySet().contains(step))
					if (new_data_map.get(step) != null)
						for (Pair<TraceNode, String> dep : new_data_map.get(step))
							if (new_kept.contains(dep.first()))
								// if (!dep.second().contains("stack"))
								writer.println("\"NewNode: " + step + "\" " + "-> " + "\"NewNode: " + dep.first()
										+ "\" [color=black style=solid arrowhead=normal constraint=false xlabel=\" "
										+ dep.second() + "   \" ];");
				if (new_ctl_map.keySet().contains(step))
					if (new_ctl_map.get(step) != null)
						for (TraceNode dep : new_ctl_map.get(step))
							if (new_kept.contains(dep))
								writer.println("\"NewNode: " + step + "\" " + "-> " + "\"NewNode: " + dep
										+ "\" [color=black style=dashed arrowhead=normal constraint=false];");
			}*/

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
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////	
	private List<Pair<TraceNode, String>> addVariable(List<TraceNode> visited, TraceNode step, List<String> vars,
			HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map, HashMap<TraceNode, Integer> Blocks,
			List<TraceNode> kept, List<TraceNode> forced_kept) {
//		System.out.println("Node is " + step);
		List<Pair<TraceNode, String>> data_deps = data_map.get(step);
//		System.out.println("the current is " + data_deps);
		List<Pair<TraceNode, String>> UpdatedDataDeps = new ArrayList<>();
		if (data_deps != null) {
			for (Pair<TraceNode, String> pair : data_deps) { // used variable for step
//				System.out.println("The dep node is " + pair.first());
				if (kept.contains(pair.first()) || forced_kept.contains(pair.first())) {// it is already kept in the
																						// trace just add it to vars
//					System.out.println("The dep node is kept => continue");
					if (!vars.contains(pair.second())) {
//						System.out.println("The var to be added from kept " + pair.second());
						vars.add(pair.second());
					}
					continue;
				}
				if (data_map.containsKey(pair.first())) {
					for (Pair<TraceNode, String> depDepsPair : data_map.get(pair.first())) {
						if (!UpdatedDataDeps.contains(depDepsPair))
							UpdatedDataDeps.add(depDepsPair);
					}
				}
				if (Blocks.get(pair.first()) == Blocks.get(step)) { // abstract pair.first()
					try {
						if (!visited.contains(pair.first())) {
							visited.add(pair.first());
							if (vars.size() < 20) {
								List<Pair<TraceNode, String>> temp = addVariable(visited, pair.first(), vars, data_map,
										Blocks, kept, forced_kept);
								UpdatedDataDeps.addAll(temp);
							}
						}
					} catch (StackOverflowError e) {
						System.err.println("oche!");
					}
				} 
				//comment code below because if pair.first is not kept and it is not in the same block with step => it means it was not in dual slice result 
				//so we don't keep the use variable without defining statement.
//				else {
//					if (!vars.contains(pair.second()))
//						vars.add(pair.second());
//				}
			}
		}
		if (UpdatedDataDeps.size() != 0 && UpdatedDataDeps != null) {
			for (Pair<TraceNode, String> pair : UpdatedDataDeps)
				if ((!data_deps.contains(pair)) && vars.contains(pair.second()))
					data_deps.add(pair);
		}
//		System.out.println("updated is " + data_deps);
		if (data_deps != null)
			data_map.put(step, data_deps);
		return UpdatedDataDeps;
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
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
	////////////////////////////////////////////////////////////////////////////////////////////////////
	
	private void PrintFinalResultAll(TestCase tc, String basePath, String projectName, String bugID, Trace newTrace, Trace oldTrace, 
			List<TraceNode> new_visited, List<TraceNode> old_visited, List<TraceNode> new_kept, List<TraceNode> old_kept, 
			List<TraceNode> new_retained, List<TraceNode> old_retained, HashMap<Integer, List<TraceNode>> newDataBlockNodes, 
			HashMap<Integer, List<TraceNode>> oldDataBlockNodes, HashMap<Integer, List<TraceNode>> newCtlBlockNodes, 
			HashMap<Integer, List<TraceNode>> oldCtlBlockNodes, int oldTraceTime, int newTraceTime, int codeTime, 
			int traceTime, int dualTime, int InPreSSTime, HashMap<Integer, Integer> oldChangeChunkInfo, HashMap<Integer, Integer> newChangeChunkInfo, 
			HashMap<Integer, Integer> oldTestCaseChunkInfo, HashMap<Integer, Integer> newTestCaseChunkInfo, 
			HashMap<Integer, Integer> oldCommonChunkInfo, HashMap<Integer, Integer> newCommonChunkInfo,
			int oldRetainedTestRemovedByDual, int newRetainedTestRemovedByDual) {
	
			System.out.println("Old trace size is " + oldTrace.getExecutionList().size());
			System.out.println("New trace size is " + newTrace.getExecutionList().size());
			System.out.println("Old dual size is " + old_visited.size());
			System.out.println("New dual size is " + new_visited.size());
			System.out.println("Old retained size (removing test that are removed by DS) is " + old_retained.size());
			System.out.println("New retained size (removing test that are removed by DS) is " + new_retained.size());
			System.out.println("Old InPreSS size (removing test that are removed by DS) is " + old_kept.size());
			System.out.println("New InPreSS size (removing test that are removed by DS) is " + new_kept.size());
			
			int oldAllRetained = old_retained.size()+oldRetainedTestRemovedByDual;
			int newAllRetained = new_retained.size()+newRetainedTestRemovedByDual;
			int oldAllInPreSSRetained = old_kept.size()+oldRetainedTestRemovedByDual;
			int newAllInPreSSRetained = new_kept.size()+newRetainedTestRemovedByDual;
			System.out.println("Old retained size (keeping all test even not removed by DS) is " + oldAllRetained);
			System.out.println("New retained size (keeping all test even not removed by DS) is " + newAllRetained);
			System.out.println("Old InPreSS size (keeping all test even not removed by DS) is " + oldAllInPreSSRetained);
			System.out.println("New InPreSS size (keeping all test even not removed by DS) is " + newAllInPreSSRetained);
			
	//		int OldTraceSourceSize = getTheSourceSize(oldTrace.getExecutionList());
	//		int NewTraceSourceSize = getTheSourceSize(newTrace.getExecutionList());
	//		int OldDualSourceSize = getTheSourceSize(old_visited);
	//		int NewDualSourceSize = getTheSourceSize(new_visited);
	//		int OldRetainedSourceSize = getTheSourceSize(old_retained);
	//		int NewRetainedSourceSize = getTheSourceSize(new_retained);
	//		int OldInPreSSSourceSize = getTheSourceSize(old_kept);
	//		int NewInPreSSSourceSize = getTheSourceSize(new_kept);
			
	//		System.out.println("Old trace size (source-level) is " + OldTraceSourceSize);
	//		System.out.println("New trace size (source-level) is " + NewTraceSourceSize);
	//		System.out.println("Old dual size (source-level) is " + OldDualSourceSize);
	//		System.out.println("New dual size (source-level) is " + NewDualSourceSize);
	//		System.out.println("Old retained size (source-level) is " + OldRetainedSourceSize);
	//		System.out.println("New retained size (source-level) is " + NewRetainedSourceSize);
	//		System.out.println("Old InPreSS size (source-level) is " + OldInPreSSSourceSize);
	//		System.out.println("New InPreSS size (source-level) is " + NewInPreSSSourceSize);
			
			System.out.println("Old #Data B is " + oldDataBlockNodes.keySet().size());
			System.out.println("New #Data B is " + newDataBlockNodes.keySet().size());
			System.out.println("Old #Control B is " + oldCtlBlockNodes.keySet().size());
			System.out.println("New #Control B is " + newCtlBlockNodes.keySet().size());
			System.out.println("old trace time is " + oldTraceTime);
			System.out.println("new trace time is " + newTraceTime);
			System.out.println("code diff " + codeTime);
			System.out.println("trace diff " + traceTime);
			System.out.println("dual time is " + dualTime);
			System.out.println("InPreSS time is " + InPreSSTime);
		    
			String results = basePath+"/results/"+projectName+".xlsx";
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
			System.out.println("Old Common block size (sum): " + oldCommonBlockSum);
			System.out.println("Old Common block size (avg) " + oldCommonBlockAvg);
			System.out.println("Old Common block size (min): " + oldCommonBlockMin);
			System.out.println("Old Common block size (max) " + oldCommonBlockMax);
			
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
			System.out.println("New Common block size (sum): " + newCommonBlockSum);
			System.out.println("New Common block size (avg) " + newCommonBlockAvg);
			System.out.println("New Common block size (min): " + newCommonBlockMin);
			System.out.println("New Common block size (max) " + newCommonBlockMax);
			
		    	
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
			System.out.println("Old data dual block size (sum): " + oldDATDualSum);
			System.out.println("Old data dual block size (avg) " + oldDATDualAvg);
			System.out.println("Old data dual block size (min): " + oldDATDualMin);
			System.out.println("Old data dual block size (max) " + oldDATDualMax);
			
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
			System.out.println("New data dual block size (sum): " + newDATDualSum);
			System.out.println("New data dual block size (avg) " + newDATDualAvg);
			System.out.println("New data dual block size (min): " + newDATDualMin);
			System.out.println("New data dual block size (max) " + newDATDualMax);
			
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
			System.out.println("Old data InPreSS block size (sum): " + oldDATInPreSSSum);
			System.out.println("Old data InPreSS block size (avg) " + oldDATInPreSSAvg);
			System.out.println("Old data InPreSS block size (min): " + oldDATInPreSSMin);
			System.out.println("Old data InPreSS block size (max) " + oldDATInPreSSMax);
			
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
			System.out.println("New data InPreSS block size (sum): " + newDATInPreSSSum);
			System.out.println("New data InPreSS block size (avg) " + newDATInPreSSAvg);
			System.out.println("New data InPreSS block size (min): " + newDATInPreSSMin);
			System.out.println("New datat InPreSS block size (max) " + newDATInPreSSMax);
			
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
			System.out.println("Old ctl dual block size (sum): " + oldCTLDualSum);
			System.out.println("Old ctl dual block size (avg) " + oldCTLDualAvg);
			System.out.println("Old ctl dual block size (min): " + oldCTLDualMin);
			System.out.println("Old ctl dual block size (max) " + oldCTLDualMax);
			
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
			System.out.println("New ctl dual block size (sum): " + newCTLDualSum);
			System.out.println("New ctl dual block size (avg) " + newCTLDualAvg);
			System.out.println("New ctl dual block size (min): " + newCTLDualMin);
			System.out.println("New ctl dual block size (max) " + newCTLDualMax);
			
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
			System.out.println("Old ctl InPreSS block size (sum): " + oldCTLInPreSSSum);
			System.out.println("Old ctl InPreSS block size (avg) " + oldCTLInPreSSAvg);
			System.out.println("Old ctl InPreSS block size (min): " + oldCTLInPreSSMin);
			System.out.println("Old ctl InPreSS block size (max) " + oldCTLInPreSSMax);
			
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
			System.out.println("New ctl InPreSS block size (sum): " + newCTLInPreSSSum);
			System.out.println("New ctl InPreSS block size (avg) " + newCTLInPreSSAvg);
			System.out.println("New ctl InPreSS block size (min): " + newCTLInPreSSMin);
			System.out.println("New ctl InPreSS block size (max) " + newCTLInPreSSMax);
			
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
		        		 "old data block InPreSS (sum)","old data block InPreSS (avg)","old data block InPreSS (min)","old data block InPreSS (max)",
		        		 "new data block InPreSS (sum)","new data block InPreSS (avg)","new data block InPreSS (min)","new data block InPreSS (max)",
		        		 "old ctl block InPreSS (sum)","old ctl block InPreSS (avg)","old ctl block InPreSS (min)","old ctl block InPreSS (max)",
		        		 "new ctl block InPreSS (sum)","new ctl block InPreSS (avg)","new ctl block InPreSS (min)","new ctl block InPreSS (max)",
		        		 "old trace time", "new trace time", 
		        		 "code diff time", "trace diff time", "dual time", "InPreSS time" 
		        		 };
		        WriteToExcel(results, header,"stats",false,true);
		    }
		    String[] data = {bugID, 
		    		String.valueOf(oldTrace.getExecutionList().size()), String.valueOf(newTrace.getExecutionList().size()), 
		    		String.valueOf(old_visited.size()), String.valueOf(new_visited.size()), 
		    		String.valueOf(oldChangeChunkInfo.keySet().size()), String.valueOf(oldLocation), String.valueOf(oldChangedStamts),
		    		String.valueOf(oldTestCaseChunkInfo.keySet().size()), String.valueOf(old_retained.size()-oldChangedStamts), 
		    		String.valueOf(old_retained.size()), String.valueOf(oldAllRetained), 
		    		String.valueOf(newChangeChunkInfo.keySet().size()), String.valueOf(newLocation), String.valueOf(newChangedStamts),
		    		String.valueOf(newTestCaseChunkInfo.keySet().size()), String.valueOf(new_retained.size()-newChangedStamts), 
		    		String.valueOf(new_retained.size()), String.valueOf(newAllRetained),
		    		String.valueOf(oldCommonChunkInfo.keySet().size()), String.valueOf(newCommonChunkInfo.keySet().size()),
		    		String.valueOf(oldCommonBlockSum),String.valueOf(oldCommonBlockAvg),String.valueOf(oldCommonBlockMin),String.valueOf(oldCommonBlockMax),
		    		String.valueOf(newCommonBlockSum),String.valueOf(newCommonBlockAvg),String.valueOf(newCommonBlockMin),String.valueOf(newCommonBlockMax),
		    		String.valueOf(old_kept.size()), String.valueOf(new_kept.size()), 
		    		String.valueOf(oldAllInPreSSRetained), String.valueOf(newAllInPreSSRetained),
		    		String.valueOf(oldDataBlockNodes.keySet().size()), String.valueOf(newDataBlockNodes.keySet().size()),
		    		String.valueOf(oldCtlBlockNodes.keySet().size()), String.valueOf(newCtlBlockNodes.keySet().size()),
		    		String.valueOf(oldDATDualSum),String.valueOf(oldDATDualAvg),String.valueOf(oldDATDualMin),String.valueOf(oldDATDualMax),
		    		String.valueOf(newDATDualSum),String.valueOf(newDATDualAvg),String.valueOf(newDATDualMin),String.valueOf(newDATDualMax),
		    		String.valueOf(oldCTLDualSum),String.valueOf(oldCTLDualAvg),String.valueOf(oldCTLDualMin),String.valueOf(oldCTLDualMax),
		    		String.valueOf(newCTLDualSum),String.valueOf(newCTLDualAvg),String.valueOf(newCTLDualMin),String.valueOf(newCTLDualMax),
		    		String.valueOf(oldDATInPreSSSum),String.valueOf(oldDATInPreSSAvg),String.valueOf(oldDATInPreSSMin),String.valueOf(oldDATInPreSSMax),
		    		String.valueOf(newDATInPreSSSum),String.valueOf(newDATInPreSSAvg),String.valueOf(newDATInPreSSMin),String.valueOf(newDATInPreSSMax),
		    		String.valueOf(oldCTLInPreSSSum),String.valueOf(oldCTLInPreSSAvg),String.valueOf(oldCTLInPreSSMin),String.valueOf(oldCTLInPreSSMax),
		    		String.valueOf(newCTLInPreSSSum),String.valueOf(newCTLInPreSSAvg),String.valueOf(newCTLInPreSSMin),String.valueOf(newCTLInPreSSMax),
		    		String.valueOf(oldTraceTime),String.valueOf(newTraceTime),
		    		String.valueOf(codeTime), String.valueOf(traceTime), String.valueOf(dualTime),String.valueOf(InPreSSTime)
		    		};
		    WriteToExcel(results,data, "stats",false,false);
			
			System.out.println("##############Final Results##############");
			
			
	}	
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	/////////
	private void PrintPaperResults(TestCase tc, String basePath, String projectName, String bugID, Trace newTrace, Trace oldTrace, 
			List<TraceNode> new_visited, List<TraceNode> old_visited, List<TraceNode> new_kept, List<TraceNode> old_kept, 
			List<TraceNode> new_retained, List<TraceNode> old_retained, HashMap<Integer, List<TraceNode>> newDataBlockNodes, 
			HashMap<Integer, List<TraceNode>> oldDataBlockNodes, HashMap<Integer, List<TraceNode>> newCtlBlockNodes, 
			HashMap<Integer, List<TraceNode>> oldCtlBlockNodes, int oldTraceTime, int newTraceTime, int codeTime, 
			int traceTime, int dualTime, int InPreSSTime, HashMap<Integer, Integer> oldChangeChunkInfo, HashMap<Integer, Integer> newChangeChunkInfo, 
			HashMap<Integer, Integer> oldTestCaseChunkInfo, HashMap<Integer, Integer> newTestCaseChunkInfo, 
			HashMap<Integer, Integer> oldCommonChunkInfo, HashMap<Integer, Integer> newCommonChunkInfo,
			int oldRetainedTestRemovedByDual, int newRetainedTestRemovedByDual, List<String> old_kept_sourceCodeLevel, List<String> new_kept_sourceCodeLevel) throws IOException {
		  
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
			double oldReduction = ((Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(old_visited.size()))/(Double.valueOf(oldTrace.getExecutionList().size())))*100.0;
			double newReduction = ((Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(new_visited.size()))/(Double.valueOf(newTrace.getExecutionList().size())))*100.0;
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
		    oldReduction = ((Double.valueOf(old_visited.size())-Double.valueOf(old_kept.size()))/(Double.valueOf(old_visited.size())))*100.0;
			newReduction = ((Double.valueOf(new_visited.size())-Double.valueOf(new_kept.size()))/(Double.valueOf(new_visited.size())))*100.0;
			
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
		    
		    double reducOldData =  ((Double.valueOf(old_visited.size())-(old_retained.size()+oldCTLDualSum+oldDATInPreSSSum))/(Double.valueOf(old_visited.size())))*100.0;
		    double reducOldCTL =  ((Double.valueOf(old_visited.size())-(old_retained.size()+oldDATDualSum+oldCTLInPreSSSum))/(Double.valueOf(old_visited.size())))*100.0;
		    double reducNewData =  ((Double.valueOf(new_visited.size())-(new_retained.size()+newCTLDualSum+newDATInPreSSSum))/(Double.valueOf(new_visited.size())))*100.0;
		    double reducNewCTL =  ((Double.valueOf(new_visited.size())-(new_retained.size()+newDATDualSum+newCTLInPreSSSum))/(Double.valueOf(new_visited.size())))*100.0;
		    
		    String[] detailedDataRQ2 = {bugID, 
		    		String.valueOf(oldDataBlockNodes.keySet().size()), String.valueOf(oldDATDualAvg),String.valueOf(oldDATDualMax),String.valueOf(reducOldData),
		    		String.valueOf(oldCtlBlockNodes.keySet().size()), String.valueOf(oldCTLDualAvg),String.valueOf(oldCTLDualMax) ,String.valueOf(reducOldCTL),
		    		String.valueOf(oldDataBlockNodes.keySet().size()), String.valueOf(oldDATDualAvg),String.valueOf(oldDATDualMax) ,String.valueOf(reducNewData),
		    		String.valueOf(newCtlBlockNodes.keySet().size()),String.valueOf(newCTLDualAvg),String.valueOf(newCTLDualMax), String.valueOf(reducNewCTL),};
		       WriteToExcel(results,detailedDataRQ2,"RQ2",true,false);
			
//			System.out.println("##############Source code statement##############");
//			System.out.println(old_kept_sourceCodeLevel.size());
//			System.out.println(new_kept_sourceCodeLevel.size());
			System.out.println("##############Finish##############");
						
	}	
//########################################################################################################################
	//########################################################################################################################
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
}

