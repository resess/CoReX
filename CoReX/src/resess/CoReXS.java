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
import resess.InPreSSS;
import sav.common.core.Pair;
import soot.ValueBox;
import tregression.StepChangeType;
import tregression.StepChangeTypeChecker;
import tregression.empiricalstudy.RootCauseNode;
import tregression.empiricalstudy.TestCase;
import tregression.model.PairList;
import tregression.model.TraceNodePair;
import tregression.separatesnapshots.DiffMatcher;

public class CoReXS {
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

	////////////////////////////////////////////////////////////////////////////////////////////////////s
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
	
	////////////////////////////////////////////////////////////////////////////////////////////////////
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

	public Pair<List<TraceNode>,List<TraceNode>> corex(String basePath, String projectName, String bugID, TestCase tc, int assertionLine, boolean slicer4J, String proPath, TraceNode observedFaultNode, Trace newTrace,
			Trace oldTrace, PairList pairList, DiffMatcher diffMatcher, int oldTraceTime, int newTraceTime, int codeTime, int traceTime, List<RootCauseNode> rootList,boolean debug, String tool2Run, String save_slice_results) throws IOException {
		
//		List<TraceNode> old_visited = new ArrayList<>();
//		List<TraceNode> new_visited = new ArrayList<>();
//		List<TraceNode> inpress_old_kept = new ArrayList<>();
//		List<TraceNode> inpress_new_kept = new ArrayList<>();
//		List<TraceNode> old_retained_dual = new ArrayList<>();		
//		List<TraceNode> new_retained_dual = new ArrayList<>();
		if(tool2Run.equals("dual") || tool2Run.equals("all")) {
			InPreSSS configS = new InPreSSS();
//			TODO:if dual slice > necessary in printing results. then (necessary = dual slice) and for all cases, (unnecessary = dual - necessary) then the (sufficient = corex - (necessary + context)). 
//			configS.dualSlicing(basePath,projectName, bugID,tc, true,proPath,observedFaultNode, newTrace, oldTrace, PairList, diffMatcher, oldTraceTime, newTraceTime, codeTime, traceTime,rootcauseFinder.getRealRootCaseList(),debug,new_visited,old_visited,inpress_new_kept,inpress_old_kept,new_retained_dual,old_retained_dual);			
			//InPreSS(basePath,projectName, bugID,tc, assertionLine, false, proPath, observedFaultNode, newTrace, oldTrace, pairList, diffMatcher, oldTraceTime, newTraceTime, codeTime, traceTime,rootList,debug,new_visited,old_visited,inpress_new_kept,inpress_old_kept,new_retained_dual,old_retained_dual);
		}
		
		List<TraceNode> new_workList = new ArrayList<>();
		List<TraceNode> new_sync_slice = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> new_data_map = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> new_ctl_map = new HashMap<>();

		List<TraceNode> old_workList = new ArrayList<>();
		List<TraceNode> old_sync_slice = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> old_data_map = new HashMap<>(); //(12, [(13,g), (14,f)])
		HashMap<TraceNode, List<TraceNode>> old_ctl_map = new HashMap<>();//(12, [13, 14])
		

		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> old_CashDeps = new HashMap<>();
		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> new_CashDeps = new HashMap<>();


//		newTheReasonToBeInResult.put(observedFaultNode, "the failed assertion");
				
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
		
		List<TraceNode> old_kept_with_reaching_and_keeping_sameDepMatched = new ArrayList<>(); //the longest
		List<TraceNode> new_kept_with_reaching_and_keeping_sameDepMatched = new ArrayList<>();//the longest
		List<TraceNode> old_kept_without_reaching_and_keeping_sameDepMatched = new ArrayList<>(); 
		List<TraceNode> new_kept_without_reaching_and_keeping_sameDepMatched = new ArrayList<>();
		List<TraceNode> old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus = new ArrayList<>(); 
		List<TraceNode> new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus = new ArrayList<>();
		List<TraceNode> old_kept_with_reaching_and_removing_sameDepMatched = new ArrayList<>(); 
		List<TraceNode> new_kept_with_reaching_and_removing_sameDepMatched = new ArrayList<>(); 
		List<TraceNode> old_kept_without_reaching_but_removing_sameDepMatche= new ArrayList<>(); //the shortest
		List<TraceNode> new_kept_without_reaching_but_removing_sameDepMatched= new ArrayList<>(); //the shortest
	
		List<TraceNode> old_retained = new ArrayList<>();		
		List<TraceNode> new_retained = new ArrayList<>();
		List<TraceNode> old_taintedContext = new ArrayList<>();	 // that is the list of contextual statements that are in the sync slice because of dependency of matched or unmatched statements so basically they are the context of secondary statements	and thus are secondary themselves
		List<TraceNode> new_taintedContext = new ArrayList<>();  
		List<TraceNode> old_PureContext = new ArrayList<>();
		List<TraceNode> new_PureContext = new ArrayList<>();
//		List<TraceNode> corex_old_kept = new ArrayList<>();//final kept after adding context of what we need
//		List<TraceNode> corex_new_kept = new ArrayList<>();//final kept after adding context of what we need
//		
//		new_sync_slice.add(observedFaultNode);
//		new_workList.add(observedFaultNode);
//		corex_new_kept.add(observedFaultNode);
//		new_retained.add(observedFaultNode);
//		StepChangeType changeType = typeChecker.getType(observedFaultNode, true, pairList, diffMatcher);
//		TraceNode observedFaultNodeMapping = changeType.getMatchingStep();
//		if(observedFaultNodeMapping!=null) {
//			old_sync_slice.add(observedFaultNodeMapping);
//			old_workList.add(observedFaultNodeMapping);
//			corex_old_kept.add(observedFaultNodeMapping);
//			old_retained.add(observedFaultNodeMapping);	
//		}
//		else {		
//			TraceNode oldObservable = getAssertionStatement(oldTrace.getExecutionList(),tc,assertionLine,oldSlicer4J,oldSlicer4JBytecodeMapping);
//			if(oldObservable!=null) {
//				old_sync_slice.add(oldObservable);
//				old_workList.add(oldObservable);
//				corex_old_kept.add(oldObservable);
//				old_retained.add(oldObservable);
//			}
//			else {
//				old_sync_slice.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
//				old_workList.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
//				corex_old_kept.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
//				old_retained.add(oldTrace.getExecutionList().get(oldTrace.getExecutionList().size()-1));
//			}
//			changeType = typeChecker.getType(oldObservable, false, pairList, diffMatcher);
//			TraceNode observedFaultNodeMappingonNew = changeType.getMatchingStep();
//			if(observedFaultNodeMappingonNew!=null) {
//				if(!new_sync_slice.contains(observedFaultNodeMappingonNew)) {
//					new_sync_slice.add(observedFaultNodeMappingonNew);
//					new_workList.add(observedFaultNodeMappingonNew);
//					corex_new_kept.add(observedFaultNodeMappingonNew);
//					new_retained.add(observedFaultNodeMappingonNew);
//				}
//			}
//			else {
//				TraceNode newObservable = getAssertionStatement(newTrace.getExecutionList(),tc,assertionLine,newSlicer4J,newSlicer4JBytecodeMapping);
//				if(newObservable!=null) {
//					if(!new_sync_slice.contains(newObservable)) {
//						new_sync_slice.add(newObservable);
//						new_workList.add(newObservable);
//						corex_new_kept.add(newObservable);
//						new_retained.add(newObservable);
//					}
//				}
//				else {
//					if(!new_sync_slice.contains(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1))) {
//						new_sync_slice.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
//						new_workList.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
//						corex_new_kept.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
//						new_retained.add(newTrace.getExecutionList().get(newTrace.getExecutionList().size()-1));
//				    }
//				}				
//			}			
//		}
		new_sync_slice.add(observedFaultNode);
		new_workList.add(observedFaultNode);
		new_retained.add(observedFaultNode);
		new_kept_without_reaching_and_keeping_sameDepMatched.add(observedFaultNode);
		new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(observedFaultNode);
		StepChangeType changeType = typeChecker.getType(observedFaultNode, true, pairList, diffMatcher);
		TraceNode observedFaultNodeMapping = changeType.getMatchingStep();
		List<Integer> matchPositions = getSlicer4JMappedNode(observedFaultNodeMapping, newSlicer4J,newSlicer4JBytecodeMapping);
		if (matchPositions != null) {
//		/if(observedFaultNodeMapping!=null) {
			old_kept_without_reaching_and_keeping_sameDepMatched.add(observedFaultNodeMapping);		
			old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(observedFaultNodeMapping);
			old_sync_slice.add(observedFaultNodeMapping);
			old_workList.add(observedFaultNodeMapping);
			old_retained.add(observedFaultNodeMapping);	
		}
		
		Long dual_start_time = System.currentTimeMillis();
		if(tool2Run.equals("corex") || tool2Run.equals("all")) {
			while (!new_workList.isEmpty() || !old_workList.isEmpty()) {
				while (!new_workList.isEmpty()) {
	//				System.out.println("#############################");
					TraceNode step = new_workList.remove(0);
					updateWorklistKeepingIdentical(new_dcfg, new_slicer, old_dcfg,
							old_slicer, new_CashDeps, old_CashDeps, newSlicer4J, oldSlicer4J, newSlicer4JBytecodeMapping,
							oldSlicer4JBytecodeMapping, slicer4J, step, newTrace, oldTrace, new_sync_slice, new_workList,
							old_sync_slice, old_workList, true, typeChecker, pairList, diffMatcher, new_data_map, new_ctl_map,
							proPath, bugID,new_retained,old_retained, new_taintedContext, old_taintedContext,new_PureContext,old_PureContext);
				}
				////////////////////////////////////////////////////////////////////////////////////////
				while (!old_workList.isEmpty()) {
	//				System.out.println("#############################");
					TraceNode step = old_workList.remove(0);
					updateWorklistKeepingIdentical(new_dcfg, new_slicer, old_dcfg,
							old_slicer, old_CashDeps, new_CashDeps, oldSlicer4J, newSlicer4J, oldSlicer4JBytecodeMapping,
							newSlicer4JBytecodeMapping, slicer4J, step, oldTrace, newTrace, old_sync_slice, old_workList,
							new_sync_slice, new_workList, false, typeChecker, pairList, diffMatcher, old_data_map, old_ctl_map,
							proPath, bugID,old_retained,new_retained,old_taintedContext, new_taintedContext,old_PureContext,new_PureContext);
				}
			}
		}
//		System.out.println(old_taintedContext.size());
//		System.out.println(new_taintedContext.size());
//		System.out.println(old_PureContext.size());
//		System.out.println(new_PureContext.size());
		for(TraceNode step:old_PureContext) {
			if(old_taintedContext.contains(step))
				old_taintedContext.remove(step);
		}
		for(TraceNode step:new_PureContext) {
			if(new_taintedContext.contains(step))
				new_taintedContext.remove(step);
		}
//		System.out.println(old_taintedContext.size());
//		System.out.println(new_taintedContext.size());
		/// ################################################################
		/// ################################################################
		Long dual_finish_time = System.currentTimeMillis();				
		int dual_Time = (int) (dual_finish_time - dual_start_time);
		
		if(tool2Run.equals("corex") || tool2Run.equals("all")) {
			for(int i=old_sync_slice.size()-1;i>=0; i--){
				TraceNode step = old_sync_slice.get(i);
				if(step==null)
					old_sync_slice.remove(i);
			}
			for(int i=new_sync_slice.size()-1;i>=0; i--){
				TraceNode step = new_sync_slice.get(i);
				if(step==null)
					new_sync_slice.remove(i);
			}
		}
		System.out.println("##########Finish Dual Slcing while keeping identical###################");
//		printDualSliceResults(old_visited, false, proPath, diffMatcher);
//		printDualSliceResults(new_visited,true, proPath,diffMatcher);
		/// ################################################################
		/// ################################################################
//		HashMap<Integer, Integer> oldChangeChunkInfo = new HashMap<>();
//		HashMap<Integer, Integer> newChangeChunkInfo = new HashMap<>();
//		HashMap<Integer, Integer> oldCommonChunkInfo = new HashMap<>();
//		HashMap<Integer, Integer> newCommonChunkInfo = new HashMap<>();
//		getChangeChunks(typeChecker, diffMatcher, old_sync_slice,new_sync_slice,oldChangeChunkInfo,newChangeChunkInfo);
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

		HashMap<Integer, List<TraceNode>> oldDataBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newDataBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> oldCtlBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newCtlBlockNodes = new HashMap<>();
	
		
		HashMap<TraceNode, List<TraceNode>> old_expandingFunctions = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> new_expandingFunctions = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> old_expandingFunctions_keeping_reaching = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> new_expandingFunctions_keeping_reaching = new HashMap<>();
		
		Long corex_start_time = System.currentTimeMillis();
		int[] BlockSize1 = {0,0,0,0,0,0};
		if(tool2Run.equals("corex")|| tool2Run.equals("all")) {
			corexMatchedBlockAlgorithm(oldSlicer4J, newSlicer4J, oldSlicer4JBytecodeMapping, newSlicer4JBytecodeMapping,tc, proPath, old_sync_slice,new_sync_slice,typeChecker,pairList, 
					diffMatcher,both_old_data_map,both_old_ctl_map,both_new_data_map,both_new_ctl_map,
					old_kept_with_reaching_and_keeping_sameDepMatched, new_kept_with_reaching_and_keeping_sameDepMatched, 
					old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched, 
					old_kept_with_reaching_and_removing_sameDepMatched, new_kept_with_reaching_and_removing_sameDepMatched, 
					old_kept_without_reaching_but_removing_sameDepMatche, new_kept_without_reaching_but_removing_sameDepMatched, 
					old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus, new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus, 
					oldDataBlockNodes, newDataBlockNodes, oldCtlBlockNodes, newCtlBlockNodes, old_retained, new_retained,old_expandingFunctions,new_expandingFunctions,old_expandingFunctions_keeping_reaching,new_expandingFunctions_keeping_reaching,BlockSize1,old_taintedContext, new_taintedContext, old_PureContext, new_PureContext,save_slice_results);				
		}
		Long corex_finish_time = System.currentTimeMillis();
		int corex_Time = (int) (corex_finish_time - corex_start_time);
			
//		for(int i=old_kept_with_reaching_and_keeping_sameDepMatched.size()-1;i>=0; i--){
//			TraceNode step = old_kept_with_reaching_and_keeping_sameDepMatched.get(i);
//			if(step==null)
//				old_kept_with_reaching_and_keeping_sameDepMatched.remove(i);
//		}
//		for(int i=new_kept_with_reaching_and_keeping_sameDepMatched.size()-1;i>=0; i--){
//			TraceNode step = new_kept_with_reaching_and_keeping_sameDepMatched.get(i);
//			if(step==null)
//				new_kept_with_reaching_and_keeping_sameDepMatched.remove(i);
//		}
		for(int i=old_kept_without_reaching_and_keeping_sameDepMatched.size()-1;i>=0; i--){
			TraceNode step = old_kept_without_reaching_and_keeping_sameDepMatched.get(i);
			if(step==null)
				old_kept_without_reaching_and_keeping_sameDepMatched.remove(i);
		}
		for(int i=new_kept_without_reaching_and_keeping_sameDepMatched.size()-1;i>=0; i--){
			TraceNode step = new_kept_without_reaching_and_keeping_sameDepMatched.get(i);
			if(step==null)
				new_kept_without_reaching_and_keeping_sameDepMatched.remove(i);
		}
		for(int i=old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.size()-1;i>=0; i--){
			TraceNode step = old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.get(i);
			if(step==null)
				old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.remove(i);
		}
		for(int i=new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.size()-1;i>=0; i--){
			TraceNode step = new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.get(i);
			if(step==null)
				new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.remove(i);
		}
		
//		PrintPaperResults(tc,basePath, projectName, bugID, typeChecker,pairList, diffMatcher, newTrace, oldTrace, new_sync_slice, old_sync_slice, 
//				new_kept_with_reaching_and_keeping_sameDepMatched, old_kept_with_reaching_and_keeping_sameDepMatched, 
//				new_kept_without_reaching_and_keeping_sameDepMatched, old_kept_without_reaching_and_keeping_sameDepMatched, 
//				 new_retained, old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes,
//				 BlockSize1, new_expandingFunctions,old_expandingFunctions,
//				 new_expandingFunctions_keeping_reaching,old_expandingFunctions_keeping_reaching,newSlicer4J, oldSlicer4J, newSlicer4JBytecodeMapping,
//					oldSlicer4JBytecodeMapping);
		PrintPaperResultsShorterVersion(tc,basePath, projectName, bugID, typeChecker,pairList, diffMatcher, newTrace, oldTrace, new_sync_slice, old_sync_slice, 
				new_kept_with_reaching_and_keeping_sameDepMatched, old_kept_with_reaching_and_keeping_sameDepMatched, 
				new_kept_without_reaching_and_keeping_sameDepMatched, old_kept_without_reaching_and_keeping_sameDepMatched, 
				new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus, old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus, 
				 new_retained, old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes,
				 BlockSize1, new_expandingFunctions,old_expandingFunctions,
				 new_expandingFunctions_keeping_reaching,old_expandingFunctions_keeping_reaching,dual_Time, corex_Time);
		Pair pair = new Pair(old_kept_with_reaching_and_keeping_sameDepMatched, new_kept_with_reaching_and_keeping_sameDepMatched);
		return pair;
		
		
		
	}
	private void corexMatchedBlockAlgorithm(BiMap<TraceNode, String> oldSlicer4J,BiMap<TraceNode, String> newSlicer4J, HashMap<String, List<String>> oldSlicer4JBytecodeMapping,
			HashMap<String, List<String>> newSlicer4JBytecodeMapping, TestCase tc,String proPath, List<TraceNode> old_sync_slice, List<TraceNode> new_sync_slice, 
			StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher, 
			HashMap<TraceNode, List<Pair<TraceNode, String>>> old_data_map, HashMap<TraceNode, List<TraceNode>> old_ctl_map, 
			HashMap<TraceNode, List<Pair<TraceNode, String>>> new_data_map, HashMap<TraceNode, List<TraceNode>> new_ctl_map, 
			List<TraceNode> old_kept_with_reaching_and_keeping_sameDepMatched, List<TraceNode>  new_kept_with_reaching_and_keeping_sameDepMatched,
			List<TraceNode> old_kept_without_reaching_and_keeping_sameDepMatched, List<TraceNode> new_kept_without_reaching_and_keeping_sameDepMatched,
			List<TraceNode> old_kept_with_reaching_and_removing_sameDepMatched, List<TraceNode> new_kept_with_reaching_and_removing_sameDepMatched, 
			List<TraceNode> old_kept_without_reaching_but_removing_sameDepMatched, List<TraceNode> new_kept_without_reaching_but_removing_sameDepMatched,
			List<TraceNode>  old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus, List<TraceNode>  new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus, 			
			HashMap<Integer, List<TraceNode>> oldDataBlockNodes, HashMap<Integer, List<TraceNode>> newDataBlockNodes,
			HashMap<Integer, List<TraceNode>> oldCtlBlockNodes,HashMap<Integer, List<TraceNode>> newCtlBlockNodes,
			List<TraceNode> old_retained, List<TraceNode> new_retained,
			HashMap<TraceNode, List<TraceNode>> old_expandingFunctions, HashMap<TraceNode, List<TraceNode>> new_expandingFunctions,
			HashMap<TraceNode, List<TraceNode>> old_expandingFunctions_keeping_reaching, HashMap<TraceNode, List<TraceNode>> new_expandingFunctions_keeping_reaching,int[] BlockSize1,
			List<TraceNode> old_taintedContext,List<TraceNode> new_taintedContext, List<TraceNode> old_pureContext,List<TraceNode> new_pureContext, String save_slice_results) {
		
		/////////////////////////////////////////////////////////////
		Collections.sort(old_sync_slice, new TraceNodeOrderComparator());
		Collections.sort(new_sync_slice, new TraceNodeOrderComparator());                	
		/////////////////////extract blocks for old/////////////////////
		HashMap<Integer, List<TraceNode>> oldCtlBlockNodesTemp = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newCtlBlockNodesTemp = new HashMap<>();
		HashMap<TraceNode, Integer> oldBlocks = new HashMap<>();
		Integer BlockID = 0;
		boolean current_matched_flag = false;
		boolean current_unmatched_flag = false;
		
		boolean firstTime = true;
		boolean isMatchedBlock = false;
		boolean isUnmatchedBlock = false;

		for(int i=old_sync_slice.size()-1;i>=0; i--){
			TraceNode step = old_sync_slice.get(i);	
//			System.out.println("step on old is: " + step);	
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
//			System.out.println("step type: " + changeType.getType());	
			//if ((changeType.getType()!=StepChangeType.DAT || i==old_visited.size()-1) && changeType.getType()!=StepChangeType.CTL) { //separate the blocks
//			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || (isATestStatement(tc, step) && isLastStatement(tc, step,old_visited))) { //it is retain		
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || old_retained.contains(step)) { //it is retain						
				isMatchedBlock = false;
				isUnmatchedBlock = false;		
				if (current_matched_flag) {//coming from a matched block
					//BlockID = BlockID + 1;
					current_matched_flag = false;
					//firstTime = false;
				}
				if (current_unmatched_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_unmatched_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isMatchedBlock = false;
				isUnmatchedBlock = true;
				if (!current_unmatched_flag) {//if we are not currently in ctl block
					BlockID = BlockID + 1;
					current_unmatched_flag = true;
					current_matched_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.DAT || changeType.getType()==StepChangeType.IDT){ //matched statements
				isMatchedBlock = true;
				isUnmatchedBlock = false;		
				if (!current_matched_flag) {//if we are not currently in matched block
					BlockID = BlockID + 1;
					current_matched_flag = true;
					current_unmatched_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
			
		}	
//		System.out.println("old blocks " + oldBlocks);	
		/////////////////////extract blocks for new/////////////////////
		HashMap<TraceNode, Integer> newBlocks = new HashMap<>();
		BlockID = 0;
		int CTLBlockID = 0;
		current_matched_flag = false;
		current_unmatched_flag = false;
		firstTime = true;
		isMatchedBlock = false;
		isUnmatchedBlock = false;
		TraceNode previousData = null;
		TraceNode previousIDT = null;
		for(int i=new_sync_slice.size()-1;i>=0; i--){
			TraceNode step = new_sync_slice.get(i);
			//System.out.println("step on new is: " + step);	
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
			//if ((changeType.getType()!=StepChangeType.DAT || i==new_visited.size()-1) && changeType.getType()!=StepChangeType.CTL) { //separate the blocks
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || new_retained.contains(step)) { //separate the blocks				
				isMatchedBlock = false;
				isUnmatchedBlock = false;
				if (current_matched_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_matched_flag = false;
					//firstTime = false;
				}
				if (current_unmatched_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_unmatched_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isMatchedBlock = false;
				isUnmatchedBlock = true;
				if (!current_unmatched_flag) {//coming from dat or other blocks
					CTLBlockID = CTLBlockID + 1;
					current_unmatched_flag = true;
					current_matched_flag = false;
					//firstTime = false;
				}
				newBlocks.put(step, CTLBlockID);//will be updated later once we know the number of all data blocks
			}
			else if (changeType.getType()==StepChangeType.DAT || changeType.getType()==StepChangeType.IDT){ 
				isMatchedBlock = true;
				isUnmatchedBlock = false;	
				if (previousData!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousData, true, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();					
					if(oldBlocks.get(matchedStep)!=oldBlocks.get(previousMatchedStep)) {//separate if it is separated in old 									
						BlockID = BlockID + 1;
						current_matched_flag = true;
						current_unmatched_flag = false;
						//firstTime = false;
					}					
					else {			
						if (!current_matched_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_matched_flag = true;
							current_unmatched_flag = false;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_matched_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_matched_flag = true;
						current_unmatched_flag = false;
						//firstTime = false;
					}
					
				}
				previousData = step;
				newBlocks.put(step, BlockID);	
			}

		
			if (isMatchedBlock){
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
			if (isUnmatchedBlock){
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
		current_matched_flag = false;
		current_unmatched_flag = false;
		firstTime = true;
		isMatchedBlock = false;
		isUnmatchedBlock = false;
		previousData = null;
		previousIDT = null; 
		for(int i=old_sync_slice.size()-1;i>=0; i--){
			TraceNode step = old_sync_slice.get(i);
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL && changeType.getType()!=StepChangeType.IDT) || old_retained.contains(step)) { //separate the blocks
				isMatchedBlock = false;
				isUnmatchedBlock = false;
				if (current_matched_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_matched_flag = false;
					//firstTime = false;
				}
				if (current_unmatched_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_unmatched_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isMatchedBlock = false;
				isUnmatchedBlock = true;
				if (!current_unmatched_flag) {//coming from dat or other blocks
					CTLBlockID = CTLBlockID + 1;
					current_unmatched_flag = true;
					current_matched_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, CTLBlockID);//will be updated later
			}
			else if (changeType.getType()==StepChangeType.DAT || changeType.getType()==StepChangeType.IDT){ 
				isMatchedBlock = true;
				isUnmatchedBlock = false;	
				if (previousData!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousData, false, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();
					if(newBlocks.get(matchedStep)!=newBlocks.get(previousMatchedStep)) {//separate them 									
						BlockID = BlockID + 1;
						current_matched_flag = true;
						current_unmatched_flag = false;
						//firstTime = false;
					}					
					else {			
						if (!current_matched_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_matched_flag = true;
							current_unmatched_flag = false;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_matched_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_matched_flag = true;
						current_unmatched_flag = false;
						//firstTime = false;
					}
				}
				previousData = step;
				oldBlocks.put(step, BlockID);
			}
			if (isMatchedBlock){
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
			if (isUnmatchedBlock){
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
//		System.out.println("old blocks " + oldBlocks);
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
//		////////////////////////////////////////////////////////////////////////////////////////////////////////
//		////////////////////////////////////////////////////////////////////////////////////////////////////////
//		////////////////////////////////////////////////////////////////////////////////////////////////////////	
//		////////////////////////////////////////////////////////////////////////////////////////////////////////
//		/////////////////////abstraction////////////////////////////////////////////////////////////////
			//should also the corresponding kept node from the other trace be add?
		
			Collections.sort(old_sync_slice, new TraceNodeOrderComparator());
			Collections.sort(new_sync_slice, new TraceNodeOrderComparator());
			
			
			if(!old_kept_without_reaching_and_keeping_sameDepMatched.contains(old_sync_slice.get(old_sync_slice.size()-1)))
				old_kept_without_reaching_and_keeping_sameDepMatched.add(old_sync_slice.get(old_sync_slice.size()-1));
			if(!new_kept_without_reaching_and_keeping_sameDepMatched.contains(new_sync_slice.get(new_sync_slice.size()-1)))
				new_kept_without_reaching_and_keeping_sameDepMatched.add(new_sync_slice.get(new_sync_slice.size()-1));

			if(!old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(old_sync_slice.get(old_sync_slice.size()-1)))
				old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(old_sync_slice.get(old_sync_slice.size()-1));
			if(!new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(new_sync_slice.get(new_sync_slice.size()-1)))
				new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(new_sync_slice.get(new_sync_slice.size()-1));

			
////////////////////////////////////First Define what to keep (like inpress but keeping the identical too)////////////////////////////////////////////////
			for(int i=old_sync_slice.size()-1;i>=0; i--){
				TraceNode step = old_sync_slice.get(i);					
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
				if(old_retained.contains(step)) {
					if(!old_kept_without_reaching_and_keeping_sameDepMatched.contains(step)) 										
						old_kept_without_reaching_and_keeping_sameDepMatched.add(step);
					if(!old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(step)) 										
						old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(step);
				}
				List<Integer> matchPositions = getSlicer4JMappedNode(changeType.getMatchingStep(), newSlicer4J,newSlicer4JBytecodeMapping);
				if (matchPositions != null) 
					if(changeType.getMatchingStep()!=null) {
						if(new_retained.contains(changeType.getMatchingStep())) {
							if(!new_kept_without_reaching_and_keeping_sameDepMatched.contains(changeType.getMatchingStep())) 										
								new_kept_without_reaching_and_keeping_sameDepMatched.add(changeType.getMatchingStep());
							if(!new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(changeType.getMatchingStep())) 										
								new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(changeType.getMatchingStep());
						}
					}
				/////////keep the dependencies in different block
				List<Pair<TraceNode, String>> data_deps = old_data_map.get(step);	
//				System.out.println("data deps: " + data_deps);
				if(data_deps!=null) 
					for(Pair<TraceNode, String> pair:data_deps) { 
						if(old_sync_slice.contains(pair.first())) {
							if(old_retained.contains(pair.first()) || (oldBlocks.get(pair.first())!=oldBlocks.get(step))) {
//									||(old_pureContext.contains(pair.first()) && pair.first().getReadVariables().size()==0)) { //keep the reaching def if it is pureContext only								
								//inpressPlus adds without any check.
								if(!old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(pair.first())) 									
									old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(pair.first());								
								StepChangeType changeTypes = typeChecker.getTypeForPrinting(pair.first(), false, pairList, matcher);	//adding the corresponding in other trace
								TraceNode matchedStep = changeTypes.getMatchingStep();
								matchPositions = getSlicer4JMappedNode(matchedStep, newSlicer4J,newSlicer4JBytecodeMapping);
								if (matchPositions != null)
									if(matchedStep!=null) 
										if(!new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(matchedStep)) 										
											new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(matchedStep);	
								
								// For CoReX: if pair.first is just in sync slice because dependency of CTL or DATA we do not want to keep it as it is also secondary. So we create a list in sync slicing of those identical statements that are tainted with DAT or CTL
								if(!old_taintedContext.contains(pair.first())) { // that we do not want to keep in corex
									if(!old_kept_without_reaching_and_keeping_sameDepMatched.contains(pair.first())) 									
										old_kept_without_reaching_and_keeping_sameDepMatched.add(pair.first());										
									if (matchPositions != null)
										if(matchedStep!=null) 
											if(!new_kept_without_reaching_and_keeping_sameDepMatched.contains(matchedStep)) 										
												new_kept_without_reaching_and_keeping_sameDepMatched.add(matchedStep);											
								}	
//								List<Integer> stepMatchPositions = getSlicer4JMappedNode(changeType.getMatchingStep(), newSlicer4J,newSlicer4JBytecodeMapping);
//								if(stepMatchPositions!=null && changeType.getMatchingStep()!=null && matchPositions != null && matchedStep!=null) {//we check if there is a different use of this identical statements between two traces, if so, add it to corex for completeness of results
//									List<Pair<TraceNode, String>> matched_data_deps = new_data_map.get(changeType.getMatchingStep());
//									if(matched_data_deps!=null) {
//										for(Pair<TraceNode, String> data_pair:matched_data_deps) { 
//										   if(!data_pair.first().equals(matchedStep)) {
//											   if(!old_kept_without_reaching_and_keeping_sameDepMatched.contains(pair.first())) 									
//													old_kept_without_reaching_and_keeping_sameDepMatched.add(pair.first());										
//												if(!new_kept_without_reaching_and_keeping_sameDepMatched.contains(matchedStep)) 										
//													new_kept_without_reaching_and_keeping_sameDepMatched.add(matchedStep);
//										   }
//										}
//									}
//								}
							}
						}
					}
				
				List<TraceNode> ctl_deps = old_ctl_map.get(step);
//				System.out.println("control deps: " + ctl_deps);
				if(changeType.getType()==StepChangeType.CTL)//if the node is control diff we also want to keep the if statement 
					if(ctl_deps!=null) 
						for(TraceNode node:ctl_deps) {
							StepChangeType changeTypes = typeChecker.getTypeForPrinting(node, false, pairList, matcher);				
							if(changeTypes.getType()==StepChangeType.SRCDAT || changeTypes.getType()==StepChangeType.DAT){//keep the control condition causing the control block
//								System.out.println("control dep which is DAT");
								if(old_sync_slice.contains(node)) {
									if(!old_kept_without_reaching_and_keeping_sameDepMatched.contains(node)) 
										old_kept_without_reaching_and_keeping_sameDepMatched.add(node);	
									if(!old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(node)) 
										old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(node);	
										
									TraceNode matchedStep = changeTypes.getMatchingStep();
									matchPositions = getSlicer4JMappedNode(matchedStep, newSlicer4J,newSlicer4JBytecodeMapping);
									if (matchPositions != null)
										if(matchedStep!=null) {
											if(!new_kept_without_reaching_and_keeping_sameDepMatched.contains(matchedStep)) 										
												new_kept_without_reaching_and_keeping_sameDepMatched.add(matchedStep);
											if(!new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(matchedStep)) 										
												new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(matchedStep);																	
										}
								}
							}
						}
							
			}
			
			for(int i=new_sync_slice.size()-1;i>=0; i--){
				TraceNode step = new_sync_slice.get(i);
//				System.out.println("this is step on new: " + step);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);				
				if(new_retained.contains(step)) {
					if(!new_kept_without_reaching_and_keeping_sameDepMatched.contains(step)) 										
						new_kept_without_reaching_and_keeping_sameDepMatched.add(step);
					if(!new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(step)) 										
						new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(step);
				}
				List<Integer> matchPositions = getSlicer4JMappedNode(changeType.getMatchingStep(), oldSlicer4J,oldSlicer4JBytecodeMapping);
				if (matchPositions != null) 
					if(changeType.getMatchingStep()!=null)
						if(old_retained.contains(changeType.getMatchingStep())) {
							if(!old_kept_without_reaching_and_keeping_sameDepMatched.contains(changeType.getMatchingStep())) 										
								old_kept_without_reaching_and_keeping_sameDepMatched.add(changeType.getMatchingStep());
							if(!old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(changeType.getMatchingStep())) 										
								old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(changeType.getMatchingStep());
						}
			    /////////keep the dependencies in different block
				List<Pair<TraceNode, String>> data_deps = new_data_map.get(step);	
//				System.out.println("data deps: " + data_deps);
				if(data_deps!=null) 
					for(Pair<TraceNode, String> pair:data_deps) { 
						if(new_sync_slice.contains(pair.first())) {
							if(new_retained.contains(pair.first()) || (newBlocks.get(pair.first())!=newBlocks.get(step))) {  
//									||(new_pureContext.contains(pair.first()) && pair.first().getReadVariables().size()==0)) { //keep the reaching def if it is pureContext only	
								//inpressPlus adds without any check.
								if(!new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(pair.first())) 									
									new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(pair.first());																
								StepChangeType changeTypes = typeChecker.getTypeForPrinting(pair.first(), true, pairList, matcher);	
								TraceNode matchedStep = changeTypes.getMatchingStep();	
								matchPositions = getSlicer4JMappedNode(matchedStep, oldSlicer4J,oldSlicer4JBytecodeMapping);
								if (matchPositions != null)  
									if(matchedStep!=null) 
										if(!old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(matchedStep)) 										
											old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(matchedStep);
								
								// For CoReX: if pair.first is just in sync slice because dependency of CTL or DATA we do not want to keep it as it is also secondary. So we create a list in sync slicing of those identical statements that are tainted with DAT or CTL
								if(!new_taintedContext.contains(pair.first())) { // that we do not want to keep in corex
									if(!new_kept_without_reaching_and_keeping_sameDepMatched.contains(pair.first())) 									
										new_kept_without_reaching_and_keeping_sameDepMatched.add(pair.first());										
									if (matchPositions != null) 
										if(matchedStep!=null) 
											if(!old_kept_without_reaching_and_keeping_sameDepMatched.contains(matchedStep)) 										
												old_kept_without_reaching_and_keeping_sameDepMatched.add(matchedStep);												
								}
//								List<Integer> stepMatchPositions = getSlicer4JMappedNode(changeType.getMatchingStep(), oldSlicer4J,oldSlicer4JBytecodeMapping);
//								if(stepMatchPositions!=null && changeType.getMatchingStep()!=null && matchPositions != null && matchedStep!=null) { //we check if there is a different use of this identical statements between two traces, if so, add it to corex for completeness of results
//									List<Pair<TraceNode, String>> matched_data_deps = old_data_map.get(changeType.getMatchingStep());
//									if(matched_data_deps!=null) {
//										for(Pair<TraceNode, String> data_pair:matched_data_deps) { 
//										   if(!data_pair.first().equals(matchedStep)) {
//											   if(!new_kept_without_reaching_and_keeping_sameDepMatched.contains(pair.first())) 									
//													new_kept_without_reaching_and_keeping_sameDepMatched.add(pair.first());										
//												if(!old_kept_without_reaching_and_keeping_sameDepMatched.contains(matchedStep)) 										
//													old_kept_without_reaching_and_keeping_sameDepMatched.add(matchedStep);
//										   }
//										}
//									}
//								}
							}
						}
					}
				
				List<TraceNode> ctl_deps = new_ctl_map.get(step);
//				System.out.println("control deps: " + ctl_deps);
				if(changeType.getType()==StepChangeType.CTL)//if the node is control diff we also want to keep the if statement 
					if(ctl_deps!=null) 
						for(TraceNode node:ctl_deps) {
							StepChangeType changeTypes = typeChecker.getTypeForPrinting(node, true, pairList, matcher);				
							if(changeTypes.getType()==StepChangeType.SRCDAT || changeTypes.getType()==StepChangeType.DAT){//keep the control condition causing the control block
//								System.out.println("control dep which is DAT");
								if(new_sync_slice.contains(node)) {
									if(!new_kept_without_reaching_and_keeping_sameDepMatched.contains(node)) 
										new_kept_without_reaching_and_keeping_sameDepMatched.add(node);	
									if(!new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(node)) 
										new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(node);	
										
									TraceNode matchedStep = changeTypes.getMatchingStep();
									matchPositions = getSlicer4JMappedNode(matchedStep, oldSlicer4J,oldSlicer4JBytecodeMapping);
									if (matchPositions != null)
										if(matchedStep!=null) {
											if(!old_kept_without_reaching_and_keeping_sameDepMatched.contains(matchedStep)) 										
												old_kept_without_reaching_and_keeping_sameDepMatched.add(matchedStep);
											if(!old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.contains(matchedStep)) 										
												old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.add(matchedStep);																				
										}								
								 }								
							}
						}
			}

//			System.out.println("#################after paralizing#################"); 

			Collections.sort(old_kept_without_reaching_and_keeping_sameDepMatched, new TraceNodeOrderComparator());
			Collections.sort(new_kept_without_reaching_and_keeping_sameDepMatched, new TraceNodeOrderComparator());

			Collections.sort(old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus, new TraceNodeOrderComparator());
			Collections.sort(new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus, new TraceNodeOrderComparator());
			
			//below code is for keeping the reaching def inside the block and also create the func: did not run it now in Aug 21 for optimization
			
			
			if(save_slice_results.equals("true")) {

				old_kept_with_reaching_and_keeping_sameDepMatched.addAll(old_kept_without_reaching_and_keeping_sameDepMatched);
				new_kept_with_reaching_and_keeping_sameDepMatched.addAll(new_kept_without_reaching_and_keeping_sameDepMatched);
	////			System.out.println("Final nodes in old " + old_kept_with_reaching_and_keeping_sameDepMatched);
	////			System.out.println("Final nodes in new " + new_kept_with_reaching_and_keeping_sameDepMatched);
	//			Collections.sort(old_kept_with_reaching_and_keeping_sameDepMatched, new TraceNodeOrderComparator());
	//			Collections.sort(new_kept_with_reaching_and_keeping_sameDepMatched, new TraceNodeOrderComparator());
				
	/////////////////////////////////////Now 2) add the internal reachingDef of variables that we decided to keep + abstracted statements  ///////////////////////////////////////////////
				HashMap<TraceNode,String> old_function_names = new HashMap<>();
				HashMap<TraceNode,String> new_function_names = new HashMap<>();
				
				for(int i=old_kept_without_reaching_and_keeping_sameDepMatched.size()-1;i>=0; i--){
					//only for abstracted steps: not retained and the block with size 1
					TraceNode step = old_kept_without_reaching_and_keeping_sameDepMatched.get(i);
					StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
					if(oldDataBlockNodes.get(oldBlocks.get(step))!=null) {
						if(oldDataBlockNodes.get(oldBlocks.get(step)).size()==1)
							BlockSize1[0]++;
					}
					if(oldCtlBlockNodes.get(oldBlocks.get(step))!=null) {
						if(oldCtlBlockNodes.get(oldBlocks.get(step)).size()==1)
							BlockSize1[0]++;
					}
					if(oldDataBlockNodes.get(oldBlocks.get(step))!=null) {
						if((oldDataBlockNodes.get(oldBlocks.get(step)).size()!=1) && !(old_retained.contains(step)) && 
								(changeType.getType()==StepChangeType.DAT || changeType.getType()==StepChangeType.CTL || changeType.getType()==StepChangeType.IDT)) {	
									if (step.getReadVariables().size()!=0) {//keep reaching def as is
										List<String> inputs = getReachingDefandExpansion(oldSlicer4J,oldSlicer4JBytecodeMapping,step,step,old_kept_with_reaching_and_keeping_sameDepMatched,old_data_map,old_ctl_map,changeType,old_expandingFunctions, old_expandingFunctions_keeping_reaching);							
										List<VarValue> written = step.getWrittenVariables();
										if (written!=null && written.size()!=0 ) { //is an assignment
											String summary = String.valueOf(step.getOrder());
											summary = summary + " : " + step.getClassCanonicalName();
											String methodName = step.getMethodName();
											if(methodName != null){
												summary = summary + ":" + methodName;
											}
											summary = summary + ": LineNo@" + step.getLineNumber() + "--->";							        
											summary = summary + written.get(0).getVarName() + " = Func_" + String.valueOf(oldBlocks.get(step)) + "(";
											for(int j=0;j<inputs.size();j++) {
												if(j!=inputs.size()-1)
													summary = summary + inputs.get(j) + ",";
												else
													summary = summary + inputs.get(j);
											}
											summary = summary + ")";
											old_function_names.put(step, summary);
										}
									}
						}
					}
					else if(oldCtlBlockNodes.get(oldBlocks.get(step))!=null) {
						if((oldCtlBlockNodes.get(oldBlocks.get(step)).size()!=1) && !(old_retained.contains(step)) && 
								(changeType.getType()==StepChangeType.DAT || changeType.getType()==StepChangeType.CTL || changeType.getType()==StepChangeType.IDT)) {	
									if (step.getReadVariables().size()!=0) {//keep reaching def as is
										List<String> inputs = getReachingDefandExpansion(oldSlicer4J,oldSlicer4JBytecodeMapping,step,step,old_kept_with_reaching_and_keeping_sameDepMatched,old_data_map,old_ctl_map,changeType,old_expandingFunctions, old_expandingFunctions_keeping_reaching);	
										List<VarValue> written = step.getWrittenVariables();
										if (written!=null && written.size()!=0 ) { //is an assignment
											String summary = String.valueOf(step.getOrder());
											summary = summary + " : " + step.getClassCanonicalName();
											String methodName = step.getMethodName();
											if(methodName != null){
												summary = summary + ":" + methodName;
											}
											summary = summary + ": LineNo@" + step.getLineNumber() + "--->";							        
											summary = summary + written.get(0).getVarName() + " = Func_" + String.valueOf(oldBlocks.get(step)) + "(";
											for(int j=0;j<inputs.size();j++) {
												if(j!=inputs.size()-1)
													summary = summary + inputs.get(j) + ",";
												else
													summary = summary + inputs.get(j);
											}
											summary = summary + ")";
											old_function_names.put(step, summary);
										}
									}
						}
					}
				}
				for(int i=new_kept_without_reaching_and_keeping_sameDepMatched.size()-1;i>=0; i--){
					TraceNode step = new_kept_without_reaching_and_keeping_sameDepMatched.get(i);
					StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
					if(newDataBlockNodes.get(newBlocks.get(step))!=null)
						if(newDataBlockNodes.get(newBlocks.get(step)).size()==1)
							BlockSize1[1]++;
					if(newCtlBlockNodes.get(newBlocks.get(step))!=null)
						if(newCtlBlockNodes.get(newBlocks.get(step)).size()==1)
							BlockSize1[1]++;
					if(newDataBlockNodes.get(newBlocks.get(step))!=null) {
						if((newDataBlockNodes.get(newBlocks.get(step)).size()!=1)  && !(new_retained.contains(step)) &&
								(changeType.getType()==StepChangeType.DAT || changeType.getType()==StepChangeType.CTL || changeType.getType()==StepChangeType.IDT)) {
									if (step.getReadVariables().size()!=0) {//keep reaching def as is		
										List<String> inputs = getReachingDefandExpansion(newSlicer4J,newSlicer4JBytecodeMapping,step,step,new_kept_with_reaching_and_keeping_sameDepMatched,new_data_map,new_ctl_map,changeType,new_expandingFunctions,new_expandingFunctions_keeping_reaching);			
										List<VarValue> written = step.getWrittenVariables();
										if (written!=null && written.size()!=0 ) { //is an assignment
											String summary = String.valueOf(step.getOrder());
											summary = summary+ " : " + step.getClassCanonicalName();
											String methodName = step.getMethodName();
											if(methodName != null){
												summary = summary + ":" + methodName;
											}
											summary = summary + ": LineNo@" + step.getLineNumber() + "--->";							        
											summary = summary + written.get(0).getVarName() + " = Func_" + String.valueOf(newBlocks.get(step)) + "(";
											for(int j=0;j<inputs.size();j++) {
												if(j!=inputs.size()-1)
													summary = summary + inputs.get(j) + ",";
												else
													summary = summary + inputs.get(j);
											}
											summary = summary + ")";
											new_function_names.put(step, summary);
										}
									}
							}
					}
					else if(newCtlBlockNodes.get(newBlocks.get(step))!=null) {
						if((newCtlBlockNodes.get(newBlocks.get(step)).size()!=1)  && !(new_retained.contains(step)) &&
								(changeType.getType()==StepChangeType.DAT || changeType.getType()==StepChangeType.CTL || changeType.getType()==StepChangeType.IDT)) {
									if (step.getReadVariables().size()!=0) {//keep reaching def as is
										List<String> inputs= getReachingDefandExpansion(newSlicer4J,newSlicer4JBytecodeMapping,step,step,new_kept_with_reaching_and_keeping_sameDepMatched,new_data_map,new_ctl_map,changeType,new_expandingFunctions,new_expandingFunctions_keeping_reaching);	
										List<VarValue> written = step.getWrittenVariables();
										if (written!=null && written.size()!=0 ) { //is an assignment
											String summary = String.valueOf(step.getOrder());
											summary = summary + " : " + step.getClassCanonicalName();
											String methodName = step.getMethodName();
											if(methodName != null){
												summary = summary + ":" + methodName;
											}
											summary = summary + ": LineNo@" + step.getLineNumber() + "--->";							        
											summary = summary + written.get(0).getVarName() + " = Func_" + String.valueOf(newBlocks.get(step)) + "(";
											for(int j=0;j<inputs.size();j++) {
												if(j!=inputs.size()-1)
													summary = summary + inputs.get(j) + ",";
												else
													summary = summary + inputs.get(j);
											}
											summary = summary + ")";
											new_function_names.put(step, summary);
										}
									}
						}
				
					}
				}
/////////////////////////////////////Now 3)add edges  ///////////////////////////////////////////////

//				Collections.sort(old_kept_without_reaching_and_keeping_sameDepMatched, new TraceNodeOrderComparator());
//				Collections.sort(new_kept_without_reaching_and_keeping_sameDepMatched, new TraceNodeOrderComparator());
//				Collections.sort(old_kept_with_reaching_and_keeping_sameDepMatched, new TraceNodeOrderComparator());
//				Collections.sort(new_kept_with_reaching_and_keeping_sameDepMatched, new TraceNodeOrderComparator());
						
				try {
				PrintWriter fileWriter = new PrintWriter(proPath + "/results/old/CoReX.txt", "UTF-8");
				for(int i=0;i<=old_kept_without_reaching_and_keeping_sameDepMatched.size()-1;i++){
					TraceNode step = old_kept_without_reaching_and_keeping_sameDepMatched.get(i);	
					if(old_function_names.containsKey(step))
						fileWriter.println(old_function_names.get(step));
					else
						fileWriter.println(getSourceCode(step, false, matcher,oldSlicer4J,oldSlicer4JBytecodeMapping));
				}
				fileWriter.close();
				/////////////////////////////////////////////////////////////
				////////////////////////add nodes of new/////////////////////
				fileWriter = new PrintWriter(proPath + "/results/new/CoReX.txt", "UTF-8");		
				for(int i=0;i<=new_kept_without_reaching_and_keeping_sameDepMatched.size()-1;i++){
					TraceNode step = new_kept_without_reaching_and_keeping_sameDepMatched.get(i);
					if(new_function_names.containsKey(step))
						fileWriter.println(new_function_names.get(step));
					else
						fileWriter.println(getSourceCode(step, true, matcher,newSlicer4J,newSlicer4JBytecodeMapping));
				}	
				fileWriter.close();
				
//				fileWriter = new PrintWriter(proPath + "/results/old/CoReXWithReachingDef.txt", "UTF-8");
//				for(int i=0;i<=old_kept_with_reaching_and_keeping_sameDepMatched.size()-1;i++){
//					TraceNode step = old_kept_with_reaching_and_keeping_sameDepMatched.get(i);				
//					if(old_function_names.containsKey(step))
//						fileWriter.println(old_function_names.get(step));
//					else
//						fileWriter.println(getSourceCode(step, false, matcher,oldSlicer4J,oldSlicer4JBytecodeMapping));
//				}
//				fileWriter.close();
//				/////////////////////////////////////////////////////////////
//				////////////////////////add nodes of new/////////////////////
//				fileWriter = new PrintWriter(proPath + "/results/new/CoReXWithReachingDef.txt", "UTF-8");		
//				for(int i=0;i<=new_kept_with_reaching_and_keeping_sameDepMatched.size()-1;i++){
//					TraceNode step = new_kept_with_reaching_and_keeping_sameDepMatched.get(i);
//					if(new_function_names.containsKey(step))
//						fileWriter.println(new_function_names.get(step));
//					else
//						fileWriter.println(getSourceCode(step, true, matcher,newSlicer4J,newSlicer4JBytecodeMapping));
//				}	
//				fileWriter.close();
				
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
	private List<String> getReachingDefandExpansion(BiMap<TraceNode, String> Slicer4JMapping, HashMap<String, List<String>> Slicer4JBytecodeMapping,TraceNode parentStep, TraceNode step, List<TraceNode> kept_with_reaching, 
			HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map, HashMap<TraceNode, List<TraceNode>> ctl_map , 
			StepChangeType changeType, HashMap<TraceNode, List<TraceNode>> expandingFunctions,HashMap<TraceNode, List<TraceNode>> expandingFunctions_keeping_reaching) {
//		System.out.println("Node is " + parentStep);
		List<Pair<TraceNode, String>> data_deps = data_map.get(step);	
//		System.out.println("the current data dep is " + data_deps);	
		List<String> variables = new ArrayList<>();
		List<TraceNode> List = expandingFunctions.get(parentStep);
		if(List==null) {
			List = new ArrayList<>();
		}
		expandingFunctions.put(parentStep, List);
		
//		List = expandingFunctions_keeping_reaching.get(parentStep);
//		if(List==null) {
//			List = new ArrayList<>();
//		}
//		expandingFunctions_keeping_reaching.put(parentStep, List);
		
		if(data_deps!=null) {
			for(Pair<TraceNode, String> pair:data_deps) {
//				System.out.println("The dep node is " + pair.first());
				if(pair.first().getReadVariables().size()==0) {//it is reaching definition and need to be kept
					List<Integer> matchPositions = getSlicer4JMappedNode(pair.first(), Slicer4JMapping, Slicer4JBytecodeMapping);
					if (matchPositions != null) {
						if(!kept_with_reaching.contains(pair.first())) {
//							kept_with_reaching.add(pair.first());
//							if(!variables.contains(pair.second()))
//								variables.add(pair.second());
							if(changeType.getType()==StepChangeType.DAT || changeType.getType()==StepChangeType.CTL || changeType.getType()==StepChangeType.IDT) {
								List<TraceNode> abstractList = expandingFunctions.get(parentStep);
								if(!abstractList.contains(pair.first()))//adding what it abstracts
									abstractList.add(pair.first());
								expandingFunctions.put(parentStep, abstractList);
							}
							
						}
					}
				}
//				if(step.getInvocationParent()!=null) {
//					if(!step.getInvocationParent().equals(pair.first().getInvocationParent())){//pair.first() is a method invocation => keep it
//						if(!kept_with_reaching.contains(pair.first())) {
//							kept_with_reaching.add(pair.first());
//						}
//					}
//				}
				if(!kept_with_reaching.contains(pair.first())){//it is not already kept in the trace and abstracted aways
					List<Integer> matchPositions = getSlicer4JMappedNode(pair.first(), Slicer4JMapping, Slicer4JBytecodeMapping);
					if (matchPositions != null) {
						variables.addAll(getReachingDefandExpansion(Slicer4JMapping,Slicer4JBytecodeMapping,parentStep, pair.first(), kept_with_reaching,data_map,ctl_map,changeType,expandingFunctions,expandingFunctions_keeping_reaching));
						if(changeType.getType()==StepChangeType.DAT || changeType.getType()==StepChangeType.CTL || changeType.getType()==StepChangeType.IDT) {
							List<TraceNode> abstractList = expandingFunctions.get(parentStep);
							if(!abstractList.contains(pair.first()))//adding what it abstracts
								abstractList.add(pair.first());
							expandingFunctions.put(parentStep, abstractList);
							
//							abstractList = expandingFunctions_keeping_reaching.get(parentStep);
//							if(!abstractList.contains(pair.first()))//adding what it abstracts
//								abstractList.add(pair.first());
//							expandingFunctions_keeping_reaching.put(parentStep, abstractList);
							
						}
					}
				}
				else {
					if(!variables.contains(pair.second()))
						variables.add(pair.second());
				}
			}
		}
		return variables;
	}
	private void PrintPaperResultsShorterVersion(TestCase tc, String basePath, String projectName, String bugID, StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher, 
			Trace newTrace,Trace oldTrace, List<TraceNode> new_sync_slice, List<TraceNode> old_sync_slice, 
			List<TraceNode> new_kept_with_reaching_and_keeping_sameDepMatched,List<TraceNode> old_kept_with_reaching_and_keeping_sameDepMatched, 
			List<TraceNode> new_kept_without_reaching_and_keeping_sameDepMatched, List<TraceNode> old_kept_without_reaching_and_keeping_sameDepMatched,  
			List<TraceNode> new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus, List<TraceNode> old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus,
			List<TraceNode> new_retained, List<TraceNode> old_retained,
			HashMap<Integer, List<TraceNode>> newMatchedBlockNodes, HashMap<Integer, List<TraceNode>> oldMatchedBlockNodes,
			HashMap<Integer, List<TraceNode>> newUnmatchedBlockNodes, HashMap<Integer, List<TraceNode>> oldUnmatchedBlockNodes,
			int[] BlockSize1,
			HashMap<TraceNode, List<TraceNode>> new_expandingFunctions, HashMap<TraceNode, List<TraceNode>> old_expandingFunctions,
			HashMap<TraceNode, List<TraceNode>> new_expandingFunctions_keeping_reaching, HashMap<TraceNode, List<TraceNode>> old_expandingFunctions_keeping_reaching,
			long dual_time, long corex_time) {
		

		Path path = Paths.get(basePath+"/results");
		if(!Files.exists(path)) 
			new File(basePath+"/results").mkdirs();
		
		String results = basePath+"/results/"+projectName+"_CoReX_Paper_Results.xlsx";
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
	    double SyncOldReduction = (Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(old_sync_slice.size()))/(Double.valueOf(oldTrace.getExecutionList().size()))*100.0;
		double SyncNewReduction = (Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(new_sync_slice.size()))/(Double.valueOf(newTrace.getExecutionList().size()))*100.0;
	    double InPreSSPlusOldReduction = (Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.size()))/(Double.valueOf(oldTrace.getExecutionList().size()))*100.0;
	    double InPreSSPlusNewReduction = (Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.size()))/(Double.valueOf(newTrace.getExecutionList().size()))*100.0;
		double CoReXOldReduction = (Double.valueOf(oldTrace.getExecutionList().size())-Double.valueOf(old_kept_without_reaching_and_keeping_sameDepMatched.size()))/(Double.valueOf(oldTrace.getExecutionList().size()))*100.0;
	    double CoReXNewReduction = (Double.valueOf(newTrace.getExecutionList().size())-Double.valueOf(new_kept_without_reaching_and_keeping_sameDepMatched.size()))/(Double.valueOf(newTrace.getExecutionList().size()))*100.0;
	   
	    
	    
//	    if (FirstTime) {		    	
//	        String[] header = {"Bug ID", 
//	        		"Old Trace" , "Old Sync Slice", "Old Retained", "Old CoReX (without internal reaching defs)", "Old CoReX (with internal reaching defs)", 
//	        		"New Trace" , "New Sync Slice", "New Retained", "New CoReX (without internal reaching defs)", "New CoReX (with internal reaching defs)", 
//	        		};
//	        WriteToExcel(results, header, "Main_Stats",true,true);
//	    }
	    if (FirstTime) {		    	
	        String[] header = {"Bug ID", 
	        		"Old Trace" , "Old Sync Slice", "Old Sync Reduc.", "Old InPreSSPlus", "Old InPreSSPlus Reduc.", "Old CoReX", "Old CoReX Reduc.", 
	        		"New Trace" , "New Sync Slice", "New Sync Reduc.", "New InPreSSPlus", "New InPreSSPlus Reduc.", "New CoReX", "New CoReX Reduc.", "Sync Time", "Summary Time"
	        		};
	        WriteToExcel(results, header, "Reduction Rate",true,true);
	    }
	    
//	    String[] detailedDataRQ2 = {bugID, 
//	    		String.valueOf(oldTrace.getExecutionList().size()), String.valueOf(old_sync_slice.size()), String.valueOf(old_retained.size()), String.valueOf(old_kept_without_reaching_and_keeping_sameDepMatched.size()), String.valueOf(old_kept_with_reaching_and_keeping_sameDepMatched.size()),
//	    		String.valueOf(newTrace.getExecutionList().size()), String.valueOf(new_sync_slice.size()), String.valueOf(new_retained.size()), String.valueOf(new_kept_without_reaching_and_keeping_sameDepMatched.size()), String.valueOf(new_kept_with_reaching_and_keeping_sameDepMatched.size())
//	    		};
	    String[] detailedDataRQ2 = {bugID, 
	    		String.valueOf(oldTrace.getExecutionList().size()), String.valueOf(old_sync_slice.size()),String.valueOf(SyncOldReduction),
	    		String.valueOf(old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.size()), String.valueOf(InPreSSPlusOldReduction),
	    		String.valueOf(old_kept_without_reaching_and_keeping_sameDepMatched.size()), String.valueOf(CoReXOldReduction),
	    		String.valueOf(newTrace.getExecutionList().size()), String.valueOf(new_sync_slice.size()),String.valueOf(SyncNewReduction),  
	    		String.valueOf(new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus.size()), String.valueOf(InPreSSPlusNewReduction),
	    		String.valueOf(new_kept_without_reaching_and_keeping_sameDepMatched.size()), String.valueOf(CoReXNewReduction),
	    		String.valueOf(dual_time), String.valueOf(corex_time)
	    		};
	    
	    WriteToExcel(results,detailedDataRQ2,"Reduction Rate",true, false);
	    
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######

//	    int Old_Matched_IDT_elements = 0; 	   
//	    int Old_Matched_DataDiff_elements = 0; 
//	    int Old_Unmatched_elements = 0; 
//	    double Old_Matched_IDT_Abstracted_stmts_sum = 0.0; 
//	    double Old_Matched_DataDiff_Abstracted_stmts_sum = 0.0; 
//	    double Old_Unmatched_Abstracted_stmts_sum = 0.0; 
//	    double Old_Matched_IDT_Abstracted_stmts_avg = 0.0; 
//	    double Old_Matched_DataDiff_Abstracted_stmts_avg= 0.0; 
//	    double Old_Unmatched_Abstracted_stmts_avg = 0.0; 
//	    double Old_Matched_IDT_Abstracted_stmts_min = 1000000.0; 
//	    double Old_Matched_DataDiff_Abstracted_stmts_min = 1000000.0; 
//	    double Old_Unmatched_Abstracted_stmts_min = 1000000.0;  	    
//	    double Old_Matched_IDT_Abstracted_stmts_max = -1000000.0; 
//	    double Old_Matched_DataDiff_Abstracted_stmts_max = -1000000.0;
//	    double Old_Unmatched_Abstracted_stmts_max = -1000000.0; 
//	    
//	   
//	    double Old_Matched_block_sum = 0.0; 
//	    double Old_Unmatched_block_sum = 0.0; 
//	    double Old_Matched_block_avg = 0.0; 
//	    double Old_Unmatched_block_avg = 0.0; 
//	    double Old_Matched_block_min = 1000000.0; 
//	    double Old_Unmatched_block_min = 1000000.0; 
//	    double Old_Matched_block_max = -100000000.0; 
//	    double Old_Unmatched_block_max = -100000000.0; 
//	    
//		for (Integer blockID :oldMatchedBlockNodes.keySet()) {
//			Integer noOfAllStmts = oldMatchedBlockNodes.get(blockID).size();
//			if(noOfAllStmts!=null) {
//				Old_Matched_block_sum = Old_Matched_block_sum + noOfAllStmts;
//				if (Old_Matched_block_max<noOfAllStmts)
//					Old_Matched_block_max = noOfAllStmts;
//				if (Old_Matched_block_min>noOfAllStmts)
//					Old_Matched_block_min = noOfAllStmts;
//			}
//			
//			if(noOfAllStmts==1) {//block size 1
//				for (TraceNode step :oldMatchedBlockNodes.get(blockID)) {
//					StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
//					if(changeType.getType()==StepChangeType.IDT) {
//						if(old_kept_without_reaching_and_keeping_sameDepMatched.contains(step))//in slice
//							BlockSize1[0]++;		
//					}
//					if(changeType.getType()==StepChangeType.DAT) {
//						if(old_kept_without_reaching_and_keeping_sameDepMatched.contains(step))
//							BlockSize1[1]++;					
//					}
//				}
//			}
//			else {//block with some abstraction
//				Integer noOfAbstractedStmts_IDT = 0;
//				Integer noOfAbstractedStmts_DataDiff = 0;
//				for (TraceNode step :oldMatchedBlockNodes.get(blockID)) {
//					StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
//					if(changeType.getType()==StepChangeType.IDT) {
//						if(!old_kept_without_reaching_and_keeping_sameDepMatched.contains(step))//summarized
//							noOfAbstractedStmts_IDT = noOfAbstractedStmts_IDT + 1;
//						else 
//							Old_Matched_IDT_elements = Old_Matched_IDT_elements + 1;
//					}
//					if(changeType.getType()==StepChangeType.DAT) {
//						if(!old_kept_without_reaching_and_keeping_sameDepMatched.contains(step))//summarized
//							noOfAbstractedStmts_DataDiff = noOfAbstractedStmts_DataDiff + 1;
//						else 
//							Old_Matched_DataDiff_elements = Old_Matched_DataDiff_elements + 1;
//					}
//				}
//				
//				Old_Matched_IDT_Abstracted_stmts_sum = Old_Matched_IDT_Abstracted_stmts_sum + noOfAbstractedStmts_IDT;
//				if (Old_Matched_IDT_Abstracted_stmts_max<noOfAbstractedStmts_IDT)
//					Old_Matched_IDT_Abstracted_stmts_max = noOfAbstractedStmts_IDT;
//				if (Old_Matched_IDT_Abstracted_stmts_min>noOfAbstractedStmts_IDT)
//					Old_Matched_IDT_Abstracted_stmts_min = noOfAbstractedStmts_IDT;
//					
//				
//				Old_Matched_DataDiff_Abstracted_stmts_sum = Old_Matched_DataDiff_Abstracted_stmts_sum + noOfAbstractedStmts_DataDiff;
//				if (Old_Matched_DataDiff_Abstracted_stmts_max<noOfAbstractedStmts_DataDiff)
//					Old_Matched_DataDiff_Abstracted_stmts_max = noOfAbstractedStmts_DataDiff;
//				if (Old_Matched_DataDiff_Abstracted_stmts_min>noOfAbstractedStmts_DataDiff)
//					Old_Matched_DataDiff_Abstracted_stmts_min = noOfAbstractedStmts_DataDiff;
//					
//			}
//		}
//		Old_Matched_block_avg = Old_Matched_block_sum/oldMatchedBlockNodes.keySet().size();
//		Old_Matched_IDT_Abstracted_stmts_avg = Old_Matched_IDT_Abstracted_stmts_sum/oldMatchedBlockNodes.keySet().size()-BlockSize1[0]-BlockSize1[1];
//		Old_Matched_DataDiff_Abstracted_stmts_avg = Old_Matched_DataDiff_Abstracted_stmts_sum/oldMatchedBlockNodes.keySet().size()-BlockSize1[0]-BlockSize1[1];
//		if(Old_Matched_IDT_Abstracted_stmts_avg<0.0)
//			Old_Matched_IDT_Abstracted_stmts_avg = 0.0;
//		if(Old_Matched_DataDiff_Abstracted_stmts_avg<0.0)
//			Old_Matched_DataDiff_Abstracted_stmts_avg = 0.0;
//		
//		for (Integer blockID :oldUnmatchedBlockNodes.keySet()) {
//			Integer noOfStmts = oldUnmatchedBlockNodes.get(blockID).size();
//			if(noOfStmts!=null) {
//				Old_Unmatched_block_sum = Old_Unmatched_block_sum + noOfStmts;
//				if (Old_Unmatched_block_max<noOfStmts)
//					Old_Unmatched_block_max = noOfStmts;
//				if (Old_Unmatched_block_min>noOfStmts)
//					Old_Unmatched_block_min = noOfStmts;
//			}	
//			
//			if(noOfStmts==1) {//block size 1
//				for (TraceNode step :oldUnmatchedBlockNodes.get(blockID)) {
//					StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
//					if(changeType.getType()==StepChangeType.CTL) {
//						if(old_kept_without_reaching_and_keeping_sameDepMatched.contains(step))//in slice
//							BlockSize1[2]++;
//					}
//				}
//			}
//			else {
//				Integer noOfAbstractedStmts = 0;
//				for (TraceNode step :oldUnmatchedBlockNodes.get(blockID)) {
//					StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
//					if(changeType.getType()==StepChangeType.CTL) {
//						if(!old_kept_without_reaching_and_keeping_sameDepMatched.contains(step))//summarized
//							noOfAbstractedStmts = noOfAbstractedStmts + 1;
//						else 
//							Old_Unmatched_elements = Old_Unmatched_elements + 1;
//					}
//				}
//				Old_Unmatched_Abstracted_stmts_sum = Old_Unmatched_Abstracted_stmts_sum + noOfAbstractedStmts;
//				if (Old_Unmatched_Abstracted_stmts_max<noOfAbstractedStmts)
//					Old_Unmatched_Abstracted_stmts_max = noOfAbstractedStmts;
//				if (Old_Unmatched_Abstracted_stmts_min>noOfAbstractedStmts)
//					Old_Unmatched_Abstracted_stmts_min = noOfAbstractedStmts;
//					
//			}
//		}
//		Old_Unmatched_block_avg = Old_Unmatched_block_sum/oldUnmatchedBlockNodes.keySet().size();
//		Old_Unmatched_Abstracted_stmts_avg = Old_Unmatched_Abstracted_stmts_sum/oldUnmatchedBlockNodes.keySet().size()-BlockSize1[2];
//		if(Old_Unmatched_Abstracted_stmts_avg<0.0)
//			Old_Unmatched_Abstracted_stmts_avg = 0.0;
//	    
//	    int New_Matched_IDT_elements = 0; 	   
//	    int New_Matched_DataDiff_elements = 0; 
//	    int New_Unmatched_elements = 0; 
//	    double New_Matched_IDT_Abstracted_stmts_sum = 0.0; 
//	    double New_Matched_DataDiff_Abstracted_stmts_sum = 0.0; 
//	    double New_Unmatched_Abstracted_stmts_sum = 0.0; 
//	    double New_Matched_IDT_Abstracted_stmts_avg = 0.0; 
//	    double New_Matched_DataDiff_Abstracted_stmts_avg= 0.0; 
//	    double New_Unmatched_Abstracted_stmts_avg = 0.0; 
//	    double New_Matched_IDT_Abstracted_stmts_min = 1000000.0; 
//	    double New_Matched_DataDiff_Abstracted_stmts_min = 1000000.0; 
//	    double New_Unmatched_Abstracted_stmts_min = 1000000.0;  	    
//	    double New_Matched_IDT_Abstracted_stmts_max = -1000000.0; 
//	    double New_Matched_DataDiff_Abstracted_stmts_max = -1000000.0;
//	    double New_Unmatched_Abstracted_stmts_max = -1000000.0; 
//	    
//	   
//	    double New_Matched_block_sum = 0.0; 
//	    double New_Unmatched_block_sum = 0.0; 
//	    double New_Matched_block_avg = 0.0; 
//	    double New_Unmatched_block_avg = 0.0; 
//	    double New_Matched_block_min = 1000000.0; 
//	    double New_Unmatched_block_min = 1000000.0; 
//	    double New_Matched_block_max = -100000000.0; 
//	    double New_Unmatched_block_max = -100000000.0; 
//	    
//		for (Integer blockID :newMatchedBlockNodes.keySet()) {
//			Integer noOfAllStmts = newMatchedBlockNodes.get(blockID).size();
//			if(noOfAllStmts!=null) {
//				New_Matched_block_sum = New_Matched_block_sum + noOfAllStmts;
//				if (New_Matched_block_max<noOfAllStmts)
//					New_Matched_block_max = noOfAllStmts;
//				if (New_Matched_block_min>noOfAllStmts)
//					New_Matched_block_min = noOfAllStmts;
//			}
//			if(noOfAllStmts==1) {//block size 1
//				for (TraceNode step :newMatchedBlockNodes.get(blockID)) {
//					StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
//					if(changeType.getType()==StepChangeType.IDT) {
//						if(new_kept_without_reaching_and_keeping_sameDepMatched.contains(step))//in slice
//							BlockSize1[3]++;			
//					}
//					if(changeType.getType()==StepChangeType.DAT) {
//						if(new_kept_without_reaching_and_keeping_sameDepMatched.contains(step))
//							BlockSize1[4]++;					
//					}
//				}
//			}
//			else {
//				Integer noOfAbstractedStmts_IDT = 0;
//				Integer noOfAbstractedStmts_DataDiff = 0;
//				for (TraceNode step :newMatchedBlockNodes.get(blockID)) {
//					StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
//					if(changeType.getType()==StepChangeType.IDT) {
//						if(!new_kept_without_reaching_and_keeping_sameDepMatched.contains(step))//summarized
//							noOfAbstractedStmts_IDT = noOfAbstractedStmts_IDT + 1;
//						else 
//							New_Matched_IDT_elements = New_Matched_IDT_elements + 1;
//					}
//					if(changeType.getType()==StepChangeType.DAT) {
//						if(!new_kept_without_reaching_and_keeping_sameDepMatched.contains(step))//summarized
//							noOfAbstractedStmts_DataDiff = noOfAbstractedStmts_DataDiff + 1;
//						else 
//							New_Matched_DataDiff_elements = New_Matched_DataDiff_elements + 1;
//					}
//				}
//
//				New_Matched_IDT_Abstracted_stmts_sum = New_Matched_IDT_Abstracted_stmts_sum + noOfAbstractedStmts_IDT;
//				if (New_Matched_IDT_Abstracted_stmts_max<noOfAbstractedStmts_IDT)
//					New_Matched_IDT_Abstracted_stmts_max = noOfAbstractedStmts_IDT;
//				if (New_Matched_IDT_Abstracted_stmts_min>noOfAbstractedStmts_IDT)
//					New_Matched_IDT_Abstracted_stmts_min = noOfAbstractedStmts_IDT;
//
//				New_Matched_DataDiff_Abstracted_stmts_sum = New_Matched_DataDiff_Abstracted_stmts_sum + noOfAbstractedStmts_DataDiff;
//				if (New_Matched_DataDiff_Abstracted_stmts_max<noOfAbstractedStmts_DataDiff)
//					New_Matched_DataDiff_Abstracted_stmts_max = noOfAbstractedStmts_DataDiff;
//				if (New_Matched_DataDiff_Abstracted_stmts_min>noOfAbstractedStmts_DataDiff)
//					New_Matched_DataDiff_Abstracted_stmts_min = noOfAbstractedStmts_DataDiff;				
//			}
//		}
//		New_Matched_block_avg = New_Matched_block_sum/newMatchedBlockNodes.keySet().size();
//		New_Matched_IDT_Abstracted_stmts_avg = New_Matched_IDT_Abstracted_stmts_sum/newMatchedBlockNodes.keySet().size()-BlockSize1[3]-BlockSize1[4];
//		New_Matched_DataDiff_Abstracted_stmts_avg = New_Matched_DataDiff_Abstracted_stmts_sum/newMatchedBlockNodes.keySet().size()-BlockSize1[3]-BlockSize1[4];
//		if(New_Matched_IDT_Abstracted_stmts_avg<0.0)
//			New_Matched_IDT_Abstracted_stmts_avg = 0.0;
//		if(New_Matched_DataDiff_Abstracted_stmts_avg<0.0)
//			New_Matched_DataDiff_Abstracted_stmts_avg = 0.0;
//		
//		for (Integer blockID :newUnmatchedBlockNodes.keySet()) {
//			Integer noOfStmts = newUnmatchedBlockNodes.get(blockID).size();
//			if(noOfStmts!=null) {
//				New_Unmatched_block_sum = New_Unmatched_block_sum + noOfStmts;
//				if (New_Unmatched_block_max<noOfStmts)
//					New_Unmatched_block_max = noOfStmts;
//				if (New_Unmatched_block_min>noOfStmts)
//					New_Unmatched_block_min = noOfStmts;
//			}	
//			if(noOfStmts==1) {//block size 1
//				for (TraceNode step :newUnmatchedBlockNodes.get(blockID)) {
//					StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
//					if(changeType.getType()==StepChangeType.CTL) {
//						if(new_kept_without_reaching_and_keeping_sameDepMatched.contains(step))//in slice
//							BlockSize1[5]++;
//					}
//				}
//			}
//			else {
//				Integer noOfAbstractedStmts = 0;
//				for (TraceNode step :newUnmatchedBlockNodes.get(blockID)) {
//					StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
//					if(changeType.getType()==StepChangeType.CTL) {
//						if(!new_kept_without_reaching_and_keeping_sameDepMatched.contains(step))//summarized
//							noOfAbstractedStmts = noOfAbstractedStmts + 1;
//						else 
//							New_Unmatched_elements = New_Unmatched_elements + 1;
//					}
//				}
//				New_Unmatched_Abstracted_stmts_sum = New_Unmatched_Abstracted_stmts_sum + noOfAbstractedStmts;
//				if (New_Unmatched_Abstracted_stmts_max<noOfAbstractedStmts)
//					New_Unmatched_Abstracted_stmts_max = noOfAbstractedStmts;
//				if (New_Unmatched_Abstracted_stmts_min>noOfAbstractedStmts)
//					New_Unmatched_Abstracted_stmts_min = noOfAbstractedStmts;
//			}
//		}
//		New_Unmatched_block_avg = New_Unmatched_block_sum/newUnmatchedBlockNodes.keySet().size();
//		New_Unmatched_Abstracted_stmts_avg = New_Unmatched_Abstracted_stmts_sum/newUnmatchedBlockNodes.keySet().size()-BlockSize1[5];
//		if(New_Unmatched_Abstracted_stmts_avg<0.0)
//			New_Unmatched_Abstracted_stmts_avg = 0.0;
//		
//        if (FirstTime) {		    	
//	        String[] header = {"Bug ID", 
//	        		"Old Block Size 1 (IDT)", "Old Block Size 1 (DataDiff)", "Old Block Size 1 (CTL)", 
//	        		"Old Matched IDT elements", "Old Matched Data diff elements", "Old Unmatched elements", 
//	        		"Old Matched IDT Abstracted Stmts Sum", "Old Matched IDT Abstracted Stmts Avg", "Old Matched IDT Abstracted Stmts Min", "Old Matched IDT Abstracted Stmts Max",
//	        		"Old Matched Data Diff Abstracted Stmts Sum", "Old Matched Data Diff Abstracted Stmts Avg", "Old Matched Data Diff Abstracted Stmts Min","Old Matched Data Diff Abstracted Stmts Max",
//	        		"Old Unmatched Abstracted Stmts Sum", "Old Unmatched Abstracted Stmts Avg",	"Old Unmatched Abstracted Stmts Min", "Old Unmatched Abstracted Stmts Max",	
//	        		"Old Matched Block Number", "Old Matched Block Sum", "Old Matched Block Avg", "Old Matched Block Min","Old Matched Block Max",
//	        		"Old Unmatched Block Number", "Old Unmatched Block Sum", "Old Unmatched Block Avg", "Old Unmatched Block Min","Old Unmatched Block Max",
//	        		"New Block Size 1 (IDT)", "New Block Size 1 (DataDiff)", "New Block Size 1 (CTL)", 
//	        		"New Matched IDT elements", "New Matched Data diff elements", "New Unmatched elements", 
//	        		"New Matched IDT Abstracted Stmts Sum", "New Matched IDT Abstracted Stmts Avg", "New Matched IDT Abstracted Stmts Min", "New Matched IDT Abstracted Stmts Max",
//	        		"New Matched Data Diff Abstracted Stmts Sum", "New Matched Data Diff Abstracted Stmts Avg", "New Matched Data Diff Abstracted Stmts Min","New Matched Data Diff Abstracted Stmts Max",
//	        		"New Unmatched Abstracted Stmts Sum", "New Unmatched Abstracted Stmts Avg",	"New Unmatched Abstracted Stmts Min", "New Unmatched Abstracted Stmts Max",	
//	        		"New Matched Block Number", "New Matched Block Sum", "New Matched Block Avg", "New Matched Block Min","New Matched Block Max",
//	        		"New Unmatched Block Number","New Unmatched Block Sum", "New Unmatched Block Avg", "New Unmatched Block Min","New Unmatched Block Max"   		
//	        		};
//	        WriteToExcel(results, header, "Internal_info_without_reaching",true, true);
//	    }
//        
//        String[] detailedDataRQ3_2 = {bugID, 
//	    		String.valueOf(BlockSize1[0]), String.valueOf(BlockSize1[1]),String.valueOf(BlockSize1[2]),
//	    		String.valueOf(Old_Matched_IDT_elements), String.valueOf(Old_Matched_DataDiff_elements), String.valueOf(Old_Unmatched_elements),
//	    		String.valueOf(Old_Matched_IDT_Abstracted_stmts_sum), String.valueOf(Old_Matched_IDT_Abstracted_stmts_avg), String.valueOf(Old_Matched_IDT_Abstracted_stmts_min), String.valueOf(Old_Matched_IDT_Abstracted_stmts_max),
//	    		String.valueOf(Old_Matched_DataDiff_Abstracted_stmts_sum), String.valueOf(Old_Matched_DataDiff_Abstracted_stmts_avg), String.valueOf(Old_Matched_DataDiff_Abstracted_stmts_min), String.valueOf(Old_Matched_DataDiff_Abstracted_stmts_max),
//	    		String.valueOf(Old_Unmatched_Abstracted_stmts_sum), String.valueOf(Old_Unmatched_Abstracted_stmts_avg), String.valueOf(Old_Unmatched_Abstracted_stmts_min), String.valueOf(Old_Unmatched_Abstracted_stmts_max),
//	    		String.valueOf(oldMatchedBlockNodes.keySet().size()),String.valueOf(Old_Matched_block_sum), String.valueOf(Old_Matched_block_avg), String.valueOf(Old_Matched_block_min), String.valueOf(Old_Matched_block_max),
//	    		String.valueOf(oldUnmatchedBlockNodes.keySet().size()), String.valueOf(Old_Unmatched_block_sum), String.valueOf(Old_Unmatched_block_avg), String.valueOf(Old_Unmatched_block_min), String.valueOf(Old_Unmatched_block_max),
//	    		String.valueOf(BlockSize1[3]), String.valueOf(BlockSize1[4]),String.valueOf(BlockSize1[5]), 
//	    		String.valueOf(New_Matched_IDT_elements), String.valueOf(New_Matched_DataDiff_elements), String.valueOf(New_Unmatched_elements),
//	    		String.valueOf(New_Matched_IDT_Abstracted_stmts_sum), String.valueOf(New_Matched_IDT_Abstracted_stmts_avg), String.valueOf(New_Matched_IDT_Abstracted_stmts_min), String.valueOf(New_Matched_IDT_Abstracted_stmts_max),
//	    		String.valueOf(New_Matched_DataDiff_Abstracted_stmts_sum), String.valueOf(New_Matched_DataDiff_Abstracted_stmts_avg), String.valueOf(New_Matched_DataDiff_Abstracted_stmts_min), String.valueOf(New_Matched_DataDiff_Abstracted_stmts_max),
//	    		String.valueOf(New_Unmatched_Abstracted_stmts_sum), String.valueOf(New_Unmatched_Abstracted_stmts_avg), String.valueOf(New_Unmatched_Abstracted_stmts_min), String.valueOf(New_Unmatched_Abstracted_stmts_max),
//	    		String.valueOf(newMatchedBlockNodes.keySet().size()), String.valueOf(New_Matched_block_sum),String.valueOf(New_Matched_block_avg), String.valueOf(New_Matched_block_min), String.valueOf(New_Matched_block_max),
//	    		String.valueOf(newUnmatchedBlockNodes.keySet().size()), String.valueOf(New_Unmatched_block_sum),String.valueOf(New_Unmatched_block_avg), String.valueOf(New_Unmatched_block_min), String.valueOf(New_Unmatched_block_max)  
//        };
//	    WriteToExcel(results,detailedDataRQ3_2,"Internal_info_without_reaching",true, false);
//		    
//	    
//	    
	     		
		/////////////////#######////#######////#######////#######////#######////#######
		/////////////////#######////#######////#######////#######////#######////#######
	       /////////////////#######////#######////#######////#######////#######////#######
	       /////////////////#######////#######////#######////#######////#######////#######
	       
//           boolean Einspect5_CoReX = CanFindTheBug(5, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	    
//           boolean Einspect10_CoReX = CanFindTheBug(10, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	       
//           boolean Einspect30_CoReX = CanFindTheBug(30, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	       
//	       boolean Einspect50_CoReX = CanFindTheBug(50, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	  
////	       boolean Einspect100_CoReX = CanFindTheBug(100, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	  
//	       boolean Einspect200_CoReX = CanFindTheBug(200, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	       
////	       boolean Einspect500_CoReX = CanFindTheBug(500, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	
//	       
//	       
//	       boolean Einspect30_InPreSSPlus = CanFindTheBug(30, old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus, new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus,old_retained,new_retained);	       
//	       boolean Einspect50_InPreSSPlus = CanFindTheBug(50, old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus, new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus,old_retained,new_retained);
//	       boolean Einspect200_InPreSSPlus = CanFindTheBug(200, old_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus, new_kept_without_reaching_and_keeping_sameDepMatched_inpressPlus,old_retained,new_retained);	

	       
//	       int traversed_old_CoReX = CalculateWastedEffort(old_kept_without_reaching_and_keeping_sameDepMatched,old_retained);
//	       int traversed_new_CoReX = CalculateWastedEffort(new_kept_without_reaching_and_keeping_sameDepMatched,new_retained);
//	       
//	       double wasted_effort_old_CoReX = ((double)traversed_old_CoReX/oldTrace.getExecutionList().size())*100.0;
//	       double wasted_effort_new_CoRex = ((double)traversed_new_CoReX/newTrace.getExecutionList().size())*100.0;
	       


//	       if (FirstTime) {		    	
//		        String[] header = {"Bug ID", 
//		        		"Einspect@30-inpressPlus",
//		        		"Einspect@50-inpressPlus",
//		        		"Einspect@200-inpressPlus",
////		        		"Einspect@5-CoReX", 
////		        		"Einspect@10-CoReX", 
//		        		"Einspect@30-CoReX",
//		        		"Einspect@50-CoReX",
////		        		"Einspect@100-CoReX",
//		        		"Einspect@200-CoReX"
////		        		"Einspect@500-CoReX",
////		        		"#Traversed Old Stmt-CoReX","#Traversed New Stmt-CoReX",
////		        		"Exam% Old-CoReX","Exam% New-CoReX"	       
//		        		};
//		        WriteToExcel(results, header, "E_inspect",true, true);
//		    }
//		    String[] detailedDataRQ4 = {bugID, 
//		    		String.valueOf(Einspect30_InPreSSPlus),
//		    		String.valueOf(Einspect50_InPreSSPlus),
//		    		String.valueOf(Einspect200_InPreSSPlus),
////		    		String.valueOf(Einspect5_CoReX),
////		    		String.valueOf(Einspect10_CoReX),
//		    		String.valueOf(Einspect30_CoReX),
//		    		String.valueOf(Einspect50_CoReX),
////		    		String.valueOf(Einspect100_CoReX),
//		    		String.valueOf(Einspect200_CoReX),
////		    		String.valueOf(Einspect500_CoReX),
////		    		String.valueOf(traversed_old_CoReX),String.valueOf(traversed_new_CoReX),
////		    		String.valueOf(wasted_effort_old_CoReX),String.valueOf(wasted_effort_new_CoRex)
//		    };
//		    WriteToExcel(results,detailedDataRQ4,"E_inspect",true, false);
						
		       
	           
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
		System.out.println("##############Finish##############");
		
	}
/////////////////#######////#######////#######////#######////#######////#######
/////////////////#######////#######////#######////#######////#######////#######
	private void PrintPaperResults(TestCase tc, String basePath, String projectName, String bugID, StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher, 
			Trace newTrace,Trace oldTrace, List<TraceNode> new_sync_slice, List<TraceNode> old_sync_slice, 
			List<TraceNode> new_kept_with_reaching_and_keeping_sameDepMatched,List<TraceNode> old_kept_with_reaching_and_keeping_sameDepMatched, 
			List<TraceNode> new_kept_without_reaching_and_keeping_sameDepMatched, List<TraceNode> old_kept_without_reaching_and_keeping_sameDepMatched,  
			List<TraceNode> new_retained, List<TraceNode> old_retained,
			HashMap<Integer, List<TraceNode>> newMatchedBlockNodes, HashMap<Integer, List<TraceNode>> oldMatchedBlockNodes,
			HashMap<Integer, List<TraceNode>> newUnmatchedBlockNodes, HashMap<Integer, List<TraceNode>> oldUnmatchedBlockNodes,
			int[] BlockSize1,
			HashMap<TraceNode, List<TraceNode>> new_expandingFunctions, HashMap<TraceNode, List<TraceNode>> old_expandingFunctions,
			HashMap<TraceNode, List<TraceNode>> new_expandingFunctions_keeping_reaching, HashMap<TraceNode, List<TraceNode>> old_expandingFunctions_keeping_reaching,
			BiMap<TraceNode, String> newSlicer4J,BiMap<TraceNode, String> oldSlicer4J, 
			HashMap<String, List<String>> newSlicer4JBytecodeMapping,
			HashMap<String, List<String>> oldSlicer4JBytecodeMapping) {
		

		Path path = Paths.get(basePath+"/results");
		if(!Files.exists(path)) 
			new File(basePath+"/results").mkdirs();
		
		String results = basePath+"/results/"+projectName+"CoReX_Paper_Results.xlsx";
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

	    
	    if (FirstTime) {		    	
	        String[] header = {"Bug ID", 
	        		"Old Trace" , "Old Sync Slice", "Old Retained", "Old CoReX (without internal reaching defs)", "Old CoReX (with internal reaching defs)", 
	        		"New Trace" , "New Sync Slice", "New Retained", "New CoReX (without internal reaching defs)", "New CoReX (with internal reaching defs)", 
	        		};
	        WriteToExcel(results, header, "Main_Stats",true,true);
	    }
	    
	    String[] detailedDataRQ2 = {bugID, 
	    		String.valueOf(oldTrace.getExecutionList().size()), String.valueOf(old_sync_slice.size()), String.valueOf(old_retained.size()), String.valueOf(old_kept_without_reaching_and_keeping_sameDepMatched.size()), String.valueOf(old_kept_with_reaching_and_keeping_sameDepMatched.size()),
	    		String.valueOf(newTrace.getExecutionList().size()), String.valueOf(new_sync_slice.size()), String.valueOf(new_retained.size()), String.valueOf(new_kept_without_reaching_and_keeping_sameDepMatched.size()), String.valueOf(new_kept_with_reaching_and_keeping_sameDepMatched.size())
	    		};
	    WriteToExcel(results,detailedDataRQ2,"Main_Stats",true, false);
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######
	    /////////////////#######////#######////#######////#######////#######////#######

	    int Old_Matched_IDT_elements = 0; 	   
	    int Old_Matched_DataDiff_elements = 0; 
	    int Old_Unmatched_elements = 0; 
	    double Old_Matched_IDT_Abstracted_stmts_sum = 0.0; 
	    double Old_Matched_DataDiff_Abstracted_stmts_sum = 0.0; 
	    double Old_Unmatched_Abstracted_stmts_sum = 0.0; 
	    double Old_Matched_IDT_Abstracted_stmts_avg = 0.0; 
	    double Old_Matched_DataDiff_Abstracted_stmts_avg= 0.0; 
	    double Old_Unmatched_Abstracted_stmts_avg = 0.0; 
	    double Old_Matched_IDT_Abstracted_stmts_min = 1000000.0; 
	    double Old_Matched_DataDiff_Abstracted_stmts_min = 1000000.0; 
	    double Old_Unmatched_Abstracted_stmts_min = 1000000.0;  	    
	    double Old_Matched_IDT_Abstracted_stmts_max = -1000000.0; 
	    double Old_Matched_DataDiff_Abstracted_stmts_max = -1000000.0;
	    double Old_Unmatched_Abstracted_stmts_max = -1000000.0; 
	    
	    for (TraceNode step :old_expandingFunctions.keySet()) {
	    	StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
	    	if(changeType.getType()==StepChangeType.IDT) {
	    		Old_Matched_IDT_elements++;
	    		int noOfStmts = old_expandingFunctions.get(step).size();
		    	Old_Matched_IDT_Abstracted_stmts_sum += noOfStmts;
					if (Old_Matched_IDT_Abstracted_stmts_max<noOfStmts)
						Old_Matched_IDT_Abstracted_stmts_max = noOfStmts;
					if (Old_Matched_IDT_Abstracted_stmts_min>noOfStmts)
						Old_Matched_IDT_Abstracted_stmts_min = noOfStmts;
			}
	    	else if(changeType.getType()==StepChangeType.DAT) {
	    		Old_Matched_DataDiff_elements++;
	    		int noOfStmts = old_expandingFunctions.get(step).size();
		    	Old_Matched_DataDiff_Abstracted_stmts_sum += noOfStmts;
					if (Old_Matched_DataDiff_Abstracted_stmts_max<noOfStmts)
						Old_Matched_DataDiff_Abstracted_stmts_max = noOfStmts;
					if (Old_Matched_DataDiff_Abstracted_stmts_min>noOfStmts)
						Old_Matched_DataDiff_Abstracted_stmts_min = noOfStmts;
			}
	    	else if(changeType.getType()==StepChangeType.CTL) {
	    		Old_Unmatched_elements++;
	    		int noOfStmts = old_expandingFunctions.get(step).size();
		    	Old_Unmatched_Abstracted_stmts_sum += noOfStmts;
					if (Old_Unmatched_Abstracted_stmts_max<noOfStmts)
						Old_Unmatched_Abstracted_stmts_max = noOfStmts;
					if (Old_Unmatched_Abstracted_stmts_min>noOfStmts)
						Old_Unmatched_Abstracted_stmts_min = noOfStmts;
			}
	    }
	    Old_Matched_IDT_Abstracted_stmts_avg = Old_Matched_IDT_Abstracted_stmts_sum/Old_Matched_IDT_elements;
	    Old_Matched_DataDiff_Abstracted_stmts_avg = Old_Matched_DataDiff_Abstracted_stmts_sum/Old_Matched_DataDiff_elements;
	    Old_Unmatched_Abstracted_stmts_avg = Old_Unmatched_Abstracted_stmts_sum/Old_Unmatched_elements;
	    
	    double Old_Matched_block_sum = 0.0; 
	    double Old_Unmatched_block_sum = 0.0; 
	    double Old_Matched_block_avg = 0.0; 
	    double Old_Unmatched_block_avg = 0.0; 
	    double Old_Matched_block_min = 1000000.0; 
	    double Old_Unmatched_block_min = 1000000.0; 
	    double Old_Matched_block_max = -100000000.0; 
	    double Old_Unmatched_block_max = -100000000.0; 
	    
		for (Integer blockID :oldMatchedBlockNodes.keySet()) {
			Integer noOfStmts = oldMatchedBlockNodes.get(blockID).size();
			if(noOfStmts!=null) {
				Old_Matched_block_sum = Old_Matched_block_sum + noOfStmts;
				if (Old_Matched_block_max<noOfStmts)
					Old_Matched_block_max = noOfStmts;
				if (Old_Matched_block_min>noOfStmts)
					Old_Matched_block_min = noOfStmts;
			}			
		}
		Old_Matched_block_avg = Old_Matched_block_sum/oldMatchedBlockNodes.keySet().size();
		
		for (Integer blockID :oldUnmatchedBlockNodes.keySet()) {
			Integer noOfStmts = oldUnmatchedBlockNodes.get(blockID).size();
			if(noOfStmts!=null) {
				Old_Unmatched_block_sum = Old_Unmatched_block_sum + noOfStmts;
				if (Old_Unmatched_block_max<noOfStmts)
					Old_Unmatched_block_max = noOfStmts;
				if (Old_Unmatched_block_min>noOfStmts)
					Old_Unmatched_block_min = noOfStmts;
			}			
		}
		Old_Unmatched_block_avg = Old_Unmatched_block_sum/oldUnmatchedBlockNodes.keySet().size();
 	    
	    
		int New_Matched_IDT_elements = 0; 	   
	    int New_Matched_DataDiff_elements = 0; 
	    int New_Unmatched_elements = 0; 
	    double New_Matched_IDT_Abstracted_stmts_sum = 0.0; 
	    double New_Matched_DataDiff_Abstracted_stmts_sum = 0.0; 
	    double New_Unmatched_Abstracted_stmts_sum = 0.0; 
	    double New_Matched_IDT_Abstracted_stmts_avg = 0.0; 
	    double New_Matched_DataDiff_Abstracted_stmts_avg= 0.0; 
	    double New_Unmatched_Abstracted_stmts_avg = 0.0; 
	    double New_Matched_IDT_Abstracted_stmts_min = 1000000.0; 
	    double New_Matched_DataDiff_Abstracted_stmts_min = 1000000.0; 
	    double New_Unmatched_Abstracted_stmts_min = 1000000.0;  	    
	    double New_Matched_IDT_Abstracted_stmts_max = -1000000.0; 
	    double New_Matched_DataDiff_Abstracted_stmts_max = -1000000.0;
	    double New_Unmatched_Abstracted_stmts_max = -1000000.0; 
	    
	    for (TraceNode step :new_expandingFunctions.keySet()) {
	    	StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
	    	if(changeType.getType()==StepChangeType.IDT) {
	    		New_Matched_IDT_elements++;
	    		int noOfStmts = new_expandingFunctions.get(step).size();
		    	New_Matched_IDT_Abstracted_stmts_sum += noOfStmts;
					if (New_Matched_IDT_Abstracted_stmts_max<noOfStmts)
						New_Matched_IDT_Abstracted_stmts_max = noOfStmts;
					if (New_Matched_IDT_Abstracted_stmts_min>noOfStmts)
						New_Matched_IDT_Abstracted_stmts_min = noOfStmts;
			}
	    	else if(changeType.getType()==StepChangeType.DAT) {
	    		New_Matched_DataDiff_elements++;
	    		int noOfStmts = new_expandingFunctions.get(step).size();
		    	New_Matched_DataDiff_Abstracted_stmts_sum += noOfStmts;
					if (New_Matched_DataDiff_Abstracted_stmts_max<noOfStmts)
						New_Matched_DataDiff_Abstracted_stmts_max = noOfStmts;
					if (New_Matched_DataDiff_Abstracted_stmts_min>noOfStmts)
						New_Matched_DataDiff_Abstracted_stmts_min = noOfStmts;
			}
	    	else if(changeType.getType()==StepChangeType.CTL) {
	    		New_Unmatched_elements++;
	    		int noOfStmts = new_expandingFunctions.get(step).size();
		    	New_Unmatched_Abstracted_stmts_sum += noOfStmts;
					if (New_Unmatched_Abstracted_stmts_max<noOfStmts)
						New_Unmatched_Abstracted_stmts_max = noOfStmts;
					if (New_Unmatched_Abstracted_stmts_min>noOfStmts)
						New_Unmatched_Abstracted_stmts_min = noOfStmts;
			}
	    }
	    New_Matched_IDT_Abstracted_stmts_avg = New_Matched_IDT_Abstracted_stmts_sum/New_Matched_IDT_elements;
	    New_Matched_DataDiff_Abstracted_stmts_avg = New_Matched_DataDiff_Abstracted_stmts_sum/New_Matched_DataDiff_elements;
	    New_Unmatched_Abstracted_stmts_avg = New_Unmatched_Abstracted_stmts_sum/New_Unmatched_elements;
	    
	    double New_Matched_block_sum = 0.0; 
	    double New_Unmatched_block_sum = 0.0; 
	    double New_Matched_block_avg = 0.0; 
	    double New_Unmatched_block_avg = 0.0; 
	    double New_Matched_block_min = 1000000.0; 
	    double New_Unmatched_block_min = 1000000.0; 
	    double New_Matched_block_max = -100000000.0; 
	    double New_Unmatched_block_max = -100000000.0; 
	    
		for (Integer blockID :newMatchedBlockNodes.keySet()) {
			Integer noOfStmts = newMatchedBlockNodes.get(blockID).size();
			if(noOfStmts!=null) {
				New_Matched_block_sum = New_Matched_block_sum + noOfStmts;
				if (New_Matched_block_max<noOfStmts)
					New_Matched_block_max = noOfStmts;
				if (New_Matched_block_min>noOfStmts)
					New_Matched_block_min = noOfStmts;
			}			
		}
		New_Matched_block_avg = New_Matched_block_sum/newMatchedBlockNodes.keySet().size();
		
		for (Integer blockID :newUnmatchedBlockNodes.keySet()) {
			Integer noOfStmts = newUnmatchedBlockNodes.get(blockID).size();
			if(noOfStmts!=null) {
				New_Unmatched_block_sum = New_Unmatched_block_sum + noOfStmts;
				if (New_Unmatched_block_max<noOfStmts)
					New_Unmatched_block_max = noOfStmts;
				if (New_Unmatched_block_min>noOfStmts)
					New_Unmatched_block_min = noOfStmts;
			}			
		}
		New_Unmatched_block_avg = New_Unmatched_block_sum/newUnmatchedBlockNodes.keySet().size();
 	    
        if (FirstTime) {		    	
	        String[] header = {"Bug ID", 
	        		"Old Block Size 1", "Old Matched IDT elements", "Old Matched Data diff elements", "Old Unmatched elements", 
	        		"Old Matched IDT Abstracted Stmts Sum", "Old Matched IDT Abstracted Stmts Avg", "Old Matched IDT Abstracted Stmts Min", "Old Matched IDT Abstracted Stmts Max",
	        		"Old Matched Data Diff Abstracted Stmts Sum", "Old Matched Data Diff Abstracted Stmts Avg", "Old Matched Data Diff Abstracted Stmts Min","Old Matched Data Diff Abstracted Stmts Max",
	        		"Old Unmatched Abstracted Stmts Sum", "Old Unmatched Abstracted Stmts Avg",	"Old Unmatched Abstracted Stmts Min", "Old Unmatched Abstracted Stmts Max",	
	        		"Old Matched Block Sum", "Old Matched Block Avg", "Old Matched Block Min","Old Matched Block Max",
	        		"Old Unmatched Block Sum", "Old Unmatched Block Avg", "Old Unmatched Block Min","Old Unmatched Block Max",
	        		"New Block Size 1", "New Matched IDT elements", "New Matched Data diff elements", "New Unmatched elements", 
	        		"New Matched IDT Abstracted Stmts Sum", "New Matched IDT Abstracted Stmts Avg", "New Matched IDT Abstracted Stmts Min", "New Matched IDT Abstracted Stmts Max",
	        		"New Matched Data Diff Abstracted Stmts Sum", "New Matched Data Diff Abstracted Stmts Avg", "New Matched Data Diff Abstracted Stmts Min","New Matched Data Diff Abstracted Stmts Max",
	        		"New Unmatched Abstracted Stmts Sum", "New Unmatched Abstracted Stmts Avg",	"New Unmatched Abstracted Stmts Min", "New Unmatched Abstracted Stmts Max",	
	        		"New Matched Block Sum", "New Matched Block Avg", "New Matched Block Min","New Matched Block Max",
	        		"New Unmatched Block Sum", "New Unmatched Block Avg", "New Unmatched Block Min","New Unmatched Block Max"   		
	        		};
	        WriteToExcel(results, header, "Internal_info_without_reaching",true, true);
	    }
        
        String[] detailedDataRQ3_2 = {bugID, 
	    		String.valueOf(BlockSize1[0]), String.valueOf(Old_Matched_IDT_elements), String.valueOf(Old_Matched_DataDiff_elements), String.valueOf(Old_Unmatched_elements),
	    		String.valueOf(Old_Matched_IDT_Abstracted_stmts_sum), String.valueOf(Old_Matched_IDT_Abstracted_stmts_avg), String.valueOf(Old_Matched_IDT_Abstracted_stmts_min), String.valueOf(Old_Matched_IDT_Abstracted_stmts_max),
	    		String.valueOf(Old_Matched_DataDiff_Abstracted_stmts_sum), String.valueOf(Old_Matched_DataDiff_Abstracted_stmts_avg), String.valueOf(Old_Matched_DataDiff_Abstracted_stmts_min), String.valueOf(Old_Matched_DataDiff_Abstracted_stmts_max),
	    		String.valueOf(Old_Unmatched_Abstracted_stmts_sum), String.valueOf(Old_Unmatched_Abstracted_stmts_avg), String.valueOf(Old_Unmatched_Abstracted_stmts_min), String.valueOf(Old_Unmatched_Abstracted_stmts_max),
	    		String.valueOf(Old_Matched_block_sum), String.valueOf(Old_Matched_block_avg), String.valueOf(Old_Matched_block_min), String.valueOf(Old_Matched_block_max),
	    		String.valueOf(Old_Unmatched_block_sum), String.valueOf(Old_Unmatched_block_avg), String.valueOf(Old_Unmatched_block_min), String.valueOf(Old_Unmatched_block_max),
	    		String.valueOf(BlockSize1[1]), String.valueOf(New_Matched_IDT_elements), String.valueOf(New_Matched_DataDiff_elements), String.valueOf(New_Unmatched_elements),
	    		String.valueOf(New_Matched_IDT_Abstracted_stmts_sum), String.valueOf(New_Matched_IDT_Abstracted_stmts_avg), String.valueOf(New_Matched_IDT_Abstracted_stmts_min), String.valueOf(New_Matched_IDT_Abstracted_stmts_max),
	    		String.valueOf(New_Matched_DataDiff_Abstracted_stmts_sum), String.valueOf(New_Matched_DataDiff_Abstracted_stmts_avg), String.valueOf(New_Matched_DataDiff_Abstracted_stmts_min), String.valueOf(New_Matched_DataDiff_Abstracted_stmts_max),
	    		String.valueOf(New_Unmatched_Abstracted_stmts_sum), String.valueOf(New_Unmatched_Abstracted_stmts_avg), String.valueOf(New_Unmatched_Abstracted_stmts_min), String.valueOf(New_Unmatched_Abstracted_stmts_max),
	    		String.valueOf(New_Matched_block_sum), String.valueOf(New_Matched_block_avg), String.valueOf(New_Matched_block_min), String.valueOf(New_Matched_block_max),
	    		String.valueOf(New_Unmatched_block_sum), String.valueOf(New_Unmatched_block_avg), String.valueOf(New_Unmatched_block_min), String.valueOf(New_Unmatched_block_max)  
        };
	    WriteToExcel(results,detailedDataRQ3_2,"Internal_info_without_reaching",true, false);
	    
	    
	     Old_Matched_IDT_elements = 0; 	   
	     Old_Matched_DataDiff_elements = 0; 
	     Old_Unmatched_elements = 0; 
	     Old_Matched_IDT_Abstracted_stmts_sum = 0.0; 
	     Old_Matched_DataDiff_Abstracted_stmts_sum = 0.0; 
	     Old_Unmatched_Abstracted_stmts_sum = 0.0; 
	     Old_Matched_IDT_Abstracted_stmts_avg = 0.0; 
	     Old_Matched_DataDiff_Abstracted_stmts_avg= 0.0; 
	     Old_Unmatched_Abstracted_stmts_avg = 0.0; 
	     Old_Matched_IDT_Abstracted_stmts_min = 1000000.0; 
	     Old_Matched_DataDiff_Abstracted_stmts_min = 1000000.0; 
	     Old_Unmatched_Abstracted_stmts_min = 1000000.0;  	    
	     Old_Matched_IDT_Abstracted_stmts_max = -1000000.0; 
	     Old_Matched_DataDiff_Abstracted_stmts_max = -1000000.0;
	     Old_Unmatched_Abstracted_stmts_max = -1000000.0; 
	    
	    for (TraceNode step :old_expandingFunctions_keeping_reaching.keySet()) {
	    	StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
	    	if(changeType.getType()==StepChangeType.IDT) {
	    		Old_Matched_IDT_elements++;
	    		int noOfStmts = old_expandingFunctions.get(step).size();
		    	Old_Matched_IDT_Abstracted_stmts_sum += noOfStmts;
					if (Old_Matched_IDT_Abstracted_stmts_max<noOfStmts)
						Old_Matched_IDT_Abstracted_stmts_max = noOfStmts;
					if (Old_Matched_IDT_Abstracted_stmts_min>noOfStmts)
						Old_Matched_IDT_Abstracted_stmts_min = noOfStmts;
			}
	    	else if(changeType.getType()==StepChangeType.DAT) {
	    		Old_Matched_DataDiff_elements++;
	    		int noOfStmts = old_expandingFunctions.get(step).size();
		    	Old_Matched_DataDiff_Abstracted_stmts_sum += noOfStmts;
					if (Old_Matched_DataDiff_Abstracted_stmts_max<noOfStmts)
						Old_Matched_DataDiff_Abstracted_stmts_max = noOfStmts;
					if (Old_Matched_DataDiff_Abstracted_stmts_min>noOfStmts)
						Old_Matched_DataDiff_Abstracted_stmts_min = noOfStmts;
			}
	    	else if(changeType.getType()==StepChangeType.CTL) {
	    		Old_Unmatched_elements++;
	    		int noOfStmts = old_expandingFunctions.get(step).size();
		    	Old_Unmatched_Abstracted_stmts_sum += noOfStmts;
					if (Old_Unmatched_Abstracted_stmts_max<noOfStmts)
						Old_Unmatched_Abstracted_stmts_max = noOfStmts;
					if (Old_Unmatched_Abstracted_stmts_min>noOfStmts)
						Old_Unmatched_Abstracted_stmts_min = noOfStmts;
			}
	    }
	    Old_Matched_IDT_Abstracted_stmts_avg = Old_Matched_IDT_Abstracted_stmts_sum/Old_Matched_IDT_elements;
	    Old_Matched_DataDiff_Abstracted_stmts_avg = Old_Matched_DataDiff_Abstracted_stmts_sum/Old_Matched_DataDiff_elements;
	    Old_Unmatched_Abstracted_stmts_avg = Old_Unmatched_Abstracted_stmts_sum/Old_Unmatched_elements;
	    
	    
		 New_Matched_IDT_elements = 0; 	   
	     New_Matched_DataDiff_elements = 0; 
	     New_Unmatched_elements = 0; 
	     New_Matched_IDT_Abstracted_stmts_sum = 0.0; 
	     New_Matched_DataDiff_Abstracted_stmts_sum = 0.0; 
	     New_Unmatched_Abstracted_stmts_sum = 0.0; 
	     New_Matched_IDT_Abstracted_stmts_avg = 0.0; 
	     New_Matched_DataDiff_Abstracted_stmts_avg= 0.0; 
	     New_Unmatched_Abstracted_stmts_avg = 0.0; 
	     New_Matched_IDT_Abstracted_stmts_min = 1000000.0; 
	     New_Matched_DataDiff_Abstracted_stmts_min = 1000000.0; 
	     New_Unmatched_Abstracted_stmts_min = 1000000.0;  	    
	     New_Matched_IDT_Abstracted_stmts_max = -1000000.0; 
	     New_Matched_DataDiff_Abstracted_stmts_max = -1000000.0;
	     New_Unmatched_Abstracted_stmts_max = -1000000.0; 
	    
	    for (TraceNode step :new_expandingFunctions_keeping_reaching.keySet()) {
	    	StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
	    	if(changeType.getType()==StepChangeType.IDT) {
	    		New_Matched_IDT_elements++;
	    		int noOfStmts = new_expandingFunctions.get(step).size();
		    	New_Matched_IDT_Abstracted_stmts_sum += noOfStmts;
					if (New_Matched_IDT_Abstracted_stmts_max<noOfStmts)
						New_Matched_IDT_Abstracted_stmts_max = noOfStmts;
					if (New_Matched_IDT_Abstracted_stmts_min>noOfStmts)
						New_Matched_IDT_Abstracted_stmts_min = noOfStmts;
			}
	    	else if(changeType.getType()==StepChangeType.DAT) {
	    		New_Matched_DataDiff_elements++;
	    		int noOfStmts = new_expandingFunctions.get(step).size();
		    	New_Matched_DataDiff_Abstracted_stmts_sum += noOfStmts;
					if (New_Matched_DataDiff_Abstracted_stmts_max<noOfStmts)
						New_Matched_DataDiff_Abstracted_stmts_max = noOfStmts;
					if (New_Matched_DataDiff_Abstracted_stmts_min>noOfStmts)
						New_Matched_DataDiff_Abstracted_stmts_min = noOfStmts;
			}
	    	else if(changeType.getType()==StepChangeType.CTL) {
	    		New_Unmatched_elements++;
	    		int noOfStmts = new_expandingFunctions.get(step).size();
		    	New_Unmatched_Abstracted_stmts_sum += noOfStmts;
					if (New_Unmatched_Abstracted_stmts_max<noOfStmts)
						New_Unmatched_Abstracted_stmts_max = noOfStmts;
					if (New_Unmatched_Abstracted_stmts_min>noOfStmts)
						New_Unmatched_Abstracted_stmts_min = noOfStmts;
			}
	    }
	    New_Matched_IDT_Abstracted_stmts_avg = New_Matched_IDT_Abstracted_stmts_sum/New_Matched_IDT_elements;
	    New_Matched_DataDiff_Abstracted_stmts_avg = New_Matched_DataDiff_Abstracted_stmts_sum/New_Matched_DataDiff_elements;
	    New_Unmatched_Abstracted_stmts_avg = New_Unmatched_Abstracted_stmts_sum/New_Unmatched_elements;
	    
	   
        if (FirstTime) {		    	
	        String[] header = {"Bug ID", 
	        		"Old Block Size 1", "Old Matched IDT elements", "Old Matched Data diff elements", "Old Unmatched elements", 
	        		"Old Matched IDT Abstracted Stmts Sum", "Old Matched IDT Abstracted Stmts Avg", "Old Matched IDT Abstracted Stmts Min", "Old Matched IDT Abstracted Stmts Max",
	        		"Old Matched Data Diff Abstracted Stmts Sum", "Old Matched Data Diff Abstracted Stmts Avg", "Old Matched Data Diff Abstracted Stmts Min","Old Matched Data Diff Abstracted Stmts Max",
	        		"Old Unmatched Abstracted Stmts Sum", "Old Unmatched Abstracted Stmts Avg",	"Old Unmatched Abstracted Stmts Min", "Old Unmatched Abstracted Stmts Max",	
	        		"New Block Size 1", "New Matched IDT elements", "New Matched Data diff elements", "New Unmatched elements", 
	        		"New Matched IDT Abstracted Stmts Sum", "New Matched IDT Abstracted Stmts Avg", "New Matched IDT Abstracted Stmts Min", "New Matched IDT Abstracted Stmts Max",
	        		"New Matched Data Diff Abstracted Stmts Sum", "New Matched Data Diff Abstracted Stmts Avg", "New Matched Data Diff Abstracted Stmts Min","New Matched Data Diff Abstracted Stmts Max",
	        		"New Unmatched Abstracted Stmts Sum", "New Unmatched Abstracted Stmts Avg",	"New Unmatched Abstracted Stmts Min", "New Unmatched Abstracted Stmts Max"	  		
	        		};
	        WriteToExcel(results, header, "Internal_info_with_reaching",true, true);
	    }
        String[] detailedDataRQ3_2_with = {bugID, 
	    		String.valueOf(BlockSize1[0]), String.valueOf(Old_Matched_IDT_elements), String.valueOf(Old_Matched_DataDiff_elements), String.valueOf(Old_Unmatched_elements),
	    		String.valueOf(Old_Matched_IDT_Abstracted_stmts_sum), String.valueOf(Old_Matched_IDT_Abstracted_stmts_avg), String.valueOf(Old_Matched_IDT_Abstracted_stmts_min), String.valueOf(Old_Matched_IDT_Abstracted_stmts_max),
	    		String.valueOf(Old_Matched_DataDiff_Abstracted_stmts_sum), String.valueOf(Old_Matched_DataDiff_Abstracted_stmts_avg), String.valueOf(Old_Matched_DataDiff_Abstracted_stmts_min), String.valueOf(Old_Matched_DataDiff_Abstracted_stmts_max),
	    		String.valueOf(Old_Unmatched_Abstracted_stmts_sum), String.valueOf(Old_Unmatched_Abstracted_stmts_avg), String.valueOf(Old_Unmatched_Abstracted_stmts_min), String.valueOf(Old_Unmatched_Abstracted_stmts_max),
	    		String.valueOf(BlockSize1[1]), String.valueOf(New_Matched_IDT_elements), String.valueOf(New_Matched_DataDiff_elements), String.valueOf(New_Unmatched_elements),
	    		String.valueOf(New_Matched_IDT_Abstracted_stmts_sum), String.valueOf(New_Matched_IDT_Abstracted_stmts_avg), String.valueOf(New_Matched_IDT_Abstracted_stmts_min), String.valueOf(New_Matched_IDT_Abstracted_stmts_max),
	    		String.valueOf(New_Matched_DataDiff_Abstracted_stmts_sum), String.valueOf(New_Matched_DataDiff_Abstracted_stmts_avg), String.valueOf(New_Matched_DataDiff_Abstracted_stmts_min), String.valueOf(New_Matched_DataDiff_Abstracted_stmts_max),
	    		String.valueOf(New_Unmatched_Abstracted_stmts_sum), String.valueOf(New_Unmatched_Abstracted_stmts_avg), String.valueOf(New_Unmatched_Abstracted_stmts_min), String.valueOf(New_Unmatched_Abstracted_stmts_max)
        };
	    WriteToExcel(results,detailedDataRQ3_2_with,"Internal_info_with_reaching",true, false);
					
		/////////////////#######////#######////#######////#######////#######////#######
		/////////////////#######////#######////#######////#######////#######////#######
	       /////////////////#######////#######////#######////#######////#######////#######
	       /////////////////#######////#######////#######////#######////#######////#######
	       
           boolean Einspect5_CoReX = CanFindTheBug(5, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	    
           boolean Einspect10_CoReX = CanFindTheBug(10, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	       
           boolean Einspect30_CoReX = CanFindTheBug(30, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	       
	       boolean Einspect50_CoReX = CanFindTheBug(50, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	  
	       boolean Einspect100_CoReX = CanFindTheBug(100, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	  
	       boolean Einspect200_CoReX = CanFindTheBug(200, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	       
	       boolean Einspect500_CoReX = CanFindTheBug(500, old_kept_without_reaching_and_keeping_sameDepMatched, new_kept_without_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	
	       
	       int traversed_old_CoReX = CalculateWastedEffort(old_kept_without_reaching_and_keeping_sameDepMatched,old_retained);
	       int traversed_new_CoReX = CalculateWastedEffort(new_kept_without_reaching_and_keeping_sameDepMatched,new_retained);
	       
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
		        		"Einspect@500-CoReX",
		        		"#Traversed Old Stmt-CoReX","#Traversed New Stmt-CoReX",
		        		"Exam% Old-CoReX","Exam% New-CoReX"	       
		        		};
		        WriteToExcel(results, header, "effort",true, true);
		    }
		    String[] detailedDataRQ4 = {bugID, 
		    		String.valueOf(Einspect5_CoReX),
		    		String.valueOf(Einspect10_CoReX),
		    		String.valueOf(Einspect30_CoReX),
		    		String.valueOf(Einspect50_CoReX),
		    		String.valueOf(Einspect100_CoReX),
		    		String.valueOf(Einspect200_CoReX),
		    		String.valueOf(Einspect500_CoReX),
		    		String.valueOf(traversed_old_CoReX),String.valueOf(traversed_new_CoReX),
		    		String.valueOf(wasted_effort_old_CoReX),String.valueOf(wasted_effort_new_CoRex)
		    };
		    WriteToExcel(results,detailedDataRQ4,"effort",true, false);
						
		       
	            Einspect5_CoReX = CanFindTheBug(5, old_kept_with_reaching_and_keeping_sameDepMatched, new_kept_with_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	    
	            Einspect10_CoReX = CanFindTheBug(10, old_kept_with_reaching_and_keeping_sameDepMatched, new_kept_with_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	       
	            Einspect30_CoReX = CanFindTheBug(30, old_kept_with_reaching_and_keeping_sameDepMatched, new_kept_with_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	       
		        Einspect50_CoReX = CanFindTheBug(50, old_kept_with_reaching_and_keeping_sameDepMatched, new_kept_with_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	  
		        Einspect100_CoReX = CanFindTheBug(100, old_kept_with_reaching_and_keeping_sameDepMatched, new_kept_with_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	  
		        Einspect200_CoReX = CanFindTheBug(200, old_kept_with_reaching_and_keeping_sameDepMatched, new_kept_with_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	       
		        Einspect500_CoReX = CanFindTheBug(500, old_kept_with_reaching_and_keeping_sameDepMatched, new_kept_with_reaching_and_keeping_sameDepMatched,old_retained,new_retained);	
		       
		        traversed_old_CoReX = CalculateWastedEffort(old_kept_with_reaching_and_keeping_sameDepMatched,old_retained);
		        traversed_new_CoReX = CalculateWastedEffort(new_kept_with_reaching_and_keeping_sameDepMatched,new_retained);
		       
		        wasted_effort_old_CoReX = ((double)traversed_old_CoReX/oldTrace.getExecutionList().size())*100.0;
		        wasted_effort_new_CoRex = ((double)traversed_new_CoReX/newTrace.getExecutionList().size())*100.0;
		       
		       if (FirstTime) {		    	
			        String[] header = {"Bug ID", 
			        		"Einspect@5-CoReX", 
			        		"Einspect@10-CoReX", 
			        		"Einspect@30-CoReX",
			        		"Einspect@50-CoReX",
			        		"Einspect@100-CoReX",
			        		"Einspect@200-CoReX",
			        		"Einspect@500-CoReX",
			        		"#Traversed Old Stmt-CoReX","#Traversed New Stmt-CoReX",
			        		"Exam% Old-CoReX","Exam% New-CoReX"
			        		};
			        WriteToExcel(results, header, "effort_keep_reaching",true, true);
			    }
			    String[] detailedDataRQ4_with = {bugID, 
			    		String.valueOf(Einspect5_CoReX),
			    		String.valueOf(Einspect10_CoReX),
			    		String.valueOf(Einspect30_CoReX),
			    		String.valueOf(Einspect50_CoReX),
			    		String.valueOf(Einspect100_CoReX),
			    		String.valueOf(Einspect200_CoReX),
			    		String.valueOf(Einspect500_CoReX),
			    		String.valueOf(traversed_old_CoReX),String.valueOf(traversed_new_CoReX),
			    		String.valueOf(wasted_effort_old_CoReX),String.valueOf(wasted_effort_new_CoRex)
			    };
			    WriteToExcel(results,detailedDataRQ4_with,"effort_keep_reaching",true, false);
							
			
			
		    /////////////////#######////#######////#######////#######////#######////#######
		    /////////////////#######////#######////#######////#######////#######////#######
		System.out.println("##############Finish##############");
		
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private TraceNode getAssertionStatement(List<TraceNode> trace,TestCase tc , int assertoinLine,BiMap<TraceNode, String> Slicer4JMapping, HashMap<String, List<String>> Slicer4JBytecodeMapping) {
		Collections.sort(trace, new TraceNodeOrderComparator());
		for(int i=trace.size()-1;i>=0;i--) {
			TraceNode step =trace.get(i); 
			String ClassName = step.getClassCanonicalName();		
			if (tc.testClass.equals(ClassName) && step.getLineNumber()==assertoinLine) 
				return step;
		}
		return null;
	}

	private void updateWorklistKeepingIdentical(
			DynamicControlFlowGraph new_dcfg, Slicer new_slicer, DynamicControlFlowGraph old_dcfg, Slicer old_slicer,
			HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> cashDeps,
			HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> OthercashDeps,
			BiMap<TraceNode, String> Slicer4JMapping, BiMap<TraceNode, String> OtherSlicer4JMapping,
			HashMap<String, List<String>> Slicer4JBytecodeMapping,
			HashMap<String, List<String>> otherSlicer4JBytecodeMapping, boolean slicer4J, TraceNode step, Trace trace,
			Trace otherTrace, List<TraceNode> visited, List<TraceNode> workList, List<TraceNode> other_visited,
			List<TraceNode> other_workList, boolean isNew, StepChangeTypeChecker typeChecker, PairList pairList,
			DiffMatcher matcher, HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map,
			HashMap<TraceNode, List<TraceNode>> ctl_map, String proPath, String bugID,List<TraceNode> retained,List<TraceNode> OtherRetained,
			List<TraceNode> taintedContext, List<TraceNode> other_taintedContext, List<TraceNode> pureContext, List<TraceNode> other_pureContext) {

		StepChangeType changeType = typeChecker.getType(step, isNew, pairList, matcher);
		String onNew = isNew ? "new" : "old";
//		System.out.println("On " + onNew + " trace," + step);
		////////////////////////////////////////////////////////////////////
		if (changeType.getType() == StepChangeType.SRC) {
//			System.out.println("debug: node is src diff");
			if(!retained.contains(step)) {			
				retained.add(step);
			}
			TraceNode matchedStep = changeType.getMatchingStep();
			List<Integer> matchPositions = getSlicer4JMappedNode(matchedStep, OtherSlicer4JMapping, otherSlicer4JBytecodeMapping);
			if (matchPositions != null) {
				if(!other_visited.contains(matchedStep)) { 
					other_visited.add(matchedStep);
					other_workList.add(matchedStep);
				}
				if(!OtherRetained.contains(matchedStep)) {
					OtherRetained.add(matchedStep);
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
				}
			}
		}
		////////////////////////////////////////////////////////////////////
		////////////////// add identical//////////////////
		if (changeType.getType() == StepChangeType.IDT) {
//			System.out.println("debug: node is identical");
			TraceNode matchedStep = changeType.getMatchingStep();
			// System.out.println("debug: matched step: " + matchedStep);
			List<Integer> matchPositions = getSlicer4JMappedNode(matchedStep, OtherSlicer4JMapping,
					otherSlicer4JBytecodeMapping);
			if (matchPositions != null) {
				if (!other_visited.contains(matchedStep)) {
					other_visited.add(matchedStep);
					other_workList.add(matchedStep);
				}
			}
		}
		////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////
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
//			 System.out.println("debug: dep node: " + d);
			StepChangeType chgType = typeChecker.getType(d.first(), isNew, pairList, matcher);
//			if (chgType.getType() != StepChangeType.IDT) {
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
				List<Integer> Positions = getSlicer4JMappedNode(d.first(), Slicer4JMapping,
						Slicer4JBytecodeMapping);
				if (Positions != null) {
					if (!visited.contains(d.first())) {
						workList.add(d.first());
						visited.add(d.first());
					}
					if((changeType.getType()==StepChangeType.DAT || changeType.getType()==StepChangeType.CTL)&&chgType.getType()==StepChangeType.IDT) //d.first is in sync slice because dep of dat and ctl
						taintedContext.add(d.first());
					if(changeType.getType()==StepChangeType.IDT && (!pureContext.contains(step)) &&chgType.getType()==StepChangeType.IDT)  //d.first is in sync slice because dep of dat and ctl
						taintedContext.add(d.first());
					if((changeType.getType()==StepChangeType.SRC || retained.contains(step)) &&chgType.getType()==StepChangeType.IDT) //d.first is in sync slice because dep of src
						pureContext.add(d.first());
					if(changeType.getType()==StepChangeType.IDT && pureContext.contains(step) &&chgType.getType()==StepChangeType.IDT) //d.first is in sync slice because transitive dep of src
						pureContext.add(d.first());

				}
			
//			  if(d.first().isException())//April 24
//			  { 
//				  TraceNode nextStep = d.first().getStepInPrevious(); 
//				  //System.out.println("debug: prev step " + nextStep); 
//				  List<TraceNode> ctlDeps = ctl_map.get(step); 
//				  if(ctlDeps==null) {
//					  ctlDeps = new ArrayList<>(); 
//				   } 
//				  ctlDeps.add(nextStep); 
//				  ctl_map.put(step, ctlDeps); 
//				  Positions = getSlicer4JMappedNode(nextStep,Slicer4JMapping,Slicer4JBytecodeMapping);
//				  if(Positions!=null) { 
//					  if(!visited.contains(nextStep)) {
//						  workList.add(nextStep); 
//						  visited.add(nextStep); 
//						} 
//				  } 
//			  } 
			 
		}
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

}

