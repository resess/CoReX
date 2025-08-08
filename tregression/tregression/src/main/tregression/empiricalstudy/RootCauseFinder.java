package tregression.empiricalstudy;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;


import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;

import microbat.codeanalysis.bytecode.ByteCodeParser;
import microbat.codeanalysis.bytecode.MethodFinderByLine;
import microbat.model.BreakPoint;
import microbat.model.ClassLocation;
import microbat.model.ControlScope;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.trace.TraceNodeOrderComparator;
import microbat.model.value.VarValue;
import sav.common.core.Pair;
import tregression.StepChangeType;
import tregression.StepChangeTypeChecker;
import tregression.model.PairList;
import tregression.model.TraceNodePair;
import tregression.separatesnapshots.DiffMatcher;
import tregression.separatesnapshots.diff.FilePairWithDiff;


/**
 * This class implement the alignment slicing and mending algorithm.
 * 
 * @author Yun Lin
 *
 */
public class RootCauseFinder {
	
	class TraceNodeW{
		TraceNode node;
		boolean isOnNew;
		public TraceNodeW(TraceNode node, boolean isOnBefore) {
			super();
			this.node = node;
			this.isOnNew = isOnBefore;
		}
	}
	
	/**
	 * visited nodes on buggy trace
	 */
	private List<TraceNode> regressionNodeList = new ArrayList<>();
	/**
	 * visited nodes on correct trace
	 */
	private List<TraceNode> correctNodeList = new ArrayList<>();
	
	/**
	 * visited "correct" statements which cannot lead to further slicing
	 */
	private List<TraceNode> stopStepsOnBuggyTrace = new ArrayList<>();
	private List<TraceNode> stopStepsOnCorrectTrace = new ArrayList<>();
	
	private List<RootCauseNode> realRootCaseList = new ArrayList<>();
	
	private TraceNode rootCause;
	
	
	public TraceNode retrieveRootCause(PairList pairList, DiffMatcher matcher, Trace buggyTrace, Trace correctTrace) {
		Collections.sort(regressionNodeList, new TraceNodeOrderComparator());
		Collections.sort(correctNodeList, new TraceNodeOrderComparator());
		
		StepChangeTypeChecker typeChecker = new StepChangeTypeChecker(buggyTrace, correctTrace);
		
		for(TraceNode node: regressionNodeList) {
			StepChangeType type = typeChecker.getType(node, true, pairList, matcher);
			if(type.getType()==StepChangeType.SRC) {
				return node;
			}
		}
		
		for(TraceNode node: correctNodeList) {
			StepChangeType type = typeChecker.getType(node, false, pairList, matcher);
			if(type.getType()==StepChangeType.SRC) {
				int startOrder  = findEndOrderInOtherTrace(node, pairList, false, buggyTrace);
				return buggyTrace.getExecutionList().get(startOrder-1);
			}
		}
		
		return null;
	}
	
	public List<TraceNode> retrieveAllRootCause(PairList pairList, DiffMatcher matcher, Trace buggyTrace, Trace correctTrace) {
		Collections.sort(regressionNodeList, new TraceNodeOrderComparator());
		Collections.sort(correctNodeList, new TraceNodeOrderComparator());
		
		List<TraceNode> roots = new ArrayList<>();
		
		StepChangeTypeChecker typeChecker = new StepChangeTypeChecker(buggyTrace, correctTrace);
		
		for(TraceNode node: regressionNodeList) {
			StepChangeType type = typeChecker.getType(node, true, pairList, matcher);
			if(type.getType()==StepChangeType.SRC) {
				roots.add(node);
			}
		}
		
		for(TraceNode node: correctNodeList) {
			StepChangeType type = typeChecker.getType(node, false, pairList, matcher);
			if(type.getType()==StepChangeType.SRC) {
				int startOrder  = findStartOrderInOtherTrace(node, pairList, false);
				TraceNode root = buggyTrace.getExecutionList().get(startOrder-1);
				roots.add(root);
			}
		}
		
		return roots;
	}
	
	private TraceNode findCorrespondingCorrectNode(PairList pairList, TraceNode buggyNode) {
		TraceNodePair pair = pairList.findByBeforeNode(buggyNode);
		if (pair != null) {
			TraceNode correctNode = pair.getAfterNode();
			if(correctNode!=null) {
				return correctNode;
			}
		}
		
		return null;
	}
	
	public void setRootCauseBasedOnDefects4J(PairList pairList, DiffMatcher matcher, Trace buggyTrace, Trace correctTrace) {
		List<RootCauseNode> list = new ArrayList<>();
		for(int i=buggyTrace.size()-1; i>=0; i--) {
			//System.out.println("debug: id: " + i);
			TraceNode buggyNode = buggyTrace.getExecutionList().get(i);
			if(matcher.checkSourceDiff(buggyNode.getBreakPoint(), true)) {
				list.add(new RootCauseNode(buggyNode, true));
			}
		}
		
		for(int i=correctTrace.size()-1; i>=0; i--) {
			//System.out.println("debug: id: " + i);
			TraceNode correctTraceNode = correctTrace.getExecutionList().get(i);
			if(matcher.checkSourceDiff(correctTraceNode.getBreakPoint(), false)) {
				list.add(new RootCauseNode(correctTraceNode, false));
			}
		}
		
		this.setRealRootCaseList(list);
	}
	
	private CausalityGraph causalityGraph;
	
	public void checkRootCause(TraceNode observedFaultNode, Trace newTrace, Trace oldTrace, 
			PairList pairList, DiffMatcher matcher){
		//System.out.println("debug: observable list: " + observedFaultNode);
		getRegressionNodeList().add(observedFaultNode);
		//System.out.println("debug: regression node list: " +getRegressionNodeList());
		
		CausalityGraph causalityGraph = new CausalityGraph();
		CausalityNode causeNode = new CausalityNode(observedFaultNode, true);
		causalityGraph.getObservedFaults().add(causeNode);
		//System.out.println("debug: causalityGraph list: " +causalityGraph.getObservedFaults());
		
		
		List<TraceNodeW> workList = new ArrayList<>();
		workList.add(new TraceNodeW(observedFaultNode, true));
		
		StepChangeTypeChecker typeChecker = new StepChangeTypeChecker(newTrace, oldTrace);
		//System.out.println("#############################");
		//System.out.println("Starting Working list");
		
		while(!workList.isEmpty()){
			
			//System.out.println("#############################");
			TraceNodeW stepW = workList.remove(0);
			TraceNode step = stepW.node;
			CausalityNode resultNode = causalityGraph.findOrCreate(step, stepW.isOnNew);
			//System.out.println("debug: causality node: " + resultNode.toString());
			
			StepChangeType changeType = typeChecker.getType(step, stepW.isOnNew, pairList, matcher);
			Trace trace = getCorrespondingTrace(stepW.isOnNew, newTrace, oldTrace);//get the other trace
			
			String isBefore = stepW.isOnNew?"new":"old";
			//System.out.println("On " + isBefore + " trace," + step);
			//System.out.println("It's a " + changeType.getType() + " type");
			
			if(changeType.getType()==StepChangeType.SRC){
				causalityGraph.addRoot(resultNode);
				//System.out.println("debug: node is src diff");
				//debug: comment the below
				/*if(resultNode.isOnBefore()){
					System.out.println("#############################");
					System.out.println("Breaking");
					System.out.println("#############################");
					break;					
				}*/
			}
			
			else if(changeType.getType()==StepChangeType.DAT){
				//System.out.println("debug: node is data diff");
			
				for(Pair<VarValue, VarValue> pair: changeType.getWrongVariableList()){
					VarValue readVar = (stepW.isOnNew)? pair.first() : pair.second();
					trace = getCorrespondingTrace(stepW.isOnNew, newTrace, oldTrace);
					
					TraceNode dataDom = trace.findDataDependency(step, readVar); 
					//System.out.println("debug: data dependency node: " + dataDom);
					
					addWorkNode(workList, dataDom, stepW.isOnNew);
					addCausality(dataDom, stepW.isOnNew, causalityGraph, resultNode, readVar);
					
					TraceNode matchedStep = changeType.getMatchingStep();
					//System.out.println("debug: data matching of the node: " + matchedStep);
					
					addWorkNode(workList, matchedStep, !stepW.isOnNew);
					CausalityNode cNode = addCausality(matchedStep, !stepW.isOnNew, causalityGraph, resultNode, null);
					
					trace = getCorrespondingTrace(!stepW.isOnNew, newTrace, oldTrace);
					
					VarValue matchedVar = MatchStepFinder.findMatchVariable(readVar, matchedStep);
					
					if(matchedVar != null) {
						TraceNode otherDataDom = trace.findDataDependency(matchedStep, matchedVar);
						//System.out.println("debug: data dependency of the mathcing node: " + otherDataDom);
						addWorkNode(workList, otherDataDom, !stepW.isOnNew);	
						addCausality(otherDataDom, !stepW.isOnNew, causalityGraph, cNode, matchedVar);
					}	
				}
			}
			
			else if(changeType.getType()==StepChangeType.CTL){
				//System.out.println("debug: node is control diff");
				TraceNode controlDom = step.getInvocationMethodOrDominator();
				//System.out.println("debug: control dep node (dominator): " + controlDom);
				
				if(step.insideException()){
					controlDom = step.getStepInPrevious();
					//System.out.println("debug: control dep node (exception): " + controlDom);
				}
				
				else if(controlDom!=null && !controlDom.isConditional() && controlDom.isBranch()
						&& !controlDom.equals(step.getInvocationParent())){
					
					
					StepChangeType t = typeChecker.getType(controlDom, stepW.isOnNew, pairList, matcher);
					
					if(t.getType()==StepChangeType.IDT){
						controlDom = findLatestControlDifferent(step, controlDom, typeChecker, pairList, matcher);
						//System.out.println("debug: control dep node (diff): " + controlDom);
					}
				}
				
				if(controlDom==null){
					TraceNode invocationParent = step.getInvocationParent();
					//System.out.println("debug: control dep node (invocation): " + invocationParent);
					if(!isMatchable(invocationParent, pairList, stepW.isOnNew)){
						controlDom = invocationParent;
						//System.out.println("debug: control dep node (not matchable): " + controlDom);
					}
				}
				//System.out.println("debug: control dep node: " + controlDom);
				addWorkNode(workList, controlDom, stepW.isOnNew);
				CausalityNode cNode = addCausality(controlDom, stepW.isOnNew, causalityGraph, resultNode, null);
				
				trace = getCorrespondingTrace(!stepW.isOnNew, newTrace, oldTrace);
				ClassLocation correspondingLocation = matcher.findCorrespondingLocation(step.getBreakPoint(), !stepW.isOnNew);
				//System.out.println("debug: control correspondingLocation " + correspondingLocation);
				
				TraceNode otherControlDom = findControlMendingNodeOnOtherTrace(step, pairList, trace, !stepW.isOnNew, correspondingLocation, matcher);
				//System.out.println("debug: control dep node of mending " + otherControlDom);
				addWorkNode(workList, otherControlDom, !stepW.isOnNew);
				addCausality(otherControlDom, !stepW.isOnNew, causalityGraph, cNode, null);
			}
			
			else if(changeType.getType()==StepChangeType.IDT){
				//System.out.println("debug: node is identical");
				if(step.isException()){
					TraceNode nextStep = step.getStepInPrevious();
					//System.out.println("debug: prev step " + nextStep);
					addWorkNode(workList, nextStep, !stepW.isOnNew);
					addCausality(nextStep, stepW.isOnNew, causalityGraph, resultNode, null);
					continue;
				}
				
				if(stepW.isOnNew){
					if(!this.stopStepsOnBuggyTrace.contains(step)){
						this.stopStepsOnBuggyTrace.add(step);
					}
				}
				else{
					if(!this.stopStepsOnCorrectTrace.contains(step)){
						this.stopStepsOnCorrectTrace.add(step);
					}
				}
			}
		}
		
		causalityGraph.generateSimulationGuidance();
		this.causalityGraph = causalityGraph;
	}
	
	private CausalityNode addCausality(TraceNode causeTraceNode, boolean isOnBefore, CausalityGraph causalityGraph, 
			CausalityNode resultNode, VarValue value) {
		if(causeTraceNode==null || resultNode==null){
			return null;
		}
		
		CausalityNode causeNode = causalityGraph.findOrCreate(causeTraceNode, isOnBefore);
		causeNode.getResults().put(resultNode, value);
		resultNode.getReasons().put(causeNode, value);
		
		return causeNode;
	}

	private TraceNode findLatestControlDifferent(TraceNode currentNode, TraceNode controlDom, 
			StepChangeTypeChecker checker, PairList pairList, DiffMatcher matcher) {
		TraceNode n = currentNode.getStepInPrevious();
		StepChangeType t = checker.getType(n, true, pairList, matcher);
		while(t.getType()==StepChangeType.CTL && n.getOrder()>controlDom.getOrder()){
			TraceNode dom = n.getInvocationMethodOrDominator();
			if(dom.getMethodSign().equals(n.getMethodSign())){
				return n;
			}
			
			n = n.getStepInPrevious();
			t = checker.getType(n, true, pairList, matcher);
		}
		return controlDom;
	}

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

	public TraceNode findControlMendingNodeOnOtherTrace(TraceNode problematicStep, PairList pairList,
			Trace otherTrace, boolean isOtherTraceTheBeforeTrace, ClassLocation correspondingLocation, DiffMatcher matcher) {
		
		int startOrder = findStartOrderInOtherTrace(problematicStep, pairList, !isOtherTraceTheBeforeTrace);
		int endOrder = findEndOrderInOtherTrace(problematicStep, pairList, !isOtherTraceTheBeforeTrace, otherTrace);
		System.currentTimeMillis();
		TraceNode bestNode = null;
		int value = -1;
		
		//TODO this implementation is problematic, I need to use soot to analyze the static control dependence relation.
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

	private void retrieveAllControlDominatees(TraceNode node, List<TraceNode> allControlDominatees) {
		for(TraceNode controlDominatee: node.getControlDominatees()){
			if(!allControlDominatees.contains(controlDominatee)){
				allControlDominatees.add(controlDominatee);
				retrieveAllControlDominatees(controlDominatee, allControlDominatees);
			}
		}
	}

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

	private List<BreakPoint> findAllExecutedStatement(Trace trace) {
		List<BreakPoint> pointList = new ArrayList<>();
		for(TraceNode node: trace.getExecutionList()){
			BreakPoint p = node.getBreakPoint();
			if(!pointList.contains(p)){
				pointList.add(p);
			}
		}
		
		return pointList;
	}

	private List<BreakPoint> collectAllInfluenceScope(BreakPoint p, HashSet<BreakPoint> allControlScope, 
			List<BreakPoint> executedStatements) {
		ControlScope scope = (ControlScope) p.getControlScope();
		if(scope != null) {
			for(ClassLocation location: scope.getRangeList()){
				BreakPoint point = findCorrespondingPoint(location, executedStatements);
				if(point != null && !allControlScope.contains(point)){
					allControlScope.add(point);
					
					collectAllInfluenceScope(point, allControlScope, executedStatements);
				}
			}			
		}
		return null;
	}

	private BreakPoint findCorrespondingPoint(ClassLocation location, List<BreakPoint> executedStatements) {
		for(BreakPoint p: executedStatements){
			if(location.getClassCanonicalName().equals(p.getDeclaringCompilationUnitName()) 
					&& location.getLineNumber()==p.getLineNumber()){
				return p;
			}
		}
		return null;
	}

	private void addWorkNode(List<TraceNodeW> workList, TraceNode node, boolean isOnBeforeTrace) {
		if(node != null){
			boolean isVisited = false;
			
			if(isOnBeforeTrace){
				if(!getRegressionNodeList().contains(node)){
					getRegressionNodeList().add(node);
					//System.out.println("debug: regression node list: " +getRegressionNodeList());
				}
				else {
					isVisited = true;
				}
			}
			else{
				if(!getCorrectNodeList().contains(node)){
					getCorrectNodeList().add(node);
					//System.out.println("debug: correct node list: " +getCorrectNodeList());
				}
				else {
					isVisited = true;
				}
			}
			
			if(!isVisited) {
				workList.add(new TraceNodeW(node, isOnBeforeTrace));
			}
		}
		
	}

	private Trace getCorrespondingTrace(boolean isOnBeforeTrace, Trace buggyTrace, Trace correctTrace) {
		return isOnBeforeTrace ? buggyTrace : correctTrace;
	}

	public List<TraceNode> getRegressionNodeList() {
		return regressionNodeList;
	}

	public void setRegressionNodeList(List<TraceNode> regressionNodeList) {
		this.regressionNodeList = regressionNodeList;
	}

	public List<TraceNode> getCorrectNodeList() {
		return correctNodeList;
	}

	public void setCorrectNodeList(List<TraceNode> correctNodeList) {
		this.correctNodeList = correctNodeList;
	}

	public TraceNode getRootCause() {
		return rootCause;
	}

	public void setRootCause(TraceNode rootCause) {
		this.rootCause = rootCause;
	}

	public List<RootCauseNode> getRealRootCaseList() {
		return realRootCaseList;
	}

	public void setRealRootCaseList(List<RootCauseNode> realRootCaseList) {
		this.realRootCaseList = realRootCaseList;
	}

	public List<TraceNode> getStopStepsOnBuggyTrace() {
		return stopStepsOnBuggyTrace;
	}

	public void setStopStepsOnBuggyTrace(List<TraceNode> stopStepsOnBuggyTrace) {
		this.stopStepsOnBuggyTrace = stopStepsOnBuggyTrace;
	}

	public List<TraceNode> getStopStepsOnCorrectTrace() {
		return stopStepsOnCorrectTrace;
	}

	public void setStopStepsOnCorrectTrace(List<TraceNode> stopStepsOnCorrectTrace) {
		this.stopStepsOnCorrectTrace = stopStepsOnCorrectTrace;
	}

	public CausalityGraph getCausalityGraph() {
		return causalityGraph;
	}

	public void setCausalityGraph(CausalityGraph causalityGraph) {
		this.causalityGraph = causalityGraph;
	}


}
