package tregression.empiricalstudy;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import microbat.Activator;
import microbat.codeanalysis.runtime.StepLimitException;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.value.VarValue;
import microbat.preference.AnalysisScopePreference;
import microbat.recommendation.DebugState;
import microbat.recommendation.UserFeedback;
import microbat.util.Settings;
import sav.common.core.Pair;
import sav.common.core.utils.SingleTimer;
import sav.strategies.dto.AppJavaClassPath;
import tregression.SimulationFailException;
import tregression.StepChangeType;
import tregression.StepChangeTypeChecker;
import tregression.empiricalstudy.RootCauseFinder.TraceNodeW;
import tregression.empiricalstudy.solutionpattern.PatternIdentifier;
import tregression.handler.PathConfiguration;
import tregression.io.RegressionRecorder;
import tregression.model.PairList;
import tregression.model.StepOperationTuple;
import tregression.preference.TregressionPreference;
import tregression.separatesnapshots.AppClassPathInitializer;
import tregression.separatesnapshots.DiffMatcher;
import tregression.separatesnapshots.RunningResult;
import tregression.separatesnapshots.TraceCollector0;
import tregression.tracematch.ControlPathBasedTraceMatcher;
import tregression.views.Visualizer;

public class TrialGenerator0 {
	public static final int NORMAL = 0;
	public static final int OVER_LONG = 1;
	public static final int MULTI_THREAD = 2;
	public static final int INSUFFICIENT_TRACE = 3;
	public static final int SAME_LENGTH = 4;
	public static final int OVER_LONG_INSTRUMENTATION_METHOD = 5;
	public static final int EXPECTED_STEP_NOT_MET = 6;
	public static final int UNDETERMINISTIC = 7;

	private RunningResult cachedBuggyRS;
	private RunningResult cachedCorrectRS;

	private DiffMatcher cachedDiffMatcher;
	private PairList cachedPairList;

	public static String getProblemType(int type) {
		switch (type) {
		case OVER_LONG:
			return "some trace is over long";
		case MULTI_THREAD:
			return "it's a multi-thread program";
		case INSUFFICIENT_TRACE:
			return "the trace is insufficient";
		case SAME_LENGTH:
			return "two traces are of the same length";
		case OVER_LONG_INSTRUMENTATION_METHOD:
			return "over long instrumented byte code method";
		case EXPECTED_STEP_NOT_MET:
			return "expected steps are not met";
		case UNDETERMINISTIC:
			return "this is undeterministic testcase";
		default:
			break;
		}
		return "I don't know";
	}
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	public void generateResult(String proPath, String buggyPath, String fixPath, boolean isReuse, boolean useSliceBreaker,
			boolean enableRandom, int breakLimit, boolean requireVisualization, 
			boolean allowMultiThread, Defects4jProjectConfig config, String testcase, String assertionLineNo, List<String> includedClassNames, List<String> excludedClassNames, String eraseorDual) {
		List<TestCase> tcList;
		EmpiricalTrial trial = null;
		TestCase workingTC = null;
		try {
			tcList = retrieveD4jFailingTestCase(buggyPath);			
			if(testcase!=null){
				tcList = filterSpecificTestCase(testcase, tcList);
			}			
			for (TestCase tc : tcList) {
				System.out.println("#####working on test case " + tc.testClass + "#" + tc.testMethod);
				workingTC = tc;				 
				analyzeTestCaseResult(proPath, buggyPath, fixPath, isReuse, allowMultiThread,tc, assertionLineNo, config, requireVisualization, true, useSliceBreaker, enableRandom, breakLimit, includedClassNames, excludedClassNames, eraseorDual);		
			}

		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	private void analyzeTestCaseResult(String proPath, String buggyPath, String fixPath, boolean isReuse, boolean allowMultiThread, 
			TestCase tc, String assertionLineNo, Defects4jProjectConfig config, boolean requireVisualization, 
			boolean isRunInTestCaseMode, boolean useSliceBreaker, boolean enableRandom, int breakLimit, List<String> includedClassNames, List<String> excludedClassNames, String eraseorDual) throws SimulationFailException, IOException {
		TraceCollector0 newCollector = new TraceCollector0(true);
		TraceCollector0 oldCollector = new TraceCollector0(false);
		long time1 = 0;
		long time2 = 0;

		RunningResult newRS = null;
		RunningResult oldRs = null;

		DiffMatcher diffMatcher = null;
		PairList dualPairList = null;
		int matchTime = -1;

		Settings.compilationUnitMap.clear();
		Settings.iCompilationUnitMap.clear();
		try {
			newRS = newCollector.run(buggyPath, tc, config, isRunInTestCaseMode, allowMultiThread, includedClassNames, excludedClassNames);
		} catch (StepLimitException e) {
			e.printStackTrace();			
		}		
		if (newRS.getRunningType() != NORMAL) {
			System.out.println("Not normal");
		}

		Settings.compilationUnitMap.clear();
		Settings.iCompilationUnitMap.clear();
		try {
			oldRs = oldCollector.run(fixPath, tc, config, isRunInTestCaseMode, allowMultiThread, includedClassNames, excludedClassNames);
		} catch (StepLimitException e) {
			e.printStackTrace();			
		}	
		if (oldRs.getRunningType() != NORMAL) {
			System.out.println("Not normal");
		}
		/////////////////////code and trace comparison
		if (newRS != null && oldRs != null) {
					
			//#####################################################
			time1 = System.currentTimeMillis();
			System.out.println("#################################");
			SaveTrace(newRS,oldRs,proPath);
			//#####################################################

			System.out.println("start matching trace..., new trace length: " + newRS.getRunningTrace().size() + ", old trace length: " + oldRs.getRunningTrace().size());
			System.out.println("#################################");
			System.out.println("Code Alignement");
			diffMatcher = new DiffMatcher(config.srcSourceFolder, config.srcTestFolder, buggyPath, fixPath);
			diffMatcher.matchCode();// a list of changed files and the mapping of the lines
					
			System.out.println("#################################");
			System.out.println("Trace Alignement");
			ControlPathBasedTraceMatcher traceMatcher = new ControlPathBasedTraceMatcher();
			dualPairList = traceMatcher.matchTraceNodePair(newRS.getRunningTrace(), oldRs.getRunningTrace(), diffMatcher,"dual");
		
			time2 = System.currentTimeMillis();
			matchTime = (int) (time2 - time1);
			System.out.println("finish matching trace, taking " + matchTime + "ms");

		}
				
		//////////////////////////dual slicing
		Trace newTrace = newRS.getRunningTrace();
		Trace oldTrace = oldRs.getRunningTrace();
				
		System.out.println("#################################");
		RootCauseFinder rootcauseFinder = new RootCauseFinder();
		rootcauseFinder.setRootCauseBasedOnDefects4J(dualPairList, diffMatcher, newTrace, oldTrace);
		System.out.println("debug: after rootCause (changes)");
		System.out.println("debug: size (changes): " +rootcauseFinder.getRealRootCaseList().size());
		System.out.println("debug: list (changes): " +rootcauseFinder.getRealRootCaseList());
		
		System.out.println("#################################");
		Simulator simulator = new Simulator(useSliceBreaker, enableRandom, breakLimit);
		simulator.prepare(newTrace, oldTrace, dualPairList, diffMatcher);//parents in getObservedFault
		

		
		return;
	}

//////////////////////////////////////////////////////////////////
	private TraceNode getAssertionNode(Trace newTrace, TestCase tc, String assertionLineNo) {
		for (TraceNode node: newTrace.executionList) {
			String ClassName = node.toString().split("~")[1].split(":")[0];
			String LineNo = node.toString().split("line ")[1].split(" ")[0];
			if (tc.testClass.equals(ClassName) && assertionLineNo.equals(LineNo)) {
				return node;
			}
		}
		return null;
	}
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	public List<EmpiricalTrial> generateTrials(String proPath, String buggyPath, String fixPath, boolean isReuse, boolean useSliceBreaker,
			boolean enableRandom, int breakLimit, boolean requireVisualization, 
			boolean allowMultiThread, Defects4jProjectConfig config, String testcase) {
		SingleTimer timer = SingleTimer.start("generateTrial");
		List<TestCase> tcList;
		EmpiricalTrial trial = null;
		TestCase workingTC = null;
		try {
			tcList = retrieveD4jFailingTestCase(buggyPath);
			
			if(testcase!=null){
				tcList = filterSpecificTestCase(testcase, tcList);
			}
			
			for (TestCase tc : tcList) {
				System.out.println("#####working on test case " + tc.testClass + "#" + tc.testMethod);
				workingTC = tc;
				 
				trial = analyzeTestCase(proPath, buggyPath, fixPath, isReuse, allowMultiThread,
						tc, config, requireVisualization, true, useSliceBreaker, enableRandom, breakLimit);
			   
				if(!trial.isDump()){
					break;					
				}
			}

		} catch (Exception e) {
			e.printStackTrace();
		}

		if (trial == null) {
			trial = EmpiricalTrial.createDumpTrial("runtime exception occurs");
			trial.setTestcase(workingTC.testClass + "::" + workingTC.testMethod);
		}
		trial.setExecutionTime(timer.getExecutionTime());
		List<EmpiricalTrial> list = new ArrayList<>();
		list.add(trial);
		return list;
	}
/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////
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

	private List<EmpiricalTrial> runMainMethodVersion( String buggyPath, String fixPath, boolean isReuse, boolean allowMultiThread,
			boolean requireVisualization, Defects4jProjectConfig config, TestCase tc) throws SimulationFailException {
		List<EmpiricalTrial> trials;
		generateMainMethod(buggyPath, tc, config);
		recompileD4J(buggyPath, config);
		generateMainMethod(fixPath, tc, config);
		recompileD4J(fixPath, config);
		
		trials = new ArrayList<>();
		String proPath =buggyPath;
		EmpiricalTrial trial = analyzeTestCase(proPath, buggyPath, fixPath, isReuse, allowMultiThread, 
				tc, config, requireVisualization, false, false, false, -1);
		trials.add(trial);
		return trials;
	}

	private void recompileD4J(String workingPath, Defects4jProjectConfig config) {
		File pathToExecutable = new File(config.rootPath);
		ProcessBuilder builder = new ProcessBuilder(pathToExecutable.getAbsolutePath(), "compile");
		builder.directory(new File(workingPath).getAbsoluteFile() ); // this is where you set the root folder for the executable to run with
		builder.redirectErrorStream(true);
		Process process;
		try {
			process = builder.start();
			Scanner s = new Scanner(process.getInputStream());
			StringBuilder text = new StringBuilder();
			while (s.hasNextLine()) {
				text.append(s.nextLine());
				text.append("\n");
			}
			s.close();
			
			int result = process.waitFor();
			
			System.out.printf( "Process exited with result %d and output %s%n", result, text );
		} catch (IOException | InterruptedException e) {
			e.printStackTrace();
		}

		
	}

	private void generateMainMethod(String workingPath, TestCase tc, Defects4jProjectConfig config) {
		MainMethodGenerator generator = new MainMethodGenerator();
		AppJavaClassPath appCP = AppClassPathInitializer.initialize(workingPath, tc, config);
		String relativePath = tc.testClass.replace(".", File.separator) + ".java";
		String sourcePath = appCP.getTestCodePath() + File.separator + relativePath;
		
		generator.generateMainMethod(sourcePath, tc);
		System.currentTimeMillis();
	}
	
	private EmpiricalTrial analyzeTestCase(String proPath, String buggyPath, String fixPath, boolean isReuse, boolean allowMultiThread, 
			TestCase tc, Defects4jProjectConfig config, boolean requireVisualization, 
			boolean isRunInTestCaseMode, boolean useSliceBreaker, boolean enableRandom, int breakLimit) throws SimulationFailException {
		TraceCollector0 newCollector = new TraceCollector0(true);
		TraceCollector0 oldCollector = new TraceCollector0(false);
		long time1 = 0;
		long time2 = 0;

		RunningResult newRS = null;
		RunningResult oldRs = null;

		DiffMatcher diffMatcher = null;
		PairList pairList = null;
		Long trace_start_time = System.currentTimeMillis();
		int matchTime = -1;
		if (cachedBuggyRS != null && cachedCorrectRS != null && isReuse) {
			newRS = cachedBuggyRS;
			oldRs = cachedCorrectRS;
			diffMatcher = cachedDiffMatcher;
			pairList = cachedPairList;
			EmpiricalTrial trial = simulateDebuggingWithCatchedObjects(newRS.getRunningTrace(), 
					oldRs.getRunningTrace(), pairList, diffMatcher, requireVisualization,
					useSliceBreaker, enableRandom, breakLimit);
			return trial;
		} else {
			
			int trialLimit = 10;
			int trialNum = 0;
			boolean isDataFlowComplete = false;
			EmpiricalTrial trial = null;
			List<String> includedClassNames = AnalysisScopePreference.getIncludedLibList();
			List<String> excludedClassNames = AnalysisScopePreference.getExcludedLibList();
			//excludedClassNames.add("org.codehaus.jettison.mapped.MappedDOMTest");//debug: add filters
			
			while(!isDataFlowComplete && trialNum<trialLimit){
				trialNum++;
			
				Settings.compilationUnitMap.clear();
				Settings.iCompilationUnitMap.clear();
				try {
					newRS = newCollector.run(buggyPath, tc, config, isRunInTestCaseMode, allowMultiThread, includedClassNames, excludedClassNames);					
				} catch (StepLimitException e) {
					e.printStackTrace();			
				}
				if (newRS.getRunningType() != NORMAL) {
					trial = EmpiricalTrial.createDumpTrial(getProblemType(newRS.getRunningType()));
					return trial;
				}

				Settings.compilationUnitMap.clear();
				Settings.iCompilationUnitMap.clear();
				try {
					oldRs = oldCollector.run(fixPath, tc, config, isRunInTestCaseMode, allowMultiThread, includedClassNames, excludedClassNames);									
				} catch (StepLimitException e) {
					e.printStackTrace();			
				}
				if (oldRs.getRunningType() != NORMAL) {
					trial = EmpiricalTrial.createDumpTrial(getProblemType(oldRs.getRunningType()));
					return trial;
				}
				/////////////////////code and trace comparison
				if (newRS != null && oldRs != null) {
					cachedBuggyRS = newRS;
					cachedCorrectRS = oldRs;
					
					//#####################################################
					time1 = System.currentTimeMillis();
					System.out.println("#################################");
					SaveTrace(newRS,oldRs,proPath);
					//#####################################################

					System.out.println("start matching trace..., new trace length: " + newRS.getRunningTrace().size() + ", old trace length: " + oldRs.getRunningTrace().size());
					System.out.println("#################################");
					System.out.println("Code Alignement");
					diffMatcher = new DiffMatcher(config.srcSourceFolder, config.srcTestFolder, buggyPath, fixPath);
					diffMatcher.matchCode();// a list of changed files and the mapping of the lines
					
					System.out.println("#################################");
					System.out.println("Trace Alignement");
					ControlPathBasedTraceMatcher traceMatcher = new ControlPathBasedTraceMatcher();
					pairList = traceMatcher.matchTraceNodePair(newRS.getRunningTrace(), oldRs.getRunningTrace(), diffMatcher, "dual");
					
					time2 = System.currentTimeMillis();
					matchTime = (int) (time2 - time1);
					System.out.println("finish matching trace, taking " + matchTime + "ms");

					cachedDiffMatcher = diffMatcher;
					cachedPairList = pairList;
				}
				
				//////////////////////////dual slicing
				Trace newTrace = newRS.getRunningTrace();
				Trace oldTrace = oldRs.getRunningTrace();
				
				if (requireVisualization) {
					Visualizer visualizer = new Visualizer();
					visualizer.visualize(newTrace, oldTrace, pairList, diffMatcher);
				}
				
				System.out.println("#################################");
				RootCauseFinder rootcauseFinder = new RootCauseFinder();
				rootcauseFinder.setRootCauseBasedOnDefects4J(pairList, diffMatcher, newTrace, oldTrace);
				System.out.println("debug: after rootCause (changes)");
				System.out.println("debug: size (changes): " +rootcauseFinder.getRealRootCaseList().size());
				System.out.println("debug: list (changes): " +rootcauseFinder.getRealRootCaseList());
				
				System.out.println("#################################");
				Simulator simulator = new Simulator(useSliceBreaker, enableRandom, breakLimit);
				simulator.prepare(newTrace, oldTrace, pairList, diffMatcher);//parents in getObservedFault
				
				if(rootcauseFinder.getRealRootCaseList().isEmpty()){
					System.out.println("#################################");
					System.out.println("debug: cannot find real root cause");
					trial = EmpiricalTrial.createDumpTrial("cannot find real root cause");
					StepOperationTuple tuple = new StepOperationTuple(simulator.getObservedFault(), 
							new UserFeedback(UserFeedback.UNCLEAR), simulator.getObservedFault(), DebugState.UNCLEAR);
					trial.getCheckList().add(tuple);
					return trial;
				}

				if(simulator.getObservedFault()==null){
					System.out.println("#################################");
					System.out.println("debug: cannot find observable fault");
					trial = EmpiricalTrial.createDumpTrial("cannot find observable fault");
					return trial;
				}
				
				//////////////////////////////////////////////////////////
				///////////////////////save slicing///////////////////////
				//System.out.println("###############data slicing##################");
				//slicing(simulator.getObservedFault(), newTrace, oldTrace, pairList, diffMatcher,proPath,false);
				//slicing(simulator.getObservedFault(), newTrace, oldTrace, pairList, diffMatcher,proPath,true);
				///////////////////////dual slicing///////////////////////
				//System.out.println("###############Signle slicing##################");
				//rootcauseFinder.singleSlicing(true,proPath,simulator.getObservedFault(), newTrace, oldTrace, pairList, diffMatcher);
				System.out.println("###############Dual slicing##################");
				//rootcauseFinder.dualSlicing(true,proPath,simulator.getObservedFault(), newTrace, oldTrace, pairList, diffMatcher, trace_start_time);
				//////////////////////////////////////////////////////////
				
				//System.out.println("#################################");
				//System.out.println("debug: before rootCause simulation");
				rootcauseFinder.checkRootCause(simulator.getObservedFault(), newTrace, oldTrace, pairList, diffMatcher);
				TraceNode rootCause = rootcauseFinder.retrieveRootCause(pairList, diffMatcher, newTrace, oldTrace);
				List<TraceNode> AllrootCause = rootcauseFinder.retrieveAllRootCause(pairList, diffMatcher, newTrace, oldTrace);
				//System.out.println("debug: after rootCause simulation");
				//System.out.println("debug: the root Cause " + rootCause);
				//System.out.println("debug: all root Causes " + AllrootCause);
				
				if(rootCause==null){
					System.out.println("[Search Lib Class] Cannot find the root cause, I am searching for library classes...");
					List<TraceNode> buggySteps = rootcauseFinder.getStopStepsOnBuggyTrace();
					List<TraceNode> correctSteps = rootcauseFinder.getStopStepsOnCorrectTrace();
					List<String> newIncludedClassNames = new ArrayList<>();
					List<String> newIncludedBuggyClassNames = RegressionUtil.identifyIncludedClassNames(buggySteps, newRS.getPrecheckInfo(), rootcauseFinder.getRegressionNodeList());
					List<String> newIncludedCorrectClassNames = RegressionUtil.identifyIncludedClassNames(correctSteps, oldRs.getPrecheckInfo(), rootcauseFinder.getCorrectNodeList());
					newIncludedClassNames.addAll(newIncludedBuggyClassNames);
					newIncludedClassNames.addAll(newIncludedCorrectClassNames);
					boolean includedClassChanged = false;
					for(String name: newIncludedClassNames){
						if(!includedClassNames.contains(name)){
							includedClassNames.add(name);
							includedClassChanged = true;
						}
					}
					
					if(!includedClassChanged) {
						trialNum = trialLimit + 1;
					}
					else {
						continue;						
					}
				}
				
				isDataFlowComplete = true;
				//System.out.println("#################################");
				//System.out.println("start simulating debugging...");
				time1 = System.currentTimeMillis();
				List<EmpiricalTrial> trials0 = simulator.detectMutatedBug(newTrace, oldTrace, diffMatcher, 0);
				time2 = System.currentTimeMillis();
				int simulationTime = (int) (time2 - time1);
				//System.out.println("finish simulating debugging, taking " + simulationTime / 1000 + "s");
				//System.out.println("#################################");
				for (EmpiricalTrial t : trials0) {
					t.setTestcase(tc.testClass + "#" + tc.testMethod);
					t.setTraceCollectionTime(newTrace.getConstructTime() + oldTrace.getConstructTime());
					t.setTraceMatchTime(matchTime);
					t.setBuggyTrace(newTrace);
					t.setFixedTrace(oldTrace);
					t.setPairList(pairList);
					t.setDiffMatcher(diffMatcher);
					
					PatternIdentifier identifier = new PatternIdentifier();
					identifier.identifyPattern(t);
				}

				trial = trials0.get(0);
				return trial;
			}

		}

		return null;
	}
		

	private void SaveTrace(RunningResult buggyRS, RunningResult correctRs, String proPath) {
		PrintWriter writer;
		try {
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

	private EmpiricalTrial simulateDebuggingWithCatchedObjects(Trace buggyTrace, Trace correctTrace, PairList pairList,
			DiffMatcher diffMatcher, boolean requireVisualization, 
			boolean useSliceBreaker, boolean enableRandom, int breakerLimit) throws SimulationFailException {
		Simulator simulator = new Simulator(useSliceBreaker, enableRandom, breakerLimit);
		simulator.prepare(buggyTrace, correctTrace, pairList, diffMatcher);
		RootCauseFinder rootcauseFinder = new RootCauseFinder();
		rootcauseFinder.setRootCauseBasedOnDefects4J(pairList, diffMatcher, buggyTrace, correctTrace);
		if(rootcauseFinder.getRealRootCaseList().isEmpty()){
			EmpiricalTrial trial = EmpiricalTrial.createDumpTrial("cannot find real root cause");
			StepOperationTuple tuple = new StepOperationTuple(simulator.getObservedFault(), 
					new UserFeedback(UserFeedback.UNCLEAR), simulator.getObservedFault(), DebugState.UNCLEAR);
			trial.getCheckList().add(tuple);
			
			return trial;
		}
		
		if(simulator.getObservedFault()==null){
			EmpiricalTrial trial = EmpiricalTrial.createDumpTrial("cannot find observable fault");
			return trial;
		}
		
		System.out.println("start simulating debugging...");
		long time1 = System.currentTimeMillis();
		List<EmpiricalTrial> trials0 = simulator.detectMutatedBug(buggyTrace, correctTrace, diffMatcher, 0);
		long time2 = System.currentTimeMillis();
		int simulationTime = (int) (time2 - time1);
		System.out.println("finish simulating debugging, taking " + simulationTime / 1000 + "s");
		
		if (requireVisualization) {
			Visualizer visualizer = new Visualizer();
			visualizer.visualize(buggyTrace, correctTrace, pairList, diffMatcher);
		}
		
		for (EmpiricalTrial t : trials0) {
			t.setTraceCollectionTime(buggyTrace.getConstructTime() + correctTrace.getConstructTime());
			t.setBuggyTrace(buggyTrace);
			t.setFixedTrace(correctTrace);
			t.setPairList(pairList);
			t.setDiffMatcher(diffMatcher);
			
			PatternIdentifier identifier = new PatternIdentifier();
			identifier.identifyPattern(t);
		}

		EmpiricalTrial trial = trials0.get(0);
		return trial;
	}

	public class DBRecording implements Runnable{

		EmpiricalTrial trial;
		Trace buggyTrace;
		Trace correctTrace;
		DiffMatcher diffMatcher;
		PairList pairList;
		Defects4jProjectConfig config;
		
		public DBRecording(EmpiricalTrial trial, Trace buggyTrace, Trace correctTrace, DiffMatcher diffMatcher,
				PairList pairList, Defects4jProjectConfig config) {
			super();
			this.trial = trial;
			this.buggyTrace = buggyTrace;
			this.correctTrace = correctTrace;
			this.diffMatcher = diffMatcher;
			this.pairList = pairList;
			this.config = config;
		}



		@Override
		public void run() {
			try {
				new RegressionRecorder().record(trial, buggyTrace, correctTrace, pairList, config.projectName, 
						String.valueOf(config.bugID));
			} catch (SQLException e) {
				e.printStackTrace();
			}	
			
		}
		
	}

	public List<TestCase> retrieveD4jFailingTestCase(String buggyVersionPath) throws IOException {
		return Defects4jProjectConfig.retrieveD4jFailingTestCase(buggyVersionPath);
	}
}
