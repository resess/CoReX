package tregression.handler;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.List;

import org.apache.bcel.Repository;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import microbat.Activator;
import microbat.model.trace.Trace;
import tregression.empiricalstudy.DeadEndCSVWriter;
import tregression.empiricalstudy.DeadEndRecord;
import tregression.empiricalstudy.Defects4jProjectConfig;
import tregression.empiricalstudy.EmpiricalTrial;
import tregression.empiricalstudy.TrialGenerator;
import tregression.empiricalstudy.TrialGenerator0;
import tregression.empiricalstudy.TrialRecorder;
import tregression.empiricalstudy.training.DED;
import tregression.empiricalstudy.training.DeadEndData;
import tregression.preference.TregressionPreference;


public class SeparateVersionHandler extends AbstractHandler{

	TrialGenerator generator = new TrialGenerator();
	TrialGenerator0 generator0 = new TrialGenerator0();
	
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	public Object execute(ExecutionEvent event) throws ExecutionException {
		Job job = new Job("Do evaluation") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				String projectPath = Activator.getDefault().getPreferenceStore().getString(TregressionPreference.PROJECT_NAME);
				System.out.println(projectPath);
				String bugID = Activator.getDefault().getPreferenceStore().getString(TregressionPreference.BUG_ID);
				System.out.println(bugID);
				String buggyPath = PathConfiguration.getBuggyPath(projectPath, bugID);
				System.out.println(buggyPath);
				String fixPath = PathConfiguration.getCorrectPath(projectPath, bugID);
				System.out.println(fixPath);
				String proPath = PathConfiguration.getBugPath(projectPath, bugID);
				System.out.println(proPath);
				
				String projectName = Activator.getDefault().getPreferenceStore().getString(TregressionPreference.PROJECT_NAME);
				System.out.println(projectName);
				String id = Activator.getDefault().getPreferenceStore().getString(TregressionPreference.BUG_ID);
				System.out.println(id);
				String testcase = Activator.getDefault().getPreferenceStore().getString(TregressionPreference.TEST_CASE);
				System.out.println(testcase);
				System.out.println("working on the " + id + "the bug of " + projectName + " project.");
				Defects4jProjectConfig config = Defects4jProjectConfig.getD4JConfig(projectName, Integer.valueOf(id));
				
				List<EmpiricalTrial> trials = generator0.generateTrials(proPath, buggyPath, fixPath, 
						false, true, true, 100, true, true, config, testcase);//debug: 100 => 3
//				List<EmpiricalTrial> trials = generator0.generateTrials(proPath, buggyPath, fixPath, 
//						false, false, false, 3, true, true, config, testcase);//debug: 100 => 3
				
//				System.out.println("############");
//				System.out.println("all the trials");
//				for(int i=0; i<trials.size(); i++) {
//					System.out.println("Trial " + (i+1));
//					System.out.println(trials.get(i));
//					
//					EmpiricalTrial t = trials.get(i);
//					Trace trace = t.getBuggyTrace();
////					System.out.println("debug DeadEnd List: "+t.getDeadEndRecordList());
//					
////					for(DeadEndRecord r: t.getDeadEndRecordList()){
////						TraceNode breakStep = trace.getTraceNode(r.getBreakStepOrder());
//////						TraceNode occurStep = trace.getTraceNode(91);
////						TraceNode occurStep = trace.getTraceNode(r.getOccurOrder());
////						
////						TraversingDistanceCalculator cal = new TraversingDistanceCalculator(trace.getAppJavaClassPath());
////						Traverse tra = cal.calculateASTTravsingDistance(occurStep.getBreakPoint(), breakStep.getBreakPoint());
////						
////						DependencyCalculator dCal = new DependencyCalculator(trace.getAppJavaClassPath());
////						Dependency dep = dCal.calculateDependency(occurStep.getBreakPoint(), breakStep.getBreakPoint());
////						
////						System.currentTimeMillis();
////						break;
////					}
//					
//					if(!t.getDeadEndRecordList().isEmpty()){
//						System.out.println("debug: No DeadEnd");
//						Repository.clearCache();
//						DeadEndRecord record = t.getDeadEndRecordList().get(0);
//						DED datas = record.getTransformedData(trace);
////						DED datas = new TrainingDataTransfer().transfer(record, trace);
//						setTestCase(datas, t.getTestcase());						
//						try {
////							new DeadEndReporter().export(datas.getAllData(), projectName, Integer.valueOf(id));
//							new DeadEndCSVWriter("_d4j", null).export(datas.getAllData(), projectName, id);
//						} catch (NumberFormatException | IOException e) {
//							e.printStackTrace();
//						}
//					}
//					
//				}
//				
//				try {
//					System.out.println("debug: trial recorder");
//					TrialRecorder recorder = new TrialRecorder();
//					recorder.export(trials, projectName, Integer.valueOf(id));
//					
//				} catch (IOException e) {
//					e.printStackTrace();
//				}
				
				return Status.OK_STATUS;
			}
			
			private void setTestCase(DED datas, String tc) {
				if(datas.getTrueData()!=null){
					datas.getTrueData().testcase = tc;					
				}
				for(DeadEndData data: datas.getFalseDatas()){
					data.testcase = tc;
				}
			}
		};
		
		job.schedule();
		
		return null;
	}
	
	

}
