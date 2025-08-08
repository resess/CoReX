package resess;

import java.io.IOException;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.concurrent.ThreadLocalRandom;

public class run {

	public static void main(String[] args) throws NumberFormatException, IOException, InterruptedException {
		 boolean debug = false;
		    
		generateResults generatoror = new generateResults();
		
		//String basePath = "/Users/.../bug_repos/";
		String basePath = args[0];
		
		
		//String projectName = "InPreSS";
		String projectName = args[1];
		
		
		//String bugID = "2";	
		String bugID = args[2];	
		
		//String testcase = "com.google.javascript.jscomp.IntegrationTest::testIssue787"; //clousr(1)
		String testcase = args[3];
		
		String  save_slice_results = "true"; // to save the actual slice in the file with Func...
//		String save_slice_results = args[4]; 
		
		
//		String tool2Run = args[5];
		String tool2Run = "corex";
		
		String EreasOrSlicer = "E";

		String proPath = basePath + projectName + "/" + bugID;
		String buggyPath = proPath + "/bug";
		String fixPath = proPath + "/fix";

		System.out.println("working on the " + bugID + "the bug of " + projectName + " project.");
		projConfig config = projConfig.getConfig(basePath, projectName, Integer.valueOf(bugID),EreasOrSlicer);	
		List<String> includedClassNames = new ArrayList<>();
		List<String> excludedClassNames = new ArrayList<>();
	  
		generatoror.generateResult(basePath, projectName, bugID, proPath, buggyPath, fixPath, 
				true, true, true, 3, true, true, config.assertionLine, config, testcase, includedClassNames,excludedClassNames, config.configFile,debug,tool2Run,save_slice_results);
	    return;

	}	

}
