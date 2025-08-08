package resess;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.LineNumberReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.Statement;

import com.github.gumtreediff.actions.ActionGenerator;
import com.github.gumtreediff.matchers.MappingStore;
import com.github.gumtreediff.matchers.Matcher;
import com.github.gumtreediff.matchers.Matchers;
import com.github.gumtreediff.tree.ITree;
import com.github.gumtreediff.tree.TreeContext;

import microbat.model.BreakPoint;
import microbat.model.ClassLocation;
import microbat.util.JavaUtil;
import microbat.util.MinimumASTNodeFinder;
import tregression.StepChangeType;
import tregression.separatesnapshots.DiffMatcher;
import tregression.separatesnapshots.diff.DiffChunk;
import tregression.separatesnapshots.diff.DiffParser;
import tregression.separatesnapshots.diff.FilePairWithDiff;
import tregression.separatesnapshots.diff.LineChange;

public class ChangeExtractor extends DiffMatcher{
	
	private String sourceFolderName;
	private String testFolderName;
	
	private String buggyPath;
	private String fixPath;
	
	protected List<FilePairWithDiff> fileDiffList;
	
	public ChangeExtractor(String sourceFolderName, String testFolderName, String buggyPath, String fixPath) {
		super(sourceFolderName,testFolderName,buggyPath,fixPath);
		this.sourceFolderName = sourceFolderName;
		this.testFolderName = testFolderName;
		this.buggyPath = buggyPath;
		this.fixPath = fixPath;
	}
	
	public boolean checkSourceDiff(BreakPoint breakPoint, boolean isOnNewTrace) {
		if (isOnNewTrace) {
			FilePairWithDiff diff = findDiffBySourceFile(breakPoint);
			if(diff != null){
				for (DiffChunk chunk : diff.getChunks()) {
					int start = chunk.getStartLineInSource();
					int end = start + chunk.getChunkLengthInSource() - 1;
					int type = findLineChange(breakPoint, chunk, start, end, isOnNewTrace);
					System.currentTimeMillis();
					if(type == StepChangeType.SRC){
						return true;
					}
//					else if(type == -1){
//						break;
//					}
				}
			}
		} else {
			FilePairWithDiff diff = findDiffByTargetFile(breakPoint);
			if(diff != null){
				for (DiffChunk chunk : diff.getChunks()) {
					int start = chunk.getStartLineInTarget();
					int end = start + chunk.getChunkLengthInTarget() - 1;
					int type = findLineChange(breakPoint, chunk, start, end, isOnNewTrace);
					if(type == StepChangeType.SRC){
						System.currentTimeMillis();
						return true;
					}
//					else if(type == -1){
//						break;
//					}
				}
				
			}
		}
		
		return false;
	}

	/**
	 * return SRC if the code of step is contained in chunk and the code is a diff
	 * return -1 if the code of step is contained in chunk and the code is not a diff
	 * return -2 if the code of step is not contained in chunk.
	 * 
	 * @param step
	 * @param chunk
	 * @param start
	 * @param end
	 * @return
	 */
	private HashMap<String, ASTNode> astMap = new HashMap<>();
	private int findLineChange(BreakPoint breakPoint, DiffChunk chunk, int start, int end, boolean isOnBeforeTrace) {
		int count = 0;
		for (int i = 0; i < chunk.getChangeList().size(); i++) {
			LineChange lineChange = chunk.getChangeList().get(i);
			if(isOnBeforeTrace){
				if(lineChange.getType() != LineChange.ADD){
					count++;
				}
			}
			else{
				if(lineChange.getType() != LineChange.REMOVE){
					count++;
				}
			}
			
			int currentLineNo = start + count - 1;
			
			if(chunk.getChanges().contains(currentLineNo)) {
				System.out.println("the gumtree change");
			}
			
			CompilationUnit cu = JavaUtil.findCompiltionUnitBySourcePath(breakPoint.getFullJavaFilePath(), 
					breakPoint.getDeclaringCompilationUnitName());
			
			ASTNode node = astMap.get(breakPoint.getFullJavaFilePath()+currentLineNo);
			if(node==null){
				MinimumASTNodeFinder finder = new MinimumASTNodeFinder(currentLineNo, cu);
				cu.accept(finder);
				node = finder.getMinimumNode();
				astMap.put(breakPoint.getFullJavaFilePath()+currentLineNo, node);
				if(node==null){
					continue;
				}
			}
			
			ASTNode parent = node.getParent();
			int nodeStartLine = cu.getLineNumber(parent.getStartPosition());
			int nodeEndLine = cu.getLineNumber(parent.getStartPosition()+parent.getLength());
			
			if(!(parent instanceof Expression) ){
				nodeStartLine = cu.getLineNumber(node.getStartPosition());
				nodeEndLine = cu.getLineNumber(node.getStartPosition()+node.getLength());
			}
			
			if(!(node instanceof Expression)){
				nodeStartLine = currentLineNo;
				nodeEndLine = currentLineNo;
			}
			
			int stepLineNo = breakPoint.getLineNumber();
			if (nodeStartLine<=stepLineNo && stepLineNo<=nodeEndLine) {
				if(isOnBeforeTrace && lineChange.getType() == LineChange.REMOVE){
					return StepChangeType.SRC;
				}
				
				if(!isOnBeforeTrace && lineChange.getType() == LineChange.ADD){
					return StepChangeType.SRC;
				}
			}
		}
		
		return -1;
	}
	
	protected static List<String> getRawDiffContent(String buggySourcePath, String fixSourcePath) {
		return getRawDiffContent(buggySourcePath, fixSourcePath, true);//debug: ignore space from false to true
	}

	protected static List<String> getRawDiffContent(String buggySourcePath, String fixSourcePath, boolean ignoreSpace) {
		List<String> cmdList = new ArrayList<>();

		cmdList.add("git");
		cmdList.add("diff");
		cmdList.add("--no-index");
		if (ignoreSpace) {
			cmdList.add("--ignore-space-change");
		}
		cmdList.add(buggySourcePath);
		cmdList.add(fixSourcePath);
		
		String[] cmds = cmdList.toArray(new String[0]);
		try {
			Process proc = Runtime.getRuntime().exec(cmds, new String[]{});
			
			InputStream stdin = proc.getInputStream();
			InputStreamReader isr = new InputStreamReader(stdin);
			BufferedReader br = new BufferedReader(isr);
			
			List<String> diffContent = new ArrayList<>();
			String line = null;
			while ( (line = br.readLine()) != null)
				diffContent.add(line);

			return diffContent;
		} catch (IOException e) {
			e.printStackTrace();
		} 
		
		return null;
	}
	
	public boolean isMatch(BreakPoint srcPoint, BreakPoint targetPoint){
		if(!srcPoint.isSourceVersion()){
			BreakPoint tmp = srcPoint;
			srcPoint = targetPoint;
			targetPoint = tmp;
		}
		System.currentTimeMillis();
		FilePairWithDiff fileDiff = findDiffBySourceFile(srcPoint);
		if(fileDiff==null){
			boolean isSameFile = srcPoint.getDeclaringCompilationUnitName().equals(targetPoint.getDeclaringCompilationUnitName());
			boolean isSameLocation = srcPoint.getLineNumber()==targetPoint.getLineNumber();
			
			return isSameFile && isSameLocation;
		}
		else{
			List<Integer> targetLines = fileDiff.getSourceToTargetMap().get(srcPoint.getLineNumber());
			if(targetLines==null){
				return false;
			}
			
			if(fileDiff.getTargetDeclaringCompilationUnit().equals(targetPoint.getDeclaringCompilationUnitName())){
				if(targetLines.contains(targetPoint.getLineNumber())){
					return true;
				}
			}
		}
		
		return false;
	}
	
	public FilePairWithDiff findDiffBySourceFile(BreakPoint srcPoint) {
		for(FilePairWithDiff diff: this.fileDiffList){
			
		
			if(diff.getSourceFile().contains("/dev/null"))//debug: added
			     continue;
			if(diff.getSourceDeclaringCompilationUnit().equals(srcPoint.getDeclaringCompilationUnitName())){
				return diff;
			}
		}
		
		return null;
	}
	public FilePairWithDiff findDiffByTargetFile(BreakPoint tarPoint) {//debug: look for file
		for(FilePairWithDiff diff: this.fileDiffList){
		    

			if(diff.getTargetFile().contains("/dev/null"))//debug: added
			     continue;
			if(diff.getTargetDeclaringCompilationUnit().equals(tarPoint.getDeclaringCompilationUnitName())){
				return diff;
			}
		}
		
		return null;
	}
	public FilePairWithDiff findDiffByTargetFile(String targetFile){
		for(FilePairWithDiff diff: this.fileDiffList){
			if(diff.getTargetFile().equals(targetFile)){
				return diff;
			}
		}
		
		return null;
	}
	
	public FilePairWithDiff findDiffBySourceFile(String sourceFile){
		for(FilePairWithDiff diff: this.fileDiffList){
			if(diff.getSourceFile().equals(sourceFile)){
				return diff;
			}
		}
		
		return null;
	}



	public void matchCode() {
		//List<String> diffContent = getRawDiffContent();
		List<String> diffContent = getRawDiffContent(sourceFolderName);
		diffContent.add("diff end");
//		List<FilePairWithDiff> fileDiffs = new DiffParser().parseDiff(diffContent, sourceFolderName);
		List<FilePairWithDiff> fileDiffs = parseDiff(diffContent, sourceFolderName);
		
		List<String> testDiffContent = getRawDiffContent(testFolderName);
 		testDiffContent.add("diff end");
// 		List<FilePairWithDiff> testFileDiffs = new DiffParser().parseDiff(testDiffContent, testFolderName);
 		List<FilePairWithDiff> testFileDiffs = parseDiff(testDiffContent, testFolderName);
 		fileDiffs.addAll(testFileDiffs);
 		
 		Iterator<FilePairWithDiff> iter = fileDiffs.iterator();
 		while(iter.hasNext()) {
 			FilePairWithDiff diff = iter.next();
 			if(diff.getSourceFile() == null)
 				iter.remove();
 		}
            
		for(FilePairWithDiff fileDiff: fileDiffs){
			//System.out.println("debug: new diff file: "+ fileDiff.getSourceFile());
			//System.out.println("debug: old diff file: "+ fileDiff.getTargetFile());
			if(fileDiff.getSourceFile().contains("dev/null")) {//debug: check
				//
			}
			else if(fileDiff.getTargetFile().contains("dev/null")) {//debug: check
				//
			}
			else {//map the lines in updated file
				HashMap<Integer, List<Integer>> sourceToTargetMap = new HashMap<>();
				HashMap<Integer, List<Integer>> targetToSourceMap = new HashMap<>();
				
				constructMapping(fileDiff, sourceToTargetMap, targetToSourceMap);
				//System.currentTimeMillis();
				fileDiff.setSourceToTargetMap(sourceToTargetMap);
				//System.out.println("debug: new to old: "+ fileDiff.getSourceToTargetMap());
				fileDiff.setTargetToSourceMap(targetToSourceMap);
				//System.out.println("debug: old to new: "+ fileDiff.getTargetToSourceMap());
			}
		}
		
		this.fileDiffList = fileDiffs;
	}

	protected List<String> getRawDiffContent(String folderName) {
 		String buggySourcePath = buggyPath + File.separator + folderName;
 		String fixSourcePath = fixPath + File.separator + folderName;
		return getRawDiffContent(buggySourcePath, fixSourcePath);
	}

	private int countLineNumber(String fileName){
		LineNumberReader lnr;
		try {
			//System.out.println("debug file in line number:" + fileName);
			File file = new File(fileName);
			lnr = new LineNumberReader(new FileReader(file));
			lnr.skip(Long.MAX_VALUE);
			int count = lnr.getLineNumber() + 1; //Add 1 because line index starts at 0
			// Finally, the LineNumberReader object should be closed to prevent resource leak
			lnr.close();
			
			return count;
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return -1;
	}
	
	public void constructMapping(FilePairWithDiff fileDiff, HashMap<Integer, List<Integer>> sourceToTargetMap,
			HashMap<Integer, List<Integer>> targetToSourceMap) {
		if(fileDiff.getSourceFile() == null) return;
		int sourceLineCursor = 1;
		int targetLineCursor = 1;
		
		for(DiffChunk chunk: fileDiff.getChunks()){
			int startLineInSource = chunk.getStartLineInSource();
			int startLineInTarget = chunk.getStartLineInTarget();
			while(sourceLineCursor<startLineInSource && targetLineCursor<startLineInTarget){
				mapLine(sourceToTargetMap, targetToSourceMap, sourceLineCursor, targetLineCursor);
				sourceLineCursor++;
				targetLineCursor++;
			}
			
			for(int index=0; index<chunk.getChangeList().size(); ){
				LineChange line = chunk.getChangeList().get(index);
				if(line.getType()==LineChange.UNCHANGE){
					mapLine(sourceToTargetMap, targetToSourceMap, sourceLineCursor, targetLineCursor);
					sourceLineCursor++;
					targetLineCursor++;
					index++;
				}
				else if(line.getType()==LineChange.REMOVE){
					int successiveRemoveLines = findSuccessiveRemoveLines(chunk, line.getIndex());
					System.currentTimeMillis();
					boolean followByAdd = checkFollowByAdd(chunk, line.getIndex(), successiveRemoveLines);
					
					if(followByAdd){
						int successiveAddLines = findSuccessiveAddLines(chunk, line.getIndex()+successiveRemoveLines);
						for(int i=sourceLineCursor; i<sourceLineCursor+successiveRemoveLines; i++){
							for(int j=targetLineCursor; j<targetLineCursor+successiveAddLines; j++){
								mapAdditionalLine(sourceToTargetMap, i, j);
								mapAdditionalLine(targetToSourceMap, j, i);
							}
						}
						
						sourceLineCursor += successiveRemoveLines;
						targetLineCursor += successiveAddLines;
						
						index += successiveAddLines + successiveRemoveLines;
					}
					else{
						sourceLineCursor += successiveRemoveLines;
						index += successiveRemoveLines;
					}
				}
				else{
					targetLineCursor++;
					index++;
				}
			}
			
		}
		
		int totalSoureLineNumber = countLineNumber(fileDiff.getSourceFile());
		int totalTargetLineNumber = countLineNumber(fileDiff.getTargetFile());
		while(sourceLineCursor<totalSoureLineNumber && targetLineCursor<totalTargetLineNumber){
			mapLine(sourceToTargetMap, targetToSourceMap, sourceLineCursor, targetLineCursor);
			sourceLineCursor++;
			targetLineCursor++;
		}
	}

	private int findSuccessiveAddLines(DiffChunk chunk, int startIndex) {
		int count = 0;
		for(int i=startIndex; i<chunk.getChangeList().size(); i++){
			LineChange line = chunk.getChangeList().get(i);
			if(line.getType()==LineChange.ADD){
				count++;
			}
			else{
				break;
			}
		}
		
		return count;
	}

	private boolean checkFollowByAdd(DiffChunk chunk, int startIndex, int successiveRemoveLines) {
		int index = startIndex+successiveRemoveLines;
		if(index < chunk.getChangeList().size()){//debug: change from <= to <
			return chunk.getChangeList().get(index).getType()==LineChange.ADD;
		}
		
		return false;
	}

	private int findSuccessiveRemoveLines(DiffChunk chunk, int startIndex) {
		int count = 0;
		for(int i=startIndex; i<chunk.getChangeList().size(); i++){
			LineChange line = chunk.getChangeList().get(i);
			if(line.getType()==LineChange.REMOVE){
				count++;
			}
			else{
				break;
			}
		}
		
		return count;
	}

	private void mapAdditionalLine(HashMap<Integer, List<Integer>> sourceToTargetMap, int sourceLineCursor,
			int targetLineCursor) {
		List<Integer> targetLines = sourceToTargetMap.get(sourceLineCursor);
		if(targetLines == null){
			targetLines = new ArrayList<>();
		}
		
		if(!targetLines.contains(targetLineCursor)){
			targetLines.add(targetLineCursor);			
		}
		
		sourceToTargetMap.put(sourceLineCursor, targetLines);
	}

	private void mapLine(HashMap<Integer, List<Integer>> sourceToTargetMap, 
			HashMap<Integer, List<Integer>> targetToSourceMap, int sourceLineCursor, int targetLineCursor){
		List<Integer> targetLines = new ArrayList<>();
		targetLines.add(targetLineCursor);
		List<Integer> sourceLines = new ArrayList<>();
		sourceLines.add(sourceLineCursor);
		
		sourceToTargetMap.put(sourceLineCursor, targetLines);
		targetToSourceMap.put(targetLineCursor, sourceLines);
	}

	public String getBuggyPath() {
		return buggyPath;
	}

	public void setBuggyPath(String buggyPath) {
		this.buggyPath = buggyPath;
	}

	public String getFixPath() {
		return fixPath;
	}

	public void setFixPath(String fixPath) {
		this.fixPath = fixPath;
	}
	
	public String getSourceFolderName(){
		return this.sourceFolderName;
	}

	public String getTestFolderName() {
		return testFolderName;
	}

	public void setTestFolderName(String testFolderName) {
		this.testFolderName = testFolderName;
	}
	


	public ClassLocation findCorrespondingLocation(BreakPoint breakPoint, boolean isOnAfter) {
		if(isOnAfter){
			return getCorrespondentLocationInSource(breakPoint);
		}
		else{
			return getCorrespondentLocationInTarget(breakPoint);
		}
	}

	private ClassLocation getCorrespondentLocationInSource(BreakPoint breakPointInTarget) {
		FilePairWithDiff diff = findDiffByTargetFile(breakPointInTarget);
		if(diff == null){
			return (BreakPoint) breakPointInTarget.clone();
		}
		else{
			List<Integer> lines = diff.getTargetToSourceMap().get(breakPointInTarget.getLineNumber());
			if (lines==null)
				return (BreakPoint) breakPointInTarget.clone();
			ClassLocation location = new ClassLocation(diff.getSourceDeclaringCompilationUnit(), null, lines.get(0));
			return location;
		}
		
	}
	

	private ClassLocation getCorrespondentLocationInTarget(BreakPoint breakPointInSource) {
		FilePairWithDiff diff = findDiffBySourceFile(breakPointInSource);
		if(diff == null){
			return (BreakPoint) breakPointInSource.clone();
		}
		else{
			List<Integer> lines = diff.getSourceToTargetMap().get(breakPointInSource.getLineNumber());
			if (lines==null)
				return (BreakPoint) breakPointInSource.clone();
			ClassLocation location = 
					new ClassLocation(diff.getTargetDeclaringCompilationUnit(), null, lines.get(0));
			return location;
			
		}
	}

	public List<FilePairWithDiff> getFileDiffList() {
		return fileDiffList;
	}
	public List<FilePairWithDiff> parseDiff(List<String> diffContent, String sourceFolderName){
		List<FilePairWithDiff> fileDiffList = new ArrayList<>();
		FilePairWithDiff fileDiff = null;
		String sourceFile = null;
		String targetFile = null;
		for(String line: diffContent){
			if(line.startsWith("diff")){
				if(fileDiff != null){
					fileDiffList.add(fileDiff);
				}
				fileDiff = new FilePairWithDiff();
				fileDiff.setSourceFolderName(sourceFolderName);
			}
			else if(line.startsWith("---")){
				String osName = System.getProperty("os.name");
				
				if(osName.contains("Win")){
					sourceFile = line.substring(line.indexOf("a/")+2, line.length()-1);
				}
				else{
					sourceFile = line.substring(line.indexOf("a/")+1, line.length());
				}
				sourceFile = sourceFile.replace("/", File.separator);
				sourceFile = sourceFile.replace("\\\\", File.separator);
				fileDiff.setSourceFile(sourceFile);
			}
			else if(line.startsWith("+++")){
				String osName = System.getProperty("os.name");
		
				if(osName.contains("Win")){
					targetFile = line.substring(line.indexOf("b/")+2, line.length()-1);
				}
				else{
					targetFile = line.substring(line.indexOf("b/")+1, line.length());
				}
				targetFile = targetFile.replace("/", File.separator);
				targetFile = targetFile.replace("\\\\", File.separator);
				fileDiff.setTargetFile(targetFile);
			}
			else if(line.startsWith("@@")){
				String chunkInfo = line.substring(line.indexOf("@@")+3, line.lastIndexOf("@@")-1);
				
				String startLineInSource = chunkInfo.substring(chunkInfo.indexOf("-")+1, chunkInfo.indexOf(","));
				int startLineInS = Integer.valueOf(startLineInSource);
				
				String lengthInSource = chunkInfo.substring(chunkInfo.indexOf(",")+1, chunkInfo.indexOf(" "));
				int lengthInS = Integer.valueOf(lengthInSource);
				
				String startLineInTarget = chunkInfo.substring(chunkInfo.indexOf(" ")+2, chunkInfo.lastIndexOf(","));
				int startLinInT = Integer.valueOf(startLineInTarget);
				
				String lengthInTarget = chunkInfo.substring(chunkInfo.lastIndexOf(",")+1, chunkInfo.length());
				int lengthInT = Integer.valueOf(lengthInTarget);
				
				
//				if(!sourceFile.contains("/dev/null") && !targetFile.contains("/dev/null")) {
//					Map<Integer, String[]> changes = null;	
//					try {					
//						changes = obtainMapChanges(sourceFile,targetFile);
//					} catch (Exception e) {
//						// TODO Auto-generated catch block
//						e.printStackTrace();
//					}
//					Set<Integer> keySet = changes.keySet();
//					ArrayList<Integer> result = new ArrayList<Integer>(keySet);				
//					Collections.sort(result);
//					
//					DiffChunk chunk = new DiffChunk(startLineInS, lengthInS, startLinInT, lengthInT,result);
//					fileDiff.getChunks().add(chunk);
//				}
//				else {
					DiffChunk chunk = new DiffChunk(startLineInS, lengthInS, startLinInT, lengthInT);
					fileDiff.getChunks().add(chunk);
//				}
			}
			else if(line.startsWith(" ") || line.startsWith("+") || line.startsWith("-")){
				int size = fileDiff.getChunks().size();
				DiffChunk chunk = fileDiff.getChunks().get(size-1);
				
				int index = chunk.getChangeList().size();
				int type = changeType(line.toCharArray()[0]);
				
				LineChange change = new LineChange(index, type, line);
				chunk.getChangeList().add(change);
			}
		}
		
		return fileDiffList;
	}
	
	private int changeType(char s){
		if(s==' '){
			return LineChange.UNCHANGE;
		}
		else if(s=='+'){
			return LineChange.ADD;
		}
		else if(s=='-'){
			return LineChange.REMOVE;
		}
		
		return -1;
	}



	private Map<Integer, String[]> obtainMapChanges(String sourceFile, String targetFile) throws Exception {
		TreeContext srctxt= new CustomJdtTreeGenerator().generateFromFile(sourceFile);
		TreeContext dsttxt=new CustomJdtTreeGenerator().generateFromFile(targetFile);
		ITree src=srctxt.getRoot();
		ITree dst = dsttxt.getRoot();
		Matcher m = Matchers.getInstance().getMatcher(src, dst);
		m.match();
		MappingStore mappings=m.getMappings();
		ActionGenerator g = new ActionGenerator(src, dst, mappings);
		g.generate();
		Map<Integer,String[]>  changes= new CustomSerializer(srctxt,dsttxt,g.getActions(),mappings).getChanes();
//		for(Integer key: changes.keySet()) {
//			System.out.println("key:" + key);
//			for(int kk=0;kk<changes.get(key).length;kk++)
//			System.out.println("changes:" + changes.get(key)[kk]);
//		}
			
		return changes;
	}
}
