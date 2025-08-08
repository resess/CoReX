package tregression.tracematch;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;

import microbat.algorithm.graphdiff.Matcher;
import microbat.algorithm.graphdiff.MatchingGraphPair;
import microbat.model.BreakPoint;
import microbat.model.value.GraphNode;
import microbat.util.JavaUtil;
import microbat.util.MinimumASTNodeFinder;
import sav.common.core.Pair;
import tregression.separatesnapshots.DiffMatcher;

public abstract class IndexTreeMatcher implements Matcher{

	/**
	 * DiffMatcher contains the information of how source code should match with each other.
	 * If this field is null, we assume there is only one-line modification between original
	 * and regression version.
	 */
	protected DiffMatcher diffMatcher;
	
//	protected Map<Integer, MatchingGraphPair> pairMap = new HashMap<>();
	protected Map<String, List<String>> lineMap = new HashMap<>();
	
	@Override
	public abstract List<MatchingGraphPair> matchList(List<? extends GraphNode> childrenBefore,
			List<? extends GraphNode> childrenAfter);

	protected IndexTreeNode findMostSimilarNode(GraphNode gNodeBefore, List<? extends GraphNode> childrenAfter, 
			Map<Integer, MatchingGraphPair> pairMap, String dualorinPreSS) {
		IndexTreeNode mostSimilarNode = null;
		double sim = -1;
		
		IndexTreeNode itNodeBefore = (IndexTreeNode)gNodeBefore;
		for(GraphNode gNodeAfter: childrenAfter){
			IndexTreeNode itNodeAfter = (IndexTreeNode)gNodeAfter;
			if(hasMatched(pairMap, itNodeAfter)){
				continue;
			}
			//System.out.println("Debug: before Node is " + itNodeBefore.getTraceNode() + " after node is " +itNodeAfter.getTraceNode() );
			if(isControlPathCompatible(itNodeBefore, itNodeAfter)){				
				if(mostSimilarNode==null){
					mostSimilarNode = itNodeAfter;
					sim = sim(itNodeBefore, itNodeAfter);
				}
				else{
					double sim1 = sim(itNodeBefore, itNodeAfter);
					if(sim1 > sim){
						mostSimilarNode = itNodeAfter;
						sim = sim1;
					}
				}
			}			
			//////for handing triangles 
			else{ 
				if(dualorinPreSS.equals("inPreSS")) {
					if(isControlPathSubset(itNodeBefore, itNodeAfter)){				
						if(mostSimilarNode==null){
							mostSimilarNode = itNodeAfter;
							sim = sim(itNodeBefore, itNodeAfter);				
						}
						else{
							double sim1 = sim(itNodeBefore, itNodeAfter);
							if(sim1 > sim){
								mostSimilarNode = itNodeAfter;
								sim = sim1;
							}
						}
					}
				}
			}
			//////for handing triangles 
		}
		
		if(sim==0){
			mostSimilarNode = null;
		}
		
		return mostSimilarNode;
	}
	private boolean hasMatched(Map<Integer, MatchingGraphPair> pairMap, IndexTreeNode itNodeAfter) {
		MatchingGraphPair p = pairMap.get(itNodeAfter.getTraceNode().getOrder());
		return p!=null;
	}
	
	private boolean isControlPathSubset(IndexTreeNode itNodeBefore, IndexTreeNode itNodeAfter) {
		List<IndexTreeNode> pathBefore = itNodeBefore.getControlPath();
		List<IndexTreeNode> pathAfter = itNodeAfter.getControlPath();
         //pathBefore is Subset of pathAfter or other way 
		boolean beforeSubsetAfter = true;
		for(int i=0; i<pathBefore.size(); i++){
			IndexTreeNode nodeBefore = pathBefore.get(i);
			boolean matchFound = false;
			for(int j=0; j<pathAfter.size(); j++) {
				IndexTreeNode nodeAfter = pathAfter.get(j);				
				if(nodeBefore.isMatchableWith(nodeAfter, diffMatcher)){
					matchFound = true;
					break;
				}
			}
			if(!matchFound) {// no corresponding for this node
				beforeSubsetAfter = false;
				break;
			}			    
		} 
		if(beforeSubsetAfter)
			return true;
		else {
			boolean AfterSubsetBefore = true;
			for(int i=0; i<pathAfter.size(); i++){
				IndexTreeNode nodeAfter = pathAfter.get(i);
				boolean matchFound = false;
				for(int j=0; j<pathBefore.size(); j++) {
					IndexTreeNode nodeBefore = pathBefore.get(j);				
					if(nodeBefore.isMatchableWith(nodeAfter, diffMatcher)){
						matchFound = true;
						break;
					}
				}
				if(!matchFound) {// no corresponding for this node
					AfterSubsetBefore = false;
					break;
				}			    
			} 
			if(AfterSubsetBefore)
				return true;
		}
		return false;
	}

	private boolean isControlPathCompatible(IndexTreeNode itNodeBefore, IndexTreeNode itNodeAfter) {
		List<IndexTreeNode> pathBefore = itNodeBefore.getControlPath();
		List<IndexTreeNode> pathAfter = itNodeAfter.getControlPath();

		if(pathBefore.size()==pathAfter.size()){
			for(int i=0; i<pathBefore.size(); i++){
				IndexTreeNode nodeBefore = pathBefore.get(i);
				IndexTreeNode nodeAfter = pathAfter.get(i);
				
				if(!nodeBefore.isMatchableWith(nodeAfter, diffMatcher)){
					return false;
				}
			}
			
			return true;
		}
		
		return false;
		
//		/**
//		 * Here is an optimization:
//		 * If parent control node has been recorded in pair list, we do not need to compare their control
//		 * path any more. 
//		 */
//		MatchingGraphPair pair = null;
//		int size = pathAfter.size();
//		for(int i=size-1; i>=0; i--) {
//			ControlNode cNode = pathAfter.get(i);
//			MatchingGraphPair p = pairMap.get(cNode.getOrder());
//			if(p!=null) {
//				pair = p;
//				break;
//			}
//		}
//		
//		int cursorBefore = 0;
//		int cursorAfter = 0;
//		if(pair!=null) {
//			cursorBefore = ((IndexTreeNode)pair.getNodeBefore()).getOrder();
//			cursorAfter = ((IndexTreeNode)pair.getNodeAfter()).getOrder();
//		}
//		
//		
//		for(ControlNode nodeBefore: pathBefore){
//			if(nodeBefore.getOrder()<=cursorBefore) {
//				continue;
//			}
//			
//			if(nodeBefore.getAppearOrder() > 1){
//				boolean flag = canFindMatchingNode(nodeBefore, pathAfter);
//				if(!flag){
//					return false;
//				}
//			}
//		}
//		
//		for(ControlNode nodeAfter: pathAfter){
//			if(nodeAfter.getOrder()<=cursorAfter) {
//				continue;
//			}
//			
//			if(nodeAfter.getAppearOrder() > 1){
//				boolean flag = canFindMatchingNode(nodeAfter, pathBefore);
//				if(!flag){
//					return false;
//				}
//			}
//		}
//		
//		
//		return true;
	}
	
	private boolean canFindMatchingNode(IndexTreeNode node, List<IndexTreeNode> path) {
		Map<BreakPoint, Boolean> map = new HashMap<>();
		for(IndexTreeNode thatNode: path){
			BreakPoint point = thatNode.getBreakPoint();
			Boolean flag = map.get(point);
			if(flag==null){
				if(node.isMatchableWith(thatNode, diffMatcher)){
					return true;
				}
				else{
					map.put(point, false);
				}				
			}
		}
		
		return false;
	}
	
	private double sim(IndexTreeNode itNodeBefore, IndexTreeNode itNodeAfter) {
		BreakPoint pointBefore = itNodeBefore.getBreakPoint();
		BreakPoint pointAfter = itNodeAfter.getBreakPoint();
		
		try {
			String pathBefore = pointBefore.getFullJavaFilePath();
			List<String> stringLinesBefore = lineMap.get(pathBefore);
			if(stringLinesBefore==null){
				stringLinesBefore = Files.readAllLines(Paths.get(pointBefore.getFullJavaFilePath()), StandardCharsets.ISO_8859_1);
				lineMap.put(pathBefore, stringLinesBefore);
			}
			String textBefore = stringLinesBefore.get(pointBefore.getLineNumber()-1);
			
			String pathAfter = pointAfter.getFullJavaFilePath();
			List<String> stringLinesAfter = lineMap.get(pathAfter); 
			if(stringLinesAfter==null){
				stringLinesAfter = Files.readAllLines(Paths.get(pointAfter.getFullJavaFilePath()), StandardCharsets.ISO_8859_1);
				lineMap.put(pathAfter, stringLinesAfter);
			}
			String textAfter = stringLinesAfter.get(pointAfter.getLineNumber()-1);
			
			if(textBefore.equals(textAfter)) {
				//System.out.println("node are exact same ");
				return 1;
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		ASTNode nodeBefore = parseASTNodeInBreakpoint(itNodeBefore, pointBefore, true);
		ASTNode nodeAfter = parseASTNodeInBreakpoint(itNodeAfter, pointAfter, false);
		
		if(nodeBefore.getNodeType()==nodeAfter.getNodeType()){
			//System.out.println("node are exact same ast ");
			return 1;
		}
		else{
			//System.out.println("node are not same ");
			return 0;			
		}
		
	}
	
	private HashMap<BreakPoint, ASTNode> point2ASTNodeMapBefore = new HashMap<>();
	private HashMap<BreakPoint, ASTNode> point2ASTNodeMapAfter = new HashMap<>();
	private ASTNode parseASTNodeInBreakpoint(IndexTreeNode itNodeBefore, BreakPoint point, boolean before) {
		//System.out.println(" node is " + itNodeBefore.getTraceNode());
		//System.out.println(" breaking point is " + point.getLineNumber());
		ASTNode node;
		if (before)
			node = point2ASTNodeMapBefore.get(point);
		else 
			node = point2ASTNodeMapAfter.get(point);
		if(node == null){
			//System.out.println("ast node is null");
			String compilationUnitName = itNodeBefore.getTraceNode().getDeclaringCompilationUnitName();
			//System.out.println("compilationUnitName" + compilationUnitName);
			CompilationUnit cu = JavaUtil.findCompiltionUnitBySourcePath(point.getFullJavaFilePath(), 
					compilationUnitName);
			node = findSpecificNode(cu, point);
			if (before)
				point2ASTNodeMapBefore.put(point, node);
			else 
				point2ASTNodeMapAfter.put(point, node);
			//
		}
		//System.out.println("ast node is " + node);
		//System.out.println("ast node is " + node.getNodeType());
		return node;
	}
	
	private ASTNode findSpecificNode(CompilationUnit cu, BreakPoint point) {
		MinimumASTNodeFinder finder = new MinimumASTNodeFinder(point.getLineNumber(), cu);
		cu.accept(finder);
		return finder.getMinimumNode();
	}
}
