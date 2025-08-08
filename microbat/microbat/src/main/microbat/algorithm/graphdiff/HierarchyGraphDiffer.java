package microbat.algorithm.graphdiff;

import java.util.ArrayList;
import java.util.List;

import microbat.model.value.GraphNode;

public class HierarchyGraphDiffer {
	private Matcher matcher = new SimpleMatcher();
	private List<GraphDiff> diffs = new ArrayList<>();
	
	private List<GraphDiff> commons = new ArrayList<>();
	
	/**
	 * the depth for hierarchical differencing, -1 means compare all the levels.
	 */
	private int depth = -1;
	
	/**
	 * This diff result does not contain the difference of rootBefore and rootAfter themselves, only the
	 * different of their children.
	 * <p>
	 * The isCompareRoot parameter is to indicate whether the algorithm need to consider the difference of
	 * the root node.
	 * 
	 * @param rootBefore
	 * @param rootAfter
	 * @param isCompareRoot
	 */
	public void diff(GraphNode rootBefore, GraphNode rootAfter, boolean isCompareRoot){
		if(isCompareRoot){
			if(!rootBefore.isTheSameWith(rootAfter)){
				GraphDiff diff = new GraphDiff(rootBefore, rootAfter);
				this.diffs.add(diff);
			}
		}
		
		diffChildren(rootBefore, rootAfter, 1);			
	}
	
	public void diff(GraphNode rootBefore, GraphNode rootAfter, boolean isCompareRoot, Matcher matcher, int depth){
		this.matcher = matcher;
		this.depth = depth;
		diff(rootBefore, rootAfter, isCompareRoot);
	}

	private void diffChildren(GraphNode rootBefore, GraphNode rootAfter, int level) {
		//System.out.println("####################");
		if (level!=1) {

		}
		List<? extends GraphNode> childrenBefore = rootBefore.getChildren();
		List<? extends GraphNode> childrenAfter = rootAfter.getChildren();
		List<MatchingGraphPair> pairs = matcher.matchList(childrenBefore, childrenAfter);

		int newLevel = level + 1;
		
		for(MatchingGraphPair pair: pairs){
			GraphNode nodeBefore = pair.getNodeBefore();
			GraphNode nodeAfter = pair.getNodeAfter();
			//System.out.println("####################");

			if(nodeBefore != null && nodeAfter != null){
				GraphDiff diff = new GraphDiff(nodeBefore, nodeAfter);
				
				boolean isParsed = isParsed(diff);
				if(!isParsed){
					if(!nodeBefore.isTheSameWith(nodeAfter)){
					
						this.diffs.add(diff);
					}
					else{
						
						this.getCommons().add(diff);
					}
					
					//if(depth != -1 && newLevel <= depth ){
						diffChildren(nodeBefore, nodeAfter, newLevel);											
					//}
				}
				
			}
			else{
				GraphDiff diff = new GraphDiff(nodeBefore, nodeAfter);
				this.diffs.add(diff);
			}
		}
		
	}
	
	private boolean isParsed(GraphDiff diff) {
		if(!diff.getNodeNew().isTheSameWith(diff.getNodeOld())){
			for(GraphDiff gd: this.diffs){
				if(gd.getNodeNew()==diff.getNodeNew() &&
						gd.getNodeOld()==diff.getNodeOld()){
					return true;
				}
			}
		}
		else{
			for(GraphDiff common: this.commons){
				if(common.getNodeNew()==diff.getNodeNew() &&
						common.getNodeOld()==diff.getNodeOld()){
					return true;
				}
			}
		}
		
		return false;
	}

	public List<GraphDiff> getDiffs(){
		return this.diffs;
	}

	public List<GraphDiff> getCommons() {
		return commons;
	}

	public void setCommons(List<GraphDiff> commons) {
		this.commons = commons;
	}

	public int getDepth() {
		return depth;
	}

	public void setDepth(int depth) {
		this.depth = depth;
	}
}
