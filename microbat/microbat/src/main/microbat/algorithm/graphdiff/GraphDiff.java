package microbat.algorithm.graphdiff;

import microbat.model.value.GraphNode;

public class GraphDiff {
	public static final String ADD = "add";
	public static final String REMOVE = "remove";
	public static final String UPDATE = "update";
	
	private GraphNode nodeNew;
	private GraphNode nodeOld;
	
	public GraphDiff(GraphNode nodeBefore, GraphNode nodeAfter) {
		super();
		
		if(nodeBefore == null && nodeAfter == null){
			System.err.println("both before-node and after-node are empty!");
		}
			
		this.nodeNew = nodeBefore;
		this.nodeOld = nodeAfter;
		
	}
	
	public GraphNode getChangedNode(){
		GraphNode node = getNodeOld();
		if(node == null){
			node = getNodeNew();
		}
		
		return node;
	}
	
	public String toString(){
		StringBuffer buffer = new StringBuffer();
		String diffType = getDiffType();
		buffer.append(diffType + ": ");
		if(this.nodeNew != null){
			buffer.append(this.nodeNew.toString());
		}
		if(diffType.equals(GraphDiff.UPDATE)){
			buffer.append(" -> ");
		}
		if(this.nodeOld != null){
			buffer.append(this.nodeOld.toString());
		}
		
		return buffer.toString();
	}

	public String getDiffType(){
		if(this.nodeNew == null && this.nodeOld != null){
			return GraphDiff.ADD;
		}
		else if(this.nodeNew != null && this.nodeOld == null){
			return GraphDiff.REMOVE;
		}
		else if(this.nodeNew != null && this.nodeOld != null){
			return GraphDiff.UPDATE;
		}
		else{
			System.err.println("both new-node and old-node are empty for a change!");
			return null;
		}
	}

	public GraphNode getNodeNew() {
		return nodeNew;
	}

	public void setNodeBefore(GraphNode nodeBefore) {
		this.nodeNew = nodeBefore;
	}

	public GraphNode getNodeOld() {
		return nodeOld;
	}

	public void setNodeAfter(GraphNode nodeAfter) {
		this.nodeOld = nodeAfter;
	}
	
	
}
