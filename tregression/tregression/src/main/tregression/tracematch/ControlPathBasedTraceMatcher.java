package tregression.tracematch;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import microbat.algorithm.graphdiff.GraphDiff;
import microbat.algorithm.graphdiff.HierarchyGraphDiffer;
import microbat.algorithm.graphdiff.SimpleMatcher;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import tregression.TraceNodePairReverseOrderComparator;
import tregression.model.PairList;
import tregression.model.TraceNodePair;
import tregression.separatesnapshots.DiffMatcher;

public class ControlPathBasedTraceMatcher{

	
	public PairList matchTraceNodePair(Trace newTrace, Trace oldTrace, DiffMatcher matcher, String dualOrinPreSS) {
		
		IndexTreeNode newRoot = initVirtualRootWrapper(newTrace);
		IndexTreeNode oldRoot = initVirtualRootWrapper(oldTrace);
		
		HierarchyGraphDiffer differ = new HierarchyGraphDiffer();
		differ.diff(newRoot, oldRoot, false, new HierarchicalIndexTreeMatcher(matcher, dualOrinPreSS), -1);//debug with true?
	
		
		List<GraphDiff> diffList = differ.getDiffs();
		List<TraceNodePair> pList = new ArrayList<>();

		//System.out.println("debug: diff lists: " + diffList);
		for (GraphDiff diff : diffList) {
			if (diff.getDiffType().equals(GraphDiff.UPDATE)) {
				IndexTreeNode wrapperNew = (IndexTreeNode) diff.getNodeNew();
				IndexTreeNode wrapperOld = (IndexTreeNode) diff.getNodeOld();
				TraceNodePair pair = new TraceNodePair(wrapperNew.getTraceNode(), wrapperOld.getTraceNode());
				pair.setExactSame(false);
				pList.add(pair);
			}
		}
		//System.out.println("debug: common lists: " + differ.getCommons());
		for (GraphDiff common : differ.getCommons()) {
			IndexTreeNode wrapperNew = (IndexTreeNode) common.getNodeNew();
			IndexTreeNode wrapperOld = (IndexTreeNode) common.getNodeOld();
			TraceNodePair pair = new TraceNodePair(wrapperNew.getTraceNode(), wrapperOld.getTraceNode());
			pair.setExactSame(true);
			pList.add(pair);
		}

		Collections.sort(pList, new TraceNodePairReverseOrderComparator());
		PairList pairList = new PairList(pList);
		return pairList;
	}
	
	private IndexTreeNode initVirtualRootWrapper(Trace trace) {
		TraceNode virtualNode = new TraceNode(null, null, -1, trace);
		//System.out.println("debug: root Before change: " +virtualNode);

		List<TraceNode> topList = trace.getTopMethodLevelNodes();
		virtualNode.setInvocationChildren(topList);
		
//		Map<TraceNode, IndexTreeNode> linkMap = new TreeMap<>(new Comparator<TraceNode>() {
//
//			@Override
//			public int compare(TraceNode o1, TraceNode o2) {
//				return o1.getOrder()-o2.getOrder();
//			}
//		});

		Map<TraceNode, IndexTreeNode> linkMap = new HashMap<TraceNode, IndexTreeNode>();
		
		IndexTreeNode root = new IndexTreeNode(virtualNode, linkMap);
		
		return root;
	}
}
