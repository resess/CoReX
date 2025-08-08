package tregression.empiricalstudy;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;

import microbat.model.trace.TraceNode;
import tregression.model.TraceNodePair;

public class TraceNodePairOrderComparator implements Comparator<TraceNode>{
	BiMap<TraceNode, String> Slicer4J = HashBiMap.create();
	HashMap<String, List<String>> Slicer4JBytecodeMapping = new HashMap<>();
	public TraceNodePairOrderComparator(BiMap<TraceNode, String> Slicer4J,
			HashMap<String, List<String>> Slicer4JBytecodeMapping) {
		this.Slicer4J=Slicer4J;
		this.Slicer4JBytecodeMapping = Slicer4JBytecodeMapping;
	}
	public TraceNodePairOrderComparator() {
		
	}

	@Override
	public int compare(TraceNode node1, TraceNode node2) {	    
		List<Integer> positions = getSlicer4JMappedNode(node1,Slicer4J,Slicer4JBytecodeMapping);
		List<Integer> positions2 = getSlicer4JMappedNode(node2,Slicer4J,Slicer4JBytecodeMapping);
		return positions.get(0) - positions2.get(0);
		//return node1.getOrder() - node2.getOrder();
	}

	private List<Integer> getSlicer4JMappedNode(TraceNode node1, BiMap<TraceNode, String> slicer4j2,
			HashMap<String, List<String>> slicer4jBytecodeMapping2) {
		String Slicer4JStmt = slicer4j2.get(node1);
		List<Integer> integers = new ArrayList<>();
		if(slicer4jBytecodeMapping2.containsKey(Slicer4JStmt)) {
			List<String> bytecodes = slicer4jBytecodeMapping2.get(Slicer4JStmt);			
			for(String bytecode: bytecodes) {
				Integer id = Integer.valueOf(bytecode.split(", ")[0]);
				integers.add(id);
			}			
		}
		return integers;
	}



	
	
}
