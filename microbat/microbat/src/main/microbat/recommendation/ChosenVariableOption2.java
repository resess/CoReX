package microbat.recommendation;

import java.util.ArrayList;
import java.util.List;
import microbat.model.trace.TraceNode;

import microbat.model.value.VarValue;
import sav.common.core.Pair;

/**
 * This class represents an option when a simulated user provide wrong-variable-value feedback.
 * 
 * @author Yun Lin
 *
 */
public class ChosenVariableOption2 {
//	private VarValue readVar;
	private VarValue writtenVar;
	private Pair<TraceNode, VarValue> readVar;

	public ChosenVariableOption2(Pair<TraceNode, VarValue> readVar, VarValue writtenVar) {
		super();
//		this.readVar = readVar;
		this.writtenVar = writtenVar;
	}

	@Override
	public String toString() {
		return "[readVar=" + readVar + ", writtenVar=" + writtenVar + "]";
	}

	public List<String> getIncludedWrongVarID(){
		List<String> varIDs = new ArrayList<>();
		if(readVar != null){
			varIDs.add(readVar.second().getVarID());
		}
		if(writtenVar != null){
			varIDs.add(writtenVar.getVarID());
		}
		
		return varIDs;
	}
	
	public List<VarValue> getIncludedWrongVars(){
		List<VarValue> vars = new ArrayList<>();
		if(readVar != null){
			vars.add(readVar.second());
		}
		if(writtenVar != null){
			vars.add(writtenVar);
		}
		
		return vars;
	}

	public VarValue getReadVar() {
		return readVar.second();
	}

	public VarValue getWrittenVar() {
		return writtenVar;
	}

	public void setReadVar(Pair<TraceNode, VarValue> readVar) {
		this.readVar = readVar;
	}

	public void setWrittenVar(VarValue writtenVar) {
		this.writtenVar = writtenVar;
	}

}
