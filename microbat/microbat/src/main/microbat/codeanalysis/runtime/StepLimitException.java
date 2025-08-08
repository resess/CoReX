package microbat.codeanalysis.runtime;

public class StepLimitException extends Exception {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private static final String ERROR_MSG = "Step Limit Exceeded";
	public int StepLenth = 0;

	public StepLimitException(int i) {
		super(ERROR_MSG);
		this.StepLenth = i;
	}

}
