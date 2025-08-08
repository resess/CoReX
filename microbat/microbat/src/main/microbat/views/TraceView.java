package microbat.views;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;


import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.Dimension;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.resource.FontDescriptor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.AnnotationModel;
import org.eclipse.jface.viewers.DelegatingStyledCellLabelProvider;
import org.eclipse.jface.viewers.DelegatingStyledCellLabelProvider.IStyledLabelProvider;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.StyledCellLabelProvider;
import org.eclipse.jface.viewers.StyledString;
import org.eclipse.jface.viewers.StyledString.Styler;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerCell;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.events.KeyAdapter;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.graphics.TextStyle;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;

import microbat.behavior.Behavior;
import microbat.behavior.BehaviorData;
import microbat.behavior.BehaviorReporter;
import microbat.model.BreakPoint;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.value.VarValue;
import microbat.util.JavaUtil;
import microbat.util.MicroBatUtil;
import microbat.util.Settings;
import sav.common.core.Pair;

public class TraceView extends ViewPart {

	protected List<Trace> traceList;
	protected List<TraceNode> kept_nodes;
	protected List<TraceNode> changed_nodes;
	protected Pair<TraceNode, String> observedFailureNode;
	private String version;
	
	private TraceNode currentNode;
	
	protected Trace trace;
	protected TreeViewer listViewer;

	private Text searchText;
	private CLabel GPTText;
	private Button searchButton;
	private Button nextButton;
	private Button gptButton;
	private Button prevButton;
	
	private boolean firstTime = true;

	private String previousSearchExpression = "";
	private boolean jumpFromSearch = false;

	public TraceView() {
	}

	public void setSearchText(String expression) {
		this.searchText.setText(expression);
		this.previousSearchExpression = expression;
	}

//	private void createSearchBox(Composite parent) {
//		searchText = new Text(parent, SWT.BORDER);
//		searchText.setToolTipText("search trace node by class name and line number, e.g., ClassName line:20 or just ClassName\n"
//				+ "press \"enter\" for forward-search and \"shift+enter\" for backward-search.");
//		FontData searchTextFont = searchText.getFont().getFontData()[0];
//		searchTextFont.setHeight(10);
//		searchText.setFont(new Font(Display.getCurrent(), searchTextFont));
//		searchText.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
//		addSearchTextListener(searchText);
//
//		searchButton = new Button(parent, SWT.PUSH);
//		GridData buttonData = new GridData(SWT.FILL, SWT.FILL, false, false);
//		// buttonData.widthHint = 50;
//		searchButton.setLayoutData(buttonData);
//		searchButton.setText("Go");
//		addSearchButtonListener(searchButton);
//	}
	
	private void createNextPrevBox(Composite parent) {
	    
		Group Group = new Group(parent, SWT.NONE);
		GridData data = new GridData(SWT.FILL, SWT.TOP, true, false);
		data.minimumHeight = 35;
		Group.setLayoutData(data);
		
		GridLayout gl = new GridLayout(2, true);
		Group.setLayout(gl);
		
		nextButton = new Button(Group, SWT.PUSH);
		GridData buttonData = new GridData(SWT.LEFT, SWT.FILL, true, false);
		buttonData.widthHint = 200;
		nextButton.setLayoutData(buttonData);
		nextButton.setText("Next");
		Image image = new Image(PlatformUI.getWorkbench().getDisplay(),System.getProperty("user.dir")+"/icons/next.png");
		nextButton.setImage(image);
		addNextButtonListener(nextButton);
		
		prevButton = new Button(Group, SWT.PUSH);
		buttonData = new GridData(SWT.RIGHT, SWT.FILL, true, false);
		 buttonData.widthHint = 200;
		prevButton.setLayoutData(buttonData);
		prevButton.setText("Previous");
		image = new Image(PlatformUI.getWorkbench().getDisplay(),System.getProperty("user.dir")+"/icons/prev.png");
		prevButton.setImage(image);
		addPrevButtonListener(prevButton);
		
		prevButton.setVisible(false);
		nextButton.setVisible(false);
}
	
	

	private void addPrevButtonListener(Button prevButton) {
		prevButton.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				int index = 0;
				for(int i = 0; i<=kept_nodes.size();i++) {
					if(kept_nodes.get(i).equals(currentNode)) {
						index = i - 1;
						break;				
					}
				}
				if (index>=0)
					jumpToNode(trace, kept_nodes.get(index).getOrder(), true);
			}
		});
		
	}

	private void addNextButtonListener(Button nextButton) {
		nextButton.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				int index = 0;
				for(int i = 0; i<=kept_nodes.size();i++) {
					if(kept_nodes.get(i).equals(currentNode)) {
						index = i + 1;
						break;				
					}
				}
				if (index<kept_nodes.size())
					jumpToNode(trace, kept_nodes.get(index).getOrder(), true);
			}
		});
		
	}

	protected void addSearchTextListener(final Text searchText) {
		searchText.addKeyListener(new KeyAdapter() {
			@Override
			public void keyPressed(KeyEvent e) {
				if (e.keyCode == 27 || e.character == SWT.CR) {

					boolean forward = (e.stateMask & SWT.SHIFT) == 0;

					String searchContent = searchText.getText();
					jumpToNode(searchContent, forward);
				}
			}
		});

	}

	protected void addSearchButtonListener(final Button serachButton) {
		searchButton.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				String searchContent = searchText.getText();
				jumpToNode(searchContent, true);
			}
		});

	}
	
	public void jumpToNode(String searchContent, boolean next) {
		// Trace trace = Activator.getDefault().getCurrentTrace();

		if (!previousSearchExpression.equals(searchContent)) {
			trace.resetObservingIndex();
			previousSearchExpression = searchContent;
		}

		int selectionIndex = -1;
		if (next) {
			selectionIndex = trace.searchForwardTraceNode(searchContent);
		} else {
			selectionIndex = trace.searchBackwardTraceNode(searchContent);
		}
		// int selectionIndex = trace.searchBackwardTraceNode(searchContent);
		if (selectionIndex != -1) {
			this.jumpFromSearch = true;
			jumpToNode(trace, selectionIndex + 1, true);
		} else {
			MessageBox box = new MessageBox(PlatformUI.getWorkbench().getDisplay().getActiveShell());
			box.setMessage("No more such node in trace!");
			box.open();
		}

	}

	/**
	 * indicate a node is selected by tool or human users.
	 */
	private boolean programmingSelection = false;

	/**
	 * indicate whether the program state should be refreshed when a trace node is
	 * selected programmatically.
	 */
	protected boolean refreshProgramState = true;

	public void jumpToNode(Trace trace, int order, boolean refreshProgramState) {
		TraceNode node = trace.getExecutionList().get(order - 1);
		setCurrentNode(node);
		List<TraceNode> path = new ArrayList<>();
		while (node != null) {
			path.add(node);
			node = node.getAbstractionParent();
		}

		/** keep the original expanded list */
		Object[] expandedElements = listViewer.getExpandedElements();
		for (Object obj : expandedElements) {
			TraceNode tn = (TraceNode) obj;
			path.add(tn);
		}

		TraceNode[] list = path.toArray(new TraceNode[0]);
		listViewer.setExpandedElements(list);

		node = trace.getExecutionList().get(order - 1);

		programmingSelection = true;
		this.refreshProgramState = refreshProgramState;
		/**
		 * This step will trigger a callback function of node selection.
		 */
		listViewer.setSelection(new StructuredSelection(node), true);
		programmingSelection = false;
		this.refreshProgramState = true;
		listViewer.refresh();
	}

	@SuppressWarnings("unchecked")
	protected void markJavaEditor(TraceNode node) {
		BreakPoint breakPoint = node.getBreakPoint();
		String qualifiedName = breakPoint.getClassCanonicalName();
		ICompilationUnit javaUnit = JavaUtil.findICompilationUnitInProject(qualifiedName);

		if (javaUnit == null) {
			return;
		}

		try {
			ITextEditor sourceEditor = (ITextEditor) JavaUI.openInEditor(javaUnit);
			AnnotationModel annotationModel = (AnnotationModel) sourceEditor.getDocumentProvider()
					.getAnnotationModel(sourceEditor.getEditorInput());
			/**
			 * remove all the other annotations
			 */
			Iterator<Annotation> annotationIterator = annotationModel.getAnnotationIterator();
			while (annotationIterator.hasNext()) {
				Annotation currentAnnotation = annotationIterator.next();
				annotationModel.removeAnnotation(currentAnnotation);
			}

			IFile javaFile = (IFile) sourceEditor.getEditorInput().getAdapter(IResource.class);
			IDocumentProvider provider = new TextFileDocumentProvider();
			provider.connect(javaFile);
			IDocument document = provider.getDocument(javaFile);
			IRegion region = document.getLineInformation(breakPoint.getLineNumber() - 1);

			if (region != null) {
				sourceEditor.selectAndReveal(region.getOffset(), 0);
			}

			ReferenceAnnotation annotation = new ReferenceAnnotation(false, "Please check the status of this line");
			Position position = new Position(region.getOffset(), region.getLength());

			annotationModel.addAnnotation(annotation, position);

		} catch (PartInitException e) {
			e.printStackTrace();
		} catch (JavaModelException e) {
			e.printStackTrace();
		} catch (BadLocationException e) {
			e.printStackTrace();
		} catch (CoreException e) {
			e.printStackTrace();
		}

	}

	@Override
	public void createPartControl(Composite parent) {
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		parent.setLayout(layout);

//		createSearchBox(parent);
		createNextPrevBox(parent);

		listViewer = new TreeViewer(parent, SWT.V_SCROLL | SWT.H_SCROLL | SWT.BORDER);
		listViewer.getTree().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true, 2, 1));
		listViewer.setContentProvider(new TraceContentProvider());
		listViewer.setLabelProvider(new TraceLabelProvider());
		
		
		// Trace trace = Activator.getDefault().getCurrentTrace();
		listViewer.setInput(trace);

		listViewer.addSelectionChangedListener(new ISelectionChangedListener() {

			@SuppressWarnings("unused")
			public void showDebuggingInfo(TraceNode node) {
				System.out.println("=========================");
				System.out.println("=========================");
				System.out.println("=========================");

				System.out.println("Data Dominator: ");
				for (TraceNode dominator : node.getDataDominators().keySet()) {
					VarValue var = node.getDataDominators().get(dominator);
					System.out.println(dominator);
					System.out.println("by: " + var);

					System.out.println("~~~~~~~~~~~~~~~~~~~~~");
				}

				System.out.println("=========================");

				System.out.println("Data Dominatee: " + node.getDataDominatee());
				for (TraceNode dominatee : node.getDataDominatee().keySet()) {
					VarValue var = node.getDataDominatee().get(dominatee);
					System.out.println(dominatee);
					System.out.println("by: " + var);

					System.out.println("~~~~~~~~~~~~~~~~~~~~~");
				}

				// System.out.println("Control Dominator: ");
				// TraceNode controlDominator = node.getControlDominator();
				// System.out.println(controlDominator);
				// System.out.println("~~~~~~~~~~~~~~~~~~~~~");
				//
				// System.out.println("Control Dominatee: ");
				// for(TraceNode dominatee: node.getControlDominatees()){
				// System.out.println(dominatee);
				// System.out.println("~~~~~~~~~~~~~~~~~~~~~");
				// }

				System.out.println("Invocation Parent: ");
				System.out.println(node.getInvocationParent());
				System.out.println("~~~~~~~~~~~~~~~~~~~~~");

				// System.out.println("Invocation Children: ");
				// for(TraceNode dominatee: node.getInvocationChildren()){
				// System.out.println(dominatee);
				// System.out.println("~~~~~~~~~~~~~~~~~~~~~");
				// }

				System.out.println("Loop Parent: ");
				System.out.println(node.getLoopParent());
				System.out.println("~~~~~~~~~~~~~~~~~~~~~");

				// System.out.println("Loop Children: ");
				// for(TraceNode dominatee: node.getLoopChildren()){
				// System.out.println(dominatee);
				// System.out.println("~~~~~~~~~~~~~~~~~~~~~");
				// }

				System.out.println("Abstract Parent: ");
				System.out.println(node.getAbstractionParent());
				System.out.println("~~~~~~~~~~~~~~~~~~~~~");

				// System.out.println("Abstract Children: ");
				// for(TraceNode dominatee: node.getAbstractChildren()){
				// System.out.println(dominatee);
				// System.out.println("~~~~~~~~~~~~~~~~~~~~~");
				// }

				System.out.println();
				System.out.println();
			}

			public void selectionChanged(SelectionChangedEvent event) {
				ISelection iSel = event.getSelection();
				if (iSel instanceof StructuredSelection) {
					StructuredSelection sel = (StructuredSelection) iSel;
					Object obj = sel.getFirstElement();

					if (obj instanceof TraceNode) {
						TraceNode node = (TraceNode) obj;
						

//						String simpleSig = node.getMethodSign().substring(node.getMethodSign().indexOf("#")+1, node.getMethodSign().length());
//						MethodFinderBySignature finder = new MethodFinderBySignature(simpleSig);
//						ByteCodeParser.parse(node.getClassCanonicalName(), finder, node.getTrace().getAppJavaClassPath());
//						System.currentTimeMillis();
						
//						 showDebuggingInfo(node);

						if (!programmingSelection) {
							Behavior behavior = BehaviorData.getOrNewBehavior(Settings.launchClass);
							behavior.increaseAdditionalClick();
							new BehaviorReporter(Settings.launchClass).export(BehaviorData.projectBehavior);
						}
 
						otherViewsBehavior(node);
						setCurrentNode(node);

						if (jumpFromSearch) {
							jumpFromSearch = false;

							Display.getDefault().asyncExec(new Runnable() {
								@Override
								public void run() {
									try {
										Thread.sleep(300);
									} catch (InterruptedException e) {
										e.printStackTrace();
									}
									searchText.setFocus();
								}
							});

						} else {
							listViewer.getTree().setFocus();
						}

						trace.setObservingIndex(node.getOrder() - 1);
					}
				}

			}			

		});
		
		appendMenuForTraceStep();
		
		createGPTBox(parent);
	}

	private void createGPTBox(Composite parent) {
	
		Group Group = new Group(parent, SWT.NONE);
		GridData data = new GridData(SWT.FILL, SWT.TOP, true, false);
		
//		data.minimumHeight = 50;
		Group.setLayoutData(data);
		
		GridLayout gl = new GridLayout(1, true);
		Group.setLayout(gl);
//		Group.setVisible(false);
		
		gptButton = new Button(Group, SWT.PUSH);
		GridData buttonData = new GridData(SWT.FILL, SWT.TOP, false, false);
		buttonData.widthHint = 200;
		buttonData.heightHint = 35;
		gptButton.setLayoutData(buttonData);
		gptButton.setText("Get GPT summary");
		Image image = new Image(PlatformUI.getWorkbench().getDisplay(),System.getProperty("user.dir")+"/icons/gpt.jpg");
		gptButton.setImage(image);
		addGPTButtonListener(gptButton);
		gptButton.setVisible(false);
		
		GPTText = new CLabel(Group, SWT.BORDER);
		FontData searchTextFont = GPTText.getFont().getFontData()[0];
		searchTextFont.setHeight(12);
		GPTText.setFont(new Font(Display.getCurrent(), searchTextFont));
		data = new GridData(SWT.FILL, SWT.TOP, true, true);
		GPTText.setLayoutData(data);
		data.minimumHeight = 200;
		data.widthHint = 200;
		int padding = 5;
		GPTText.setMargins(padding, padding, padding, padding);
		GPTText.setVisible(false);
		
	}

	private void addGPTButtonListener(Button gptButton2) {
		gptButton.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				//TODO: get From ChatGPT
				if(observedFailureNode.second().equals("OLD")) {
					GPTText.setText("In the old version of the program, the variable d is calculated as ii * 2, "
							+ "which is then compared to x in the if statement. Since the condition evaluates to false, the subsequent statement "
							+ "within the if block is not executed, leaving c with its original value, calculated as b * 2. "
							+ "Following this, the variable f is determined, and an assertion checks if f equals 35, "
							+ "which likely evaluates to true given the presence of the assert statement. Therefore, in this version, the assertion likely passes.");
				}
				else {
					GPTText.setText("In the new version of the program, the calculation of d is modified to ii * 4. "
							+ "This alteration causes the value of d to exceed x, "
							+ "resulting in the if condition evaluating to true. "
							+ "Consequently, the subsequent statement within the if block executes, updating the value of c. "
							+ "This change potentially alters the value of c, which in turn affects the value of f. "
							+ "Despite f still being subject to the same function, its value may differ due to the altered value of c. "
							+ "Consequently, the assertion, which expects f to equal 35, fails in this new version because the value of f might have been "
							+ "altered by the change in c. Therefore, the assertion failure in the new version can be traced back to the "
							+ "change in the calculation of d, leading to a different path of execution and ultimately affecting the value of f.");
				}
				
			}
		});
		
	}

	protected Action createForSearchAction() {
		Action action = new Action() {
			public void run() {
				if (listViewer.getSelection().isEmpty()) {
					return;
				}

				if (listViewer.getSelection() instanceof IStructuredSelection) {
					IStructuredSelection selection = (IStructuredSelection) listViewer.getSelection();
					TraceNode node = (TraceNode) selection.getFirstElement();
					
					String className = node.getBreakPoint().getDeclaringCompilationUnitName();
					int lineNumber = node.getBreakPoint().getLineNumber();
					String searchString = Trace.combineTraceNodeExpression(className, lineNumber);
					TraceView.this.searchText.setText(searchString);
				}
				
			}
			
			public String getText() {
				return "for search";
			}
		};
		return action;
	}
	
	protected MenuManager menuMgr = new MenuManager("#PopupMenu");
	protected void appendMenuForTraceStep() {
		menuMgr.setRemoveAllWhenShown(true);
		menuMgr.addMenuListener(new IMenuListener() {
			@Override
			public void menuAboutToShow(IMenuManager manager) {
				Action action = createForSearchAction();
				menuMgr.add(action);
				
			}
		});
		
		listViewer.getTree().setMenu(menuMgr.createContextMenu(listViewer.getTree()));
	}
	public void setCurrentNode(TraceNode node) {
		this.currentNode = node;
		if(kept_nodes.get(kept_nodes.size()-1).equals(currentNode)) {
			nextButton.setEnabled(false);
			prevButton.setEnabled(true);
			return;
		}
		if(kept_nodes.get(0).equals(currentNode)) {
			prevButton.setEnabled(false);
			nextButton.setEnabled(true);
			return;
		}
		prevButton.setEnabled(true);
		nextButton.setEnabled(true);
	
	}
	protected void otherViewsBehavior(TraceNode node) {
		DebugFeedbackView feedbackView = MicroBatViews.getDebugFeedbackView();

		if (this.refreshProgramState) {
			feedbackView.setTraceView(TraceView.this);
			feedbackView.refresh(node);
		}

		ReasonView reasonView = MicroBatViews.getReasonView();
		reasonView.refresh(feedbackView.getRecommender());

		markJavaEditor(node);
	}

	public void updateData() {
		listViewer.setInput(trace);
		listViewer.refresh();
	}

	@Override
	public void setFocus() {

	}

	public Trace getTrace() {
		return trace;
	}

	public void setMainTrace(Trace trace) {
		this.trace = trace;
	}
	public void setMainKeptNodes(List<TraceNode> nodes) {
		this.kept_nodes = nodes;
	}
	public void setObservedFailuredNode(Pair<TraceNode, String> node) {
		this.observedFailureNode = node;
		
	}
	public void setChangedNodes(List<TraceNode> nodes) {
		this.changed_nodes = nodes;		
	}
	public List<Trace> getTraceList() {
		return traceList;
	}

	public void setTraceList(List<Trace> traceList) {
		this.traceList = traceList;
	}

	class TraceContentProvider implements ITreeContentProvider {
		public void dispose() {

		}

		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {

		}

		@Override
		public Object[] getChildren(Object parentElement) {
	
			if (parentElement instanceof Trace) {
				if(firstTime) {
					prevButton.setVisible(true);
					nextButton.setVisible(true);
					prevButton.setEnabled(false);
					nextButton.setEnabled(false);
					gptButton.setVisible(true);
					GPTText.setVisible(true);
					firstTime = false;
				}
				
				Trace trace = (Trace) parentElement;
				return trace.getExecutionList().toArray(new TraceNode[0]);
				
			}
//				// List<TraceNode> nodeList = trace.getExectionList();
////				 List<TraceNode> nodeList = trace.getTopMethodLevelNodes();
//				// List<TraceNode> nodeList = trace.getTopLoopLevelNodes();
//				List<TraceNode> nodeList = trace.getTopAbstractionLevelNodes();
//				return nodeList.toArray(new TraceNode[0]);
//			} else if (parentElement instanceof TraceNode) {				
//				TraceNode parentNode = (TraceNode) parentElement;
//				// List<TraceNode> nodeList = parentNode.getInvocationChildren();
//				// List<TraceNode> nodeList = parentNode.getLoopChildren();
//				List<TraceNode> nodeList = parentNode.getAbstractChildren();
//				return nodeList.toArray(new TraceNode[0]);		
//			}
			return null;
		}
		public void addChildren(TraceNode parentNode,List<TraceNode> nodeList) {			
			for(TraceNode node:parentNode.getAbstractChildren()){
				nodeList.add(node);
				if(!node.getAbstractChildren().isEmpty())
					addChildren(node,nodeList);					
			}		
		}

		@Override
		public Object getParent(Object element) {
			return null;
		}

		@Override
		public boolean hasChildren(Object element) {
			if (element instanceof TraceNode) {
				TraceNode node = (TraceNode) element;
				// return !node.getInvocationChildren().isEmpty();
				// return !node.getLoopChildren().isEmpty();
				return !node.getAbstractChildren().isEmpty();
			}
			return false;
		}

		@Override
		public Object[] getElements(Object inputElement) {
			return getChildren(inputElement);
		}

	}
	public class TraceLabelProvider extends StyledCellLabelProvider {

		private Styler defaultStyler;
		private Styler keptStyler;
		private Styler old_failureStyler;
		private Styler new_failureStyler;
		private Styler changeStyler;
		public TraceLabelProvider () {
		        defaultStyler = new Styler() {
		            @Override
		            public void applyStyles(TextStyle textStyle) {	                
		                textStyle.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_GRAY);
		                
		            }
		        };
		        keptStyler = new Styler() {
		            @Override
		            public void applyStyles(TextStyle textStyle) {	                
		                textStyle.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_BLACK);
		                FontData fontData = Display.getCurrent().getSystemFont().getFontData()[0];
		                fontData.setStyle(SWT.BOLD);
		                Font boldFont = new Font(Display.getCurrent(), fontData);
		                textStyle.font = boldFont;
		            }
		        };
		        new_failureStyler = new Styler() {
		            @Override
		            public void applyStyles(TextStyle textStyle) {	                
		            	textStyle.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_BLACK);
		            	textStyle.background = Display.getCurrent().getSystemColor(SWT.COLOR_RED);
		                FontData fontData = Display.getCurrent().getSystemFont().getFontData()[0];
		                fontData.setStyle(SWT.BOLD);
		                Font boldFont = new Font(Display.getCurrent(), fontData);
		                textStyle.font = boldFont;		                
		            }
		        };
		        old_failureStyler = new Styler() {
		            @Override
		            public void applyStyles(TextStyle textStyle) {	                
		            	textStyle.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_BLACK);
		            	textStyle.background = Display.getCurrent().getSystemColor(SWT.COLOR_GREEN);
		                FontData fontData = Display.getCurrent().getSystemFont().getFontData()[0];
		                fontData.setStyle(SWT.BOLD);
		                Font boldFont = new Font(Display.getCurrent(), fontData);
		                textStyle.font = boldFont;		                
		            }
		        };
		        changeStyler = new Styler() {
		            @Override
		            public void applyStyles(TextStyle textStyle) {	                
		            	textStyle.foreground = Display.getCurrent().getSystemColor(SWT.COLOR_RED);
		                FontData fontData = Display.getCurrent().getSystemFont().getFontData()[0];
		                fontData.setStyle(SWT.BOLD);
		                Font boldFont = new Font(Display.getCurrent(), fontData);
		                textStyle.font = boldFont;		                
		            }
		        };
		    }

		public void addListener(ILabelProviderListener listener) {

		}

		public void dispose() {

		}

		public boolean isLabelProperty(Object element, String property) {
			return false;
		}

		public void removeListener(ILabelProviderListener listener) {

		}

		public Image getImage(Object element) {
			if (element instanceof TraceNode) {
				TraceNode node = (TraceNode) element;

				if (node.hasChecked()) {
					if (!node.isAllReadWrittenVarCorrect(true)) {
						return Settings.imageUI.getImage(ImageUI.WRONG_VALUE_MARK);
					} else if (node.isWrongPathNode()) {
						return Settings.imageUI.getImage(ImageUI.WRONG_PATH_MARK);
					} else {
						return Settings.imageUI.getImage(ImageUI.CHECK_MARK);
					}
				} else {
					if(kept_nodes.contains(node))
						return Settings.imageUI.getImage(ImageUI.QUESTION_MARK);
					if(node.equals(observedFailureNode.first())) {
						if("OLD".equals(observedFailureNode.second()))
							return  Settings.imageUI.getImage(ImageUI.CHECK_MARK);
						else if("NEW".equals(observedFailureNode.second()))
							return  Settings.imageUI.getImage(ImageUI.WRONG_VALUE_MARK);
					}
				}
			}

			return null;
		}
		@Override
		    public void update(ViewerCell cell) {
		        Object element = cell.getElement();
		        StyledString styledString = getStyledString(element);
		        cell.setText(styledString.toString());
		        cell.setStyleRanges(styledString.getStyleRanges());
		        Image image = getImage(element);
		        cell.setImage(image);
		        super.update(cell);
		    }

		    @SuppressWarnings("unchecked")
		    private StyledString getStyledString(Object element) {
		    	if (element instanceof TraceNode) {
					TraceNode node = (TraceNode) element;
					
					BreakPoint breakPoint = node.getBreakPoint();
					// BreakPointValue programState = node.getProgramState();

					String className = breakPoint.getClassCanonicalName();
					if (className.contains(".")) {
						className = className.substring(className.lastIndexOf(".") + 1, className.length());
					}

					// String methodName = breakPoint.getMethodName();
					int lineNumber = breakPoint.getLineNumber();
					int order = node.getOrder();

					long duration = node.calulcateDuration();
					

					String message = order + "." + MicroBatUtil.combineTraceNodeExpression(className, lineNumber, duration);
					if(node.equals(observedFailureNode.first())) {
						if("OLD".equals(observedFailureNode.second()))
							return new StyledString(message, old_failureStyler);
						else
							return new StyledString(message, new_failureStyler);
					}
						
					else {
						if(changed_nodes.contains(node))
							return new StyledString(message, changeStyler);
						else {
							if(kept_nodes.contains(node))
								return new StyledString(message, keptStyler);
							else
								return new StyledString(message, defaultStyler);
						}
					}
					
				}
				return null;	       
		    }
		}
	

	public Trace getCurrentTrace() {
		return this.trace;
	}

}
