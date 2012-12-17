/**
 * TypeDroid - LintChecker
 * LintCheckerRegistry.java: Custom issues registry plugin for ADT Lint.
 * (C) 2012 @author Frazza Alessandro @ Universita' Ca' Foscari di Venezia.
 */

package it.unive.dais.typedroid.lintent;

import java.util.ArrayList;
import java.util.List;
import com.android.tools.lint.client.api.IssueRegistry;
import com.android.tools.lint.detector.api.Issue;

/**
 * Custom implementation of an issue registry. Its purpose is to register all our custom issues
 * and to expose them to BuiltinIssueRegistry class in the Lint API. This way our list of issues
 * will be merged with the default one, allowing our code to be called as expected.
 * In order to be recognized by the BuiltinIssueRegistry, this class must be pointed by the manifest
 * found inside our project jar.
 */
public class LintentRegistry extends IssueRegistry{

	List<Issue> issues;
	
	
	/**
	 * Constructs a new LintCheckerRegistry.
	 */
	public LintentRegistry(){
		createIssuesList();
	}
	
	
	
	/**
	 * Initializes and populates the list of issues registered by this IssueRegistry.
	 */
	private void createIssuesList(){
		issues = new ArrayList<Issue>();
		
		/* For each Detector, gets a list of all possible issues and adds them all. */
		issues.addAll(Lintent.getIssues());
	}
	
	
	
	
	/**
     * Returns the list of issues that can be found by all our custom detectors.
     *
     * @return the list of issues to be checked (including possibly disabled ones).
     */
	@Override
	public List<Issue> getIssues() {
		
		if (issues == null)
			createIssuesList();
		
		return issues;
	}
	

}
