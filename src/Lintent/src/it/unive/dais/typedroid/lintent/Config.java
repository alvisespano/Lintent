package it.unive.dais.typedroid.lintent;

import java.io.File;

import com.android.tools.lint.detector.api.Category;
import com.android.tools.lint.detector.api.Issue;
import com.android.tools.lint.detector.api.Scope;
import com.android.tools.lint.detector.api.Severity;

public class Config {

	public static final boolean DEBUG = false;
	public static final boolean DEBUG_IMPORT_UNFOLDING = false;
	public static final boolean CREATE_LOG_FILE = DEBUG;
	public static final boolean PRINT_TO_STDERR = DEBUG;
	public static final boolean REPORT_UNEXPECTED_TOKEN_AS_ERROR = !DEBUG;
	public static final boolean VERBOSE_DEBUG = false;
	public static final int SOCKET_LISTENING_PORT = 52341;
	public static final int SOCKET_TIMEOUT = 30000;

	public static final String ACTIVITY_TAG = "activity";
	public static final String ANDROID_PLATFORM_JAR_LOC = System.getenv("ANDROID_LIBRARY");
	public static final String ARGS_FILENAME = "lintent_args.txt";
	public static final String EOF = "$EOF$";
	public static final String ENGINE_FILENAME = "LintentEngine.exe";
	public static final String FSHARP_ENGINE_HOST = "127.0.0.1";
	public static final String JAVAP_ERROR_MSG_START = "Error:";
	public static final String LOCATION_UNKNOWN_FILENAME = "<UNKNOWN-FILE>";	
	public static final String MANIFEST_RELATIVE_PATH = File.separator + "AndroidManifest.xml";
	public static final String MANIFEST_USES_PERMISSION_TAG = "uses-permission";
	public static final String MANIFEST_USES_PERMISSION_ATTRIBUTE = "android:name";
	public static final String MANIFEST_DEFINED_PERMISSIONS_TAG = "permission";
	public static final String MANIFEST_TAG = "manifest";
	public static final String MANIFEST_PACKAGE = "package";
	public static final String MANIFEST_ACTIVITY_NAME = "android:name";
	public static final String MANIFEST_ACTIVITY_CALLING_PERMISSION = "android:permission";
	public static final String REPORT_SEPARATOR = "$&$";
	public static final String TAG_DEBUG = "[DEBUG]";
	public static final String TAG_FATAL = "[FATAL]";
	public static final String TAG_HINTS = "[HINT]";
	public static final String TAG_ISSUES = "[ISSUE]";
	
	public static final String[] JAVA_IMPLICIT_IMPORTS = {"java.lang"};
	public static final String[] MANIFEST_DEFINED_PERMISSIONS_ATTRIBUTES = { "android:description", 
		"android:icon","android:label","android:name","android:permissionGroup","android:protectionLevel" };

	public static final Issue ISSUE_ANNOTATION = Issue.create("Lintent: Annotation", "Checks for the correctness of Lintent annotations.", 
			"Lintent allows you to use specific annotations in order to enforce typing inference. This issues is reported anytime there's something wrong with them.", 
			Category.CORRECTNESS, 4, Severity.WARNING, Lintent.class, Scope.JAVA_FILE_SCOPE); 
	
	public static final Issue ISSUE_HINT = Issue.create("Lintent: Hint", "Presents some hints to the programmer.", 
			"Gives the programmer some hints in order to obtain a safer and better application.",
			Category.SECURITY, 2, Severity.INFORMATIONAL, Lintent.class, Scope.JAVA_FILE_SCOPE);
	
	public static final Issue ISSUE_INFORMATION_FLOW = Issue.create("Lintent: Information Flow", "Reports all illegal information flows found by the LintentEngine.", 
			"Thoroughly describes type errors thrown by the DLM checker that point to potential illegal information flows.", 
			Category.SECURITY, 8, Severity.ERROR, Lintent.class, Scope.JAVA_FILE_SCOPE);
	
	public static final Issue ISSUE_INTENT = Issue.create("Lintent: Intent", "Checks for error within the Intent system.", 
			"Looks for any possible error or unrecommended behaviour during the creation and/or the manipulation of Intents.", 
			Category.CORRECTNESS, 8, Severity.ERROR, Lintent.class, Scope.JAVA_FILE_SCOPE);

	public static final Issue ISSUE_NOT_IMPLEMENTED = Issue.create("Lintent: Not Implemented", "Reports all situations not yet implemented in the LintentEngine.", 
			"Warns the user that the LintentEngine can't complete some kind of analysis on the given node because it's not fully implemented yet.", 
			Category.CORRECTNESS, 6, Severity.WARNING, Lintent.class, Scope.JAVA_FILE_SCOPE);

	public static final Issue ISSUE_PARTIAL_EVALUATION = Issue.create("Lintent: Partial Evaluation", "Report problems with static evaluation.", 
			"!!Placeholder!!", 
			Category.CORRECTNESS, 6, Severity.WARNING, Lintent.class, Scope.JAVA_FILE_SCOPE);

	public static final Issue ISSUE_PERMS = Issue.create("Lintent: Permissions", "Looks for code that breaks permissions rules.", 
			"!!Placeholder!!", 
			Category.CORRECTNESS, 8, Severity.ERROR, Lintent.class, Scope.JAVA_FILE_SCOPE);

	public static final Issue ISSUE_UNEXPECTED = Issue.create("Lintent: Unexpected", "Reports unexpected LintentEngine's exceptions.", 
			"This issue contains detailed description of everything that caused an unexpected exception in the LintentEngine.", 
			Category.CORRECTNESS, 8, Severity.ERROR, Lintent.class, Scope.JAVA_FILE_SCOPE);

	public static final Issue ISSUE_UNKNOWN = Issue.create("Lintent: Unknown", "Reports all situations unknown by the LintentEngine.", 
			"Unknown", 
			Category.CORRECTNESS, 6, Severity.WARNING, Lintent.class, Scope.JAVA_FILE_SCOPE);
	
	
//	public static final Issue ISSUE_ILLEGAL_INFORMATION_FLOW = Issue.create("Lintent: Illegal Information Flow", "Checks for illegal information flows.", 
//			"Checks for the presence of eventual illegal information flows that would allow potential dangerous information leaks.",
//			Category.SECURITY, 8, Severity.ERROR, Lintent.class, Scope.JAVA_FILE_SCOPE);
	
	public static final int NUMBER_OF_ISSUES = 9;
	
	public static RuntimeException newPackageNotFoundException(String packageName){
		return new RuntimeException("Lintent ClassLoader couldn't find resources for the package: " + packageName);
	}
	
	public static RuntimeException newClassNotFoundException(String packageName, String className){
		String s = String.format("Lintent ClassLoader couldn't load class \"%s\" inside package \"%s\"", className, packageName);
		return new RuntimeException(s);
	}
	
	/**
	 * Tells whether or not the imported path is already imported by default, rending it useless.
	 * @param imported The package defined by the import (e.g: java.lang.*, java.util.ArrayList, etc..)
	 * @return True if the import is part of any of the default loaded packages, false otherwise.
	 */
	public static boolean isDefaultImport(String imported){
		String s = imported.replace(".*", "");
		for (int i = 0; i < JAVA_IMPLICIT_IMPORTS.length; i++)
			if (s.startsWith(Config.JAVA_IMPLICIT_IMPORTS[i]))
				return true;
		return false;
	}
	
	
}
