/**
 * TypeDroid - LintChecker
 * LintChecker.java: Custom Java source code issues detector plug-in for ADT Lint.
 * (C) 2012 @author Frazza Alessandro @ Universita' Ca' Foscari di Venezia.
 */

package it.unive.dais.typedroid.lintent;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.SocketTimeoutException;
import java.rmi.UnexpectedException;
import java.util.ArrayList;
import java.util.List;

import lombok.ast.AstVisitor;
import lombok.ast.Node;

import com.android.tools.lint.detector.api.Context;
import com.android.tools.lint.detector.api.Detector;
import com.android.tools.lint.detector.api.Issue;
import com.android.tools.lint.detector.api.JavaContext;
import com.android.tools.lint.detector.api.Speed;


/**
 * Implements a whole set of checks for Android applications.
 * Amongst them it looks for DLM annotations inside the code and type checks it in order to assure
 * there's no undesired information flow.
 * It will also try ensure type safety amongst startActivities, Intents and onResults.
 */
public class Lintent extends Detector implements Detector.JavaScanner{

	private boolean aborted = false;
	private boolean clientMode = false;
	private Socket communicationSocket = null;
	private Process lintentEngineProcess;
	private AstPrinterVisitor visitor = null;
	private static ServerSocket serverSocket = null;
	private static PrintWriter debugLog = null;
	private static PrintStream errorPrinter = System.err;
	private static IssuesListener issuesListener = null;
	private static ArrayList<JavaContext> contexts = new ArrayList<JavaContext>();

	/**
	 * Constructs a new instance of a LintChecker.
	 */
	public Lintent() {
		try {
			createDebugLog();
			communicationSocket = parseArguments();
			if (!clientMode){
				Lintent.println("communication socket established: " + communicationSocket.getInetAddress().toString());
				
					issuesListener = new IssuesListener(communicationSocket, lintentEngineProcess);
					issuesListener.start();
				Lintent.println("issues listener started.. ");
			}
		} catch (RuntimeException e) {
			errorPrinter.println("RuntimeException: " + e.getMessage());
			aborted = true;
		} catch (IOException e) {
			errorPrinter.println("RuntimeException: " + e.getMessage());
			aborted = true;
		}
	}



	/**
	 * Returns true if this detector applies to the given file.
	 * 
	 * @param context The context to check.
	 * @param file The file in the context to check.
	 * @return True if this detector applies to the given context and file, false otherwise.
	 */
	@Override
	public boolean appliesTo(Context context, File file) {
		// NEEDS TO BE FURTHER INVESTIGATED. e.g. JavaPerformanceDetector.
		// I believe that always true should be ok (we must check every source file).
		return true;
	}



	public static void closeStreams() throws IOException {
		if (Lintent.serverSocket != null)
			Lintent.serverSocket.close();

		if (Lintent.debugLog != null){
			Lintent.debugLog.flush();
			Lintent.debugLog.close();
		}
	}



	public static void createDebugLog() throws IOException{
		if (Config.CREATE_LOG_FILE) {
			final String logFilePath = String.format("%s%slintent_debug.txt", System.getProperty("user.home"), File.separator);
			try {
				if (Config.VERBOSE_DEBUG)
					errorPrinter.println("Creating debug logfile: " + logFilePath);
				File logFile = new File(logFilePath);
				Lintent.debugLog = new PrintWriter(new FileOutputStream(logFile, false));
			} catch (IOException e) {
				String info = "Please verify you have the requested permissions to create such a file.";
				errorPrinter.println(String.format("log file cannot be created: %s. %s", logFilePath, info));
				throw e;
			}
		}
		else
			Lintent.debugLog = null;
	}



	/**
	 * Create a parse tree visitor to process the parse tree. All JavaScanner
	 * detectors must provide a visitor, unless they implement appliesToResourceRefs()
	 * or return non null getApplicableMethodNames().
	 * 
	 * @param context The context for the file being analyzed.
	 * @return a visitor.
	 */
	@Override
	public AstVisitor createJavaVisitor(JavaContext context) {

		if (aborted)
			return null;

		contexts.add(context);
		if (null != visitor) {
			Lintent.verbosePrintln("updating visitor context... " + context.file.getPath());
			visitor.setContext(context);
			return visitor;
		}

		final List<File> files = context.getMainProject().getJavaSourceFolders();
		File[] listOfFiles = files.get(files.size() - 1).listFiles();

		while(listOfFiles[listOfFiles.length-1].isDirectory()) {
			listOfFiles = listOfFiles[listOfFiles.length-1].listFiles();
		}

		int n = listOfFiles.length-1;
		String lastClassName = listOfFiles[n].getName();
		while(!lastClassName.contains(".java")) {
			n--;
			if (n >= 0)
				lastClassName = listOfFiles[n].getName();
			else{
				File father = listOfFiles[0].getParentFile();
				File[] grandpaList = father.getParentFile().listFiles();
				int k = 0;
				while (grandpaList[k] != father)
					k++;

				if (k == 0)
					listOfFiles = grandpaList[0].getParentFile().listFiles();
				else
					listOfFiles = grandpaList[k-1].listFiles();

				n = listOfFiles.length - 1;
				lastClassName = listOfFiles[n].getName();
			}
		}

		lastClassName = lastClassName.replaceAll(".java", "");
		Lintent.verbosePrintln("lastclassname: " + lastClassName);
		Lintent.verbosePrintln("creating visitor... ");
		try {
			visitor = new AstPrinterVisitor(context, communicationSocket, lastClassName);
		}
		catch (IllegalArgumentException e) {
			aborted = true;
			errorPrinter.println(e.getMessage() + " Aborting...");
		}
		return visitor;

	}


	/**
	 * Returns the list of all issues that can be found by this detector. The method initializes
	 * and populates the list every time it is called, since it's supposed to be called only once.
	 * Notice that it's a static method since it must be called by our custom IssueRegistry while
	 * an instance of this class doesn't exist yet.
	 * 
	 * @return The list of all issues possibly found by this checker.
	 */
	public static List<Issue> getIssues() {
		List<Issue> issues = new ArrayList<Issue>(Config.NUMBER_OF_ISSUES);
		issues.add(Config.ISSUE_ANNOTATION);
		issues.add(Config.ISSUE_HINT);
		issues.add(Config.ISSUE_INFORMATION_FLOW);
		issues.add(Config.ISSUE_INTENT);
		issues.add(Config.ISSUE_NOT_IMPLEMENTED);
		issues.add(Config.ISSUE_PARTIAL_EVALUATION);
		issues.add(Config.ISSUE_PERMS);
		issues.add(Config.ISSUE_UNEXPECTED);
		issues.add(Config.ISSUE_UNKNOWN);
		return issues;
	}


	public static IssuesListener getIssuesListener(){
		return issuesListener;
	}


	/**
	 * Return the types of AST nodes that the visitor returned from
	 * {@link #createJavaVisitor(JavaContext)} should visit, in order to make it
	 * more efficient. By returning null, the visitor will process the full tree.
	 *
	 * @return the list of applicable node types (AST node classes), or null.
	 */
	@Override
	public List<Class<? extends Node>> getApplicableNodeTypes() {
		return null;
	}



	public static ArrayList<JavaContext> getContexts(){
		return contexts;
	}



	/**
	 * Returns the expected speed of this detector.
	 * 
	 * @return the expected speed of this detector.
	 */
	@Override
	public Speed getSpeed() {
		// MUST BE REWRITTEN ONCE THE CHECKER IS COMPLETE!!!!!!!
		return Speed.NORMAL;
	}



	public static void logPrintln(String s){
		if (!Config.CREATE_LOG_FILE)
			return;
		if (null == debugLog)
			return;

		debugLog.println(s);
		debugLog.flush();
	}



	static synchronized public void println(String s){
		Lintent.logPrintln(s);
		if (Config.PRINT_TO_STDERR)
			errorPrinter.println(s);
	}
	
	
	
	static synchronized public void printStackTrace(Exception e){
		if (Config.CREATE_LOG_FILE)
			e.printStackTrace(debugLog);
	}



	static synchronized public void verbosePrintln(String s){
		if (!Config.VERBOSE_DEBUG) 
			return;

		Lintent.println(s);
	}


	private String getJarFolder() {
		// get name and path
		String name = getClass().getName().replace('.', '/');
		name = getClass().getResource("/" + name + ".class").toString();
		// remove junk
		name = name.substring(0, name.indexOf(".jar"));
		name = name.substring(name.lastIndexOf(':')-1, name.lastIndexOf('/')+1).replace('%', ' ');
		// remove escape characters
		String s = "";
		for (int k=0; k<name.length(); k++) {
			s += name.charAt(k);
			if (name.charAt(k) == ' ') k += 2;
		}
		// replace '/' with system separator char
		return s.replace('/', File.separatorChar);
	}



	/**
	 * 
	 * @return
	 * @throws IOException
	 */
	private Socket parseArguments() throws IOException {

		String s = "", argsFullPath = "", engineFullPath = "";
		String engineFolder;

		engineFolder = getJarFolder();
		Lintent.verbosePrintln("looking for args file: " + engineFolder + Config.ARGS_FILENAME);
		File f = null;
		try {
			f = new File(engineFolder, Config.ARGS_FILENAME);
			clientMode = f.isFile() && f.canRead();
		}
		catch (Exception e) {
			clientMode = false;
		}

		argsFullPath = engineFolder + Config.ARGS_FILENAME;
		engineFullPath = engineFolder + Config.ENGINE_FILENAME;

		if (clientMode) {
			try (InputStreamReader argsStream = new InputStreamReader(new FileInputStream(argsFullPath));
				BufferedReader br = new BufferedReader(argsStream)) {
				s = br.readLine();
				if (s.equals("--client-mode")) {
					br.close();
					Lintent.println("engine is in client mode.");
					return new Socket(Config.FSHARP_ENGINE_HOST, Config.SOCKET_LISTENING_PORT);
				}
				br.close();
			}
			catch (FileNotFoundException e) {
				aborted = true;
				throw new RuntimeException("Couldn't find args file '" + argsFullPath + "'. Please verify that " +
						"the LintentEngine creates it. Please also recall that the LintentEngine will automatically " +
						"delete the file before ending itself.");
			}
			catch (IOException e){
				Lintent.printStackTrace(e);
				throw new IOException("Error while reading the args file. Please verify that it can be found at '" +
						argsFullPath + " and that both the Lintent plugin and the LintentEngine are up-to-date.");
			}
		}
		else {
			Lintent.println("spawning engine in server mode...");
			String engineArgs = " --server-mode --log-file log.txt";
			String engineCmd = engineFolder + File.separator + Config.ENGINE_FILENAME + engineArgs;
			try {
				lintentEngineProcess = Runtime.getRuntime().exec(engineCmd, null, new File(engineFolder));
			} catch (IOException e) {
				String error = e.getClass().getName() + " while trying to launch the LintentEngine.exe executable. " +
						"Please verify that both the exe and its dependencies are inside the folder: " + engineFolder;
				Lintent.printStackTrace(e);
				aborted = true;
				throw new IOException(error);
			}

			Lintent.verbosePrintln("child process (" + engineFullPath +") started");
			try {
				Lintent.verbosePrintln("listening for connections from the LintentEngine...");
				Lintent.serverSocket = new ServerSocket(Config.SOCKET_LISTENING_PORT);
				Lintent.serverSocket.setSoTimeout(Config.SOCKET_TIMEOUT);
				Socket commSocket = serverSocket.accept();
				return commSocket;
			}
			catch (SocketTimeoutException e){
				Lintent.printStackTrace(e);
				aborted = true;
				throw new RuntimeException("SocketTimeoutException while waiting for a connection from the LintentEngine " +
						"executable. Please verify that the executable is up-to-date and that it has access to all of its " +
						"required dependencies.");
			}
			catch (IOException e){
				Lintent.printStackTrace(e);
				aborted = true;
				throw new IOException("Error while trying to accept a connection from the LintentEngine executable.");
			}
		}

		throw new UnexpectedException("Unexpected: LintentEngine should have been spawned in server mode but " +
				"the operation has been aborted.");		
	}

}
