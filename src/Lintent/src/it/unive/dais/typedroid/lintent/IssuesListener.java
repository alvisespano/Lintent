package it.unive.dais.typedroid.lintent;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.Socket;
import java.rmi.UnexpectedException;
import java.util.Scanner;
import java.util.StringTokenizer;

import com.android.tools.lint.detector.api.DefaultPosition;
import com.android.tools.lint.detector.api.Issue;
import com.android.tools.lint.detector.api.JavaContext;
import com.android.tools.lint.detector.api.Location;



public class IssuesListener extends Thread {
	
	private BufferedReader socketReader;
	private LintentStreamReader stdoutReader;
	private LintentStreamReader stderrReader;
	private Socket socket;
	private boolean eof = false;
	
	/**
	 * Creates a new IssuesListener object. It will scan the inputStream looking for replies by the
	 * LintentEngine, in order to have them reraised to the ADT Lint tool.
	 * @param inputStream The input stream to be listened to.
	 */
	public IssuesListener(Socket socket, Process lintentEngine) throws IOException{
		this.socket = socket;
		this.socketReader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
		this.stdoutReader = new LintentStreamReader(lintentEngine.getInputStream(), "<LINTENT_STDOUT> ");
		this.stderrReader = new LintentStreamReader(lintentEngine.getErrorStream(), "<LINTENT_STDERR> ");
		Lintent.verbosePrintln("issue listener created...");
	}

	@Override
	public void run() throws RuntimeException{
		
		String s = "";
		
		Thread stdoutThread = new Thread(stdoutReader);
		Thread stderrThread = new Thread(stderrReader);
		stdoutThread.start();
		stderrThread.start();
		
		while (!eof){
			try{
				s = socketReader.readLine();
				eof = (s == null) || (parseReport(s));
				Lintent.verbosePrintln(s);
			} catch (Exception e){
				try {
					if (socket.getInputStream().read() < 0)
						eof = true;
				} catch (IOException e1) {
					Lintent.printStackTrace(e1);
					throw new RuntimeException("Exception while trying to parse LintentEngine's output: " + e.getMessage());
				}
			}

			if (eof){
				Lintent.println("<LINTENT_ENGINE_SOCKET> closing socket... ");
				stdoutReader.stopReading();
				stderrReader.stopReading();
				try {
					socketReader.close();
					socket.close();
				} catch (IOException e) {
					throw new RuntimeException("Exception while Lintent plugin was trying to close socket " +
							"communications with LintentEngine: " + e.getMessage());
				}
			}
		}
		try {
			stdoutThread.join();
			stderrThread.join();
			Lintent.verbosePrintln("StreamReaders closed.");
		} catch (InterruptedException e) {
			throw new RuntimeException("InterruptedException while the main thread was waiting StreamReader " +
					"threads in order to join with them.");
		}
		
	}
	
	
	
	/**
	 * 
	 * @param report
	 * @return
	 */
	private static boolean parseReport(String report) throws IllegalArgumentException, UnexpectedException {
		
		String error = "Couldn't parse correctly the output of the LintentEngine: " + report + ".\n";
		StringTokenizer st = new StringTokenizer(report, Config.REPORT_SEPARATOR);
		
		if (st.countTokens() <= 0){
			if (Config.REPORT_UNEXPECTED_TOKEN_AS_ERROR)
				throw new IllegalArgumentException(error + "No valid token found.");
			Lintent.println("<LINTENT_SOCKET_UNEXPECTED> " + report);
			return false;
		}
			
		String token = st.nextToken();
		if (token.equals(Config.TAG_ISSUES)){
			if (st.countTokens() != 3)
				throw new IllegalArgumentException(error + "Three tokens expected (after the TAG token), but found " + st.countTokens() + ".");
			raiseIssue(st.nextToken(), parseIssue(st.nextToken()), st.nextToken());
		}
		else if (token.equals(Config.TAG_HINTS)){
			if (st.countTokens() != 2)
				throw new IllegalArgumentException(error + "Two tokens expected (after the TAG token), but found " + st.countTokens() + ".");
			raiseIssue(st.nextToken(), Config.ISSUE_HINT, st.nextToken());
		}
		else if (token.equals(Config.TAG_DEBUG)){
			if (st.countTokens() != 1)
				throw new IllegalArgumentException(error + "One token expected (after the TAG token), but found " + st.countTokens() + ".");
			Lintent.println("<LINTENT_SOCKET_DEBUG> " + st.nextToken());
		}
		else if (token.equals(Config.TAG_FATAL)){
			if (st.countTokens() != 2)
				throw new IllegalArgumentException(error + "Two tokens expected (after the TAG token), but found " + st.countTokens() + ".");
			raiseIssue(null, parseIssue(st.nextToken()), st.nextToken());
			return true;
		}
		else{
			if (Config.REPORT_UNEXPECTED_TOKEN_AS_ERROR)
				throw new IllegalArgumentException(error + "No valid (or unexpected) TAG token found.");
			Lintent.println("<LINTENT_SOCKET_UNEXPECTED> " + report);
			return false;
		}
		
		return false;
		
	}
	
	
	
	/**
	 * 
	 * @param location
	 * @param issue
	 * @param message
	 * @throws IllegalArgumentException
	 * @throws UnexpectedException
	 */
	private static void raiseIssue(String location, Issue issue, String message) 
										throws IllegalArgumentException, UnexpectedException {

		File unitFile = null;
		JavaContext context = null;
		Location issueLocation = null;
		String fileName = "", line = "", column = "";
		
		if (location != null){
			int colon = location.indexOf(":");
			int comma = location.indexOf(",");
			
			if ((colon < 1) || (comma < 1))
				throw new IllegalArgumentException("Location \"" + location + "\" is ill-formed.");
			
			fileName = location.substring(0, colon);
			line = location.substring(colon+1, comma);
			column = location.substring(comma+1);
		}
		

		if (Lintent.getContexts() != null){
			if ((null == location) || (fileName.equals(Config.LOCATION_UNKNOWN_FILENAME))){
				context = Lintent.getContexts().get(0);
				if (context != null){
					context.report(issue, null, message, null);
					return;
				}
			}
			else
				for (JavaContext c : Lintent.getContexts())
					if (c.file.getName().contains(fileName)){
						context = c;
						unitFile = c.file;
					}
		}
		
		if (null == context)
			throw new UnexpectedException("Couldn't obtain any JavaContext from Lint. Couldn't report " +
					"issue \"" + issue.getId() + "\": " + message);
		
		int lineBegin = Integer.MIN_VALUE, lineEnd = Integer.MIN_VALUE;
		int colBegin = Integer.MIN_VALUE, colEnd = Integer.MIN_VALUE;
		
		int dash = line.indexOf("-");
		
		try{
			if (dash < 0){
				lineBegin = Integer.parseInt(line);
				lineEnd = lineBegin;
			}
			else{
				lineBegin = Integer.parseInt(line.substring(0, dash));
				lineEnd = Integer.parseInt(line.substring(dash+1));
			}
			
			dash = column.indexOf("-");

			if (dash < 0){
				colBegin = Integer.parseInt(column);
				colEnd = colBegin;
			}
			else{
				colBegin = Integer.parseInt(column.substring(0, dash));
				colEnd = Integer.parseInt(column.substring(dash+1));
			}
		}
		catch (NumberFormatException e){
			Lintent.println("NumberFormatException in " + line + "," + column + ": " + e.getMessage());
			context.report(issue, null, message, null);
		}
		
		issueLocation = Location.create(unitFile, new DefaultPosition(lineBegin, colBegin, -1), new DefaultPosition(lineEnd, colEnd, -1));
		
		context.report(issue, issueLocation, message, null);
		
	}
	
	
	
	/**
	 * Tells whether or not the listener recognized the LintentEngine to have already finished reporting issues.
	 * @return True if it's still reading the socket for LintentEngine further input, false if it has already finished.
	 */
	public boolean isReading(){
		return !eof;
	}
	
	
	
	/**
	 * Given a string representing the ID of an issue returns an instance of that type of issue.
	 * @param issueID The ID of the desired issue.
	 * @return An instance of that type of issue.
	 */
	private static Issue parseIssue(String issueID){

		if (issueID.equals("Annotation"))
			return Config.ISSUE_ANNOTATION;
		if (issueID.equals("Hint"))
			return Config.ISSUE_HINT;
		if (issueID.equals("InformationFlow"))
			return Config.ISSUE_INFORMATION_FLOW;
		if (issueID.equals("Intent"))
			return Config.ISSUE_INTENT;
		if (issueID.equals("NotImplemented"))
			return Config.ISSUE_NOT_IMPLEMENTED;
		if (issueID.equals("PartialEvaluation"))
			return Config.ISSUE_PARTIAL_EVALUATION;
		if (issueID.equals("Perms"))
			return Config.ISSUE_PERMS;
		if (issueID.equals("Unexpected"))
			return Config.ISSUE_UNEXPECTED;
		if (issueID.equals("Unknown"))
			return Config.ISSUE_UNKNOWN;
		
		throw new RuntimeException("Couldn't find issue \"" + issueID + "\" in the list of Lintent issues.");
		
	}

}



class LintentStreamReader implements Runnable{

	private boolean eof;
	private String tag = "";
	private Scanner scanner = null;
	
	public LintentStreamReader(InputStream istream, String tag){
		this.eof = false;
		this.scanner = new Scanner(istream);
		this.tag = tag;
	}
	
	@Override
	public void run(){
		while (!eof){
			while (scanner.hasNext())
				Lintent.println(tag + scanner.nextLine());
		}
		scanner.close();
		Lintent.verbosePrintln(tag + " stream closed.");
	}
	
	public void stopReading(){
		eof = true;
	}
	
}
