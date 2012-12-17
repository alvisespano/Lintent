/**
 * TypeDroid - LintChecker
 * AstPrinterVisitor.java: Abstract Syntax Tree Printer visitor.
 * (C) 2012 Frazza Alessandro @ Universita' Ca' Foscari di Venezia.
 */

package it.unive.dais.typedroid.lintent;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Iterator;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import lombok.ast.AlternateConstructorInvocation;
import lombok.ast.Annotation;
import lombok.ast.AnnotationDeclaration;
import lombok.ast.AnnotationElement;
import lombok.ast.AnnotationMethodDeclaration;
import lombok.ast.AnnotationValueArray;
import lombok.ast.ArrayAccess;
import lombok.ast.ArrayCreation;
import lombok.ast.ArrayDimension;
import lombok.ast.ArrayInitializer;
import lombok.ast.Assert;
import lombok.ast.BinaryExpression;
import lombok.ast.BinaryOperator;
import lombok.ast.Block;
import lombok.ast.BooleanLiteral;
import lombok.ast.Break;
import lombok.ast.Case;
import lombok.ast.Cast;
import lombok.ast.Catch;
import lombok.ast.CharLiteral;
import lombok.ast.ClassDeclaration;
import lombok.ast.ClassLiteral;
import lombok.ast.Comment;
import lombok.ast.CompilationUnit;
import lombok.ast.ConstructorDeclaration;
import lombok.ast.ConstructorInvocation;
import lombok.ast.Continue;
import lombok.ast.Default;
import lombok.ast.DoWhile;
import lombok.ast.EmptyDeclaration;
import lombok.ast.EmptyStatement;
import lombok.ast.EnumConstant;
import lombok.ast.EnumDeclaration;
import lombok.ast.EnumTypeBody;
import lombok.ast.ExpressionStatement;
import lombok.ast.FloatingPointLiteral;
import lombok.ast.For;
import lombok.ast.ForEach;
import lombok.ast.ForwardingAstVisitor;
import lombok.ast.Identifier;
import lombok.ast.If;
import lombok.ast.ImportDeclaration;
import lombok.ast.InlineIfExpression;
import lombok.ast.InstanceInitializer;
import lombok.ast.InstanceOf;
import lombok.ast.IntegralLiteral;
import lombok.ast.InterfaceDeclaration;
import lombok.ast.KeywordModifier;
import lombok.ast.LabelledStatement;
import lombok.ast.MethodDeclaration;
import lombok.ast.MethodInvocation;
import lombok.ast.Modifiers;
import lombok.ast.Node;
import lombok.ast.NormalTypeBody;
import lombok.ast.NullLiteral;
import lombok.ast.PackageDeclaration;
import lombok.ast.RawListAccessor;
import lombok.ast.Return;
import lombok.ast.Select;
import lombok.ast.StaticInitializer;
import lombok.ast.StringLiteral;
import lombok.ast.Super;
import lombok.ast.SuperConstructorInvocation;
import lombok.ast.Switch;
import lombok.ast.Synchronized;
import lombok.ast.This;
import lombok.ast.Throw;
import lombok.ast.Try;
import lombok.ast.TypeReference;
import lombok.ast.TypeReferencePart;
import lombok.ast.TypeVariable;
import lombok.ast.UnaryExpression;
import lombok.ast.VariableDeclaration;
import lombok.ast.VariableDefinition;
import lombok.ast.VariableDefinitionEntry;
import lombok.ast.VariableReference;
import lombok.ast.While;
import lombok.ast.WildcardKind;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

import com.android.tools.lint.detector.api.JavaContext;

public class AstPrinterVisitor extends ForwardingAstVisitor{	
	
	private PrintWriter out;
	private PrintWriter log;
	private boolean endVisit = false;
	private String buffer = "";
	private String lastClassName;
	private String lastPackageName = "";
	private JavaContext context;
	private Socket socket;

	private final static String[] MODIFIER_KEYS = {"static", "final", "abstract", 
													"strictfp", "native", "synchronized" };
	
	private final static String[] VISIBILITY_KEYS = {"public", "private", "protected"};
	
	private final static BinaryOperator[] OP_ASSIGNS = { BinaryOperator.AND_ASSIGN, 
			BinaryOperator.DIVIDE_ASSIGN, BinaryOperator.MINUS_ASSIGN, BinaryOperator.MULTIPLY_ASSIGN,
			BinaryOperator.OR_ASSIGN, BinaryOperator.PLUS_ASSIGN, BinaryOperator.REMAINDER_ASSIGN,
			BinaryOperator.SHIFT_LEFT_ASSIGN, BinaryOperator.SHIFT_RIGHT_ASSIGN, BinaryOperator.XOR_ASSIGN};
	
	
	
	/**
	 * Constructor of the AstPrinterVisitor. It takes the context of the program and a polymorphous
	 * output stream object in which it will write a representation of the program.
	 * @param context The JavaContext of the application.
	 * @param outStream The OutputStream in which it will print the AST.
	 */
	public AstPrinterVisitor(JavaContext context, Socket socket, String lastClassName) throws IllegalArgumentException, RuntimeException {
		if (null == context)
			throw new IllegalArgumentException("Lintent AstVisitor received a null JavaContext.");
		this.context = context;
		Lintent.println(String.format("Lintent v%s", this.getClass().getPackage().getSpecificationVersion()));
		this.socket = socket;
		try {
			this.out = new PrintWriter(socket.getOutputStream());
		} catch (IOException e) {
			throw new RuntimeException("Couldn't obtain the output stream of the socket.");
		}
		if (Config.CREATE_LOG_FILE) {
			final String logfile = String.format("%s\\lintent_log.txt", System.getProperty("user.home"));
			try {
				this.log = new PrintWriter(new FileOutputStream(logfile, false));				
			} catch (Exception e) {
				throw new RuntimeException(String.format("AST visitor log file cannot be created: %s. " +
						"Please verify that all permissions are granted.", logfile));
			}
		}
		this.lastClassName = lastClassName;
		printManifestPermissions();
		printImplicitImports();
		//out.println("opening...");
	}
	


	/**
	 * To be called at the end of the visit. It flushes and closes the output stream in which
	 * the AST had been previously printed.
	 */
	private void closeOutStream() throws RuntimeException {

		out.println("");
		out.flush();
		try {
			socket.shutdownOutput();
		} catch (IOException e) {
			throw new RuntimeException("Lintent couldn't shut down the ouput stream of the socket.");
		}
		
		if (log != null){
			log.println("");
			log.flush();
			log.close();
		}
	}
	
	
	
	/**
	 * Prints the given string to a temporary buffer. Notice that it will be printed to the OutputStream
	 * as expected only once the println(s) method will be called.
	 * @param s The String to be printed.
	 */
	private void print(String s){
		buffer = buffer + s;
	}
	
	
	
	/**
	 * Prints the given body of a class, ordering all its member by the type of their AST node.
	 * @param classBody The body of a class to be printed.
	 */
	private void printClassBody(NormalTypeBody classBody){
				
		boolean first = true;
		ArrayList<VariableDeclaration> attributes = new ArrayList<VariableDeclaration>();
		ArrayList<ConstructorDeclaration> constructors = new ArrayList<ConstructorDeclaration>();
		ArrayList<MethodDeclaration> methods = new ArrayList<MethodDeclaration>();
		ArrayList<InstanceInitializer> initializers = new ArrayList<InstanceInitializer>();
		ArrayList<StaticInitializer> staticInits = new ArrayList<StaticInitializer>();
		ArrayList<ClassDeclaration> innerClasses = new ArrayList<ClassDeclaration>();
		ArrayList<InterfaceDeclaration> innerInterfaces = new ArrayList<InterfaceDeclaration>();
		
		for (Node n : classBody.rawMembers()){
			if (n instanceof ClassDeclaration)
				innerClasses.add((ClassDeclaration)n);
			if (n instanceof ConstructorDeclaration)
				constructors.add((ConstructorDeclaration)n);
			if (n instanceof InstanceInitializer)
				initializers.add((InstanceInitializer)n);
			if (n instanceof InterfaceDeclaration)
				innerInterfaces.add((InterfaceDeclaration)n);
			if (n instanceof MethodDeclaration)
				methods.add((MethodDeclaration)n);
			if (n instanceof StaticInitializer)
				staticInits.add((StaticInitializer)n);
			if (n instanceof VariableDeclaration)
				attributes.add((VariableDeclaration)n);
			// TODO: Se non è una di queste????
		}
		
		print("(");

		for (VariableDeclaration attribute : attributes){
			if (first) first = false;
			else print(" ");
			visit(attribute);
		}
		
		
		print(")\n(");
		

		first = true;
		for (ConstructorDeclaration constructor : constructors){
			if (first) first = false;
			else print(" ");
			visit(constructor);
		}
		
		
		print(")\n(");
		

		first = true;
		for (MethodDeclaration method : methods){
			if (first) first = false;
			else print("\n");
			visit(method);
		}
		
		
		print(")\n(");
		

		first = true;
		for (InstanceInitializer init : initializers){
			if (first) first = false;
			else print("\n");
			visit(init);
		}
		
		
		print(")\n(");
		

		first = true;
		for (StaticInitializer staticInit : staticInits){
			if (first) first = false;
			else print("\n");
			visit(staticInit);
		}
		
		
		print(")\n(");
		

		first = true;
		for (ClassDeclaration c : innerClasses){
			if (first) first = false;
			else print("\n");
			visit(c);
		}
		
		
		print(")\n(");
		

		first = true;
		for (InterfaceDeclaration i : innerInterfaces){
			if (first) first = false;
			else print("\n");
			visit(i);
		}
		
		println(")");
	}
	
	
	
	private void printImplicitImports(){
		println("@ImplicitImports(");
		for (int i = 0; i < Config.JAVA_IMPLICIT_IMPORTS.length; i++)
			printStarImport(Config.JAVA_IMPLICIT_IMPORTS[i]);
		println("\n)");
	}
	
	
	
	/**
	 * Prints the information about the location of the given node inside the source file, with the 
	 * following format: "(filename, row, column)".
	 * @param node The node whose location must be printed.
	 */
	private void printLocationInfos(Node node){
		int line, col, endCol;
		
		try {
			line = context.getLocation(node).getStart().getLine();
			col = context.getLocation(node).getStart().getColumn();
			endCol = context.getLocation(node).getEnd().getColumn();
		}
		catch(Exception e){
			// TODO: Decidere bene cosa fare in questo caso.
			line = -1;
			col = -1;
			endCol = -1;
//			Lintent.logPrintln("Location not found for node: " + node.toString());
//			Lintent.logPrintln("Printing stack trace: ");
//			for (StackTraceElement el : e.getStackTrace()){
//				Lintent.logPrintln(el.toString());
//			}
//			Lintent.logPrintln("\n\n");
		}
		
		print(String.format(" (%d %d %d)", line, col, endCol));
	}
	
	
	
	
	/**
	 * Prints the current buffer followed by the given string and by a new line to the OutputStream. 
	 * Also adds the expected amount of tabulations at the beginning of the line.
	 * @param s The String to be printed.
	 */
	private void println(String s){
						
		out.println(buffer + s);
		out.flush();

		if (Config.CREATE_LOG_FILE){
			log.println(buffer + s);
			log.flush();
		}
		
		buffer = "";
	}
	
	
	
	/**
	 * Prints all relevant information about system permission written in the Android application manifest.
	 */
	private void printManifestPermissions() throws RuntimeException {
		
		String rootDirPath = context.getMainProject().getDir().getAbsolutePath();
		File androidManifest = new File(rootDirPath + Config.MANIFEST_RELATIVE_PATH);
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		DocumentBuilder builder = null;
		Document document = null;
		try {
			builder = factory.newDocumentBuilder();
			document = builder.parse(androidManifest);
		} catch (Exception e) {
			throw new RuntimeException("Couldn't open project's manifest at " + androidManifest.getAbsolutePath());
		} 	
		
		document.getDocumentElement().normalize();
		NodeList usedPermissions = document.getElementsByTagName(Config.MANIFEST_USES_PERMISSION_TAG);
		NodeList definedPermissions = document.getElementsByTagName(Config.MANIFEST_DEFINED_PERMISSIONS_TAG);
		NodeList activities = document.getElementsByTagName(Config.ACTIVITY_TAG);
		Element manifest = (Element) document.getElementsByTagName(Config.MANIFEST_TAG).item(0);
		String packageName = manifest.getAttribute(Config.MANIFEST_PACKAGE);
		packageName = trimDots(packageName);
		
		print("@UsesPermissions(");
		for (int i = 0; i < usedPermissions.getLength(); i++){
			if (org.w3c.dom.Node.ELEMENT_NODE == usedPermissions.item(i).getNodeType()){
				Element permissionNode = (Element) usedPermissions.item(i);
				String permission = permissionNode.getAttribute(Config.MANIFEST_USES_PERMISSION_ATTRIBUTE);
				if (!permission.equals("")){
					if (i > 0)
						print(", ");
					print("\"" + permission + "\"");
				}
			}
		}
		println(")");
		
		print("@DefinesPermissions(");
		for (int i = 0; i < definedPermissions.getLength(); i++){
			if (org.w3c.dom.Node.ELEMENT_NODE == definedPermissions.item(i).getNodeType()){
				Element permissionNode = (Element) definedPermissions.item(i);

				print("(");
				for (int j = 0; j < Config.MANIFEST_DEFINED_PERMISSIONS_ATTRIBUTES.length; j++){
					String permission = permissionNode.getAttribute(Config.MANIFEST_DEFINED_PERMISSIONS_ATTRIBUTES[j]);
					if (!permission.equals(""))
						print("\"" + permission + "\" ");
				}
				println(")");
			}
		}
		println(")");
		
		print("@CallingPermissions(");
		for (int i = 0; i < activities.getLength(); i++){
			if (org.w3c.dom.Node.ELEMENT_NODE == activities.item(i).getNodeType()){
				Element activityNode = (Element) activities.item(i);
				String activityName = activityNode.getAttribute(Config.MANIFEST_ACTIVITY_NAME);
				String activityPermission = activityNode.getAttribute(Config.MANIFEST_ACTIVITY_CALLING_PERMISSION);
				
				activityName = trimDots(activityName);
				if (!activityName.contains("."))
					activityName = String.format("%s.%s", packageName, activityName);
				if (!activityPermission.isEmpty())
					print(String.format("(%s \"%s\")\n", activityName, activityPermission));
			}

		}
		print(")\n\n\n");
		
		
	}
	
	
	
	/**
	 * Given a qualified ID of a star import (e.g: "java.lang.*") it prints the fully qualified ID of all
	 * the classes inside the given package. Notice that the list of classes will be exhaustive only if all
	 * its classes reside within the same jar file.
	 * @param importPath A string containing the qualified ID of a star import <strong>without</strong> the 
	 * 				star and the last dot. For instance, to print all classes imported by "java.lang.*" you 
	 * 				<strong>have to</strong> pass "java.lang".
	 */
	private void printStarImport(String importPath){
		boolean first = true;
		ArrayList<String> importedClasses = ClassFinder.getAllClassesInPackage(importPath, context);

		for (String classFQId : importedClasses){
			if (first) first = false;
			else println("");
			print(classFQId + " false");
		}
	}

	
	
	/**
	 * Removes any eventual dot from the beginning and the end of the given string.
	 * @param s The string to be trimmed.
	 * @return The same string without dots at the beginning or the end.
	 */
	private static String trimDots(String s){
		String resultString = s;
		while (resultString.startsWith("."))
			resultString = resultString.substring(1);
		while (resultString.endsWith("."))
			resultString = resultString.substring(0, resultString.length()-1);
		return resultString;
	}
	
	
	
	/**
	 * If the node is NOT null then performs the visit, otherwise it does nothing.
	 * @param node The node to be visited
	 */
	private void visit(Node node){
		if (node != null)
			node.accept(this);
	}
	
	
	
	/**
	 * Prints (and visits) all nodes in the given list, adding prefixes, separators and suffixes.
	 * @param nodes The list of nodes to be printed.
	 * @param separator An eventual separator to be printed between nodes.
	 * @param prefix An eventual prefix to be printed before the nodes. Pass null or "" if you don't need it.
	 * @param suffix An eventual suffix to be printed after the nodes.
	 */
	private void visitAll(RawListAccessor<?,?> nodes, String separator){
		
		if (nodes.isEmpty())
			return;
		
		boolean first = true;
		boolean printSeparator = (separator != null) && (!separator.equals(""));
		
		for (Node n : nodes){
			if (first)
				first = false;
			else if (printSeparator)
				print(separator);
			
			visit(n);
		}
		
	}
	
	
	
	/**
	 * Sets a new JavaContext for the AstPrinter visitor. It should be called any time the visitor will
	 * have to print a different compilation unit.
	 * @param newContext The new JavaContext object.
	 */
	public void setContext(JavaContext newContext){
		this.context = newContext;
	}
	
	
	/**
	 * Visits the invocation of a constructor inside another constructor.
	 * E.g: public myConstructor(int x){
	 * 			myConstructor(x, 0);
	 * 		}
	 */
	@Override
	public boolean visitAlternateConstructorInvocation(AlternateConstructorInvocation node) {
		
		print("ThisCons((");
		visitAll(node.rawConstructorTypeArguments(), " ");
		print(") (");
		visitAll(node.rawArguments(), ", ");
		print(")");
		printLocationInfos(node);
		print(")");
		
		return true;
	}

	
	
	/**
	 * Visits and prints an Annotation. 
	 */
	@Override
	public boolean visitAnnotation(Annotation node) {
		print("");
		visit(node.rawAnnotationTypeReference());
		print(" (");
		visitAll(node.rawElements(), " ");
		print(")");
		printLocationInfos(node);
		
		return true;
	}

	
	
	/**
	 * Visits and prints the Declaration of a custom Annotation.
	 */
	@Override
	public boolean visitAnnotationDeclaration(AnnotationDeclaration node) {

		// Just ignore them.
		
		/*print("AnnotationDeclaration(");
		visit(node.astName());
		println(", Body(");
		
		visit(node.rawBody());
		
		print("))");*/
		
		return true;
		
	}

	
	
	/**
	 * Visits and prints an annotation element.
	 */
	@Override
	public boolean visitAnnotationElement(AnnotationElement node) {

		boolean elementIsArray = node.astValue() instanceof ArrayInitializer;
		if ((null == node.astName()) || (node.astName().equals("")))
			print("value");
		else
			visit(node.astName());
		
		print(" ");
		
		// TODO: Verificare se possibile inserire ty vero anzichè String() 1!!
		if (elementIsArray)
			print("ArrayLit(String() 1 ");	
		visit(node.astValue());
		if (elementIsArray)
			print(")");
		
		return true;
	}
	
	

	/**
	 * Visits and prints the declaration of a method inside an annotation interface declaration.
	 */
	@Override
	public boolean visitAnnotationMethodDeclaration(AnnotationMethodDeclaration node) {

		// Just ignore them.
		
		/*print("AnnotationMethodDeclaration(");
		visit(node.astMethodName());
		print(", ");
		visit(node.astModifiers());
		print(", ReturnType(");
		visit(node.rawReturnTypeReference());
		print("), DefaultValue(");
		
		if (node.rawDefaultValue() != null){
			visit(node.rawDefaultValue());
		}
		
		print("))");*/
		return true;
		
	}

	
	
	/**
	 * Visits an array of values in an annotation.
	 */
	@Override
	public boolean visitAnnotationValueArray(AnnotationValueArray node) {
		
		print("(");
		visitAll(node.rawValues(), ", ");
		print(")");

		return true;
		
	}

	
	
	/**
	 * Visits an array access node.
	 */
	@Override
	public boolean visitArrayAccess(ArrayAccess node) {
	
		print("Subscript(");
		visit(node.rawOperand());
		print(" ");
		visit(node.rawIndexExpression());
		printLocationInfos(node);
		print(")");
		
		return true;
	}



	/**
	 * Visits the creation of an array.
	 */
	@Override
	public boolean visitArrayCreation(ArrayCreation node) {
		
		boolean first = true;
			
		if (node.rawInitializer() != null) {
			print("ArrayLit(");
			TypeReference n = (TypeReference) node.rawComponentTypeReference();
			visitAll(n.rawParts(), ".");
			print(" " + node.rawDimensions().size() + " ");
			visit(node.rawInitializer());
		}
		else {
			print("Cons(");
			TypeReference n = (TypeReference) node.rawComponentTypeReference();
			visitAll(n.rawParts(), ".");
			print(" " + node.rawDimensions().size());
			print(" () (");
			for (Node rawDim : node.rawDimensions()){
				ArrayDimension dim = null;
				try{
					dim = (ArrayDimension) rawDim;
				}
				catch(Exception e){
					throw new RuntimeException("Unexpected non-ArrayDimension node in array creation.");
				}
				if (null == dim.rawDimension()) continue;
				if (first) first = false;
				else print(", ");
				visit(dim);
			}
			print(") ()");
			printLocationInfos(node);
		}
		print(")");
			
		return true;
	}

	
	
	/**
	 * Visits the node that represent the dimension of an array.
	 */
	@Override
	public boolean visitArrayDimension(ArrayDimension node) {

		visit(node.rawDimension());
		
		return true;
		
	}

	
	
	/**
	 * Visits the initializer of an array.
	 */
	@Override
	public boolean visitArrayInitializer(ArrayInitializer node) {
		
		print("ArrayInit((");
		visitAll(node.rawExpressions(), ", ");
		print(")");
		printLocationInfos(node);
		print(")");
		return true;
		
	}

	
	
	/**
	 * Visits an assertion.
	 */
	@Override
	public boolean visitAssert(Assert node) {

		print("Assert(");
		visit(node.rawAssertion());
		print(" ");
		print("(");
		if (node.rawMessage() != null)
			visit(node.rawMessage());
		print(")");
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	
	
	/**
	 * Visits a binary expression.
	 */
	@Override
	public boolean visitBinaryExpression(BinaryExpression node) {
		
		boolean found = false;
		
		print("(");
		visit(node.astLeft());
		
		for (BinaryOperator assignOperator : OP_ASSIGNS)
			if (assignOperator.equals(node.astOperator())){
				print(" " + BinaryOperator.ASSIGN.name() + " (");
				visit(node.astLeft());
				print(" " + assignOperator.name().replaceAll("_ASSIGN", "") + " ");
				found = true;
				break;
			}
		
		if (!found)
			print(" " + node.astOperator().name() + " ");
		
		visit(node.astRight());
		
		if (found){
			printLocationInfos(node);
			print (")");
		}
		printLocationInfos(node);
		print(")");
		
		return true;
	}

	
	
	/**
	 * Visits a block of code. It simply iterates through all statements appending a
	 * semicolon and an endline character after each statement.
	 */
	@Override
	public boolean visitBlock(Block node) {
		
		visitAll(node.rawContents(), "\n");

		return true;
		
	}

	
	
	/**
	 * Visits boolean literal.
	 */
	@Override
	public boolean visitBooleanLiteral(BooleanLiteral node) {

		print(""+node.astValue());
		
		return true;
		
	}

	
	
	/**
	 * Visits a break statement.
	 */
	@Override
	public boolean visitBreak(Break node) {
		
		String s = "";
		if ((node.astLabel() != null) && (node.astLabel().astValue() != null))
			if (!node.astLabel().astValue().toUpperCase().equals("NULL"))
				s = node.astLabel().astValue();
		print("Break (" + s + ") ");
		printLocationInfos(node);

		return true;
		
	}

	
	
	/**
	 * Visits a case statement.
	 */
	@Override
	public boolean visitCase(Case node) {

		visit(node.rawCondition());
		
		return true;
		
	}

	
	
	/**
	 * Visits a cast.
	 */
	@Override
	public boolean visitCast(Cast node) {

		print("Cast(");
		visit(node.rawTypeReference());
		print(" ");
		visit(node.rawOperand());
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	/**
	 * Visit a catch node.
	 */
	@Override
	public boolean visitCatch(Catch node) {

		visit(node.rawExceptionDeclaration());
		print(" (");
		visit(node.rawBody());
		print(")");
				
		return true;
		
	}

	
	
	/**
	 * Visits a char literal.
	 */
	@Override
	public boolean visitCharLiteral(CharLiteral node) {

		print("'" + node.rawValue() + "'");
		
		return true;
		
	}

	
	
	/**
	 * Visits a class declaration node.
	 */
	@Override
	public boolean visitClassDeclaration(ClassDeclaration node) {

		// TODO: qualificare con QID le inner class e interface col path preciso dato dal package + i parent ricorsivamente
		/*if (!lastPackageName.equals(""))
			print(lastPackageName + ".");*/
		visit(node.astName());
		print(" (");
		if (node.astModifiers() != null)
			visit(node.astModifiers());
		
		print(")\n(");
		if (!node.rawTypeVariables().isEmpty())
			visitAll(node.rawTypeVariables(), " ");
		
		print(")\n(");
		if (node.rawExtending() != null)
			visit(node.rawExtending());
		
		print(")\n(");
		if (!node.rawImplementing().isEmpty())
			visitAll(node.rawImplementing(), ", ");
		
		print(")\n");
		
		if (node.rawBody() instanceof NormalTypeBody)
			printClassBody((NormalTypeBody)node.rawBody());
		else
			throw new RuntimeException("Unexpected class body of type: " + node.rawBody().getClass().getName());		
		
		
		printLocationInfos(node);

		return true;
		
	}

	
	
	/**
	 * Visits a class literal (e.g: AstPrinterVisitor.class).
	 */
	@Override
	public boolean visitClassLiteral(ClassLiteral node) {

		print("ClassOp(" + node.rawTypeReference());
		printLocationInfos(node);
		print(")");

		return true;
		
	}

	
	
	/**
	 * Visits a comment.
	 */
	@Override
	public boolean visitComment(Comment node) {
		return true;
	}

	
	
	/**
	 * Visits a compilation unit.
	 */
	@Override
	public boolean visitCompilationUnit(CompilationUnit node) {
		
		ClassDeclaration classDec;
		ArrayList<ClassDeclaration> classes = new ArrayList<ClassDeclaration>();
		ArrayList<InterfaceDeclaration> interfaces = new ArrayList<InterfaceDeclaration>();
		
		for (Node typeDec : node.rawTypeDeclarations()){
			if (typeDec instanceof ClassDeclaration){
				classDec = (ClassDeclaration) typeDec;
				classes.add(classDec);
				if (classDec.astName().astValue().equals(lastClassName))
					endVisit = true;
			}
			else{
				if (typeDec instanceof InterfaceDeclaration){
					InterfaceDeclaration interfaceDec = (InterfaceDeclaration) typeDec;
					interfaces.add(interfaceDec);
					if (interfaceDec.astName().astValue().equals(lastClassName))
						endVisit = true;
				}
				else{
					if (typeDec instanceof AnnotationDeclaration) continue;
					throw new RuntimeException("Unexpected declaration inside" +
								"class: " + typeDec.getClass().getName());
				}
						
			}
					
		}
		
//		lombok.ast.Position position = node.getPosition();
//		com.android.tools.lint.detector.api.Location loc =
//				com.android.tools.lint.detector.api.Location.create(context.file, context.getContents(),
//                position.getStart(), position.getEnd());
//		println("file = " + context.file.getAbsolutePath() + " , contents = " + context.getContents() 
//				+ " , start = " + position.getStart() + ", end = " + position.getEnd());
		
		File unitFile = context.file;
		File projectDir = context.getMainProject().getDir();
		String publicClassName = unitFile.getName().replace(".java", "");
		
		String relativeFilePath = "";
		
		while (unitFile.compareTo(projectDir) != 0){
			relativeFilePath = unitFile.getName() + File.separator + relativeFilePath;
			unitFile = unitFile.getParentFile();
			if (null == unitFile)
				throw new RuntimeException("Could not compute source relative file path from project directory.");
		}
		
		relativeFilePath = relativeFilePath.substring(0, relativeFilePath.length()-1);
		
		println("@\"" + relativeFilePath + "\"");
		print(publicClassName);
		
		print("(");
		if (node.rawPackageDeclaration() != null)
			visit(node.rawPackageDeclaration());
		println(")");
		
		print("(");
		if (!node.rawImportDeclarations().isEmpty())
			visitAll(node.rawImportDeclarations(), "\n");
		println(")");

		print("(");
		for (ClassDeclaration cd : classes){
			visit(cd);
			println("");
		}
		println(")");
		
		print("(");
		for (InterfaceDeclaration idecl : interfaces){
			visit(idecl);
			println("");
		}
		println(")\n\n");
		
		if(endVisit){
			closeOutStream();
			IssuesListener listener = Lintent.getIssuesListener();
			if (listener != null){
				try {
					listener.join();
					Lintent.verbosePrintln("IssueListener closed.");
				} catch (InterruptedException e) {
					throw new RuntimeException("InterruptedException while the main thread was waiting to join.");
				}
			}
			try{
				Lintent.closeStreams();
			}
			catch (IOException e){
				throw new RuntimeException("Lintent couldn't close properly its ServerSocket and logger.");
			}
		}
		
		return true;
		
	}

	
	
	/**
	 * Visits the declaration of a constructor.
	 */
	@Override
	public boolean visitConstructorDeclaration(ConstructorDeclaration node) {

		if (!lastPackageName.equals(""))
			print(lastPackageName + ".");
		visit(node.astTypeName());
		print(" (");
		if (node.astModifiers() != null)
			visit(node.astModifiers());
		print(") (");
		visitAll(node.rawTypeVariables(), " ");
		print(") (");
		visitAll(node.rawParameters(), " ");
		print(") (");
		visitAll(node.rawThrownTypeReferences(), " ");
		println(") (");
		visit(node.rawBody());
		print(")");
		printLocationInfos(node);
		
		return true;
		
	}

	
	/**
	 * Visits a constructor invocation.
	 */
	@Override
	public boolean visitConstructorInvocation(ConstructorInvocation node) {

		print("Cons(");
		if (node.rawQualifier() != null){
			visit(node.rawQualifier());
			print(".");
		}
		visit(node.rawTypeReference());
		print(" (");
		visitAll(node.rawConstructorTypeArguments(), " ");
		print(") (");
		visitAll(node.rawArguments(), ", ");
		print(") (");
		if (node.rawAnonymousClassBody() != null)
			visit(node.rawAnonymousClassBody());
		
		print(")");
		printLocationInfos(node);
		print(")");

		return true;
		
	}

	
	
	/**
	 * Visits a Continue statement.
	 */
	@Override
	public boolean visitContinue(Continue node) {

		print("Continue (" + node.astLabel() + ") ");
		printLocationInfos(node);

		return true;
		
	}

	
	
	/**
	 * Visits the default node of a case switch.
	 */
	@Override
	public boolean visitDefault(Default node) {

		print("Default");
		
		return true;
		
	}

	
	
	/**
	 * Visits a Do While statement.
	 */
	@Override
	public boolean visitDoWhile(DoWhile node) {

		print("DoWhile(");
		visit(node.rawCondition());
		println(" (");
		
		visit(node.rawStatement());
		
		print(")");
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}
	
	
	
	/**
	 * Visits an empty declaration. 
	 */
	@Override
	public boolean visitEmptyDeclaration(EmptyDeclaration node) {

		print("EmptyDeclaration");
		return true;
		
	}

	
	
	/**
	 * Visits an empty statement.
	 */
	@Override
	public boolean visitEmptyStatement(EmptyStatement node) {

		print("EmptyStatement");
		return true;
		
	}

	
	
	/**
	 * Visits an EnumConstant.
	 */
	@Override
	public boolean visitEnumConstant(EnumConstant node) {
		
		//TODO: Ci servono?
		
		print("EnumConstant(");
		visit(node.astName());
		print(" Annotations(");
		visitAll(node.rawAnnotations(), ", ");
		print(") Arguments(");
		visitAll(node.rawArguments(), ", ");
		println(") Body(");
		
		visit(node.rawBody());
		
		print(")");
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	
	/**
	 * Visits an EnumDeclaration.
	 */
	@Override
	public boolean visitEnumDeclaration(EnumDeclaration node) {

		//TODO: Ci servono?
		
		print("EnumDeclaration(");
		visit(node.astName());
		print(" (");
		if (node.astModifiers() != null)
			visit(node.astModifiers());
		print(") Implements(");
		visitAll(node.rawImplementing(), ", ");
		println(") Body(");
		
		visit(node.rawBody());
		
		print(")");
		printLocationInfos(node);
		print(")");

		return true;
		
	}

	
	
	/**
	 * Visits an EnumTypeBody.
	 */
	@Override
	public boolean visitEnumTypeBody(EnumTypeBody node) {
		
		// TODO: Ci servono??
		
		visitAll(node.rawConstants(), "\n");
		visitAll(node.rawMembers(), "\n");
		
		return true;
		
	}

	
	/**
	 * Visits an ExpressionStatement.
	 */
	@Override
	public boolean visitExpressionStatement(ExpressionStatement node) {
		
		visit(node.rawExpression());
		return true;
		
	}

	
	
	/**
	 * Visits a floating point literal.
	 */
	@Override
	public boolean visitFloatingPointLiteral(FloatingPointLiteral node) {

		print(node.rawValue());
		return true;
		
	}

	
	
	/**
	 * Visits a for statement.
	 */
	@Override
	public boolean visitFor(For node) {

		print("For((");
		if (node.isVariableDeclarationBased())
			visit(node.rawVariableDeclaration());
		else
			if (!node.rawExpressionInits().isEmpty())
				visitAll(node.rawExpressionInits(), ", ");
		
		print(") (");
		if (node.rawCondition() != null)
			visit(node.rawCondition());
		print(") (");
		if (!node.rawUpdates().isEmpty())
			visitAll(node.rawUpdates(), ", ");
		println(") (");
		
		visit(node.rawStatement());
		
		print(")");
		printLocationInfos(node);
		print(")");

		return true;
		
	}

	
	
	/**
	 * Visits for each.
	 */
	@Override
	public boolean visitForEach(ForEach node) {

		print("ForEach(");
		visit(node.rawVariable());
		print(" ");
		visit(node.rawIterable());
		println(" (");
		
		visit(node.rawStatement());
		
		print(")");
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	
	/**
	 * Visits an identifier.
	 */
	@Override
	public boolean visitIdentifier(Identifier node) {

		print(node.astValue());
		
		return true;
	
	}

	
	
	/**
	 * Visits an if then else statement.
	 */
	@Override
	public boolean visitIf(If node) {

		print("If(");
		visit(node.rawCondition());
		print(" (");
		visit(node.rawStatement());
		print(") (");
		if (node.rawElseStatement() != null)
			visit(node.rawElseStatement());
		print(")");
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	
	/**
	 * Visits an import declaration statement.
	 */
	@Override
	public boolean visitImportDeclaration(ImportDeclaration node) {
		
		boolean first = true;
		String importPath = "";
	
		for (Node id : node.rawParts()){
			if (first) first = false;
			else importPath += ".";
			importPath += id.toString();
		}
		
		if (node.astStarImport()){
			if (Config.isDefaultImport(importPath))
				return true;
			printStarImport(importPath);
		} 
		else
			print(importPath + " " + node.astStaticImport());
		
		
		return true;
		
	}

	
	
	
	/**
	 * Visits an inline if expression.
	 */
	@Override
	public boolean visitInlineIfExpression(InlineIfExpression node) {
		
		print("InlineIf(");
		visit(node.rawCondition());
		print(" ");
		visit(node.rawIfTrue());
		print(" ");
		visit(node.rawIfFalse());
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	/**
	 * Visits an instance initializer.
	 */
	@Override
	public boolean visitInstanceInitializer(InstanceInitializer node) {

		visit(node.rawBody());

		return true;
		
	}

	
	/**
	 * Visits an instanceof statement.
	 */
	@Override
	public boolean visitInstanceOf(InstanceOf node) {

		print("InstanceOf(");
		visit(node.rawObjectReference());
		print(" Type(");
		visit(node.rawTypeReference());
		print(")");
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	/**
	 * Visits an int/long literal.
	 */
	@Override
	public boolean visitIntegralLiteral(IntegralLiteral node) {
		
		if(node.astMarkedAsLong())
			print("" + node.astLongValue() + "L");
		else
			print("" + node.astIntValue());
		
		return true;
		
	}

	
	
	/**
	 * Visits the declaration of an interface.
	 */
	@Override
	public boolean visitInterfaceDeclaration(InterfaceDeclaration node) {
		
//		// If we should need FQId again
//		if (!lastPackageName.equals(""))
//			print(lastPackageName + ".");
		
		visit(node.astName());
		print(" (");
		if (node.astModifiers() != null)
			visit(node.astModifiers());
		print(") (");
		visitAll(node.rawTypeVariables(), " ");
		print(") (");
		visitAll(node.rawExtending(), " ");
		print(")");

		
		ArrayList<VariableDeclaration> attributes = new ArrayList<VariableDeclaration>();
		ArrayList<MethodDeclaration> methods = new ArrayList<MethodDeclaration>();
		ArrayList<ClassDeclaration> innerClasses = new ArrayList<ClassDeclaration>();
		ArrayList<InterfaceDeclaration> innerInterfaces = new ArrayList<InterfaceDeclaration>();
		
		for (Node n : ((NormalTypeBody)node.rawBody()).rawMembers()){
			if (n instanceof ClassDeclaration)
				innerClasses.add((ClassDeclaration)n);
			if (n instanceof InterfaceDeclaration)
				innerInterfaces.add((InterfaceDeclaration)n);
			if (n instanceof MethodDeclaration)
				methods.add((MethodDeclaration)n);
			if (n instanceof VariableDeclaration)
				attributes.add((VariableDeclaration)n);
			// TODO: Se non è una di queste????
		}
		
		
		print("\n(");

		boolean first = true;
		for (VariableDeclaration attribute : attributes){
			if (first) first = false;
			else print(" ");
			visit(attribute);
		}
		
		print(")\n(");

		first = true;
		for (MethodDeclaration method : methods){
			if (first) first = false;
			else print(" ");
			visit(method);
		}
		
		print(")\n(");

		first = true;
		for (ClassDeclaration c : innerClasses){
			if (first) first = false;
			else print(" ");
			visit(c);
		}
		
		print(")\n(");

		first = true;
		for (InterfaceDeclaration i : innerInterfaces){
			if (first) first = false;
			else print(" ");
			visit(i);
		}

		print(")");
		printLocationInfos(node);
		
		return true;
		
	}

	
	
	/**
	 * Visits a keyword modifier.
	 */
	@Override
	public boolean visitKeywordModifier(KeywordModifier node) {

		print(node.astName());
		return true;
		
	}

	
	/**
	 * Visits a labeled statement.
	 */
	@Override
	public boolean visitLabelledStatement(LabelledStatement node) {

		print("LabelledStatement(");
		visit(node.astLabel());
		print(" ");
		visit(node.astStatement());
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	/**
	 * Visits a method declaration.
	 */
	@Override
	public boolean visitMethodDeclaration(MethodDeclaration node) {
	
		visit(node.astMethodName());
		print(" (");
		
		visit(node.rawReturnTypeReference());
		print(") (");

		if (node.astModifiers() != null)
			visit(node.astModifiers());
		
		print(") (");
		visitAll(node.rawTypeVariables(), " ");
	
		print(") (");
		visitAll(node.rawParameters(), " ");
		
		print(") (");
		visitAll(node.rawThrownTypeReferences(), " ");
		
		println(") (");
		
		visit(node.rawBody());
		print(") ");
		printLocationInfos(node);
		
		return true;
		
	}

	
	
	/**
	 * Visits the invocation of a method.
	 */
	@Override
	public boolean visitMethodInvocation(MethodInvocation node) {
	
		print("Call(");
		
		if (node.rawOperand() != null){
			visit(node.rawOperand());
			print(" ");
		}
		
		visit(node.astName());
		
		print(" (");
		
		visitAll(node.rawMethodTypeArguments(), " ");
		print(") (");
		visitAll(node.rawArguments(), ", ");
		print(")");

		printLocationInfos(node);
		print(")");

		return true;
		
	}

	
	
	/**
	 * Visits the list of modifiers.
	 */
	@Override
	public boolean visitModifiers(Modifiers node) {
		
		boolean first = true;
		boolean lookForVisibility = false;

		Iterator<Node> itKeys, itAnns;
		String visibility = "";
		
		itKeys = node.rawKeywords().iterator();
		itAnns = node.rawAnnotations().iterator();

		boolean[] modifierBools = new boolean[MODIFIER_KEYS.length];
		for (int i = 0; i < modifierBools.length; i++)
			modifierBools[i] = false;
		
		while(itKeys.hasNext()){

			String s = ((KeywordModifier)itKeys.next()).astName();
			if (visibility.equals(""))
				lookForVisibility = true;
			
			for (int i = 0; i < MODIFIER_KEYS.length; i++)
				if (s.equals(MODIFIER_KEYS[i])){
					modifierBools[i] = true;
					lookForVisibility = false;
					break;
				}
			
			if (lookForVisibility)
				for (int i = 0; i < VISIBILITY_KEYS.length; i++)
					if (s.equals(VISIBILITY_KEYS[i])){
						visibility = s;
						lookForVisibility = false;
						break;
					}
		}
		
		if (visibility.equals(""))
			visibility = "package";
		print(visibility);
		for (boolean b : modifierBools)
			print(" " + b);
		print(" (");
		
		
		while(itAnns.hasNext()){
			if (first)
				first = false;
			else
				print(" ");
			
			visit(itAnns.next());
		}
		print(")");

		return true;
		
	}

	
	
	/**
	 * Visits a normal type body (The body of a class?).
	 */
	@Override
	public boolean visitNormalTypeBody(NormalTypeBody node) {

		printClassBody(node);
		printLocationInfos(node);
		
		return true;
		
	}

	
	
	/**
	 * Visits a null literal.
	 */
	@Override
	public boolean visitNullLiteral(NullLiteral node) {

		print("Null");
		printLocationInfos(node);
		return true;
		
	}

	
	
	/**
	 * Visits a package declaration.
	 */
	@Override
	public boolean visitPackageDeclaration(PackageDeclaration node) {
		
		
		lastPackageName = "";
		
		if (!node.rawParts().isEmpty()){
			for (Node n : node.rawParts())
				lastPackageName += ((Identifier)n).astValue() + ".";
			lastPackageName = lastPackageName.substring(0, lastPackageName.length()-1);
		}
			
		print(lastPackageName);
		
		// + " (");
		//visitAll(node.rawAnnotations(), " ");
		//print(")");
		
		return true;
		
	}
	
	
	
	/**
	 * Visits an artifact produced by the parsing.
	 */
	@Override
	public boolean visitParseArtefact(Node node) {
		return true;
	}

	
	
	/**
	 * Visits a return node.
	 */
	@Override
	public boolean visitReturn(Return node) {

		print("Return(");
		visit(node.rawValue());
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	
	/**
	 * Visits a select statement.
	 */
	@Override
	public boolean visitSelect(Select node) {

		
		print("Select(");
		visit(node.rawOperand());
		print(" ");
		visit(node.astIdentifier());
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	
	/**
	 * Visits a static initializer
	 */
	@Override
	public boolean visitStaticInitializer(StaticInitializer node) {

		visit(node.rawBody());
		return true;
		
	}

	
	
	/**
	 * Visits a string literal.
	 */
	@Override
	public boolean visitStringLiteral(StringLiteral node) {
		
		print(node.rawValue());
		
		return true;
		
	}

	
	
	/**
	 * Visits a super node.
	 */
	@Override
	public boolean visitSuper(Super node) {

		print("Super");
		return true;

	}

	
	
	/**
	 * Visits a super constructor invocation.
	 */
	@Override
	public boolean visitSuperConstructorInvocation(SuperConstructorInvocation node) {

		print("SuperCons((");
		if (!node.rawConstructorTypeArguments().isEmpty())
			visitAll(node.rawConstructorTypeArguments(), " ");
		print(") (");
		visitAll(node.rawArguments(), ", ");
		print(")");
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	
	/**
	 * Visits a switch statement.
	 */
	@Override
	public boolean visitSwitch(Switch node) {

		boolean firstCase = true;
		boolean defaultFound = false;
		
		print("Switch(");
		visit(node.rawCondition());
		print(" (");
		
		for (Node n : ((Block)node.rawBody()).rawContents()){
			if (n instanceof Case){
				if (firstCase)
					firstCase = false;
				else
					print(") ");
				visit(n);
				print(" (");
			}
			else if (n instanceof Default) {
				defaultFound = true;
				print(")) (");
			}
			else{				
				print(" ");
				visit(n);
			}
		}
		if (defaultFound)
			print(")");	// Always closes Cases' bracket OR Default's.
		else
			print(")) ()");
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	
	/**
	 * Visits a synchronized ast node.
	 */
	@Override
	public boolean visitSynchronized(Synchronized node) {

		//TODO: Come lo gestiamo???
		
		print("Synchronized(Lock(");
		visit(node.rawLock());
		print(") Body(");
		
		visit(node.rawBody());
		
		print(")");
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	
	/**
	 * Visits a this expression.
	 */
	@Override
	public boolean visitThis(This node) {

		print("This");
		printLocationInfos(node);
		return true;
	}

	
	
	/**
	 * Visits a throw statement.
	 */
	@Override
	public boolean visitThrow(Throw node) {

		print("Throw(");
		visit(node.rawThrowable());
		printLocationInfos(node);
		print(")");
		return true;
		
	}

	
	
	/**
	 * Visits a try statement.
	 */
	@Override
	public boolean visitTry(Try node) {

		print("Try((");
		visit(node.rawBody());
		print(") (");
		visitAll(node.rawCatches(), " ");
		print(") (");
		visit(node.rawFinally());
		print(")");
		printLocationInfos(node);
		print(")");
		
		return true;
		
	}

	
	
	/**
	 * Visits a type reference.
	 */
	@Override
	public boolean visitTypeReference(TypeReference node) {
		
		WildcardKind kind = node.astWildcard();
				
		if (kind == WildcardKind.UNBOUND)
			print("Wildcard");
		else {
			if (kind == WildcardKind.EXTENDS) print("WildcardExtends ");
			else if (kind == WildcardKind.SUPER) print("WildcardSuper ");
			
			visitAll(node.rawParts(), ".");
			/*for (Node n : node.rawParts()){
				if (n instanceof TypeReferencePart){
					if (first) first = false;
					else print(".");
					TypeReferencePart part = (TypeReferencePart) n;
					print(part.getTypeName());
				}
				else
					// TODO: Investigare, unexpected?
					throw new RuntimeException("Unexpected: " + node.getClass().getName());
			}*/

			print(" " + node.astArrayDimensions());
		
		}	
		
		return true;
		
	}

	
	
	/**
	 * Visits a single part of a type reference.
	 */
	@Override
	public boolean visitTypeReferencePart(TypeReferencePart node) {
		
		visit(node.astIdentifier());
		
		print("(");
		if ((node.rawTypeArguments() != null) && (!node.rawTypeArguments().isEmpty()))
			visitAll(node.rawTypeArguments(), " ");
		print(")");
		
		return true;
		
	}

	
	/**
	 * Visits a type parameter.
	 */
	@Override
	public boolean visitTypeVariable(TypeVariable node) {
		print("");
		visit(node.astName());
		print(" (");
		if ((!node.rawExtending().isEmpty()) && (node.rawExtending() != null)) {
			visitAll(node.rawExtending(), " ");
		}
		//printLocationInfos(node);
		print(")");
		return true;
	}

	
	
	/**
	 * Visits an UnaryExpression.
	 */
	@Override
	public boolean visitUnaryExpression(UnaryExpression node) {
		print("(");
		visit(node.rawOperand());
		print(" " + node.astOperator().name());
		printLocationInfos(node);
		print(")");
		
		return true;
	}

	
	
	/**
	 * Visits a variable declaration.
	 */
	@Override
	public boolean visitVariableDeclaration(VariableDeclaration node) {
		
		/*if (!(node.rawDefinition() instanceof VariableDefinition)){
			print("(");
			visit(node.rawDefinition());
			print(")");
			return true;
		}

		VariableDefinition vd = (VariableDefinition) node.rawDefinition();
		
		for (Node var : vd.rawVariables()){
			visit(var);
			print(" ");
			visit(vd.rawTypeReference());
			print(" (");
			if (vd.astModifiers() != null)
				visit(vd.astModifiers());
			print(")");
			printLocationInfos(var);
			print(" ");
		}*/
		
		visit(node.rawDefinition());

		return true;
		
	}

	
	
	/**
	 * Visits a variable definition.
	 */
	@Override
	public boolean visitVariableDefinition(VariableDefinition node) {

		/*if (node.astVarargs())
			print("Varargs(");
		else
			print("(");*/
		// TODO: Implement varargs.
	
		for (Node var : node.rawVariables()){
//			if (((VariableDefinitionEntry)var).astName().astValue().equals("canvas"))
//				return true;
			visit(var);
			print(" ");
			visit(node.rawTypeReference());
			print(" (");
			if (node.astModifiers() != null)
				visit(node.astModifiers());
			print(")");
			printLocationInfos(var);
			print(" ");
		}
		
		return true;
		
		
	}

	
	
	/**
	 * Visits a variable definition entry.
	 */
	@Override
	public boolean visitVariableDefinitionEntry(VariableDefinitionEntry node) {
		
		boolean isArray = node.rawInitializer() instanceof ArrayInitializer;
		
		visit(node.astName());
		print(" (");
		if (node.rawInitializer() != null){
			if (isArray)
				print("ArrayLit(String() 1");
			// TODO: Inserire tipo vero dell'array literal.
			visit(node.rawInitializer());
			if (isArray)
				print(")");
		}
		print(")");
		return true;
		
	}

	
	
	/**
	 * Visits a variable reference.
	 */
	@Override
	public boolean visitVariableReference(VariableReference node) {

		visit(node.astIdentifier());
		printLocationInfos(node);
		return true;
		
	}

	
	
	/**
	 * Visits a while loop.
	 */
	@Override
	public boolean visitWhile(While node) {
		
		print("While(");
		visit(node.rawCondition());
		println(" (");
		
		visit(node.rawStatement());
		
		print(")");
		printLocationInfos(node);
		print(")");
		
		return true;
	}

}

