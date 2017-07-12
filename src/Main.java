import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.matheclipse.core.eval.ExprEvaluator;
import org.matheclipse.core.interfaces.IExpr;

import constraintfactory.AuxMethods;
import constraintfactory.ConstraintFactory;
import constraintfactory.ExternalFunction;
import javaparser.simpleJavaLexer;
import javaparser.simpleJavaParser;
import jsonast.Root;
import jsonparser.jsonLexer;
import jsonparser.jsonParser;

import sketchobj.core.FcnHeader;
import sketchobj.core.Function;
import sketchobj.core.SketchObject;
import sketchobj.expr.Expression;
import sketchobj.stmts.Statement;
import visitor.JavaVisitor;
import visitor.JsonVisitor;

import static org.matheclipse.core.expression.F.*;

import org.matheclipse.core.basic.Config;
import org.matheclipse.core.eval.ExprEvaluator;
import org.matheclipse.core.interfaces.IAST;
import org.matheclipse.core.interfaces.IExpr;
import org.matheclipse.parser.client.SyntaxError;
import org.matheclipse.parser.client.math.MathException;


public class Main {

	private String incorrectProgram;
	private String[] examples;
	private String functionName;
	private Root root;

	private int specification; 	// 0: Input/Output Examples
								// 1: Assertions
	
	
	public Main(String incorrectProgram, String[] examples, String functionName, int specification) {
		this.incorrectProgram 	= incorrectProgram;
		this.examples			= examples;
		this.functionName		= functionName;
		this.specification		= specification;
	}
	
	public void begin() throws InterruptedException{
		this.incorrectProgram	= this.incorrectProgram.replace("\\n", "\n").replace("\\t", "\t");
		ANTLRInputStream input 	= new ANTLRInputStream(this.incorrectProgram);
		Function targetFunction = (Function) javaCompile(input, this.functionName);
		//System.out.println(targetFunction);
		ConstraintFactory cf 	= new ConstraintFactory(targetFunction, specification, examples,
									new FcnHeader(targetFunction.getName(), targetFunction.getReturnType(), 
									targetFunction.getParams()));
		String script;
		script 					= cf.getSketchScript(targetFunction.getBody());

		this.synthesize(script, cf, null);
	}
	
	public void synthesize(String script, ConstraintFactory cf,
			Statement targetStmt) throws InterruptedException {
		List<ExternalFunction> externalFuncs = cf.externalFuncs;

		System.out.println(script);
		System.out.println("...................."+cf.coeffIndexToLine+"-----------------------------------");

		// no external Functions
		if (externalFuncs.size() == 0) {

			SketchResult resultS = CallSketch.CallByString(script);
			Map<Integer, Integer> result = resultS.Result;
			Map<Integer, Integer> constResult = resultS.constResult;
			System.out.println("Result is: " + result);

			System.out.println("ConstResult is: " + constResult);
			Set<Integer> validIndexSet = resultS.valid_Set;
			Set<Integer> validConst	   = resultS.constValidSet;
			List<Integer> indexset = new ArrayList<Integer>();
			System.out.println("Valid Const is: " + validConst);
			indexset.addAll(result.keySet());
			List<Integer> constIndexSet = new ArrayList<Integer>();
			constIndexSet.addAll(constResult.keySet());
			Map<Integer, List<Integer>> lineToCoeff = new HashMap<Integer, List<Integer>>();
			Map<Integer, List<Integer>> lineToConst = new HashMap<Integer, List<Integer>>();

			for (int coeff : cf.coeffIndexToLine.keySet()) {
				int line = cf.coeffIndexToLine.get(coeff);
				if (validIndexSet.contains(coeff)) {
					if (lineToCoeff.containsKey(line))
						lineToCoeff.get(line).add(coeff);
					else {
						lineToCoeff.put(line, new ArrayList<Integer>(coeff));
					}
				}
			}
			for (int constNo : cf.constMapLine.keySet()) {
				int line = cf.constMapLine.get(constNo);
				if (validIndexSet.contains(constNo)) {	
					if (lineToConst.containsKey(line))
						lineToConst.get(line).add(constNo);
					else {
						List<Integer> l = new ArrayList<Integer>();
						l.add(constNo);
						lineToConst.put(line, l);
					}
			
				}
			}
			System.out.println("Line to Coeff: " + lineToCoeff);
			System.out.println("Line to Const: " + lineToConst);
			Map<Integer, String> repair = new HashMap<Integer, String>();
			int tmpLine = -1;
/*			for (int k : result.keySet()) {
				if (ConstraintFactory.coeffIndexToLine.get(k) == tmpLine)
					continue;
				if (!validIndexSet.contains(k))
					continue;

				tmpLine = ConstraintFactory.coeffIndexToLine.get(k);
				String stmtString = ConstraintFactory.lineToString.get(tmpLine);
				repair.put(tmpLine, replaceCoeff(stmtString, result, ConstraintFactory.coeffIndexToLine, tmpLine));
			}*/
			for (int line : cf.lineToString.keySet()) {
				if (lineToCoeff.containsKey(line) || lineToConst.containsKey(line)){
					String stmtString = cf.lineToString.get(line);
					System.out.println("Line "+ line +"is : " + stmtString);
					repair.put(line, replaceCoeff(stmtString, result, constResult, cf.coeffIndexToLine,
							cf.constMapLine, line));
				}
			}
			System.out.println(repair);
			//return repair;
		} else {
			boolean consistancy = false;
			List<ExternalFunction> efs = new ArrayList<ExternalFunction>();
			for (ExternalFunction s : externalFuncs) {
				efs.add(s);
			}
			while (!consistancy) {
				String script_ex = script;
				for (ExternalFunction ef : efs) {
					script_ex = ef.toString() + script_ex;
				}
				// System.out.println(script_ex);
				// Map<Integer, Integer> result =
				// CallSketch.CallByString(script_ex);
				consistancy = true;
			}
			//return null;
		}
	}
	
	private String replaceCoeff(String stmtString, Map<Integer, Integer> result,
			Map<Integer, Integer> constResult, Map<Integer, Integer> coeffIndexToLine,
			Map<Integer, Integer> constMapLine, int tmpLine) {
		List<Integer> rangedCoeff = new ArrayList<Integer>();
		List<Integer> rangedConst = new ArrayList<Integer>();
		// System.out.println(result);
		for (int k : coeffIndexToLine.keySet()) {
			if (coeffIndexToLine.get(k) == tmpLine)
				rangedCoeff.add(k);
		}
		for (int k : constMapLine.keySet()) {
			if (constMapLine.get(k) == tmpLine) {
				System.out.println(k);
				rangedConst.add(k);
			}
		}
		for (int c : rangedCoeff) {
			if (result.containsKey(c))
				stmtString = stmtString.replace("(Coeff" + c + "())", result.get(c).toString());
			else
				stmtString = stmtString.replace("(Coeff" + c + "())", "0");

		}
		for (int c : rangedConst) {
			if (constResult.containsKey(c)) {
				System.out.println(stmtString);

				stmtString = stmtString.replace("(Const" + c + "())", constResult.get(c).toString());
				System.out.println(stmtString);

			}
			else
				stmtString = stmtString.replace("(Const" + c + "())", "0");

		}
		System.out.println(stmtString);
		stmtString = simplifyByCAS(stmtString);

		return stmtString;
	}
	
	private String simplifyByCAS(String stmtString) {
		System.out.println("The stmt string is: " + stmtString);
		String[] s;
		if (stmtString.substring(0, 2).equals("if")){
			String tmp = stmtString.substring(3, stmtString.length()-1);
			stmtString= "if(" +eval(tmp)+")";
			return stmtString;
		}
		if (stmtString.substring(0, 3).equals("for")) {
			s = stmtString.split(";", 3);
			s[0] = s[0].split("=",2)[0]+"= " + eval(s[0].split("=",2)[1]);
			s[1] = eval(s[1]);
			s[2] = eval(s[2].substring(0, s[2].length()-1));
			return s[0]+";"+s[1]+";"+s[2]+"){";
		}
		s = stmtString.split("=", 2);
		return s[0] + "= " + eval(s[1].substring(0, s[1].length() - 1)) + ";";

	}

	public String simplifyByRegEx(String stmtString) {
		String tmp = "";
		while (!tmp.equals(stmtString)) {
			tmp = stmtString;
			stmtString = stmtString.replaceAll("[(]0( )*[*]( )*[-]?( )*([0-9A-Za-z])*( )*[)]", "0");
			stmtString = stmtString.replaceAll("[(]( )*[-]?( )*([0-9A-Za-z])*( )*[*]( )*[0]( )*[)]", "0");
			stmtString = stmtString.replaceAll("[(]0( )*[+]( )*", "(");
			stmtString = stmtString.replaceAll("( )*[+]( )*0[)]", ")");
			stmtString = stmtString.replaceAll("( )*[-]( )*0[)]", ")");
			stmtString = stmtString.replaceAll("( )*[+]( )*0[;]", ";");
			stmtString = stmtString.replaceAll("( )*[-]( )*0[;]", ";");
			stmtString = stmtString.replaceAll("[(]0[)]", "0");
			stmtString = stmtString.replaceAll("[(]1( )*[*]( )*", "(");
			stmtString = stmtString.replaceAll("( )*[*]( )*1( )*[)]", ")");
			stmtString = stmtString.replaceAll("( )*[*]( )*1( )*[;]", ";");
			stmtString = deleRedPara(stmtString);

		}
		return stmtString;
	}

	public String deleRedPara(String s) {
		int len = s.length();
		for (int k = 2; k < len; k++) {
			for (int i = 0; i <= len - k; i++) {
				if (s.substring(i, i + k).matches("[(]( )*[\\d\\w]*( )*[)]")) {
					s = s.substring(0, i) + s.substring(i + 1, i + k - 1) + s.substring(i + k);
					len = len - 2;
					k = 4;
					i = 0;
					continue;
				}
				if (s.substring(i, i + k).matches("[(]( )*[(][\\w\\W]*[)]()*[)]")) {
					s = s.substring(0, i) + s.substring(i + 1, i + k - 1) + s.substring(i + k);
					len = len - 2;
					k = 4;
					i = 0;
				}
			}
		}
		return s;
	}


	public static SketchObject javaCompile(ANTLRInputStream input, String target) {
		simpleJavaLexer lexer 	 = new simpleJavaLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		simpleJavaParser parser  = new simpleJavaParser(tokens);
		ParseTree tree 			 = parser.compilationUnit();
		
		return new JavaVisitor(target).visit(tree);
	}
	
	public static Root jsonRootCompile(String s) {
		ANTLRInputStream input = new ANTLRInputStream(s);
		jsonLexer lexer = new jsonLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		jsonParser parser = new jsonParser(tokens);
		ParseTree tree = parser.json();
		return (Root) new JsonVisitor().visit(tree);
	}

	public String eval(String input) {

		ExprEvaluator util = new ExprEvaluator(false, 100);
		IExpr result = util.evaluate(input);
		return result.toString();
	}

	public static void main(String[] args) throws FileNotFoundException, InterruptedException {
	    String incorrectProgram = new Scanner(new File("benchmarks/double/double.java")).useDelimiter("\\Z").next();
	    String[] examples   	= {"x=1, y=2, z=3, 3", "x=3, y=2, z=1, 3", "x=5, y=8, z=1, 8"};
		Main m					= new Main(incorrectProgram, examples, "doubleUp", 1);
		m.begin();
	}
}
