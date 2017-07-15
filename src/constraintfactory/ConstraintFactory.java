package constraintfactory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import jsonast.Trace;
import jsonast.Traces;
import sketchobj.core.*;
import sketchobj.core.Function.FcnType;
import sketchobj.expr.*;
import sketchobj.stmts.*;

public class ConstraintFactory {

	static Function inputFunction;
	static String[] examples;
	static FcnHeader inputFunctionHeader;
	List<Parameter> inputArgs;
	Integer minimizationMode;
	Integer distanceMode;
	Integer specification;
	Integer semanticDistanceBound;
	public String distanceOperator;

	List<List<Expression>> inputs = new ArrayList<List<Expression>>();
	List<Expression>  outputs     = new ArrayList<Expression>();
	List<Expression> in           = new ArrayList<Expression>();

	// map from coefficient index to line number in the code
	public Map<Integer, Integer> coeffIndexToLine = new HashMap<Integer, Integer>();

	// map from line number to code string
	public Map<Integer, String> lineToString = new HashMap<Integer, String>();

	// map for external function
	public List<ExternalFunction> externalFuncs = new ArrayList<ExternalFunction>();

	public Map<String, Set<Integer>> constMap = new HashMap<String, Set<Integer>>();
	public Map<Integer, Integer> constMapLine = new HashMap<Integer, Integer>();


	int numberOfConstants = 0;  // number of constants in code
	Integer numLines      = -1; // number of lines in code
	Integer coeffIndex    = 0;  // number  of coefficients
	List<Integer> noWeightCoeff   = new ArrayList<Integer>();
	Map<String, Type> namesToType = new HashMap<String, Type>();
	List<String> varsList         = new ArrayList<String>();
	Integer length          	  = 100;  // sketch bound

	public ConstraintFactory(Function inputFunction, int specification, String[] examples, FcnHeader functionHeader,
			List<Parameter> args, Integer mode, Integer distanceBound, Integer length, String distanceOperator) {
		this.inputFunction     	 = inputFunction; // incorrect input function
		this.examples      		 = examples;    // test-cases
		this.inputFunctionHeader = functionHeader;  // incorrect input function header
		this.inputArgs       	 = args;      // arguments
		this.specification       = specification; // specification type e.g I/O examples, assertions
		this.minimizationMode    = mode;      // minimization mode
		this.distanceMode        = 0;         // Hamming Distance
		this.distanceOperator    = distanceOperator;
		if (specification == 0)
			parseExamples(examples);
		else if (specification == 1) {
			if (distanceBound == null)
				this.semanticDistanceBound = 5;
			else
				this.semanticDistanceBound = distanceBound;
			if (length != null)
				this.length = length;
		}

	}

	public ConstraintFactory(Function inputFunction, int specification, String[] examples, FcnHeader functionHeader,
			List<Parameter> args, Integer distanceBound, Integer length, String distanceOperator) {
		this(inputFunction, specification, examples, functionHeader, args, 0, distanceBound, length, distanceOperator);
	}

	public ConstraintFactory(Function inputFunction, int specification, String[] examples, FcnHeader functionHeader) {
		this(inputFunction, specification, examples, functionHeader, inputFunction.getParams(), null, null, "<");
	}

	public ConstraintFactory(Function inputFunction, int specification, String[] examples, FcnHeader functionHeader,
			int distanceBound, Integer length, String distanceOperator) {
		this(inputFunction, specification, examples, functionHeader, inputFunction.getParams(), distanceBound, length, distanceOperator);
	}



	private void parseExamples(String[] examples) {
		for (int i = 0; i < examples.length; i++) {
			List<Expression> input  = new ArrayList<Expression>();
			Expression output = null;
			String[] tokens = examples[i].split(",");
			for (int j = 0; j < tokens.length; j++) {
				if (tokens[j].trim().contains("=")) {
					String varName = tokens[j].split("=")[0].trim();
					System.out.print(varName + " = " );
					for (Parameter p : inputArgs) {
						if (p.getName().equals(varName)) {
							if (p.getType().toString().equals("int")) {
								System.out.println(tokens[j].split("=")[1]);
								Expression e = new ExprConstInt(tokens[j].split("=")[1]);
								input.add(e);
							}
						}
					}
				}
				else {
					System.out.println("Output = " + tokens[j].trim());
					output = new ExprConstInt(tokens[j].trim());
				}
			}
			inputs.add(input);
			outputs.add(output);
		}
	}

	// get sketch script for linear combinations
	public String getSketchScript(Statement source) {
		switch (specification) {
		case 0:
			return getSketchScriptForExamples(source);
		case 1:
			return getSketchScriptForAssertions(source);
		}
		return "";
	}

	private String getSketchScriptForAssertions(Statement s) {
		Statement source      	  = ((StmtBlock) s).clone();
		StmtBlock originalSource  = ((StmtBlock) source).clone();
		Statement coeffFunDecls   = null;
		Statement constFunDecls   = null;
		String reservedFunctions  = ReservedFuncs();

		System.out.println("*************************SOURCE**********************************");
		System.out.println(source);

		externalFuncs = source.extractExternalFuncs(externalFuncs);
		if (externalFuncs.size() > 0)
			System.out.println(externalFuncs.get(0).getName_Java());

		List<Statement> st = new ArrayList<Statement>();
		buildContext((StmtBlock) source, inputArgs, new ArrayList<Statement>());
		buildContext(originalSource, inputArgs, new ArrayList<Statement>());
		ConstraintFactory.addRecordStmtOriginal(originalSource);


		/*System.out.println("*************************ORIGINAL SOURCE**********************************");
    System.out.println(originalSource);
    System.out.println("*************************SOURCE CONTEXT**********************************");
    System.out.println(source.toString_Context());*/

		coeffFunDecls = replaceLinearCombination(source);
		/*System.out.println("*************************COEFFICIENT FUNCTION DECLARATIONS**********************************");
    System.out.println(coeffFunDecls);


    System.out.println("*************************ORIGINAL SOURCE**********************************");
    System.out.println(originalSource);*/

		Statement globalVarDecls = getGlobalDecls();
		/*System.out.println("*************************GLOBAL VARIABLE DECLARATIONS**********************************");
    System.out.println(globalVarDecls);*/

		constFunDecls = replaceConst(source);

		// add record statements to source code and collect variables info
		Map<String, Type> vars  = ConstraintFactory.addRecordStmt((StmtBlock) source);

		for (int i = 0; i < inputArgs.size(); i++) {
			vars.put(inputArgs.get(i).getName(), inputArgs.get(i).getType());
		}

		namesToType       		= vars;
		List<String> varsNames  = new ArrayList<String>(vars.keySet());
		varsList        		= varsNames;
		List<Type> varsTypes  	= new ArrayList<Type>();
		for (int i = 0; i < varsNames.size(); i++) {
			varsTypes.add(vars.get(varsNames.get(i)));
			//System.out.println(varsNames.get(i));
		}

		/*for (int i : constMapLine.keySet()) {
      System.out.println("The line number is: " + i + " and the value is: " + constMapLine.get(i));
    }*/
		List<Statement> stmts = new ArrayList<>();
		stmts.add(globalVarDecls);
		// add declare of constant functions
		stmts.add(coeffFunDecls);
		stmts.add(constFunDecls);
		// add line array
		stmts.add(
				new StmtBlock(varArrayDecl("line", length, new TypePrimitive(4)), varArrayDecls(varsNames, varsTypes, false)));
		stmts.add(
				new StmtBlock(varArrayDecl("lineOriginal", length, new TypePrimitive(4)), varArrayDecls(varsNames, varsTypes, true)));

		stmts.add(new StmtVarDecl(new TypePrimitive(4), "count", new ExprConstInt(-1), 0));
		stmts.add(new StmtVarDecl(new TypePrimitive(4), "originalCount", new ExprConstInt(-1), 0));


		Statement block = new StmtBlock(stmts);
		/*System.out.println("*************************BLOCK**********************************");
    System.out.println(block);*/

		source = new StmtBlock(new StmtVarDecl(new TypePrimitive(4), "linehit", new ExprConstInt(0), 0), source);

		Function f = new Function(ConstraintFactory.inputFunctionHeader, source);
		/*System.out.println("*************************FUNCTION**********************************");
    System.out.println(f);*/

		Function fOriginal = new Function(new FcnHeader(inputFunction.getName()+"Original", inputFunction.getReturnType(), 
				inputFunction.getParams()), originalSource);
		//constraintFunctionAssertions();

		StmtBlock inputHandling = new StmtBlock();
		/*System.out.println("The number of constants: " + numberOfConstants);*/
		for (int i = 0; i < inputArgs.size(); i++){
			inputHandling.addStmt(new StmtVarDecl(new TypePrimitive(1), "const"+numberOfConstants+"change", new ExprStar(), 0));
			inputHandling.addStmt(new StmtFunDecl(addConstFun(numberOfConstants, 1, new TypePrimitive(4))));
			in.add(new ExprFunCall("Const"+numberOfConstants));

			numberOfConstants++;

		}
		return block.toString() + "\n" + fOriginal.toString() + "\n" + f.toString() + "\n" +
		inputHandling.toString() + "\n" + constraintFunctionAssertions().toString() +
		"\n" + distanceFunctionAssertions().toString();
	}


	private Function constraintFunctionAssertions() {
		List<Statement> stmts = new ArrayList<Statement>();
		List<Expression> assertInputs = new ArrayList<Expression>();
		List<Parameter> params      = new ArrayList<Parameter>();
		for (int i = 0; i < inputArgs.size(); i++) {
			Expression e = new ExprVar("input"+i);
			assertInputs.add(e);
			Parameter p  = new Parameter(new TypePrimitive(4), ("input"+i), 0, false);
			params.add(p);
		}
		Statement cons   = new StmtAssert(new ExprBinary(new ExprFunCall(inputFunction.getName(), assertInputs),
				"==", new ExprVar("input0"), 0));
		Statement cons2  = new StmtAssert(new ExprBinary(new ExprFunCall(inputFunction.getName(), assertInputs),
				"==", new ExprVar("input1"), 0));
		Statement cons3  = new StmtAssert(new ExprBinary(new ExprFunCall(inputFunction.getName(), assertInputs),
				"==", new ExprVar("input2"), 0));
		Expression cond1 = new ExprBinary(new ExprBinary(new ExprVar("input0"), ">=", new ExprVar("input1"), 0), "&&",
				new ExprBinary(new ExprVar("input0"), ">=", new ExprVar("input2"), 0), 0);
		Expression cond2 = new ExprBinary(new ExprBinary(new ExprVar("input1"), ">=", new ExprVar("input0"), 0), "&&",
				new ExprBinary(new ExprVar("input1"), ">=", new ExprVar("input2"), 0), 0);
		stmts.add(new StmtIfThen(cond1, cons, new StmtIfThen(cond2, cons2, cons3)));

		return new Function("Constraint", new TypeVoid(), params, new StmtBlock(stmts),
				FcnType.Harness);
	}

	private Function distanceFunctionAssertions() {
		List<Statement> stmts = new ArrayList<Statement>();
		stmts.add(new StmtVarDecl(new TypePrimitive(4), "SyntacticDistance", new ExprConstInt(0), 0));
		stmts.add(new StmtVarDecl(new TypePrimitive(4), "SemanticDistance", new ExprConstInt(0), 0));

		// semantic distance
		if (distanceMode == 0)
			stmts.add(hammingDistanceAssertions());   

		// syntactic distance
		StmtBlock syntacticDistance = new StmtBlock();
		for (int i = 0; i < numberOfConstants; i++) {
			// if (!ConstraintFactory.noWeightCoeff.contains(i))
			syntacticDistance.addStmt(new StmtAssign(new ExprVar("SyntacticDistance"), new ExprVar("coeff" + i + "change"), 1, 1));
		}
		stmts.add(syntacticDistance);

		Expression sumOfConstChange = new ExprVar("const" + 0 + "change");
		stmts.add(new StmtAssert(new ExprBinary(new ExprVar("SemanticDistance"), distanceOperator, new ExprConstInt(semanticDistanceBound), 0), 0));

		stmts.add(new StmtMinimize(new ExprVar("SyntacticDistance+SemanticDistance"), true));

		return new Function("Distance", new TypeVoid(), new ArrayList<Parameter>(), new StmtBlock(stmts),
				FcnType.Harness);

	}

	private Statement hammingDistanceAssertions(){
		List<Statement> stmts = new ArrayList<Statement>();
		stmts.addAll(varArrayInitialization().stmts);

		StmtBlock cons = new StmtBlock();
		cons.addStmt(varArrayInitialization());
		cons.addStmt(new StmtAssign(new ExprVar("count"), new ExprConstInt(-1), 0));
		cons.addStmt(new StmtAssign(new ExprVar("originalCount"), new ExprConstInt(-1), 0));

		cons.addStmt(new StmtVarDecl(new TypePrimitive(4), "out", new ExprConstInt(0), 0));
		cons.addStmt(new StmtVarDecl(new TypePrimitive(4), "outOriginal", new ExprConstInt(0), 0));

		//cons.addStmt(new StmtAssign(new ExprVar("out"), new ExprFunCall(inputFunctionHeader.getName(), in, inputFunctionHeader.getName()), 0));
		//cons.addStmt(new StmtAssign(new ExprVar("outOriginal"), new ExprFunCall(inputFunctionHeader.getName()+"Original",
		//    in, inputFunctionHeader.getName()), 0));
		Statement cons1   = new StmtAssert(new ExprBinary(new ExprFunCall(inputFunction.getName(), in),
				"==", new ExprFunCall("Const"+(numberOfConstants-3)), 0));
		Statement cons2  = new StmtAssert(new ExprBinary(new ExprFunCall(inputFunction.getName(), in),
				"==", new ExprFunCall("Const"+(numberOfConstants-2)), 0));
		Statement cons3  = new StmtAssert(new ExprBinary(new ExprFunCall(inputFunction.getName(), in),
				"==", new ExprFunCall("Const"+(numberOfConstants-1)), 0));
		Expression cond1 = new ExprBinary(new ExprBinary(new ExprFunCall("Const"+(numberOfConstants-3)), ">=", new ExprFunCall("Const"+(numberOfConstants-2)), 0), "&&",
				new ExprBinary(new ExprFunCall("Const"+(numberOfConstants-3)), ">=", new ExprFunCall("Const"+(numberOfConstants-1)), 0), 0);
		Expression cond2 = new ExprBinary(new ExprBinary(new ExprFunCall("Const"+(numberOfConstants-2)), ">=", new ExprFunCall("Const"+(numberOfConstants-3)), 0), "&&",
				new ExprBinary(new ExprFunCall("Const"+(numberOfConstants-2)), ">=", new ExprFunCall("Const"+(numberOfConstants-1)), 0), 0);
		cons.addStmt(new StmtIfThen(cond1, cons1, new StmtIfThen(cond2, cons2, cons3)));

		Statement cons11   = new StmtAssert(new ExprBinary(new ExprFunCall(inputFunction.getName()+"Original", in),
				"==", new ExprFunCall("Const"+(numberOfConstants-3)), 0));
		Statement cons22  = new StmtAssert(new ExprBinary(new ExprFunCall(inputFunction.getName()+"Original", in),
				"==", new ExprFunCall("Const"+(numberOfConstants-2)), 0));
		Statement cons33  = new StmtAssert(new ExprBinary(new ExprFunCall(inputFunction.getName()+"Original", in),
				"==", new ExprFunCall("Const"+(numberOfConstants-1)), 0));
		Expression cond11 = new ExprBinary(new ExprBinary(new ExprFunCall("Const"+(numberOfConstants-3)), ">=", new ExprFunCall("Const"+(numberOfConstants-2)), 0), "&&",
				new ExprBinary(new ExprFunCall("Const"+(numberOfConstants-3)), ">=", new ExprFunCall("Const"+(numberOfConstants-1)), 0), 0);
		Expression cond22 = new ExprBinary(new ExprBinary(new ExprFunCall("Const"+(numberOfConstants-2)), ">=", new ExprFunCall("Const"+(numberOfConstants-3)), 0), "&&",
				new ExprBinary(new ExprFunCall("Const"+(numberOfConstants-2)), ">=", new ExprFunCall("Const"+(numberOfConstants-1)), 0), 0);
		cons.addStmt(new StmtIfThen(cond11, cons11, new StmtIfThen(cond22, cons22, cons33)));
		/*cons.addStmt(new StmtAssert(
        new ExprBinary(new ExprVar("out"),
            "==", new ExprBinary(new ExprFunCall("Const"+(numberOfConstants-2)), "+", new ExprFunCall("Const"+(numberOfConstants-1)), 0), 0)));
    cons.addStmt(new StmtAssert(
        new ExprBinary(new ExprVar("outOriginal"),
            "==", new ExprBinary(new ExprFunCall("Const"+(numberOfConstants-2)), "+", new ExprFunCall("Const"+(numberOfConstants-1)), 0), 0)));*/
		numberOfConstants -= inputArgs.size();

		List<Statement> forBody = new ArrayList<Statement>();
		Statement forinit = new StmtVarDecl(new TypePrimitive(4), "i", new ExprConstInt(0), 0);
		Expression forcon = new ExprBinary(new ExprVar("i"), "<", new ExprConstInt(length), 0);
		Statement forupdate = new StmtExpr(new ExprUnary(5, new ExprVar("i"), 0), 0);

		for (String v : varsList) {
			if (namesToType.get(v) instanceof TypeArray)
				continue;
			forBody.add(new StmtAssign(new ExprVar("SemanticDistance"),
					new ExprBinary(new ExprArrayRange(v + "Array", "i", 0), "!=",
							new ExprArrayRange(v + "OriginalArray", "i", 0), 0),
					1, 1));
		}

		//forBody.add(new StmtAssign(new ExprVar("SemanticDistance"), new ExprBinary(new ExprArrayRange("lineArray", "i", 0),
		//  "!=", new ExprArrayRange("lineOriginalArray", "i", 0), 0), 1, 1));
		cons.addStmt(new StmtFor(forinit, forcon, forupdate, new StmtBlock(forBody), false, 0));
		stmts.addAll(cons.stmts);

		StmtBlock s = new StmtBlock(stmts);
		return s;
	}

	private String getSketchScriptForExamples(Statement source) {
		StmtBlock originalSource  = ((StmtBlock) source).clone();
		Statement coeffFunDecls   = null;
		String reservedFunctions  = ReservedFuncs();

		System.out.println("*************************SOURCE**********************************");
		System.out.println(source);

		externalFuncs = source.extractExternalFuncs(externalFuncs);
		if (externalFuncs.size() > 0)
			System.out.println(externalFuncs.get(0).getName_Java());

		List<Statement> st = new ArrayList<Statement>();
		buildContext((StmtBlock) source, inputArgs, new ArrayList<Statement>());
		buildContext(originalSource, inputArgs, new ArrayList<Statement>());
		ConstraintFactory.addRecordStmtOriginal(originalSource);


		System.out.println("*************************ORIGINAL SOURCE**********************************");
		System.out.println(originalSource);


		Function fOriginal = new Function(new FcnHeader(inputFunction.getName()+"Original", inputFunction.getReturnType(), 
				inputFunction.getParams()), originalSource);

		System.out.println("*************************SOURCE CONTEXT**********************************");
		System.out.println(source.toString_Context());

		coeffFunDecls = replaceLinearCombination(source);
		System.out.println("*************************COEFFICIENT FUNCTION DECLARATIONS**********************************");
		System.out.println(coeffFunDecls);

		Statement globalVarDecls = getGlobalDecls();
		System.out.println("*************************GLOBAL VARIABLE DECLARATIONS**********************************");
		System.out.println(globalVarDecls);

		// add record statements to source code and collect variables info
		Map<String, Type> vars        = ConstraintFactory.addRecordStmt((StmtBlock) source);

		for (int i = 0; i < inputArgs.size(); i++) {
			vars.put(inputArgs.get(i).getName(), inputArgs.get(i).getType());
		}

		namesToType       = vars;
		List<String> varsNames  = new ArrayList<String>(vars.keySet());
		varsList        = varsNames;
		List<Type> varsTypes  = new ArrayList<Type>();
		for (int i = 0; i < varsNames.size(); i++) {
			varsTypes.add(vars.get(varsNames.get(i)));
			//System.out.println(varsNames.get(i));
		}

		List<Statement> stmts = new ArrayList<>();
		stmts.add(globalVarDecls);
		// add declare of constant functions
		stmts.add(coeffFunDecls);
		// add line array
		stmts.add(
				new StmtBlock(varArrayDecl("line", length, new TypePrimitive(4)), varArrayDecls(varsNames, varsTypes, false)));
		stmts.add(
				new StmtBlock(varArrayDecl("lineOriginal", length, new TypePrimitive(4)), varArrayDecls(varsNames, varsTypes, true)));

		stmts.add(new StmtVarDecl(new TypePrimitive(4), "count", new ExprConstInt(-1), 0));
		stmts.add(new StmtVarDecl(new TypePrimitive(4), "originalCount", new ExprConstInt(-1), 0));


		Statement block = new StmtBlock(stmts);
		System.out.println("*************************BLOCK**********************************");
		System.out.println(block);

		source = new StmtBlock(new StmtVarDecl(new TypePrimitive(4), "linehit", new ExprConstInt(0), 0), source);

		Function f = new Function(ConstraintFactory.inputFunctionHeader, source);
		System.out.println("*************************FUNCTION**********************************");
		System.out.println(f);

		constraintFunctionExamples();
		return block.toString() + "\n" + fOriginal.toString() + "\n" + f.toString() + "\n" + constraintFunctionExamples().toString();

	}

	private Function constraintFunctionExamples() {
		List<Statement> stmts = new ArrayList<Statement>();
		for (int i = 0; i < outputs.size(); i++) {
			stmts.add(new StmtAssert(
					new ExprBinary(new ExprFunCall(inputFunctionHeader.getName(),inputs.get(i), inputFunctionHeader.getName()),
							"==", outputs.get(i), 0)));

		}

		// distance initialization
		stmts.add(new StmtVarDecl(new TypePrimitive(4), "SyntacticDistance", new ExprConstInt(0), 0));
		stmts.add(new StmtVarDecl(new TypePrimitive(4), "SemanticDistance", new ExprConstInt(0), 0));

		// semantic distance
		if (distanceMode == 0)
			stmts.add(hammingDistance());   

		// syntactic distance
		StmtBlock syntacticDistance = new StmtBlock();
		for (int i = 0; i < numberOfConstants; i++) {
			// if (!ConstraintFactory.noWeightCoeff.contains(i))
			syntacticDistance.addStmt(new StmtAssign(new ExprVar("SyntacticDistance"), new ExprVar("coeff" + i + "change"), 1, 1));
		}
		stmts.add(syntacticDistance);

		Expression sumOfConstChange = new ExprVar("const" + 0 + "change");
		stmts.add(new StmtMinimize(new ExprVar("SemanticDistance+SyntacticDistance"), true));

		return new Function("Constraint", new TypeVoid(), new ArrayList<Parameter>(), new StmtBlock(stmts),
				FcnType.Harness);

	}

	private Statement hammingDistance() {
		List<Statement> stmts = new ArrayList<Statement>();
		stmts.addAll(varArrayInitialization().stmts);
		for (int i = 0; i < outputs.size(); i++) {
			Expression cond = new ExprBinary(new ExprFunCall(inputFunctionHeader.getName()+"Original", inputs.get(i), inputFunctionHeader.getName()+"Original"),
					"==", outputs.get(i), 0);
			StmtBlock cons = new StmtBlock();
			cons.addStmt(varArrayInitialization());
			cons.addStmt(new StmtAssign(new ExprVar("count"), new ExprConstInt(-1), 0));
			cons.addStmt(new StmtAssign(new ExprVar("originalCount"), new ExprConstInt(-1), 0));

			cons.addStmt(new StmtVarDecl(new TypePrimitive(4), "max"+i, new ExprConstInt(0), 0));
			cons.addStmt(new StmtVarDecl(new TypePrimitive(4), "maxOriginal"+i, new ExprConstInt(0), 0));

			cons.addStmt(new StmtAssign(new ExprVar("max"+i), new ExprFunCall(inputFunctionHeader.getName(), inputs.get(i), inputFunctionHeader.getName()), 0));
			cons.addStmt(new StmtAssign(new ExprVar("maxOriginal"+i), new ExprFunCall(inputFunctionHeader.getName()+"Original",
					inputs.get(i), inputFunctionHeader.getName()), 0));
			List<Statement> forBody = new ArrayList<Statement>();
			Statement forinit = new StmtVarDecl(new TypePrimitive(4), "i", new ExprConstInt(0), 0);
			Expression forcon = new ExprBinary(new ExprVar("i"), "<", new ExprConstInt(length), 0);
			Statement forupdate = new StmtExpr(new ExprUnary(5, new ExprVar("i"), 0), 0);

			for (String v : varsList) {
				if (namesToType.get(v) instanceof TypeArray)
					continue;
				forBody.add(new StmtAssign(new ExprVar("SemanticDistance"),
						new ExprBinary(new ExprArrayRange(v + "Array", "i", 0), "!=",
								new ExprArrayRange(v + "OriginalArray", "i", 0), 0),
						1, 1));
			}

			//forBody.add(new StmtAssign(new ExprVar("SemanticDistance"), new ExprBinary(new ExprArrayRange("lineArray", "i", 0),
			//  "!=", new ExprArrayRange("lineOriginalArray", "i", 0), 0), 1, 1));
			cons.addStmt(new StmtFor(forinit, forcon, forupdate, new StmtBlock(forBody), false, 0));
			cons.addStmt(varArrayInitialization());
			stmts.add(new StmtIfThen(cond, cons, null, 0));
			//stmts.add(cons);
		}
		StmtBlock s = new StmtBlock(stmts);
		return s;

	}

	private Statement replaceLinearCombination(Statement source) {
		List<Statement> list          = new ArrayList<Statement>();
		Stack<SketchObject> stmtStack = new Stack<SketchObject>();
		List<Integer> coeffIndices    = new ArrayList<Integer>();
		int index = 0;
		stmtStack.push(source);
		while (!stmtStack.empty()) {
			SketchObject target = stmtStack.pop();
			ConstData data    	= null;
			data        		= target.replaceLinearCombination(index);
			if (data.getType() != null) {
				while (index <= data.getPrimaryCoeffIndex()) {
					if (!coeffIndices.contains(index)) {
						list.add(coeffChangeDecl(index, new TypePrimitive(1)));
						list.add(new StmtFunDecl(addCoeffFun(index, 1, data.getType())));
						coeffIndexToLine.put(index, data.getOriline());
						coeffIndices.add(index);
					}
					index++;
				}
				if (data.getLiveVarsIndexSet() != null) {
					for (int ii : data.getLiveVarsIndexSet()) {
						if (!coeffIndices.contains(ii)) {
							list.add(coeffChangeDecl(ii, new TypePrimitive(1)));
							list.add(new StmtFunDecl(addCoeffFun(ii, 0, data.getType())));
							coeffIndexToLine.put(ii, data.getOriline());
							coeffIndices.add(ii);
						}
					}

				}
				index = data.getIndex();
				if (!data.isLC()) {
					if (!coeffIndices.contains(index - 2)) {
						noWeightCoeff.add(index - 2);
						list.add(coeffChangeDecl(index - 2, new TypePrimitive(1)));
						list.add(new StmtFunDecl(addCoeffFun(index - 2, 0, data.getType())));
						coeffIndexToLine.put(index - 2, data.getOriline());
						coeffIndices.add(index - 2);
					}
					if (!coeffIndices.contains(index - 1)) {
						list.add(coeffChangeDecl(index - 1, new TypePrimitive(4)));
						list.add(new StmtFunDecl(addLCConstFun(index - 1, data.getType())));
						coeffIndexToLine.put(index - 1, data.getOriline());
						coeffIndices.add(index - 1);
					}

				}
			}
			index = data.getIndex();
			pushAll(stmtStack, data.getChildren());
		}
		numberOfConstants = index;
		return new StmtBlock(list);
	}

	public Statement replaceConst(Statement source) {
		List<Statement> list = new ArrayList<Statement>();
		Stack<SketchObject> stmtStack = new Stack<SketchObject>();
		int index = 0;
		stmtStack.push(source);
		while (!stmtStack.empty()) {
			SketchObject target = stmtStack.pop();
			ConstData data = null;
			data = target.replaceConst(index);
			if (data.getType() != null) {
				//System.out.println("Data index is : " + data.getIndex());
				addToConstMap(data, index);
				addToConstMapLine(data, index);
				list.add(constChangeDecl(index, new TypePrimitive(1)));
				list.add(new StmtFunDecl(addConstFun(index, data.getValue(), data.getType())));
			}
			//System.out.println("Target value is : " + target);

			index = data.getIndex();
			pushAll(stmtStack, data.getChildren());
		}
		source.ConstructLineToString(lineToString);

		/*System.out.println("*************************LINE TO STRING**********************************");
    System.out.println(lineToString);*/
		return new StmtBlock(list);

	}

	private static Statement coeffChangeDecl(int index, TypePrimitive typePrimitive) {
		return new StmtVarDecl(typePrimitive, "coeff" + index + "change", new ExprStar(), 0);
	}


	private static Function addCoeffFun(int index, int value, Type type) {
		Expression condition  = new ExprBinary(new ExprVar("coeff" + index + "change"), "==", new ExprConstInt(0), 0);
		StmtReturn return1    = new StmtReturn(new ExprConstInt(value), 0);
		Expression condition2   = new ExprStar();
		StmtReturn return2    = new StmtReturn(new ExprConstInt(1 - value), 0);
		Statement ifst      = new StmtIfThen(condition, return1, null, 0);
		Statement ifst2     = new StmtIfThen(condition2, return2, null, 0);
		StmtReturn return3    = new StmtReturn(new ExprConstInt(-1), 0);
		StmtBlock sb      = new StmtBlock();
		sb.addStmt(ifst);
		sb.addStmt(ifst2);
		sb.addStmt(return3);
		return new Function("Coeff" + index, type, new ArrayList<Parameter>(), sb, FcnType.Static);
	}


	private static Function addLCConstFun(int index, Type type) {
		Expression condition2 = new ExprStar();
		StmtReturn return2    = new StmtReturn(new ExprConstInt(0), 0);
		StmtReturn return3    = new StmtReturn(new ExprVar("coeff" + index + "change"), 0);

		Statement ifst2     = new StmtIfThen(condition2, return2, null, 0);
		StmtBlock sb      = new StmtBlock();
		sb.addStmt(ifst2);
		sb.addStmt(return3);
		return new Function("Coeff" + index, type, new ArrayList<Parameter>(), sb, FcnType.Static);
	}

	private static Function addInputCoeffFun(int index, Type type) {
		StmtReturn returnStmt = new StmtReturn(new ExprVar("coeff" + index + "change"), 0);
		StmtBlock sb        = new StmtBlock();
		sb.addStmt(returnStmt);
		return new Function("Coeff" + index, type, new ArrayList<Parameter>(), sb, FcnType.Static);

	}

	static public Statement constChangeDecl(int index, Type t) {
		return new StmtVarDecl(t, "const" + index + "change", new ExprStar(), 0);
	}

	static public Statement constChangeDecls(int number, Type t) {
		StmtBlock result = new StmtBlock();
		for (int i = 0; i < number; i++) {
			result.addStmt(new StmtVarDecl(t, "const" + i + "change", new ExprStar(), 0));
		}
		return result;
	}

	private void addToConstMapLine(ConstData data, int index) {
		//System.out.println("Const index is: " + data.getIndex());
		constMapLine.put(index, data.getOriline());
	}

	private void addToConstMap(ConstData data, int index) {
		if (constMap.containsKey(data.getName())) {
			Set<Integer> s = constMap.get(data.getName());
			s.add(index);
		} else {
			Set<Integer> s = new HashSet<Integer>();
			s.add(index);
			constMap.put(data.getName(), s);
		}
	}

	static public Function addConstFun(int index, int ori, Type t) {
		Expression condition = new ExprBinary(new ExprVar("const" + index + "change"), "==", new ExprConstInt(1), 0);
		StmtReturn return_1 = new StmtReturn(new ExprStar(), 0);
		StmtReturn return_2 = new StmtReturn(new ExprConstInt(ori), 0);
		Statement ifst = new StmtIfThen(condition, return_1, return_2, 0);

		return new Function("Const" + index, t, new ArrayList<Parameter>(), ifst, FcnType.Static);
	}


	private Statement getGlobalDecls() {
		StmtBlock result = new StmtBlock();
		List<Integer> appeared = new ArrayList<Integer>();
		for (int line : coeffIndexToLine.values()) {
			if (appeared.contains(line))
				continue;
			result.addStmt(new StmtVarDecl(new TypePrimitive(1), "line" + line + "change", new ExprConstInt(0), 0));
			appeared.add(line);
		}
		numLines = appeared.size();
		return result;
	}

	static public void buildContext(StmtBlock sb, List<Parameter> args, List<Statement> originalStatements) {
		Context context = new Context();
		Map<String, Type> currentVars = new HashMap<String, Type>();
		for (int i = 0; i < args.size(); i++) {
			currentVars.put(args.get(i).getName(), args.get(i).getType());
		}
		context.setCurrentVars(currentVars);
		context.pushVars(currentVars);
		sb.buildContext(context, 0, originalStatements);
	}

	static public Map<String, Type> addRecordStmt(StmtBlock source) {
		return source.addRecordStmt(null, 0, new HashMap<String, Type>());
	}

	static public void addRecordStmtOriginal(StmtBlock source) {

		source.addRecordStmtOriginal(null, 0);
	}

	static public Statement recordState(int lineNumber, Map<String, Type> allVars) {
		List<String> vars   = new ArrayList<String>(allVars.keySet());
		StmtBlock result  = new StmtBlock();

		result.addStmt(new StmtExpr(new ExprUnary(5, new ExprVar("count"), 0), 0));
		result.addStmt(
				new StmtAssign(
						new ExprArrayRange(new ExprVar("lineArray"),
								new ExprArrayRange.RangeLen(new ExprVar("count"), null), 0),
						new ExprConstInt(lineNumber), 0));

		for (String s : vars) {
			if (allVars.get(s) instanceof TypeArray)
				continue;
			result.addStmt(new StmtAssign(new ExprArrayRange(new ExprVar(s + "Array"),
					new ExprArrayRange.RangeLen(new ExprVar("count"), null), 0), new ExprVar(s), 0));
		}
		return result;
	}

	static public Statement recordStateOriginal(int lineNumber, Map<String, Type> allVars) {
		List<String> vars   = new ArrayList<String>(allVars.keySet());
		StmtBlock result  = new StmtBlock();
		result.addStmt(new StmtExpr(new ExprUnary(5, new ExprVar("originalCount"), 0), 0));
		result.addStmt(
				new StmtAssign(
						new ExprArrayRange(new ExprVar("lineOriginalArray"),
								new ExprArrayRange.RangeLen(new ExprVar("originalCount"), null), 0),
						new ExprConstInt(lineNumber), 0));

		for (String s : vars) {
			if (allVars.get(s) instanceof TypeArray)
				continue;
			result.addStmt(new StmtAssign(new ExprArrayRange(new ExprVar(s + "OriginalArray"),
					new ExprArrayRange.RangeLen(new ExprVar("originalCount"), null), 0), new ExprVar(s), 0));
		}
		return result;

	}

	static public Statement varArrayDecl(String name, int length, Type type) {
		Type t = new TypeArray(type, new ExprConstInt(length));
		List<Expression> lineArrayInit = new ArrayList<>();
		for (int j = 0; j < length; j++) {
			lineArrayInit.add(new ExprConstInt(0));
		}
		return new StmtVarDecl(t, name + "Array", new ExprArrayInit(lineArrayInit), 0);
	}

	private StmtBlock varArrayDecls(List<String> names, List<Type> types, boolean original) {
		List<Statement> stmts = new ArrayList<Statement>();
		String arrayName    = original ? "OriginalArray" : "Array";
		for (int i = 0; i < names.size(); i++) {
			if (types.get(i) instanceof TypeArray)
				continue;
			Type tarray = new TypeArray(types.get(i), new ExprConstInt(length));

			List<Expression> arrayinit = new ArrayList<>();
			for (int j = 0; j < length; j++) {
				arrayinit.add(new ExprConstInt(0));
			}

			stmts.add(new StmtVarDecl(tarray, names.get(i) + arrayName, new ExprArrayInit(arrayinit), 0));
		}

		return new StmtBlock(stmts);
	}

	private StmtBlock varArrayInitialization() {
		List<Statement> stmts = new ArrayList<Statement>();
		for (String v : varsList) {
			List<Expression> arrayinit = new ArrayList<>();
			for (int j = 0; j < length; j++) {
				arrayinit.add(new ExprConstInt(0));
			}
			stmts.add(new StmtAssign(new ExprVar(v + "Array"), new ExprArrayInit(arrayinit), 0));
			stmts.add(new StmtAssign(new ExprVar(v + "OriginalArray"), new ExprArrayInit(arrayinit), 0));
		}
		List<Expression> linearrayinit = new ArrayList<>();
		for (int j = 0; j < length; j++) {
			linearrayinit.add(new ExprConstInt(0));
		}
		stmts.add(new StmtAssign(new ExprVar("lineOriginalArray"), new ExprArrayInit(linearrayinit), 0));
		stmts.add(new StmtAssign(new ExprVar("lineArray"), new ExprArrayInit(linearrayinit), 0));
		return new StmtBlock(stmts);
	}

	static public void addOriginalFunction(Statement source) {
		String[] lines = source.toString().split("\n");
		System.out.println(lines.length);
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	static public void pushAll(Stack s, List l) {
		for (int i = l.size() - 1; i >= 0; i--) {
			s.push(l.get(i));
		}
	}

	private String ReservedFuncs() {
		// TODO Auto-generated method stub
		return null;
	}
}

