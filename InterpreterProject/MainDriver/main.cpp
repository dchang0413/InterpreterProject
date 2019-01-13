#include <iostream>
#include <fstream>
#include <string>
#include <FlexLexer.h>
#include "ErrorMsg.h"
#include "Env.h"
#include "Print.h"
#include "Interpreter.h"
#include "TypeChecking.h"

using namespace std;

extern int yyparse(void);
extern ErrorMsg	errormsg;
extern absyn::Exp*	root;

yyFlexLexer		lexer;

int parse(string fname) 
{
	ifstream	ifs(fname);
	errormsg.reset(fname);
	lexer.switch_streams(&ifs, NULL);

	return yyparse();
}

extern int yydebug;

int main(int argc, char **argv) 
{
	yydebug = 0;
	if (argc!=2) 
	{
		cerr <<"usage: " << argv[0] << " filename" << endl; 
		return 1;
	}
	if ( parse(argv[1]) == 0 )
		cout << "Parsing successful!\n" << endl;
	else
	{
		cout << "Parsing failed\n" << endl;
		return -1;
	}

	absyn::Print	print(cout);
	//print.prExp(root, 0);
	//cout << endl << endl;

	semantics::TypeChecking			typechecking(&errormsg);
	interpreter::Interpreter		interp(&errormsg);
	
	//typechecking.visit(root);
	if ( typechecking.hasSemanticError() )
		cout << "The program has semantic errors. It cannot be interpreted!";
	else
	{
		runtime::VarEntry result = interp.interp( root );

		cout << endl << "The result of the program is: ";
		if ( result.isInt() )
			cout << result.ival << endl;
		else if ( result.isString() )
			cout << result.sval << endl;
		else
			cout << "VOID" << endl;
	}
	cout << endl;

	return 0;
}