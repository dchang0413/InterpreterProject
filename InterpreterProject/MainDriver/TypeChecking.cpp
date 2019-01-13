#include "TypeChecking.h"
#include <iostream>
#include <sstream>

/*
PROGRAMMER: David Mathis
PROGRAM: project6
DUE DATE: 11/26/18
INSTRUCTOR: Dr. Zhijiang Dong
*/


using namespace symbol;


namespace semantics
{
	const string		TypeChecking::breakSign = "breaksign";

	//insert a variable into the var/function symbol table
	void TypeChecking::insertVar(string name, symbol::SymTabEntry entry)
	{
		string			msg;
		stringstream	ss(msg);

		if (env.getVarEnv()->localContains(name))
		{
			symbol::SymTabEntry		old = env.getVarEnv()->lookup(name);
			ss << "variable " << name << " is already defined at line " << old.node->getLineno();
			error(entry.node, ss.str());

		}
		else
			env.getVarEnv()->insert(name, entry);
	}

	//insert a function into the var/function symbol table
	void TypeChecking::insertFunc(string name, symbol::SymTabEntry entry)
	{
		string			msg;
		stringstream	ss(msg);

		if (env.getVarEnv()->localContains(name))
		{
			symbol::SymTabEntry		old = env.getVarEnv()->lookup(name);
			ss << "function " << name << " is already defined at line " << old.node->getLineno();
			error(entry.node, ss.str());

		}
		else
			env.getVarEnv()->insert(name, entry);
	}

	//insert a type into the type symbol table
	void TypeChecking::insertType(string name, symbol::SymTabEntry entry)
	{
		string			msg;
		stringstream	ss(msg);

		if (env.getTypeEnv()->localContains(name))
		{
			symbol::SymTabEntry		old = env.getTypeEnv()->lookup(name);
			ss << "variable " << name << " is already defined at line " << old.node->getLineno();
			error(entry.node, ss.str());

		}
		else
			env.getTypeEnv()->insert(name, entry);
	}

	const types::Type* TypeChecking::visit(const Absyn *v)
	{
		if (dynamic_cast<const Exp *>(v) != NULL)
			return visit(dynamic_cast<const Exp *>(v));
		else if (dynamic_cast<const Var *>(v) != NULL)
			return visit(dynamic_cast<const Var *>(v));
		else if (dynamic_cast<const Dec *>(v) != NULL)
			return visit(dynamic_cast<const Dec *>(v));
		else
			throw runtime_error("invalid node");
	}

	const types::Type* TypeChecking::visit(const Exp *e)
	{
		if (dynamic_cast<const OpExp*>(e) != NULL)			return visit((const OpExp*)e);
		else if (dynamic_cast<const VarExp*>(e) != NULL)	return visit((const VarExp*)e);
		else if (dynamic_cast<const NilExp*>(e) != NULL)	return visit((const NilExp*)e);
		else if (dynamic_cast<const IntExp*>(e) != NULL)	return visit((const IntExp*)e);
		else if (dynamic_cast<const StringExp*>(e) != NULL) return visit((const StringExp*)e);
		else if (dynamic_cast<const CallExp*>(e) != NULL)	return visit((const CallExp*)e);
		//		else if (dynamic_cast<const RecordExp*>(e) != NULL) return visit((const RecordExp*)e);
		else if (dynamic_cast<const SeqExp*>(e) != NULL)	return visit((const SeqExp*)e);
		else if (dynamic_cast<const AssignExp*>(e) != NULL) return visit((const AssignExp*)e);
		else if (dynamic_cast<const IfExp*>(e) != NULL)		return visit((const IfExp*)e);
		else if (dynamic_cast<const WhileExp*>(e) != NULL)	return visit((const WhileExp*)e);
		else if (dynamic_cast<const ForExp*>(e) != NULL)	return visit((const ForExp*)e);
		else if (dynamic_cast<const BreakExp*>(e) != NULL)	return visit((const BreakExp*)e);
		else if (dynamic_cast<const LetExp*>(e) != NULL)	return visit((const LetExp*)e);
		else if (dynamic_cast<const ArrayExp*>(e) != NULL)	return visit((const ArrayExp*)e);
		else throw new runtime_error("ExpType.visit(Exp*)");
	}

	const types::Type* TypeChecking::visit(const Var *v)
	{
		if (dynamic_cast<const SimpleVar *>(v) != NULL)			return visit((const SimpleVar *)v);
		//		else if (dynamic_cast<const FieldVar *>(v) != NULL)		return visit((const FieldVar *) v);
		else if (dynamic_cast<const SubscriptVar *>(v) != NULL) return visit((const SubscriptVar *)v);
		else throw new runtime_error("ExpType.visit(Var*)");
	}

	const types::Type* TypeChecking::visit(const Ty *t)
	{
		if (dynamic_cast<const NameTy *>(t) != NULL)			return visit((const NameTy *)t);
		else if (dynamic_cast<const ArrayTy *>(t) != NULL)		return visit((const ArrayTy *)t);
		//		else if (dynamic_cast<const RecordTy *>(t) != NULL)		return visit((const RecordTy *)t);
		else throw new runtime_error("ExpType.visit(Ty*)");
	}

	const types::Type* TypeChecking::visit(const Dec *d)
	{
		if (dynamic_cast<const TypeDec *>(d) != NULL)			return visit((const TypeDec *)d);
		else if (dynamic_cast<const VarDec *>(d) != NULL)		return visit((const VarDec *)d);
		//		else if (dynamic_cast<const FunctionDec *>(d) != NULL)	return visit((const FunctionDec *)d);
		else throw new runtime_error("ExpType.visit(Dec*)");
	}

	const types::Type* TypeChecking::visit(const SimpleVar *v)
	{
		if (!(env.getVarEnv()->contains(v->getName())))
		{
			error(v, "undefined variable");
			//undeclared variables is treated as INT variable
			insertVar(v->getName(), SymTabEntry(env.getVarEnv()->getLevel(),
				new types::INT(),
				v));
			return new types::INT();
		}
		else
		{
			const types::Type*	t = env.getVarEnv()->lookup(v->getName()).info->actual();

			if (dynamic_cast<const types::FUNCTION *>(t) != NULL)
			{
				error(v, "function with the same name exists");
				//undeclared variables is treated as INT variable
				return new types::INT();
			}
			return t;
		}
	}

	/*	const types::Type* TypeChecking::visit(const FieldVar *v)
	{
	//add your implementation here
	//syntax: lvalue.fieldname

	Algorithm:
	1.	Perform type checking on lvalue, and get its data type (say t)
	2.	if t is not a record type
	report an error
	return INT
	else
	3.		cast t to RECORD *;
	4.		For each filed in the RECORD definition
	if the fieldname is the one we are looking for
	return the type of current field
	5.		report an error for non-existing field
	6.		return INT.
	}
	*/

	//This function checks if the subscript is an int and if lvalue is an array type
	const types::Type* TypeChecking::visit(const SubscriptVar *v)
	{
		//add your implementation here

		const types::Type*	t = visit(v->getVar());
		if (dynamic_cast<const types::ARRAY *>(t) != NULL)
		{
			error(v, "lvalue must be of type: ARRAY");
		}
		const types::Type* te = visit(v->getIndex());
		if (dynamic_cast<const types::INT *>(te) != NULL)
		{
			error(v, "index_exp must be of type: INT");
		}
		if (dynamic_cast<const types::ARRAY *>(t) != NULL)
		{
			return new types::INT();
		}
		else
		{
			return t->actual();
		}
		//syntax: lvalue[index_exp]
		/*
		Algorithm:
		1.	Perform type checking on lvalue, and get its data type (say t)
		2.	if t is not ARRAY type
		report an error
		3.	Perform type checking on index_exp, and get its data type (say te)
		4.	if te is not INT
		report an error
		5.	if t is not ARRAY
		return INT
		else
		return the type of array element which can be
		found at ((ARRAY *)t)
		*/
	}

	//This function checks for valid operator expressions
	const types::Type* TypeChecking::visit(const OpExp *e)
	{
		//add your implementation here

		const types::Type*	lt = visit(e->getLeft());
		const types::Type*	rt = visit(e->getRight());
		OpExp::OpType x = e->getOper();
		if (x == OpExp::OpType::PLUS || x == OpExp::OpType::MINUS || OpExp::OpType::MUL || OpExp::OpType::DIV)
		{
			if (dynamic_cast<const types::INT *>(lt) != NULL)
			{
				error(e, "The left operand must be of type: INT");
			}
			if (dynamic_cast<const types::INT *>(rt) != NULL)
			{
				error(e, "The right operand must be of type: INT");
			}
			return new types::INT();
		}
		else if (x == OpExp::OpType::GT || x == OpExp::OpType::LT || OpExp::OpType::GE || OpExp::OpType::GT)
		{
			if (dynamic_cast<const types::INT *>(lt) != NULL || dynamic_cast<const types::STRING*>(lt) != NULL)
			{
				error(e, "The left operand must be of type: INT or STRING");
			}
			if (dynamic_cast<const types::INT *>(rt) != NULL || dynamic_cast<const types::STRING*>(rt) != NULL)
			{
				error(e, "The right operand must be of type: INT or STRING");
			}
			if (lt->coerceTo(rt) == false || rt->coerceTo(lt) == false)
			{
				error(e, "The two operands are not compatible");
			}
			return new types::INT();
		}
		else
		{
			if (dynamic_cast<const types::INT *>(lt) != NULL || dynamic_cast<const types::STRING *>(lt) != NULL ||
				dynamic_cast<const types::RECORD *>(lt) != NULL || dynamic_cast<const types::NIL *>(lt) != NULL)
			{
				error(e, "The left operand must be of type: INT, STRING, RECORD, or NIL");
			}
			if (dynamic_cast<const types::INT *>(rt) != NULL || dynamic_cast<const types::STRING *>(rt) != NULL ||
				dynamic_cast<const types::RECORD *>(rt) != NULL || dynamic_cast<const types::NIL *>(rt) != NULL)
			{
				error(e, "The right operand must be of type: INT, STRING, RECORD, or NIL");
			}
			if (lt->coerceTo(rt) == false || rt->coerceTo(lt) == false)
			{
				error(e, "The two operands are not compatible");
			}
			if (dynamic_cast<const types::NIL *>(lt) != NULL || dynamic_cast<const types::NIL *>(rt) != NULL)
			{
				error(e, "The two operands cannot both be of type: NIL");
			}
			return new types::INT();
		}

		//syntax: left_exp Operator right_exp
		/*
		Algorithm:
		1.	Perform type checking on left_exp, and get its data type (say lt)
		2.	Perform type checking on right_exp, and get its data type (say rt)
		3.	if Operator is one of +, -, *, /
		if lt is not an INT, report an error
		if rt is not an INT, report an error
		return INT
		4.	else if Operator is one of >, >=, <, <=
		if lt is not an INT/STRING, report an error
		if rt is not an INT/STRING, report an error
		if lt and rt are not compatible
		report an error
		return INT;
		5.	else //i.e. =, <>
		if lt is not an INT/STRING/ARRAY/RECORD/NIL, report an error
		if rt is not an INT/STRING/ARRAY/RECORD/NIL, report an error
		if lt and rt are not compatible
		report an error
		if both lt and rt are NIL
		report an error
		return INT
		*/
	}

	const types::Type* TypeChecking::visit(const VarExp *e)
	{
		const types::Type*		t = visit(e->getVar());
		return t->actual();
	}

	const types::Type* TypeChecking::visit(const NilExp *e)
	{
		return new types::NIL();
	}

	const types::Type* TypeChecking::visit(const IntExp *e)
	{
		return new types::INT();
	}

	const types::Type* TypeChecking::visit(const StringExp *e)
	{
		return new types::STRING();
	}

	//This function checks for valid function calls
	const types::Type* TypeChecking::visit(const CallExp *e)
	{
		//add your implementation here

		//syntax: fname(exp1, exp2, ..., expn)
		/*
		Algorithm:
		things that can go wrong:
		1. fname is undefined
		2. fname is defined as variable
		3. the type of exp_i doesn't match the type of param_i
		4. the # of expressions doesn't match the # of parameters
		*/
		//check if fname is defined by looking up the symbol table
		string fname = e->getFunc();
		if (!(env.getVarEnv()->contains(fname)))
		{
			//if fname is not defined, report an error, and return INT
			error(e, "fname is undefined");
			return new types::INT();
		}
		else
		{
			//if fname is defined, get its data type, say t
			const types::Type *t = env.getVarEnv()->lookup(fname).info->actual();
			//if t is not FUNCTION, report and error and return INT;
			if (dynamic_cast<const types::FUNCTION *>(t) == NULL)
			{
				error(e, "fname is defined as variable");
				return new types::INT();
			}
			//convert t to FUNCTION *
			else
			{
				//Let c_arg refers to the first argument (argument list can be found in CallExp)
				//Let c_par refers to the first parameter(parameter list can be found in FUNCTION)
				const ExpList* c_arg = e->getArgs();
				vector <const types::Type*> c_par;
				c_par = dynamic_cast <const types::FUNCTION*>(env.getVarEnv()->lookup(e->getFunc()).info)->getFieldType();
				vector <const types::Type*>::iterator c_iter = c_par.begin();
				/*			repeat as long as both c_arg and c_par are not NULL
				perform type checking on c_arg and get its type, see ta
				if (ta is not compatible with type of c_par)
				report an error
				update c_arg to refer to next argument
				update c_par to refer to next parameter
				end repeat	*/
				while (c_arg != NULL && c_iter != c_par.end())
				{
					const types::Type* ta = visit(c_arg->getHead());
					if (!ta->coerceTo((*c_iter)))
					{
						error(e, "the type of exp_i doesn't match the type of param_i");
					}
					c_iter++;
					c_arg = c_arg->getRest();
				}
				//			if (c_arg is not null && c_par is null )
				//					report an error : too many arguments provided
				if (c_arg == NULL && c_iter != c_par.end())
				{
					error(e, "the # of expressions doesn't match the # of parameters");
				}
				//			if (c_arg is null && c_par is not null )
				//					report an error : too few arguments provided
				if (c_arg != NULL && c_iter == c_par.end())
				{
					error(e, "the # of expressions doesn't match the # of parameters");
				}
			}
			//		return the result type of the function (can be found in t)
			return t;
		}

		/*
		1.	check if fname is defined by looking up the symbol table
		2.	if fname is not defined, report an error, and return INT
		3.	if fname is defined, get its data type, say t
		4.	if t is not FUNCTION, report an error and return INT;
		convert t to FUNCTION *.
		5.	Let c_arg refers to the first argument (argument list can be found in CallExp)
		Let c_par refers to the first parameter (parameter list can be found in FUNCTION)
		6.	repeat as long as both c_arg and c_par are not NULL
		perform type checking on c_arg and get its type, see ta
		if ( ta is not compatible with type of c_par )
		report an error
		update c_arg to refer to next argument
		update c_par to refer to next parameter
		end repeat
		7.	if (c_arg is not null && c_par is null )
		report an error: too many arguments provided
		8.	if (c_arg is null && c_par is not null )
		report an error: too few arguments provided
		9.	return the result type of the function (can be found in t)
		*/

	}

	const types::Type* TypeChecking::visit(const SeqExp *e)
	{
		//add your implementation here
		const types::Type*	t = NULL;
		const absyn::ExpList* list = e->getList();
		while (list != NULL)
		{
			t = visit(list->getHead());
			list = list->getRest();
		}
		return t;
		//syntax: exp1; exp2; exp3; ....; expn
		/*
		Algorithm:
		for each expression exp_i in the list
		perform type checking on exp_i and save its data type to t
		return t;
		*/
	}

	//This function checks type compatibility in an assignment statement
	const types::Type* TypeChecking::visit(const AssignExp *e)
	{
		//add your implementation here
		const types::Type*	t = visit(e->getVar());
		const types::Type*	te = visit(e->getExp());
		if (t->coerceTo(te) == false || te->coerceTo(t) == false)
		{
			error(e, "The types are not compatible");
		}
		return new types::VOID();
		//syntax: lvalue := exp
		/*
		Algorithm:
		1.	perform type checking on lvalue and save its data type to t
		2.	perform type checking on exp and save its data type to te
		3.	if ( te is NOT compatible with t )
		report an error
		4.	return VOID
		*/
	}

	//This function tests for errors in an if statement
	const types::Type* TypeChecking::visit(const IfExp *e)
	{
		//add your implementation here
		const types::Type*	t = visit(e->getTest());
		if (dynamic_cast<const types::INT *>(t) != NULL)
		{
			error(e, "Test must be of type: INT");
		}
		const types::Type*	t1 = visit(e->getThenClause());
		if (e->getElseClause() == NULL)
		{
			if (dynamic_cast<const types::VOID *>(t1) != NULL)
			{
				error(e, "Then clause must be of type: VOID");
			}
			return new types::VOID();
		}
		else
		{
			const types::Type*	t2 = visit(e->getElseClause());
			if (t1->coerceTo(t2) == true)
			{
				return t2->actual();
			}
			else if (t2->coerceTo(t1) == true)
			{
				return t1->actual();
			}
			if (t1->coerceTo(t2) == false && t2->coerceTo(t1) == false)
			{
				error(e, "These statements are not of compatible types");
				return t1->actual();
			}
		}
		//const types::Type*	t2 = visit(e->getElseClause());
		//if (dynamic_cast<const types::VOID *>(t2) == NULL)

		//syntax: if test then
		//				exp1
		//			else
		//				exp2

		/*
		Algorithm:
		1.	perform type checking on test and save its data type to t
		2.	if t is not INT, report an error
		3.	perform type checking on exp1 and save its data type to t1
		4.	if it is a if-then satement (no else-clause)
		if t1 is not VOID, report an error
		return VOID;
		5.	else (if-then-else expression)
		perform type checking on exp2 and save its data type to t2
		if t1 is compatible with t2
		return t2
		else if t2 is compatible with t1
		return t1
		else
		report an error;
		return t1
		*/

	}

	//This function checks for errors in while statements
	const types::Type* TypeChecking::visit(const WhileExp *e)
	{
		//add your implementation here
		const types::Type*	t = visit(e->getTest());
		if (dynamic_cast<const types::INT *>(t) != NULL)
		{
			error(e, "Test must be of type: INT");
		}
		const types::Type*	t1 = visit(e->getBody());
		if (dynamic_cast<const types::VOID *>(t) != NULL)
		{
			error(e, "Body must be of type: VOID");
		}
		return new types::VOID();
		//syntax: while test do exp1
		/*
		Algorithm:
		1.	perform type checking on test and save its data type to t
		2.	if t is not INT, report an error
		3.	perform type checking on exp1 and save its data type to t1
		4.	if t1 is not VOID, report an error
		5.	return VOID;
		*/
	}

	//This function tests for errors in for loops
	const types::Type* TypeChecking::visit(const ForExp *e)
	{
		//add your implementation here
		//syntax: for vname := exp1 to exp2 do exp3
		env.getVarEnv()->beginScope();
		const types::Type*	t1 = visit(e->getVar());
		if (env.getVarEnv()->contains(e->getVar()->getName()))
		{
			const types::Type*	t1 = visit(e->getVar());
			if (dynamic_cast<const types::INT *>(t1) != NULL)
			{
				error(e, "Test must be of type: INT");
			}
		}
		const types::Type*	t2 = visit(e->getHi());
		if (dynamic_cast<const types::INT *>(t2) != NULL)
		{
			error(e, "High must be of type: INT");
		}
		const types::Type*	t3 = visit(e->getBody());
		if (dynamic_cast<const types::VOID *>(t3) != NULL)
		{
			error(e, "Body must be of type: VOID");
		}
		env.getVarEnv()->endScope();
		return new types::VOID();
		/*
		Algorithm:
		1.	Create a new scope for var/function symbol table
		2.	Perform type checking on (vname := exp1), which is treated
		as a variable declaration
		3.	lookup var/function symbol table to find and save the data type of vname
		to t1;
		4.	if t1 is not INT, report an error
		5.	Perform type checking on exp2, and save its data type to t2
		6.	if t2 is not INT, report an error
		7.	Perform type checking on exp3, and save its data type to t3
		8.	if t3 is not VOID, report an error
		9.	end the scope of var/function symbol table
		10.	return VOID;
		*/
	}

	//This function checks for break expression errors
	const types::Type* TypeChecking::visit(const BreakExp *e)
	{
		//add your implementation here
		return new types::VOID();
		/*Algorithm:
		return VOID if you don't want bonus points.
		*/
	}

	//This function detects errors in let expressions
	const types::Type* TypeChecking::visit(const LetExp *e)
	{
		//add your implementation here
		env.getVarEnv()->beginScope();
		env.getTypeEnv()->beginScope();
		if (e->getDecs() != NULL)
		{
			const DecList* dec_list = e->getDecs();
			const Dec* dec1 = dec_list->getHead();
			while (dec_list != NULL)
			{
				visit(dec1);
				dec_list = dec_list->getRest();
				if (dec_list != NULL)
				{
					dec1 = dec_list->getHead();
				}
			}
		}
		const types::Type* t = visit(e->getBody());
		env.getVarEnv()->endScope();
		env.getTypeEnv()->endScope();
		return t;
		//syntax: let decls in exps end
		/*
		Algorithm:
		1.	Create a new scope for var/function symbol table
		2.	Create a new scope for type symbol table
		3.	for each decl in the declaration list
		perform type checking on the decl
		4.	Perform type checking on exps and save its data type to t
		5.	if t is an VOID, report an error (???)
		6.	end scope of both symbol tables
		7.	return t;

		*/
	}

	//This function checks for errors with array declarations
	const types::Type* TypeChecking::visit(const ArrayExp *e)
	{
		//add your implementation here

		if (!env.getTypeEnv()->contains(e->getType()))
		{
			error(e, "array_type doesn't exist");
		}
		else
		{
			const types::Type* t = env.getTypeEnv()->lookup(e->getType()).info->actual();
			if (dynamic_cast <const types::ARRAY *>(t) == NULL)
			{
				error(e, "t is not ARRAY");
				return new types::ARRAY(new types::INT());
			}
			const types::Type* t1 = visit(e->getSize());
			if (dynamic_cast <const types::INT *>(t1) == NULL)
			{
				error(e, "t1 is not INT");
			}
			const types::Type* t2 = visit(e->getInit());
			if (!t2->coerceTo(t))
			{
				error(e, "t2 is not compatible");
			}
			else
			{
				return t;
			}
		}
		//syntax: array_type [exp1] of exp2
		/*
		Algorithm:
		1.	if array_type exists.
		If it doesn't exist, report an error;
		Let t be ARRAY of INT
		2.	else
		lookup type symbol table to find and save its type
		to t;
		if t is not ARRAY,
		report an error;
		Let t be ARRAY of INT
		3.	perform type checking on exp1 and save its type to t1
		4.	if t1 is not INT, report an error
		5.	perform type checking on exp2 and save its type to t2
		6.	if t2 is not compatible to ((ARRAY *)t)->getElement();
		report an error
		7.	return t;
		*/
		//return new types::INT();
	}

	/*	const types::Type* TypeChecking::visit(const FunctionDec *d)
	{
	//add your implementation
	//syntax: function fname(p1:type1, ..., pn:typen) : rtype = exp1
	}
	*/

	//This function checks for errors in declaring an variable
	const types::Type* TypeChecking::visit(const VarDec *d)
	{
		//add your implementation here
		if (env.getVarEnv()->localContains(d->getName()))
		{
			error(d, "vname cannot be defined locally");
		}
		if (d->getType() != NULL)
		{
			if (!env.getTypeEnv()->contains(d->getType()->getName()))
			{
				error(d, "Type does not exitst in the type symbol table");
			}
			else
			{
				const types::Type *tt = env.getTypeEnv()->lookup(d->getType()->getName()).info;
				const types::Type* t1 = visit(d->getInit());
				if (t1->coerceTo(tt) == false)
				{
					error(d, "Type and initialization are not compatible");
				}
				insertVar(d->getName(), SymTabEntry(env.getVarEnv()->getLevel(), (types::Type*)t1, d));
			}
		}
		else
		{
			const types::Type* t1 = visit(d->getInit());
			insertVar(d->getName(), SymTabEntry(env.getVarEnv()->getLevel(), (types::Type*)t1, d));
		}
		return NULL;


		// syntax: var vname : Type = exp1
		/*
		Algorithm:
		1.	if vname is defined locally  (use localContains function)
		report an error
		2.	if Type is provided
		Let tt be INT
		if Type doesn't exist in type symbol table
		report an error
		else
		lookup type symbol table to find and save
		its type information to tt;
		Perform type checking on exp1 and save its type to t1
		if t1 is not compatible with tt
		report an error
		insert vname into the var/function symbol table
		3.	else (Type is not provided)
		Perform type checking on exp1 and save its type to t1
		insert vname into the var/function symbol table
		4.	return NULL;
		*/
	}

	const types::Type* TypeChecking::visit(const TypeDec *d)
	{
		const types::Type*		type;
		types::NAME*			name = new types::NAME(d->getName());

		//find type redefine in the consecutive type declarations 
		const absyn::TypeDec*	td = d->getNext();
		while (td != NULL) {
			if (td->getName() == d->getName())
				error(td, "type redefined");
			td = td->getNext();
		}

		name->bind(new types::INT());	//just for avoiding the self loop, later it
										//will be replaced by actual value

		insertType(d->getName(), SymTabEntry(env.getVarEnv()->getLevel(), name, d));

		if (d->getNext() != NULL)
			visit(d->getNext());
		type = visit(d->getTy());

		name->bind((types::Type *)type);
		env.getTypeEnv()->lookup(d->getName()) = SymTabEntry(env.getVarEnv()->getLevel(),
			name,
			d);

		if (name->isLoop()) {
			error(d, "illegal cycle found in type definition");
			name->bind(new types::INT());
		}
		return NULL;

	}


	const types::Type* TypeChecking::visit(const NameTy *t)
	{
		if (!(env.getTypeEnv()->contains(t->getName())))
		{
			error(t, "undefined type name");
			return new types::INT();
		}

		return env.getTypeEnv()->lookup(t->getName()).info;
	}

	/*	const types::Type* TypeChecking::visit(const RecordTy *t)
	{
	const absyn::FieldList*		fl = t->getFields();

	if ( fl == NULL ) {
	//empty record
	return new types::RECORD( "", NULL, NULL );
	}
	else {
	types::RECORD		*r = NULL, *tail = NULL, *head = NULL;

	while ( fl != NULL ) {
	if ( !env.getTypeEnv()->contains(fl->getType()) )
	r = new types::RECORD(	fl->getName(),
	new types::INT(),
	NULL );
	else
	r = new types::RECORD(	fl->getName(),
	env.getTypeEnv()->lookup(fl->getType()).info,
	NULL );
	if ( head == NULL )
	head = tail = r;
	else {
	tail->setRest(r);
	tail = r;
	}
	fl = fl->getRest();
	}
	return head;
	}
	}
	*/
	const types::Type* TypeChecking::visit(const ArrayTy *t)
	{
		if (!(env.getTypeEnv()->contains(t->getName())))
		{
			error(t, "undefined type");
			return new types::INT();
		}

		return new types::ARRAY(env.getTypeEnv()->lookup(t->getName()).info);
	}



} // end of namespace semantics



  /*
  Bonus points:
  1. Break expression
  algorithm:
  1. create a symbol table say lv (lv is actually a member data of class TypeChecking;
  2. everytime entering a loop:
  create a new scope for lv,
  insert breakSign into lv, its data type is INT
  3. everytime exiting a loop;
  destroy the scope for lv
  4. everytime entering a function declaration
  create a new scope for lv,
  insert breakSign into lv, its data type is VOID
  5. everytime exiting a function;
  destroy the scope for lv
  6. in visit(BreakExp)
  lookup lv symbol table to find the definition of breakSign
  and get its data type t

  if t is VOID, report an error

  2. No modification to loop variable
  algorithm:
  1. Everytime entering a for loop
  create a new scope for lv
  insert the loop variable into lv
  2. Every time leaving a for loop
  destroy the scope for lv
  3. In visit(AssignExp)
  if Var in the assignment expression is a simple var
  retrieve information (say v1) of var from the var/function symbol table
  retrieve information (say v2) of var from the lv symbol table
  if v1 and v2 points to the same node in the AbstractSyntaxTree,
  report an error

  */
