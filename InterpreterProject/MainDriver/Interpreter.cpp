#include "Interpreter.h"

using namespace symbol;

namespace interpreter
{
	const runtime::VarEntry Interpreter::interp(const Absyn *v)
	{
		if ( dynamic_cast<const Exp *>(v) != NULL )
			return interp( dynamic_cast<const Exp *>(v) );
		else
			throw runtime_error("invalid node");
	}

	const runtime::VarEntry Interpreter::interp(const Exp *e)
	{
		if (dynamic_cast<const OpExp*>(e) != NULL)			
			return interp((const OpExp*)e);
		else if (dynamic_cast<const VarExp*>(e) != NULL)	
			return interp((const VarExp*)e);
		else if (dynamic_cast<const NilExp*>(e) != NULL)	
			return interp((const NilExp*)e);
		else if (dynamic_cast<const IntExp*>(e) != NULL)	
			return interp((const IntExp*)e);
		else if (dynamic_cast<const StringExp*>(e) != NULL) 
			return interp((const StringExp*)e);
		else if (dynamic_cast<const CallExp*>(e) != NULL)	
			return interp((const CallExp*)e);
		else if (dynamic_cast<const RecordExp*>(e) != NULL) 
			return interp((const RecordExp*)e);
		else if (dynamic_cast<const SeqExp*>(e) != NULL)	
			return interp((const SeqExp*)e);
		else if (dynamic_cast<const AssignExp*>(e) != NULL) 
			return interp((const AssignExp*)e);
		else if (dynamic_cast<const IfExp*>(e) != NULL)		
			return interp((const IfExp*)e);
		else if (dynamic_cast<const WhileExp*>(e) != NULL)	
			return interp((const WhileExp*)e);
		else if (dynamic_cast<const ForExp*>(e) != NULL)	
			return interp((const ForExp*)e);
		else if (dynamic_cast<const BreakExp*>(e) != NULL)	
			return interp((const BreakExp*)e);
		else if (dynamic_cast<const LetExp*>(e) != NULL)	
			return interp((const LetExp*)e);
		else if (dynamic_cast<const ArrayExp*>(e) != NULL)	
			return interp((const ArrayExp*)e);
		else 
			throw new runtime_error("ExpType.interp(Exp*)");
	}

	runtime::VarEntry& Interpreter::interp(const Var *v)
	{
		if (dynamic_cast<const SimpleVar *>(v) != NULL)			
			return interp((const SimpleVar *) v);
		else if (dynamic_cast<const FieldVar *>(v) != NULL)		
			return interp((const FieldVar *) v);
		else if (dynamic_cast<const SubscriptVar *>(v) != NULL) 
			return interp((const SubscriptVar *)v);
		else 
			throw new runtime_error("ExpType.interp(Var*)");
	}

	runtime::VarEntry& Interpreter::interp(const SimpleVar *v)
	{
		return renv.lookup(v->getName());
	}

	runtime::VarEntry& Interpreter::interp(const FieldVar *v)
	{
		/* Not supported */
		throw runtime_error("Record data type not supported!");
	}

	runtime::VarEntry& Interpreter::interp(const SubscriptVar *v)
	{
		/* Not supported */
		throw runtime_error("Array data type not supported!");
	}

	const runtime::VarEntry Interpreter::interp(const OpExp *e)
	{
		runtime::VarEntry left = interp(e->getLeft());
		runtime::VarEntry right = interp(e->getRight());

		if (e->getOper() == 0) //Plus
		{
			return runtime::VarEntry(left.ival + right.ival);
		}
		else if (e->getOper() == 1) //Minus
		{
			return runtime::VarEntry(left.ival - right.ival);
		}
		else if (e->getOper() == 2) //Times
		{
			return runtime::VarEntry(left.ival * right.ival);
		}
		else if (e->getOper() == 3) //Divide
		{
			return runtime::VarEntry(left.ival / right.ival);
		}
		else if (e->getOper() == 4) //EQ
		{
			return runtime::VarEntry(left.ival == right.ival);
		}
		else if (e->getOper() == 5) //NEQ
		{
			return runtime::VarEntry(left.ival != right.ival);
		}
		else if (e->getOper() == 6) //LT
		{
			return runtime::VarEntry(left.ival < right.ival);
		}
		else if (e->getOper() == 7) //LE
		{
			return runtime::VarEntry(left.ival <= right.ival);
		}
		else if (e->getOper() == 8) //GT
		{
			return runtime::VarEntry(left.ival > right.ival);
		}
		else if (e->getOper() == 9) //GE
		{
			return runtime::VarEntry(left.ival >= right.ival);
		}
	}

	const runtime::VarEntry Interpreter::interp(const VarExp *e)
	{
		return interp(e->getVar());
	}

	const runtime::VarEntry Interpreter::interp(const NilExp *e)
	{
		throw runtime_error("Nil is not supported");
	}

	const runtime::VarEntry Interpreter::interp(const IntExp *e)
	{
		return runtime::VarEntry( e->getValue() );
	}

	const runtime::VarEntry Interpreter::interp(const StringExp *e)
	{
		return runtime::VarEntry( e->getValue() );
	}

	/* The implementation of interp(CallExp *) is provided by the instructor */
	const runtime::VarEntry Interpreter::interp(const CallExp *e)
	{
		symbol::SymTabEntry	fd = env.getVarEnv()->lookup(e->getFunc());
		types::FUNCTION*	f = dynamic_cast<types::FUNCTION *>(fd.info);
		const absyn::FunctionDec *node = dynamic_cast<const absyn::FunctionDec *>(fd.node);

		//handle specially if it is a built-in function
		//currently only print functions are considered
		if ( f->getFuncName() == "print" && node == NULL && fd.level == 0 )
		{	//reserved function
			runtime::VarEntry	value;

			//print function has only one parameter
			value = interp( e->getArgs()->getHead() );
			cout << value.sval;
			return runtime::VarEntry(); //return VOID
		} else if ( f->getFuncName() == "iprint" && node == NULL && fd.level == 0 )
		{	//reserved function
			runtime::VarEntry	value;

			//print function has only one parameter
			value = interp( e->getArgs()->getHead() );
			cout << value.ival;
			return runtime::VarEntry(); //return VOID
		}

		const absyn::ExpList		*el = e->getArgs();
		const absyn::FieldList		*fl = node->getParams();
		vector<string>				paramList;
		vector<runtime::VarEntry>	valueList;

		//push all arguments into the runtime stack
		while ( (el != NULL) && (fl != NULL) ) {
			runtime::VarEntry	value;
			
			value = interp( el->getHead() );
			paramList.push_back( fl->getName() );
			valueList.push_back( value );

			el = el->getRest();
			fl = fl->getRest();
		}

		renv.push(&fd);		//create a new activation record
		for(unsigned int i=0; i<paramList.size(); ++i)
			renv.insert( paramList[i], valueList[i] );

		const absyn::Exp*		body = node->getBody();
		runtime::VarEntry		result;

		result = interp( body );
		
		renv.pop();	//pop the topmost activation record
		return result;
	}

	const runtime::VarEntry Interpreter::interp(const RecordExp *e)
	{
		throw runtime_error("Record is not supported");
	}

	const runtime::VarEntry Interpreter::interp(const SeqExp *e)
	{
		const absyn::ExpList *list = e->getList();
		runtime::VarEntry head;

		while (list != NULL)
		{
			head = interp(list->getHead());
			list = list->getRest();
		}
		return head;
	}

	const runtime::VarEntry Interpreter::interp(const AssignExp *e)
	{
		return interp(e->getVar()) = interp(e->getExp());
	}

	const runtime::VarEntry Interpreter::interp(const IfExp *e)
	{
		if (interp(e->getTest()).ival != 0)
		{
			return interp(e->getThenClause());
		}
		else if (e->getElseClause() != NULL)
		{
			return interp(e->getElseClause());
		}
		return runtime::VarEntry();
	}

	const runtime::VarEntry Interpreter::interp(const WhileExp *e)
	{
		while (interp(e->getTest()).ival != 0)
		{
			interp(e->getBody());
		}
		return runtime::VarEntry();
	}

	const runtime::VarEntry Interpreter::interp(const ForExp *e)
	{
		env.getVarEnv()->beginScope();
		renv.beginScope();

		interp(e->getVar());

		for (int i = renv.lookup(e->getVar()->getName()).ival ; i <= interp(e->getHi()).ival; i++)
		{
			try
			{
				interp(e->getBody());
				renv.update(e->getVar()->getName(), i + 1);
			}
			catch (BreakExpException)
			{
				break;
			}
		}

		env.getVarEnv()->endScope();
		renv.endScope();

		return runtime::VarEntry();
	}

	const runtime::VarEntry Interpreter::interp(const BreakExp *e)
	{
		throw BreakExpException();
	}

	const runtime::VarEntry Interpreter::interp(const LetExp *e)
	{
		env.getVarEnv()->beginScope();
		renv.beginScope();

		const absyn::DecList* list = e->getDecs();
		while (list != NULL)
		{
			interp(list->getHead());
			list = list->getRest();
		}
		runtime::VarEntry rt = interp(e->getBody());

		env.getVarEnv()->endScope();
		renv.endScope();

		return rt;
	}

	const runtime::VarEntry Interpreter::interp(const ArrayExp *e)
	{
		throw runtime_error("Array data type supported currently!");
	}

	void Interpreter::interp(const FunctionDec *d)
	{
		const absyn::FieldList*		fl = d->getParams();

		//all all function names in the list to the symbol table first
		vector<const types::Type *>		params;

		
		fl = d->getParams();
		//generating FUNCTION according to the parameters of the function
		while ( fl != NULL ) {
			if ( env.getTypeEnv()->contains(fl->getType()) )
				params.push_back( env.getTypeEnv()->lookup(fl->getType()).info );
			fl = fl->getRest();
		}

		types::FUNCTION*		f;
		if ( d->getResult() == NULL )
			f = new types::FUNCTION(d->getName(), params, new types::VOID());
		else
			f = new types::FUNCTION(d->getName(), params, (types::Type *)interp(d->getResult())->actual() ); //function
		env.getVarEnv()->insert( d->getName(), SymTabEntry(env.getVarEnv()->getLevel(), f, d) );	//push function signature to the symbol table
		

		if ( d->getNext() != NULL )
			interp( d->getNext() );

		return;
	}

	void Interpreter::interp(const VarDec *d)
	{
		runtime::VarEntry		init = interp( d->getInit() );
		types::Type				*ty;

		if ( d->getType() == NULL ) {
			if ( init.isInt() )
				ty = new types::INT();
			else if ( init.isString() )
				ty = new types::STRING();
			else
				throw runtime_error("Data types not supported!");
			env.getVarEnv()->insert(d->getName(), SymTabEntry(env.getVarEnv()->getLevel(), ty, d));	
		}
		else {
			ty = interp( d->getType() );
			if ( ty != NULL )
				ty = (types::Type *)ty->actual();
			env.getVarEnv()->insert(d->getName(), SymTabEntry(env.getVarEnv()->getLevel(), ty, d));	
		}

		renv.insert(d->getName(), init);
		return;
	}

	void Interpreter::interp(const TypeDec *d)
	{
		types::Type*		type;
		types::NAME*		name = new types::NAME( d->getName() );
	
		name->bind( new types::INT() );	//just for avoiding the self loop, later it
							//will be replaced by actual value
		
		env.getTypeEnv()->insert(d->getName(), SymTabEntry(env.getTypeEnv()->getLevel(), name, d));	

		if ( d->getNext() != NULL )
			interp( d->getNext() );
		type = interp( d->getTy() );

		name->bind( (types::Type *)type );
		env.getTypeEnv()->lookup(d->getName()) = SymTabEntry(env.getTypeEnv()->getLevel(), name);	

		return;
	}

	void Interpreter::interp(const Dec *d)
	{
		if (dynamic_cast<const TypeDec *>(d) != NULL)			
			return interp((const TypeDec *) d);
		else if (dynamic_cast<const VarDec *>(d) != NULL)		
			return interp((const VarDec *) d);
		else if (dynamic_cast<const FunctionDec *>(d) != NULL)	
			return interp((const FunctionDec *)d);
		else 
			throw new runtime_error("ExpType.interp(Dec*)");
	}

	types::Type* Interpreter::interp(const NameTy *t)
	{
		return env.getTypeEnv()->lookup(t->getName()).info;
	}

	types::Type* Interpreter::interp(const RecordTy *t)
	{
		throw runtime_error("Record data type not supported!");
	}

	types::Type* Interpreter::interp(const ArrayTy *t)
	{
		throw runtime_error("Array data type not supported!");
	}

	types::Type* Interpreter::interp(const Ty *t)
	{
		if (dynamic_cast<const NameTy *>(t) != NULL)			
			return interp((const NameTy *) t);
		else if (dynamic_cast<const ArrayTy *>(t) != NULL)		
			return interp((const ArrayTy *) t);
		else if (dynamic_cast<const RecordTy *>(t) != NULL)		
			return interp((const RecordTy *)t);
		else 
			throw new runtime_error("ExpType.interp(Ty*)");
	}
} // end of namespace semantics
