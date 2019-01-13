#pragma once
#include "ErrorMsg.h"
#include "Env.h"
#include "RuntimeStack.h"

using namespace absyn;

namespace interpreter
{

	class Interpreter 
	{
	private:
		symbol::Env					env;	//symbol tables
		runtime::RuntimeStack		renv;	//runtime environment
		ErrorMsg					*errormsg;

		class BreakExpException
		{};

	public:
		Interpreter(ErrorMsg *r)
			: errormsg(r)
		{}

		const runtime::VarEntry interp(const Absyn *v);

		const runtime::VarEntry interp(const Exp *e);
		const runtime::VarEntry interp(const OpExp *e);
		const runtime::VarEntry interp(const VarExp *e);
		const runtime::VarEntry interp(const NilExp *e);
		const runtime::VarEntry interp(const IntExp *e);
		const runtime::VarEntry interp(const StringExp *e);
		const runtime::VarEntry interp(const CallExp *e);
		const runtime::VarEntry interp(const RecordExp *e);
		const runtime::VarEntry interp(const SeqExp *e);
		const runtime::VarEntry interp(const AssignExp *e);
		const runtime::VarEntry interp(const IfExp *e);
		const runtime::VarEntry interp(const WhileExp *e);
		const runtime::VarEntry interp(const ForExp *e);
		const runtime::VarEntry interp(const BreakExp *e);
		const runtime::VarEntry interp(const LetExp *e);
		const runtime::VarEntry interp(const ArrayExp *e);

		void interp(const FunctionDec *d);
		void interp(const VarDec *d);
		void interp(const TypeDec *d);
		void interp(const Dec *d);

		types::Type* interp(const NameTy *t);
		types::Type* interp(const RecordTy *t);
		types::Type* interp(const ArrayTy *t);
		types::Type* interp(const Ty *t);

		runtime::VarEntry& interp(const Var *v);
		runtime::VarEntry& interp(const SimpleVar *v);
		runtime::VarEntry& interp(const FieldVar *v);
		runtime::VarEntry& interp(const SubscriptVar *v);

	};
} // end of namespace semantics
